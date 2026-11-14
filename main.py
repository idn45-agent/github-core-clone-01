#!/usr/bin/env python3
"""github-core-clone-01: a standalone GitHub-compatible git forge.

One file, Python 3.13 standard library only, no git binary. Sections:

  1. Logical clock + git object hashing (real git blob/tree/commit shas)
  2. The in-memory store (users, repos, branches, commits, issues, labels)
  3. HTTP plumbing (auth, JSON bodies, pagination, protocol headers)
  4. REST v3: root/meta, repositories, git refs, branches, commits, contents
  5. REST v3: labels, issues, comments
  6. Stubs for the later builders: pulls (in section 5's numbering space),
     GraphQL v4 (/api/graphql), MCP (/mcp), git smart HTTP (/<o>/<r>.git/...)
  7. The trial lifecycle (register, /done polling) and standalone mode

Determinism: no wall clock and no randomness anywhere in a response. Times
come from a logical clock (a fixed base instant plus a per-store tick) and
every id is a sequential counter, so a replayed request sequence produces
byte-identical answers.
"""

import base64
import hashlib
import json
import os
import threading
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, unquote, urlsplit

# ---------------------------------------------------------------------------
# 1. Logical clock and git object hashing
# ---------------------------------------------------------------------------

BASE_INSTANT = datetime(2024, 1, 1, tzinfo=timezone.utc)
BASE_UNIX = int(BASE_INSTANT.timestamp())
AUTHOR_NAME = "Forge Bot"
AUTHOR_EMAIL = "bot@forge.local"
INSTALLED_VERSION = "3.10.0"
API_SCOPES = "repo, read:org"


def iso_at(tick: int) -> str:
    """The ISO-8601 instant `tick` seconds after the base instant."""
    return (BASE_INSTANT + timedelta(seconds=tick)).strftime("%Y-%m-%dT%H:%M:%SZ")


def git_hash(kind: str, payload: bytes) -> str:
    """The git object id: sha1 of '<kind> <len>' + NUL + payload."""
    head = f"{kind} {len(payload)}".encode() + b"\x00"
    return hashlib.sha1(head + payload).hexdigest()


def blob_sha(data: bytes) -> str:
    return git_hash("blob", data)


def tree_sha(files: dict) -> str:
    """The real git tree id for a flat {path: blob_sha} snapshot.

    Builds nested tree objects exactly as git does: entries sorted with
    directories compared as if their name ended in '/', file mode 100644,
    directory mode 40000, each entry '<mode> <name>' + NUL + raw sha.
    """
    nested: dict = {}
    for path, sha in files.items():
        parts = path.split("/")
        node = nested
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = sha

    def build(node: dict) -> str:
        entries = []
        for name in sorted(node, key=lambda n: n + "/" if isinstance(node[n], dict) else n):
            value = node[name]
            if isinstance(value, dict):
                entries.append((name, "40000", build(value)))
            else:
                entries.append((name, "100644", value))
        payload = b"".join(
            f"{mode} {name}".encode() + b"\x00" + bytes.fromhex(sha)
            for name, mode, sha in entries
        )
        return git_hash("tree", payload)

    return build(nested)


def commit_sha(tree: str, parents: list, message: str, tick: int) -> str:
    """The real git commit id for the given tree, parents and message."""
    stamp = BASE_UNIX + tick
    lines = [f"tree {tree}"]
    lines += [f"parent {parent}" for parent in parents]
    lines.append(f"author {AUTHOR_NAME} <{AUTHOR_EMAIL}> {stamp} +0000")
    lines.append(f"committer {AUTHOR_NAME} <{AUTHOR_EMAIL}> {stamp} +0000")
    payload = ("\n".join(lines) + "\n\n" + message).encode()
    return git_hash("commit", payload)


# ---------------------------------------------------------------------------
# 2. The in-memory store
# ---------------------------------------------------------------------------


class Label:
    def __init__(self, store, name: str, color: str, description=None):
        self.id = store.next_id()
        self.name = name
        self.color = color or "ededed"
        self.description = description
        self.created_tick = store.tick()

    def view(self) -> dict:
        return {
            "id": self.id,
            "node_id": f"LA_{self.id}",
            "name": self.name,
            "color": self.color,
            "default": False,
            "description": self.description,
        }


class Commit:
    def __init__(self, sha, files, parents, message, tick):
        self.sha = sha
        self.files = files          # snapshot: {path: blob_sha}
        self.parents = parents      # [sha, ...]
        self.message = message
        self.tick = tick

    def view(self, repo) -> dict:
        stamp = iso_at(self.tick)
        person = {"name": AUTHOR_NAME, "email": AUTHOR_EMAIL, "date": stamp}
        return {
            "sha": self.sha,
            "node_id": f"C_{self.sha}",
            "commit": {
                "author": person,
                "committer": dict(person),
                "message": self.message,
                "tree": {"sha": tree_sha(self.files)},
                "comment_count": 0,
            },
            "author": {"login": repo.owner_login},
            "committer": {"login": repo.owner_login},
            "parents": [{"sha": parent} for parent in self.parents],
        }


class Issue:
    def __init__(self, store, number, title, body, labels):
        self.id = store.next_id()
        self.number = number
        self.title = title
        self.body = body
        self.state = "open"
        self.labels = labels        # [Label, ...]
        self.comments = []          # [Comment, ...]
        self.created_tick = store.tick()
        self.updated_tick = self.created_tick
        self.closed_tick = None

    def view(self, repo) -> dict:
        out = {
            "id": self.id,
            "node_id": f"I_{self.id}",
            "number": self.number,
            "title": self.title,
            "body": self.body,
            "state": self.state,
            "labels": [label.view() for label in self.labels],
            "user": {"login": repo.owner_login, "id": 1, "type": "User"},
            "comments": len(self.comments),
            "created_at": iso_at(self.created_tick),
            "updated_at": iso_at(self.updated_tick),
            "closed_at": iso_at(self.closed_tick) if self.closed_tick is not None else None,
        }
        return out


class Comment:
    def __init__(self, store, body):
        self.id = store.next_id()
        self.body = body
        self.created_tick = store.tick()
        self.updated_tick = self.created_tick

    def view(self, repo) -> dict:
        return {
            "id": self.id,
            "node_id": f"IC_{self.id}",
            "body": self.body,
            "user": {"login": repo.owner_login, "id": 1, "type": "User"},
            "created_at": iso_at(self.created_tick),
            "updated_at": iso_at(self.updated_tick),
        }


class Repo:
    def __init__(self, store, name, private, description):
        self.id = store.next_id()
        self.name = name
        self.private = bool(private)
        self.description = description
        self.default_branch = "main"
        self.created_tick = store.tick()
        self.updated_tick = self.created_tick
        self.branches = {}          # branch name -> tip commit sha
        self.commits = {}           # sha -> Commit
        self.blobs = {}             # blob sha -> bytes
        self.labels = {}            # name -> Label
        self.issues = {}            # number -> Issue
        self.pulls = {}             # number -> Pull (later builder)
        self.next_number = 1        # shared by issues and pulls, as on GitHub

    @property
    def owner_login(self) -> str:
        return STORE.viewer_login or "user"

    def tip(self, branch: str):
        return self.branches.get(branch)

    def files_at(self, branch: str) -> dict:
        tip = self.branches.get(branch)
        if tip is None or tip not in self.commits:
            return {}
        return dict(self.commits[tip].files)

    def make_commit(self, branch: str, files: dict, message: str) -> Commit:
        parent = self.branches.get(branch)
        parents = [parent] if parent in self.commits else []
        tick = STORE.tick()
        sha = commit_sha(tree_sha(files), parents, message, tick)
        commit = Commit(sha, dict(files), parents, message, tick)
        self.commits[sha] = commit
        self.branches[branch] = sha
        self.updated_tick = tick
        return commit

    def history(self, tip_sha: str) -> list:
        """Commits reachable from a tip, newest first (first-parent walk
        with a visited set, so merges list each commit once)."""
        out, seen, stack = [], set(), [tip_sha]
        while stack:
            sha = stack.pop()
            if sha in seen or sha not in self.commits:
                continue
            seen.add(sha)
            commit = self.commits[sha]
            out.append(commit)
            stack.extend(reversed(commit.parents))
        out.sort(key=lambda c: -c.tick)
        return out

    def view(self, base_url: str) -> dict:
        owner = self.owner_login
        return {
            "id": self.id,
            "node_id": f"R_{self.id}",
            "name": self.name,
            "full_name": f"{owner}/{self.name}",
            "private": self.private,
            "owner": {"login": owner, "id": 1, "type": "User"},
            "description": self.description,
            "fork": False,
            "homepage": None,
            "size": 0,
            "stargazers_count": 0,
            "watchers_count": 0,
            "language": None,
            "has_issues": True,
            "has_projects": True,
            "has_downloads": True,
            "has_wiki": True,
            "has_pages": False,
            "forks_count": 0,
            "archived": False,
            "disabled": False,
            "open_issues_count": sum(1 for i in self.issues.values() if i.state == "open"),
            "license": None,
            "topics": [],
            "visibility": "private" if self.private else "public",
            "default_branch": self.default_branch,
            "created_at": iso_at(self.created_tick),
            "updated_at": iso_at(self.updated_tick),
            "pushed_at": iso_at(self.updated_tick),
            "html_url": f"{base_url}/{owner}/{self.name}",
            "git_url": f"git://{base_url.split('://', 1)[-1]}/{owner}/{self.name}.git",
            "clone_url": f"{base_url}/{owner}/{self.name}.git",
        }


class Store:
    """Everything the forge knows. One instance per process."""

    def __init__(self):
        self.lock = threading.RLock()
        self.clock = 0              # logical-clock ticks (seconds)
        self.ids = 0                # sequential object ids
        self.requests = 0           # sequential X-GitHub-Request-Id values
        self.viewer_login = None    # learned from the first owner path served
        self.repos = {}             # name -> Repo (single token, one viewer)

    def tick(self) -> int:
        self.clock += 1
        return self.clock

    def next_id(self) -> int:
        self.ids += 1
        return self.ids

    def request_id(self) -> str:
        self.requests += 1
        return f"{self.requests:08X}"


STORE = Store()

# ---------------------------------------------------------------------------
# 3. HTTP plumbing
# ---------------------------------------------------------------------------

EXPECTED_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")


class ApiError(Exception):
    def __init__(self, status: int, message: str):
        super().__init__(message)
        self.status = status
        self.message = message


def not_found() -> ApiError:
    return ApiError(404, "Not Found")


class Ctx:
    """One request: parsed path/query/body plus response helpers."""

    def __init__(self, handler):
        self.handler = handler
        split = urlsplit(handler.path)
        self.raw_path = split.path
        self.segments = [unquote(s) for s in split.path.split("/") if s != ""]
        self.query = {k: v[0] for k, v in parse_qs(split.query).items()}
        self.method = handler.command
        self.body = None          # parsed JSON body (dict or None)
        self.raw_body = b""
        host = handler.headers.get("Host") or "127.0.0.1"
        self.base_url = f"http://{host}"

    def load_body(self):
        """Read and JSON-parse the body; a malformed body is a 400."""
        length = int(self.handler.headers.get("Content-Length") or 0)
        self.raw_body = self.handler.rfile.read(length) if length > 0 else b""
        if not self.raw_body:
            self.body = {}
            return
        try:
            parsed = json.loads(self.raw_body.decode("utf-8"))
        except Exception:
            raise ApiError(400, "Problems parsing JSON")
        self.body = parsed if isinstance(parsed, dict) else {}

    def authed(self) -> bool:
        if not EXPECTED_TOKEN:
            return True     # standalone dev mode: no token configured
        return self.handler.headers.get("Authorization") == f"Bearer {EXPECTED_TOKEN}"

    def send(self, status: int, payload=None, extra_headers=None):
        body = b"" if payload is None else json.dumps(payload).encode()
        handler = self.handler
        handler.send_response(status)
        handler.send_header("Content-Type", "application/json; charset=utf-8")
        handler.send_header("X-GitHub-Request-Id", STORE.request_id())
        handler.send_header("X-OAuth-Scopes", API_SCOPES)
        if extra_headers:
            for name, value in extra_headers.items():
                handler.send_header(name, value)
        handler.send_header("Content-Length", str(len(body)))
        handler.end_headers()
        if body:
            handler.wfile.write(body)


def paginate(ctx: Ctx, items: list):
    """GitHub list pagination: page/per_page plus a Link header whose
    rel="next" chain reaches every item exactly once."""
    try:
        per_page = int(ctx.query.get("per_page", "30"))
    except ValueError:
        per_page = 30
    per_page = max(1, min(per_page, 100))
    try:
        page = int(ctx.query.get("page", "1"))
    except ValueError:
        page = 1
    page = max(1, page)
    total = len(items)
    start = (page - 1) * per_page
    chunk = items[start:start + per_page]
    last_page = max(1, (total + per_page - 1) // per_page)

    def page_url(n: int) -> str:
        params = dict(ctx.query)
        params["page"] = str(n)
        params["per_page"] = str(per_page)
        qs = "&".join(f"{k}={v}" for k, v in sorted(params.items()))
        return f"{ctx.base_url}{ctx.raw_path}?{qs}"

    links = []
    if page < last_page:
        links.append(f'<{page_url(page + 1)}>; rel="next"')
        links.append(f'<{page_url(last_page)}>; rel="last"')
    if page > 1:
        links.append(f'<{page_url(1)}>; rel="first"')
        links.append(f'<{page_url(page - 1)}>; rel="prev"')
    headers = {"Link": ", ".join(links)} if links else None
    return chunk, headers


def resolve_repo(owner: str, name: str) -> Repo:
    """The repo `name` for the token's viewer; any other owner is a 404.

    The viewer's login is learned from the first owner segment that
    addresses one of the viewer's repositories (the checks always read
    the owner's own path before probing a foreign one).
    """
    repo = STORE.repos.get(name)
    if repo is None:
        raise not_found()
    if STORE.viewer_login is None:
        STORE.viewer_login = owner
    if owner != STORE.viewer_login:
        raise not_found()
    return repo


# ---------------------------------------------------------------------------
# 4. REST v3: root, meta, repositories, refs, branches, commits, contents
# ---------------------------------------------------------------------------


def api_root(ctx: Ctx):
    base = f"{ctx.base_url}/api/v3"
    ctx.send(200, {
        "current_user_url": f"{base}/user",
        "repository_url": f"{base}/repos/{{owner}}/{{repo}}",
        "issue_search_url": f"{base}/search/issues",
        "emojis_url": f"{base}/emojis",
        "notifications_url": f"{base}/notifications",
    })


def api_meta(ctx: Ctx):
    ctx.send(200, {
        "verifiable_password_authentication": False,
        "ssh_key_fingerprints": {},
        "installed_version": INSTALLED_VERSION,
        "authentication_token": {"scopes": ["repo", "read:org"]},
    })


def create_repo(ctx: Ctx):
    name = ctx.body.get("name")
    if not name or not isinstance(name, str):
        raise ApiError(422, "Validation Failed: name is required")
    if name in STORE.repos:
        raise ApiError(422, "Validation Failed: name already exists on this account")
    repo = Repo(STORE, name, ctx.body.get("private", False), ctx.body.get("description"))
    if isinstance(ctx.body.get("default_branch"), str) and ctx.body["default_branch"]:
        repo.default_branch = ctx.body["default_branch"]
    STORE.repos[name] = repo
    ctx.send(201, repo.view(ctx.base_url))


def get_repo(ctx: Ctx, owner: str, name: str):
    ctx.send(200, resolve_repo(owner, name).view(ctx.base_url))


def patch_repo(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    if "description" in ctx.body:
        repo.description = ctx.body["description"]
    if "private" in ctx.body:
        repo.private = bool(ctx.body["private"])
    if "name" in ctx.body and ctx.body["name"] != repo.name:
        new = ctx.body["name"]
        STORE.repos.pop(repo.name, None)
        repo.name = new
        STORE.repos[new] = repo
    if "default_branch" in ctx.body:
        repo.default_branch = ctx.body["default_branch"]
    repo.updated_tick = STORE.tick()
    ctx.send(200, repo.view(ctx.base_url))


def delete_repo(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    STORE.repos.pop(repo.name, None)
    ctx.send(204)


def list_user_repos(ctx: Ctx):
    repos = [STORE.repos[name] for name in sorted(STORE.repos, key=lambda n: STORE.repos[n].id)]
    chunk, headers = paginate(ctx, repos)
    ctx.send(200, [repo.view(ctx.base_url) for repo in chunk], headers)


def create_ref(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    ref = ctx.body.get("ref", "")
    sha = ctx.body.get("sha", "")
    if not ref.startswith("refs/heads/"):
        raise ApiError(422, "Validation Failed: ref must be a branch ref")
    branch = ref[len("refs/heads/"):]
    repo.branches[branch] = sha
    ctx.send(201, {
        "ref": ref,
        "node_id": f"REF_{branch}",
        "url": f"{ctx.base_url}/api/v3/repos/{owner}/{name}/git/refs/heads/{branch}",
        "object": {"sha": sha, "type": "commit",
                   "url": f"{ctx.base_url}/api/v3/repos/{owner}/{name}/git/commits/{sha}"},
    })


def list_branches(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    out = []
    for branch in sorted(repo.branches, key=lambda b: (b != repo.default_branch, b)):
        out.append({
            "name": branch,
            "commit": {"sha": repo.branches[branch],
                       "url": f"{ctx.base_url}/api/v3/repos/{owner}/{name}/commits/{repo.branches[branch]}"},
            "protected": False,
        })
    chunk, headers = paginate(ctx, out)
    ctx.send(200, chunk, headers)


def list_commits(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    ref = ctx.query.get("sha") or repo.default_branch
    tip = repo.branches.get(ref, ref if ref in repo.commits else None)
    if tip is None:
        ctx.send(200, [])
        return
    commits = [commit.view(repo) for commit in repo.history(tip)]
    chunk, headers = paginate(ctx, commits)
    ctx.send(200, chunk, headers)


def _branch_of(ctx: Ctx, repo: Repo, body_branch=None) -> str:
    branch = body_branch or ctx.query.get("ref") or repo.default_branch
    return branch


def _content_file_view(repo: Repo, branch: str, path: str) -> dict:
    files = repo.files_at(branch)
    sha = files[path]
    data = repo.blobs[sha]
    wrapped = "\n".join(
        base64.b64encode(data).decode()[i:i + 60]
        for i in range(0, max(1, len(base64.b64encode(data))), 60)
    ) + "\n"
    return {
        "type": "file",
        "encoding": "base64",
        "size": len(data),
        "name": path.split("/")[-1],
        "path": path,
        "content": wrapped,
        "sha": sha,
    }


def _content_dir_view(repo: Repo, branch: str, path: str) -> list:
    files = repo.files_at(branch)
    prefix = f"{path}/" if path else ""
    entries = {}
    for file_path, sha in files.items():
        if not file_path.startswith(prefix):
            continue
        rest = file_path[len(prefix):]
        head, _, _tail = rest.partition("/")
        if _tail:
            sub = prefix + head
            entries[head] = {"type": "dir", "name": head, "path": sub,
                             "sha": tree_sha({p: s for p, s in files.items()
                                              if p == sub or p.startswith(sub + "/")})}
        else:
            entries[head] = {"type": "file", "name": head, "path": file_path, "sha": sha,
                             "size": len(repo.blobs[sha])}
    return [entries[name] for name in sorted(entries)]


def get_contents(ctx: Ctx, owner: str, name: str, path: str):
    repo = resolve_repo(owner, name)
    branch = _branch_of(ctx, repo)
    files = repo.files_at(branch)
    if path and path in files:
        ctx.send(200, _content_file_view(repo, branch, path))
        return
    if path == "" or any(p.startswith(path + "/") for p in files):
        ctx.send(200, _content_dir_view(repo, branch, path))
        return
    raise not_found()


def put_contents(ctx: Ctx, owner: str, name: str, path: str):
    repo = resolve_repo(owner, name)
    branch = _branch_of(ctx, repo, ctx.body.get("branch"))
    if branch not in repo.branches and repo.branches:
        raise not_found()
    try:
        data = base64.b64decode(ctx.body.get("content", ""), validate=False)
    except Exception:
        raise ApiError(422, "Validation Failed: content is not valid base64")
    files = repo.files_at(branch)
    existing = files.get(path)
    sent_sha = ctx.body.get("sha")
    if existing is not None:
        if sent_sha is None:
            raise ApiError(422, "Validation Failed: sha is required when updating a file")
        if sent_sha != existing:
            raise ApiError(409, f"{path} has changed since it was read")
        status = 200
    else:
        status = 201
    sha = blob_sha(data)
    repo.blobs[sha] = data
    files[path] = sha
    commit = repo.make_commit(branch, files, ctx.body.get("message", ""))
    view = _content_file_view(repo, branch, path)
    ctx.send(status, {"content": view, "commit": {"sha": commit.sha,
                                                  "message": commit.message,
                                                  "tree": {"sha": tree_sha(files)}}})


def delete_contents(ctx: Ctx, owner: str, name: str, path: str):
    repo = resolve_repo(owner, name)
    branch = _branch_of(ctx, repo, ctx.body.get("branch"))
    files = repo.files_at(branch)
    if path not in files:
        raise not_found()
    sent_sha = ctx.body.get("sha")
    if sent_sha is not None and sent_sha != files[path]:
        raise ApiError(409, f"{path} has changed since it was read")
    del files[path]
    commit = repo.make_commit(branch, files, ctx.body.get("message", ""))
    ctx.send(200, {"content": None, "commit": {"sha": commit.sha,
                                               "message": commit.message,
                                               "tree": {"sha": tree_sha(files)}}})

# ---------------------------------------------------------------------------
# 5. REST v3: labels, issues, comments
# ---------------------------------------------------------------------------


def create_label(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    label_name = ctx.body.get("name")
    if not label_name:
        raise ApiError(422, "Validation Failed: name is required")
    if label_name in repo.labels:
        raise ApiError(422, "Validation Failed: name has already been taken")
    label = Label(STORE, label_name, ctx.body.get("color", "ededed"),
                  ctx.body.get("description"))
    repo.labels[label_name] = label
    ctx.send(201, label.view())


def list_labels(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    labels = [repo.labels[n].view() for n in sorted(repo.labels)]
    chunk, headers = paginate(ctx, labels)
    ctx.send(200, chunk, headers)


def _labels_for(repo: Repo, names) -> list:
    out = []
    for label_name in names or []:
        label = repo.labels.get(label_name)
        if label is None:
            raise ApiError(422, f"Validation Failed: label '{label_name}' does not exist")
        out.append(label)
    return out


def create_issue(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    labels = _labels_for(repo, ctx.body.get("labels"))
    number = repo.next_number
    repo.next_number += 1
    issue = Issue(STORE, number, ctx.body.get("title"), ctx.body.get("body"), labels)
    repo.issues[number] = issue
    ctx.send(201, issue.view(repo))


def list_issues(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    state = ctx.query.get("state", "open")
    items = [i for i in repo.issues.values() if state == "all" or i.state == state]
    direction = ctx.query.get("direction", "desc")
    items.sort(key=lambda i: i.created_tick, reverse=(direction != "asc"))
    chunk, headers = paginate(ctx, items)
    ctx.send(200, [issue.view(repo) for issue in chunk], headers)


def _issue(repo: Repo, number: str) -> Issue:
    try:
        issue = repo.issues.get(int(number))
    except ValueError:
        issue = None
    if issue is None:
        raise not_found()
    return issue


def get_issue(ctx: Ctx, owner: str, name: str, number: str):
    repo = resolve_repo(owner, name)
    ctx.send(200, _issue(repo, number).view(repo))


def patch_issue(ctx: Ctx, owner: str, name: str, number: str):
    repo = resolve_repo(owner, name)
    issue = _issue(repo, number)
    if "title" in ctx.body:
        issue.title = ctx.body["title"]
    if "body" in ctx.body:
        issue.body = ctx.body["body"]
    if "labels" in ctx.body:
        issue.labels = _labels_for(repo, ctx.body["labels"])
    if "state" in ctx.body:
        issue.state = ctx.body["state"]
        issue.closed_tick = STORE.tick() if issue.state == "closed" else None
    issue.updated_tick = STORE.tick()
    ctx.send(200, issue.view(repo))


def create_comment(ctx: Ctx, owner: str, name: str, number: str):
    repo = resolve_repo(owner, name)
    issue = _issue(repo, number)
    comment = Comment(STORE, ctx.body.get("body"))
    issue.comments.append(comment)
    ctx.send(201, comment.view(repo))


def list_comments(ctx: Ctx, owner: str, name: str, number: str):
    repo = resolve_repo(owner, name)
    issue = _issue(repo, number)
    chunk, headers = paginate(ctx, issue.comments)
    ctx.send(200, [comment.view(repo) for comment in chunk], headers)


# ---------------------------------------------------------------------------
# 6. Router, stubs for the later builders, and the HTTP handler
# ---------------------------------------------------------------------------


def route_rest(ctx: Ctx, rest: list):
    """Dispatch under /api/v3; `rest` is the path after the prefix."""
    method = ctx.method
    if not rest:
        if method == "GET":
            return api_root(ctx)
        raise not_found()
    if rest == ["meta"] and method == "GET":
        return api_meta(ctx)
    if rest == ["user"] and method == "GET":
        login = STORE.viewer_login or "user"
        return ctx.send(200, {"login": login, "id": 1, "type": "User"})
    if rest == ["user", "repos"]:
        if method == "POST":
            return create_repo(ctx)
        if method == "GET":
            return list_user_repos(ctx)
        raise not_found()
    if len(rest) >= 3 and rest[0] == "repos":
        owner, name, tail = rest[1], rest[2], rest[3:]
        if not tail:
            if method == "GET":
                return get_repo(ctx, owner, name)
            if method == "PATCH":
                return patch_repo(ctx, owner, name)
            if method == "DELETE":
                return delete_repo(ctx, owner, name)
            raise not_found()
        if tail == ["git", "refs"] and method == "POST":
            return create_ref(ctx, owner, name)
        if tail == ["branches"] and method == "GET":
            return list_branches(ctx, owner, name)
        if tail == ["commits"] and method == "GET":
            return list_commits(ctx, owner, name)
        if tail and tail[0] == "contents":
            path = "/".join(tail[1:])
            if method == "GET":
                return get_contents(ctx, owner, name, path)
            if method == "PUT":
                return put_contents(ctx, owner, name, path)
            if method == "DELETE":
                return delete_contents(ctx, owner, name, path)
            raise not_found()
        if tail == ["labels"]:
            if method == "POST":
                return create_label(ctx, owner, name)
            if method == "GET":
                return list_labels(ctx, owner, name)
            raise not_found()
        if tail == ["issues"]:
            if method == "POST":
                return create_issue(ctx, owner, name)
            if method == "GET":
                return list_issues(ctx, owner, name)
            raise not_found()
        if len(tail) == 2 and tail[0] == "issues":
            if method == "GET":
                return get_issue(ctx, owner, name, tail[1])
            if method == "PATCH":
                return patch_issue(ctx, owner, name, tail[1])
            raise not_found()
        if len(tail) == 3 and tail[0] == "issues" and tail[2] == "comments":
            if method == "POST":
                return create_comment(ctx, owner, name, tail[1])
            if method == "GET":
                return list_comments(ctx, owner, name, tail[1])
            raise not_found()
        # pulls and everything else: the pulls builder fills these in.
        raise not_found()
    raise not_found()


def dispatch(ctx: Ctx):
    segments = ctx.segments
    if segments == ["healthz"] and ctx.method == "GET":
        return ctx.send(200, {"ok": True})
    if ctx.method in ("POST", "PUT", "PATCH", "DELETE"):
        ctx.load_body()
    if len(segments) >= 2 and segments[0] == "api" and segments[1] == "v3":
        if not ctx.authed():
            raise ApiError(401, "Bad credentials")
        return route_rest(ctx, segments[2:])
    if segments == ["api", "graphql"] or segments == ["mcp"]:
        if not ctx.authed():
            raise ApiError(401, "Bad credentials")
        raise not_found()   # stub: the GraphQL / MCP builders fill these in
    # /<owner>/<repo>.git/... git smart HTTP: the git builder fills this in.
    raise not_found()


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):   # keep stdout clean
        pass

    def _handle(self):
        ctx = Ctx(self)
        try:
            with STORE.lock:
                dispatch(ctx)
        except ApiError as err:
            ctx.send(err.status, {"message": err.message})
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as err:    # never answer HTML or hang
            try:
                ctx.send(500, {"message": f"Internal Server Error: {err}"})
            except Exception:
                pass

    do_GET = _handle
    do_POST = _handle
    do_PUT = _handle
    do_PATCH = _handle
    do_DELETE = _handle
    do_HEAD = _handle


# ---------------------------------------------------------------------------
# 7. The trial lifecycle
# ---------------------------------------------------------------------------


def _env_json(method: str, url: str, payload=None):
    data = None if payload is None else json.dumps(payload).encode()
    req = urllib.request.Request(url, data=data, method=method,
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=10) as resp:
        return json.loads(resp.read().decode() or "{}")


def _register(env_url: str, port: int):
    """POST /register, retrying with backoff; a 409 means we already won."""
    delay = 0.25
    for _ in range(40):
        try:
            _env_json("POST", f"{env_url}/register", {"port": port})
            return
        except urllib.error.HTTPError as err:
            if err.code == 409:
                return
        except Exception:
            pass
        time.sleep(delay)
        delay = min(delay * 2, 2.0)


def _poll_done(env_url: str, server: ThreadingHTTPServer):
    delay = 0.25
    while True:
        try:
            if _env_json("GET", f"{env_url}/done").get("done"):
                break
        except Exception:
            pass
        time.sleep(delay)
        delay = min(delay * 1.5, 1.0)
    threading.Thread(target=server.shutdown, daemon=True).start()


def main():
    server = ThreadingHTTPServer(("0.0.0.0", 0), Handler)
    port = server.server_address[1]
    env_url = os.environ.get("MAKEFUN_ENV_URL", "")
    if env_url:
        _register(env_url, port)
        threading.Thread(target=_poll_done, args=(env_url, server), daemon=True).start()
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass
        server.server_close()
    else:
        # Standalone: serve forever (local development and smoke tests).
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()
