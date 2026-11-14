#!/usr/bin/env python3
"""github-core-clone-01: a standalone GitHub-compatible git forge.

One file, Python 3.13 standard library only, no git binary. Sections:

  1. Logical clock + git object hashing (real git blob/tree/commit shas)
  2. The in-memory store (users, repos, branches, commits, issues, labels)
  3. HTTP plumbing (auth, JSON bodies, pagination, protocol headers)
  4. REST v3: root/meta, repositories, git refs, branches, commits, contents
  5. REST v3: labels, issues, comments
  5b. REST v3: pull requests (create/list/get/files/merge over the odb)
  6. Stubs for the later builders: GraphQL v4 (/api/graphql), MCP (/mcp);
     git smart HTTP (/<o>/<r>.git/...) lives in its own sections below
  7. The trial lifecycle (register, /done polling) and standalone mode

Determinism: no wall clock and no randomness anywhere in a response. Times
come from a logical clock (a fixed base instant plus a per-store tick) and
every id is a sequential counter, so a replayed request sequence produces
byte-identical answers.
"""

import base64
import difflib
import hashlib
import json
import os
import struct
import threading
import time
import urllib.error
import urllib.request
import zlib
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


class Pull:
    """A pull request: head branch into base branch, sharing the repo's
    issue/PR number counter. The head/base shas are the branch tips
    resolved at creation; merging is computed from the live tips."""

    def __init__(self, store, number, title, body, head_ref, head_sha,
                 base_ref, base_sha):
        self.id = store.next_id()
        self.number = number
        self.title = title
        self.body = body
        self.state = "open"
        self.head_ref = head_ref
        self.head_sha = head_sha
        self.base_ref = base_ref
        self.base_sha = base_sha
        self.merged = False
        self.merged_tick = None
        self.merge_commit_sha = None
        self.created_tick = store.tick()
        self.updated_tick = self.created_tick
        self.closed_tick = None

    def view(self, repo) -> dict:
        return {
            "id": self.id,
            "node_id": f"PR_{self.id}",
            "number": self.number,
            "state": self.state,
            "title": self.title,
            "body": self.body,
            "user": {"login": repo.owner_login, "id": 1, "type": "User"},
            "head": {"ref": self.head_ref, "sha": self.head_sha,
                     "label": self.head_ref},
            "base": {"ref": self.base_ref, "sha": self.base_sha,
                     "label": self.base_ref},
            "merged": self.merged,
            "merged_at": iso_at(self.merged_tick) if self.merged_tick is not None else None,
            "merge_commit_sha": self.merge_commit_sha,
            "mergeable": pull_mergeable(repo, self),
            "closed_at": iso_at(self.closed_tick) if self.closed_tick is not None else None,
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
        self.odb = {}               # object id -> (kind, payload): every git object
        self.tags = {}              # tag name -> object id (refs/tags/<name>)
        self.extra_refs = {}        # full ref name -> object id (other refs/*)
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
        materialize_rest_commit(self, commit)
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
# 5b. REST v3: pull requests
# ---------------------------------------------------------------------------


def _ancestor_distances(repo: Repo, tip: str) -> dict:
    """sha -> shortest parent-walk distance from `tip` (inclusive)."""
    dist = {tip: 0}
    queue = [tip]
    while queue:
        sha = queue.pop(0)
        commit = repo.commits.get(sha)
        if commit is None:
            continue
        for parent in commit.parents:
            if parent not in dist:
                dist[parent] = dist[sha] + 1
                queue.append(parent)
    return dist


def merge_base(repo: Repo, a: str, b: str):
    """The best common ancestor of two commits, or None."""
    if a not in repo.commits or b not in repo.commits:
        return None
    ancestors = _ancestor_distances(repo, a)
    seen, queue, best = set(), [b], None
    while queue:
        sha = queue.pop(0)
        if sha in seen:
            continue
        seen.add(sha)
        if sha in ancestors:
            if best is None or ancestors[sha] < ancestors[best]:
                best = sha
            continue
        commit = repo.commits.get(sha)
        if commit is not None:
            queue.extend(commit.parents)
    return best


def three_way_merge(base: dict, ours: dict, theirs: dict):
    """File-level three-way merge over {path: blob_sha} snapshots.

    Returns the merged snapshot, or None when both sides changed the
    same path to different blobs relative to the merge base."""
    merged = {}
    for path in set(base) | set(ours) | set(theirs):
        b, o, t = base.get(path), ours.get(path), theirs.get(path)
        if o == t:
            winner = o
        elif b == o:
            winner = t
        elif b == t:
            winner = o
        else:
            return None
        if winner is not None:
            merged[path] = winner
    return merged


def _merge_plan(repo: Repo, base_tip: str, head_tip: str):
    """(merge_base_sha, merged snapshot) for base<-head, or None on
    conflict. A head already contained in the base merges trivially."""
    base_sha = merge_base(repo, base_tip, head_tip)
    if base_sha is None:
        return None
    base_files = repo.commits[base_sha].files
    merged = three_way_merge(base_files, repo.commits[base_tip].files,
                             repo.commits[head_tip].files)
    if merged is None:
        return None
    return base_sha, merged


def pull_mergeable(repo: Repo, pull: Pull):
    """GitHub-style mergeable flag: True/False for open pulls whose two
    tips are known, None once merged (or when it cannot be computed)."""
    if pull.merged:
        return None
    base_tip = repo.branches.get(pull.base_ref, pull.base_sha)
    head_tip = repo.branches.get(pull.head_ref, pull.head_sha)
    if base_tip not in repo.commits or head_tip not in repo.commits:
        return None
    return _merge_plan(repo, base_tip, head_tip) is not None


def _resolve_pull_ref(repo: Repo, value, field: str):
    """Resolve a create-pull head/base: a branch name, an 'owner:branch'
    label, or a bare commit sha. Returns (ref label, tip sha)."""
    if not isinstance(value, str) or not value:
        raise ApiError(422, f"Validation Failed: {field} is required")
    ref = value.split(":", 1)[-1] if ":" in value else value
    if ref in repo.branches:
        return ref, repo.branches[ref]
    if value in repo.commits:
        return value, value
    raise ApiError(422, f"Validation Failed: {field} '{value}' does not exist")


def _pull(repo: Repo, number: str) -> Pull:
    try:
        pull = repo.pulls.get(int(number))
    except (ValueError, TypeError):
        pull = None
    if pull is None:
        raise not_found()
    return pull


def create_pull(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    head_ref, head_sha = _resolve_pull_ref(repo, ctx.body.get("head"), "head")
    base_ref, base_sha = _resolve_pull_ref(repo, ctx.body.get("base"), "base")
    number = repo.next_number
    repo.next_number += 1
    title = ctx.body.get("title")
    body = ctx.body.get("body")
    pull = Pull(STORE, number,
                title if isinstance(title, str) else "",
                body if isinstance(body, str) else "",
                head_ref, head_sha, base_ref, base_sha)
    repo.pulls[number] = pull
    ctx.send(201, pull.view(repo))


def list_pulls(ctx: Ctx, owner: str, name: str):
    repo = resolve_repo(owner, name)
    state = ctx.query.get("state", "open")
    items = [p for p in repo.pulls.values()
             if state == "all" or p.state == state]
    direction = ctx.query.get("direction", "desc")
    items.sort(key=lambda p: p.created_tick, reverse=(direction != "asc"))
    chunk, headers = paginate(ctx, items)
    ctx.send(200, [pull.view(repo) for pull in chunk], headers)


def get_pull(ctx: Ctx, owner: str, name: str, number: str):
    repo = resolve_repo(owner, name)
    ctx.send(200, _pull(repo, number).view(repo))


def _blob_lines(repo: Repo, sha) -> list:
    if sha is None:
        return []
    data = repo.blobs.get(sha, b"")
    return data.decode("utf-8", "replace").splitlines()


def pull_files(repo: Repo, pull: Pull) -> list:
    """The changed-path list: merge-base tree diffed against head tip."""
    head_tip = repo.branches.get(pull.head_ref, pull.head_sha)
    if head_tip not in repo.commits:
        return []
    base_sha = merge_base(repo, pull.base_sha, head_tip) or pull.base_sha
    base_files = repo.commits[base_sha].files if base_sha in repo.commits else {}
    head_files = repo.commits[head_tip].files
    out = []
    for path in sorted(set(base_files) | set(head_files)):
        old, new = base_files.get(path), head_files.get(path)
        if old == new:
            continue
        if old is None:
            status = "added"
        elif new is None:
            status = "removed"
        else:
            status = "modified"
        old_lines, new_lines = _blob_lines(repo, old), _blob_lines(repo, new)
        additions = deletions = 0
        matcher = difflib.SequenceMatcher(a=old_lines, b=new_lines,
                                          autojunk=False)
        for tag, i1, i2, j1, j2 in matcher.get_opcodes():
            if tag in ("insert", "replace"):
                additions += j2 - j1
            if tag in ("delete", "replace"):
                deletions += i2 - i1
        patch_lines = [f"--- a/{path}", f"+++ b/{path}"]
        for tag, i1, i2, j1, j2 in matcher.get_opcodes():
            if tag == "equal":
                continue
            patch_lines += [f"-{line}" for line in old_lines[i1:i2]]
            patch_lines += [f"+{line}" for line in new_lines[j1:j2]]
        entry = {
            "sha": new if new is not None else old,
            "filename": path,
            "status": status,
            "additions": additions,
            "deletions": deletions,
            "changes": additions + deletions,
            "patch": "\n".join(patch_lines),
        }
        out.append(entry)
    return out


def list_pull_files(ctx: Ctx, owner: str, name: str, number: str):
    repo = resolve_repo(owner, name)
    pull = _pull(repo, number)
    chunk, headers = paginate(ctx, pull_files(repo, pull))
    ctx.send(200, chunk, headers)


def merge_pull(ctx: Ctx, owner: str, name: str, number: str):
    repo = resolve_repo(owner, name)
    pull = _pull(repo, number)
    if pull.merged or pull.state != "open":
        raise ApiError(405, "Pull Request is not mergeable")
    base_tip = repo.branches.get(pull.base_ref, pull.base_sha)
    head_tip = repo.branches.get(pull.head_ref, pull.head_sha)
    plan = None
    if base_tip in repo.commits and head_tip in repo.commits:
        plan = _merge_plan(repo, base_tip, head_tip)
    if plan is None:
        raise ApiError(405, "Pull Request is not mergeable")
    _base_sha, merged_files = plan
    message = (f"Merge pull request #{pull.number} from {pull.head_ref}"
               f"\n\n{pull.title}")
    tick = STORE.tick()
    parents = [base_tip] if base_tip == head_tip else [base_tip, head_tip]
    sha = commit_sha(tree_sha(merged_files), parents, message, tick)
    commit = Commit(sha, dict(merged_files), parents, message, tick)
    repo.commits[sha] = commit
    materialize_rest_commit(repo, commit)
    repo.branches[pull.base_ref] = sha
    repo.updated_tick = tick
    pull.merged = True
    pull.merged_tick = tick
    pull.merge_commit_sha = sha
    pull.state = "closed"
    pull.closed_tick = tick
    pull.updated_tick = tick
    ctx.send(200, {"sha": sha, "merged": True,
                   "message": "Pull Request successfully merged"})


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
        if tail == ["pulls"]:
            if method == "POST":
                return create_pull(ctx, owner, name)
            if method == "GET":
                return list_pulls(ctx, owner, name)
            raise not_found()
        if len(tail) == 2 and tail[0] == "pulls":
            if method == "GET":
                return get_pull(ctx, owner, name, tail[1])
            raise not_found()
        if len(tail) == 3 and tail[0] == "pulls" and tail[2] == "files":
            if method == "GET":
                return list_pull_files(ctx, owner, name, tail[1])
            raise not_found()
        if len(tail) == 3 and tail[0] == "pulls" and tail[2] == "merge":
            if method == "PUT":
                return merge_pull(ctx, owner, name, tail[1])
            raise not_found()
        raise not_found()
    raise not_found()


def dispatch(ctx: Ctx):
    segments = ctx.segments
    if segments == ["healthz"] and ctx.method == "GET":
        return ctx.send(200, {"ok": True})
    if len(segments) >= 3 and segments[1].endswith(".git"):
        # Git smart HTTP bodies are binary pkt-lines, never JSON: route
        # before load_body() gets a chance to reject them.
        return route_git(ctx, segments[0], segments[1][:-4], segments[2:])
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
# 6b. Git smart HTTP: pkt-lines, packfiles, upload-pack and receive-pack
# ---------------------------------------------------------------------------

ZERO_OID = "0" * 40
GIT_KIND_CODES = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
GIT_CODE_KINDS = {code: kind for kind, code in GIT_KIND_CODES.items()}
GIT_KIND_ORDER = {"commit": 0, "tag": 1, "tree": 2, "blob": 3}
PKT_DELIM = b"0001"
PKT_FLUSH = b"0000"


def pkt_line(payload) -> bytes:
    """One pkt-line; None encodes the flush packet."""
    if payload is None:
        return PKT_FLUSH
    if isinstance(payload, str):
        payload = payload.encode()
    return f"{len(payload) + 4:04x}".encode() + payload


class PktReader:
    """Decode the pkt-lines at the front of a request body."""

    def __init__(self, data: bytes):
        self.data = data
        self.pos = 0

    def next(self):
        """('data', bytes) | ('delim',) | ('flush',) | None at end of input."""
        if self.pos >= len(self.data):
            return None
        head = self.data[self.pos:self.pos + 4]
        if len(head) < 4:
            raise ValueError("truncated pkt-line")
        try:
            size = int(head, 16)
        except ValueError:
            raise ValueError("malformed pkt-line length")
        if size == 0:
            self.pos += 4
            return ("flush",)
        if size == 1:
            self.pos += 4
            return ("delim",)
        if size == 2:
            self.pos += 4
            return ("response-end",)
        if size < 4 or self.pos + size > len(self.data):
            raise ValueError("pkt-line size out of range")
        payload = self.data[self.pos + 4:self.pos + size]
        self.pos += size
        return ("data", payload)

    def rest(self) -> bytes:
        return self.data[self.pos:]


# --- object payloads -------------------------------------------------------


def parse_tree_payload(payload: bytes):
    """[(mode, name, oid)] for a raw tree object."""
    entries = []
    pos = 0
    while pos < len(payload):
        space = payload.index(b" ", pos)
        mode = payload[pos:space].decode()
        nul = payload.index(b"\x00", space)
        name = payload[space + 1:nul].decode("utf-8", "replace")
        oid = payload[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        pos = nul + 21
    return entries


def parse_commit_payload(payload: bytes):
    head, _, message = payload.partition(b"\n\n")
    tree, parents = None, []
    for line in head.split(b"\n"):
        if line.startswith(b"tree "):
            tree = line[5:].decode()
        elif line.startswith(b"parent "):
            parents.append(line[7:].decode())
    return {"tree": tree, "parents": parents, "message": message}


def parse_tag_payload(payload: bytes):
    head = payload.split(b"\n\n", 1)[0]
    target, kind = None, None
    for line in head.split(b"\n"):
        if line.startswith(b"object "):
            target = line[7:].decode()
        elif line.startswith(b"type "):
            kind = line[5:].decode()
    return {"object": target, "type": kind}


def peel_object(repo: Repo, oid: str) -> str:
    """Follow tag objects to the first non-tag object."""
    seen = set()
    while oid in repo.odb and repo.odb[oid][0] == "tag" and oid not in seen:
        seen.add(oid)
        target = parse_tag_payload(repo.odb[oid][1])["object"]
        if target is None:
            break
        oid = target
    return oid


def build_tree_objects(repo: Repo, files: dict) -> str:
    """Store every tree object for a {path: blob_sha} snapshot in the odb,
    exactly as tree_sha hashes them; returns the root tree id."""
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
        sha = git_hash("tree", payload)
        repo.odb[sha] = ("tree", payload)
        return sha

    return build(nested)


def materialize_rest_commit(repo: Repo, commit: Commit):
    """Put a REST-created commit and everything it reaches into the odb,
    so the git layer can advertise and ship it."""
    for sha in commit.files.values():
        if sha not in repo.odb and sha in repo.blobs:
            repo.odb[sha] = ("blob", repo.blobs[sha])
    root = build_tree_objects(repo, commit.files)
    stamp = BASE_UNIX + commit.tick
    lines = [f"tree {root}"]
    lines += [f"parent {parent}" for parent in commit.parents]
    lines.append(f"author {AUTHOR_NAME} <{AUTHOR_EMAIL}> {stamp} +0000")
    lines.append(f"committer {AUTHOR_NAME} <{AUTHOR_EMAIL}> {stamp} +0000")
    payload = ("\n".join(lines) + "\n\n" + commit.message).encode()
    repo.odb[commit.sha] = ("commit", payload)


def tree_snapshot(repo: Repo, tree_oid: str, prefix: str = "") -> dict:
    """The {path: blob_sha} snapshot a tree object describes."""
    out: dict = {}
    obj = repo.odb.get(tree_oid)
    if obj is None or obj[0] != "tree":
        return out
    for mode, name, oid in parse_tree_payload(obj[1]):
        if mode == "40000":
            out.update(tree_snapshot(repo, oid, prefix + name + "/"))
        elif mode != "160000":      # gitlinks have no blob to snapshot
            out[prefix + name] = oid
    return out


# --- refs ------------------------------------------------------------------


def repo_refs(repo: Repo) -> dict:
    refs = {f"refs/heads/{name}": oid for name, oid in repo.branches.items()}
    refs.update({f"refs/tags/{name}": oid for name, oid in repo.tags.items()})
    refs.update(repo.extra_refs)
    return refs


def set_ref(repo: Repo, ref: str, oid):
    """Point `ref` at `oid`, or delete it when oid is None."""
    if ref.startswith("refs/heads/"):
        table, key = repo.branches, ref[len("refs/heads/"):]
    elif ref.startswith("refs/tags/"):
        table, key = repo.tags, ref[len("refs/tags/"):]
    else:
        table, key = repo.extra_refs, ref
    if oid is None:
        table.pop(key, None)
    else:
        table[key] = oid


def is_ancestor(repo: Repo, ancestor: str, descendant: str) -> bool:
    stack, seen = [descendant], set()
    while stack:
        oid = stack.pop()
        if oid == ancestor:
            return True
        if oid in seen or oid not in repo.odb or repo.odb[oid][0] != "commit":
            continue
        seen.add(oid)
        stack.extend(parse_commit_payload(repo.odb[oid][1])["parents"])
    return False


def integrate_repo_objects(repo: Repo):
    """Fold the odb back into the REST model: blobs become readable file
    content and every commit reachable from a ref gains a Commit record
    (ticks assigned parents-first so history lists children last)."""
    for oid, (kind, payload) in list(repo.odb.items()):
        if kind == "blob":
            repo.blobs.setdefault(oid, payload)
    missing, seen, stack = [], set(), []
    for target in repo_refs(repo).values():
        root = peel_object(repo, target)
        if root in repo.odb and repo.odb[root][0] == "commit":
            stack.append(root)
    while stack:
        oid = stack.pop()
        if oid in seen or oid in repo.commits or oid not in repo.odb:
            continue
        seen.add(oid)
        missing.append(oid)
        stack.extend(parse_commit_payload(repo.odb[oid][1])["parents"])
    missing_set = set(missing)
    done: set = set()
    remaining = list(missing)
    while remaining:
        progressed = False
        for oid in list(remaining):
            info = parse_commit_payload(repo.odb[oid][1])
            if any(p in missing_set and p not in done for p in info["parents"]):
                continue
            files = tree_snapshot(repo, info["tree"]) if info["tree"] else {}
            message = info["message"].decode("utf-8", "replace")
            repo.commits[oid] = Commit(oid, files, info["parents"], message,
                                       STORE.tick())
            done.add(oid)
            remaining.remove(oid)
            progressed = True
        if not progressed:
            break


# --- packfiles -------------------------------------------------------------


def pack_object_header(kind: str, size: int) -> bytes:
    code = GIT_KIND_CODES[kind]
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    out = bytearray()
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


def write_pack(objects) -> bytes:
    """A version-2 packfile of undeltified objects + its SHA-1 trailer."""
    objects = list(objects)
    body = bytearray(b"PACK" + struct.pack(">II", 2, len(objects)))
    for kind, payload in objects:
        body += pack_object_header(kind, len(payload))
        body += zlib.compress(payload)
    return bytes(body) + hashlib.sha1(bytes(body)).digest()


def _inflate_at(data: bytes, pos: int):
    obj = zlib.decompressobj()
    out = obj.decompress(data[pos:])
    if not obj.eof:
        raise ValueError("truncated zlib stream in pack")
    return out, len(data) - len(obj.unused_data)


def apply_delta(base: bytes, delta: bytes) -> bytes:
    pos = 0

    def read_varint() -> int:
        nonlocal pos
        value, shift = 0, 0
        while True:
            byte = delta[pos]
            pos += 1
            value |= (byte & 0x7F) << shift
            shift += 7
            if not byte & 0x80:
                return value

    if read_varint() != len(base):
        raise ValueError("delta base size mismatch")
    target_size = read_varint()
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            offset, size = 0, 0
            for i in range(4):
                if op & (1 << i):
                    offset |= delta[pos] << (8 * i)
                    pos += 1
            for i in range(3):
                if op & (0x10 << i):
                    size |= delta[pos] << (8 * i)
                    pos += 1
            out += base[offset:offset + (size or 0x10000)]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != target_size:
        raise ValueError("delta result size mismatch")
    return bytes(out)


def read_pack(data: bytes, external) -> dict:
    """Parse a packfile into {oid: (kind, payload)}, resolving OFS/REF
    deltas; `external(oid)` supplies bases a thin pack leaves out."""
    if len(data) < 12 + 20 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    version, count = struct.unpack(">II", data[4:12])
    if version not in (2, 3):
        raise ValueError(f"pack version {version}")
    if hashlib.sha1(data[:-20]).digest() != data[-20:]:
        raise ValueError("pack checksum mismatch")
    entries = []            # (offset, kind|None, base|None, raw)
    pos = 12
    for _ in range(count):
        start = pos
        byte = data[pos]
        pos += 1
        code = (byte >> 4) & 7
        size = byte & 0x0F
        shift = 4
        while byte & 0x80:
            byte = data[pos]
            pos += 1
            size |= (byte & 0x7F) << shift
            shift += 7
        if code == 6:                       # OFS_DELTA
            byte = data[pos]
            pos += 1
            offset = byte & 0x7F
            while byte & 0x80:
                byte = data[pos]
                pos += 1
                offset = ((offset + 1) << 7) | (byte & 0x7F)
            raw, pos = _inflate_at(data, pos)
            entries.append((start, None, ("ofs", start - offset), raw))
        elif code == 7:                     # REF_DELTA
            base_oid = data[pos:pos + 20].hex()
            pos += 20
            raw, pos = _inflate_at(data, pos)
            entries.append((start, None, ("ref", base_oid), raw))
        elif code in GIT_CODE_KINDS:
            raw, pos = _inflate_at(data, pos)
            if len(raw) != size:
                raise ValueError("pack object size mismatch")
            entries.append((start, GIT_CODE_KINDS[code], None, raw))
        else:
            raise ValueError(f"pack object type {code}")
    resolved: dict = {}
    by_offset: dict = {}
    pending = list(entries)
    while pending:
        progressed, remaining = False, []
        for start, kind, base, raw in pending:
            if kind is not None:
                base_kind, payload = kind, raw
            else:
                found = None
                if base[0] == "ofs" and base[1] in by_offset:
                    found = resolved[by_offset[base[1]]]
                elif base[0] == "ref":
                    found = resolved.get(base[1]) or external(base[1])
                if found is None:
                    remaining.append((start, kind, base, raw))
                    continue
                base_kind, payload = found[0], apply_delta(found[1], raw)
            oid = git_hash(base_kind, payload)
            resolved[oid] = (base_kind, payload)
            by_offset[start] = oid
            progressed = True
        if not progressed:
            raise ValueError("pack delta base is missing")
        pending = remaining
    return resolved


# --- fetch planning --------------------------------------------------------


def _tree_closure(repo: Repo, tree_oid: str, out: set):
    stack = [tree_oid]
    while stack:
        oid = stack.pop()
        if oid in out:
            continue
        obj = repo.odb.get(oid)
        if obj is None or obj[0] != "tree":
            continue
        out.add(oid)
        for mode, _name, child in parse_tree_payload(obj[1]):
            if mode == "40000":
                stack.append(child)
            elif mode != "160000":
                out.add(child)


def compute_fetch(repo: Repo, wants, haves, client_shallow, depth):
    """Plan a fetch: ({oid: (kind, payload)} to send, shallow, unshallow).

    Commit generations are counted from the wants (the tip is generation
    1); a depth limit includes generations 1..depth and reports the
    generation-`depth` commits as the new shallow boundary. The client's
    shallow commits cut the have-closure: their parents are not assumed
    to be held.
    """
    gens: dict = {}
    queue: list = []
    for want in wants:
        root = peel_object(repo, want)
        if root in repo.odb and repo.odb[root][0] == "commit" and root not in gens:
            gens[root] = 1
            queue.append(root)
    index = 0
    while index < len(queue):
        commit = queue[index]
        index += 1
        gen = gens[commit]
        if depth is not None and gen >= depth:
            continue
        for parent in parse_commit_payload(repo.odb[commit][1])["parents"]:
            if parent not in repo.odb:
                continue
            if parent not in gens or gens[parent] > gen + 1:
                gens[parent] = gen + 1
                queue.append(parent)

    want_objects: set = set()
    for want in wants:
        oid = want
        while oid in repo.odb and repo.odb[oid][0] == "tag":
            want_objects.add(oid)
            oid = parse_tag_payload(repo.odb[oid][1])["object"]
            if oid is None:
                break
        if oid in repo.odb and repo.odb[oid][0] != "commit":
            want_objects.add(oid)           # a directly wanted tree/blob
    for commit in gens:
        want_objects.add(commit)
        tree = parse_commit_payload(repo.odb[commit][1])["tree"]
        if tree:
            _tree_closure(repo, tree, want_objects)

    have_objects: set = set()
    stack = list(haves)
    while stack:
        oid = stack.pop()
        if oid in have_objects or oid not in repo.odb:
            continue
        have_objects.add(oid)
        kind, payload = repo.odb[oid]
        if kind == "commit":
            info = parse_commit_payload(payload)
            if info["tree"]:
                _tree_closure(repo, info["tree"], have_objects)
            if oid not in client_shallow:
                stack.extend(info["parents"])
        elif kind == "tag":
            target = parse_tag_payload(payload)["object"]
            if target:
                stack.append(target)

    send = {oid: repo.odb[oid] for oid in want_objects - have_objects
            if oid in repo.odb}
    shallow, unshallow = [], []
    if depth is not None:
        boundary = set()
        for commit, gen in gens.items():
            if gen != depth:
                continue
            parents = parse_commit_payload(repo.odb[commit][1])["parents"]
            if any(p in repo.odb and p not in gens for p in parents):
                boundary.add(commit)
                shallow.append(commit)
        for old in client_shallow:
            if old in gens and old not in boundary:
                unshallow.append(old)
    return send, shallow, unshallow


def pack_bytes_for(send: dict) -> bytes:
    items = sorted(send.items(),
                   key=lambda kv: (GIT_KIND_ORDER[kv[1][0]], kv[0]))
    return write_pack([kind_payload for _oid, kind_payload in items])


def sideband_packets(pack: bytes) -> bytes:
    out = bytearray()
    for start in range(0, len(pack), 32768):
        out += pkt_line(b"\x01" + pack[start:start + 32768])
    return bytes(out)


# --- smart HTTP handlers ---------------------------------------------------

UPLOAD_PACK_CAPS = (
    "multi_ack_detailed side-band-64k thin-pack ofs-delta shallow "
    "deepen-since deepen-not allow-tip-sha1-in-want "
    "allow-reachable-sha1-in-want agent=forge/1.0"
)
RECEIVE_PACK_CAPS = (
    "report-status delete-refs side-band-64k ofs-delta "
    "agent=forge/1.0"
)


def read_raw_body(ctx: Ctx) -> bytes:
    handler = ctx.handler
    if (handler.headers.get("Transfer-Encoding") or "").lower() == "chunked":
        chunks = []
        while True:
            size_line = handler.rfile.readline(65536).strip()
            size = int(size_line.split(b";")[0], 16)
            if size == 0:
                while True:
                    line = handler.rfile.readline(65536)
                    if line in (b"\r\n", b"\n", b""):
                        break
                break
            chunks.append(handler.rfile.read(size))
            handler.rfile.read(2)
        return b"".join(chunks)
    length = int(handler.headers.get("Content-Length") or 0)
    return handler.rfile.read(length) if length > 0 else b""


def send_raw(ctx: Ctx, status: int, body: bytes, content_type: str):
    handler = ctx.handler
    handler.send_response(status)
    handler.send_header("Content-Type", content_type)
    handler.send_header("Cache-Control", "no-cache, max-age=0, must-revalidate")
    handler.send_header("Content-Length", str(len(body)))
    handler.end_headers()
    if body:
        handler.wfile.write(body)


def route_git(ctx: Ctx, owner: str, name: str, tail: list):
    if not ctx.authed():
        raise ApiError(401, "Bad credentials")
    repo = resolve_repo(owner, name)
    try:
        if tail == ["info", "refs"] and ctx.method == "GET":
            return git_info_refs(ctx, repo)
        if tail == ["git-upload-pack"] and ctx.method == "POST":
            return git_upload_pack(ctx, repo)
        if tail == ["git-receive-pack"] and ctx.method == "POST":
            return git_receive_pack(ctx, repo)
    except ValueError as err:
        return send_raw(ctx, 400, f"error: {err}\n".encode(), "text/plain")
    raise not_found()


def git_info_refs(ctx: Ctx, repo: Repo):
    service = ctx.query.get("service", "")
    if service not in ("git-upload-pack", "git-receive-pack"):
        raise ApiError(400, "unknown service")
    wants_v2 = "version=2" in (ctx.handler.headers.get("Git-Protocol") or "")
    if service == "git-upload-pack" and wants_v2:
        lines = ["version 2", "agent=forge/1.0", "ls-refs=unborn",
                 "fetch=shallow", "object-format=sha1"]
        body = pkt_line(f"# service={service}\n") + PKT_FLUSH
        body += b"".join(pkt_line(line + "\n") for line in lines) + PKT_FLUSH
    else:
        body = pkt_line(f"# service={service}\n") + PKT_FLUSH
        body += v0_advertisement(repo, service)
    send_raw(ctx, 200, body, f"application/x-{service}-advertisement")


def v0_advertisement(repo: Repo, service: str) -> bytes:
    caps = UPLOAD_PACK_CAPS if service == "git-upload-pack" else RECEIVE_PACK_CAPS
    if service == "git-upload-pack":
        caps += f" symref=HEAD:refs/heads/{repo.default_branch}"
    refs = repo_refs(repo)
    lines = []
    if not refs:
        lines.append(f"{ZERO_OID} capabilities^{{}}\x00{caps}")
    else:
        head_oid = repo.branches.get(repo.default_branch, ZERO_OID)
        lines.append(f"{head_oid} HEAD\x00{caps}")
        for name in sorted(refs):
            oid = refs[name]
            lines.append(f"{oid} {name}")
            peeled = peel_object(repo, oid)
            if peeled != oid:
                lines.append(f"{peeled} {name}^{{}}")
    return b"".join(pkt_line(line + "\n") for line in lines) + PKT_FLUSH


def _v2_sections(body: bytes):
    """Split a protocol v2 request into (capability lines, argument lines)."""
    reader = PktReader(body)
    caps, args, section = [], [], "caps"
    while True:
        packet = reader.next()
        if packet is None or packet[0] == "flush":
            break
        if packet[0] == "delim":
            section = "args"
            continue
        if packet[0] != "data":
            continue
        line = packet[1].decode("utf-8", "replace").rstrip("\n")
        (caps if section == "caps" else args).append(line)
    return caps, args


def git_upload_pack(ctx: Ctx, repo: Repo):
    body = read_raw_body(ctx)
    proto = ctx.handler.headers.get("Git-Protocol") or ""
    if "version=2" in proto or body[4:].startswith(b"command="):
        caps, args = _v2_sections(body)
        command = caps[0] if caps else ""
        if command == "command=ls-refs":
            payload = ls_refs_response(repo, args)
        elif command == "command=fetch":
            payload = fetch_response_v2(repo, args)
        else:
            raise ValueError(f"unsupported v2 command {command!r}")
    else:
        payload = fetch_response_v0(repo, body)
    send_raw(ctx, 200, payload, "application/x-git-upload-pack-result")


def ls_refs_response(repo: Repo, args) -> bytes:
    peel = "peel" in args
    symrefs = "symrefs" in args
    unborn = "unborn" in args
    prefixes = [line[len("ref-prefix "):] for line in args
                if line.startswith("ref-prefix ")]

    def matches(name: str) -> bool:
        return not prefixes or any(name.startswith(p) for p in prefixes)

    refs = repo_refs(repo)
    head_ref = f"refs/heads/{repo.default_branch}"
    head_oid = repo.branches.get(repo.default_branch)
    out = []
    if matches("HEAD"):
        if head_oid is not None:
            line = f"{head_oid} HEAD"
            if symrefs:
                line += f" symref-target:{head_ref}"
            out.append(line)
        elif unborn:
            line = "unborn HEAD"
            if symrefs:
                line += f" symref-target:{head_ref}"
            out.append(line)
    for name in sorted(refs):
        if not matches(name):
            continue
        oid = refs[name]
        line = f"{oid} {name}"
        if peel:
            peeled = peel_object(repo, oid)
            if peeled != oid:
                line += f" peeled:{peeled}"
        out.append(line)
    return b"".join(pkt_line(line + "\n") for line in out) + PKT_FLUSH


def _fetch_args(args):
    wants, haves, client_shallow, depth = [], [], set(), None
    for line in args:
        if line.startswith("want "):
            wants.append(line[5:].strip())
        elif line.startswith("have "):
            haves.append(line[5:].strip())
        elif line.startswith("shallow "):
            client_shallow.add(line[8:].strip())
        elif line.startswith("deepen "):
            try:
                depth = int(line[7:].strip())
            except ValueError:
                depth = None
    return wants, haves, client_shallow, depth


def fetch_response_v2(repo: Repo, args) -> bytes:
    wants, haves, client_shallow, depth = _fetch_args(args)
    for want in wants:
        if want not in repo.odb:
            raise ValueError(f"upload-pack: not our ref {want}")
    send, shallow, unshallow = compute_fetch(repo, wants, haves,
                                             client_shallow, depth)
    common = next((h for h in haves if h in repo.odb), None)
    if "done" not in args:
        # Negotiation round: one acknowledgments section, ended by the
        # flush that closes the response (a delim here would promise
        # another section fetch-pack does not expect without `ready`).
        # A request carrying `done` is answered with the pack directly;
        # fetch-pack rejects an acknowledgments section there.
        out = bytearray(pkt_line("acknowledgments\n"))
        out += pkt_line(f"ACK {common}\n" if common else "NAK\n")
        out += PKT_FLUSH
        return bytes(out)
    # Sections are delim-separated; the last one ends with the flush.
    sections = []
    if shallow or unshallow:
        section = bytearray(pkt_line("shallow-info\n"))
        for oid in shallow:
            section += pkt_line(f"shallow {oid}\n")
        for oid in unshallow:
            section += pkt_line(f"unshallow {oid}\n")
        sections.append(bytes(section))
    if send:
        sections.append(pkt_line("packfile\n")
                        + sideband_packets(pack_bytes_for(send)))
    return PKT_DELIM.join(sections) + PKT_FLUSH if sections else PKT_FLUSH


def fetch_response_v0(repo: Repo, body: bytes) -> bytes:
    reader = PktReader(body)
    wants, haves, client_shallow, depth = [], [], set(), None
    caps: list = []
    sections = 0
    while True:
        packet = reader.next()
        if packet is None:
            break
        if packet[0] == "flush":
            sections += 1
            if sections >= 2:
                break
            continue
        if packet[0] != "data":
            continue
        line = packet[1].decode("utf-8", "replace").rstrip("\n")
        if line.startswith("want "):
            parts = line[5:].split(" ")
            wants.append(parts[0])
            if len(parts) > 1:
                caps = parts[1:]
        elif line.startswith("have "):
            haves.append(line[5:])
        elif line.startswith("shallow "):
            client_shallow.add(line[8:])
        elif line.startswith("deepen "):
            try:
                depth = int(line[7:])
            except ValueError:
                depth = None
    for want in wants:
        if want not in repo.odb:
            raise ValueError(f"upload-pack: not our ref {want}")
    send, shallow, unshallow = compute_fetch(repo, wants, haves,
                                             client_shallow, depth)
    common = next((h for h in haves if h in repo.odb), None)
    out = bytearray()
    for oid in shallow:
        out += pkt_line(f"shallow {oid}\n")
    for oid in unshallow:
        out += pkt_line(f"unshallow {oid}\n")
    if common and "multi_ack_detailed" in caps:
        out += pkt_line(f"ACK {common} ready\n")
    elif common:
        out += pkt_line(f"ACK {common}\n")
    else:
        out += pkt_line("NAK\n")
    if send:
        out += sideband_packets(pack_bytes_for(send))
    out += PKT_FLUSH
    return bytes(out)


def git_receive_pack(ctx: Ctx, repo: Repo):
    body = read_raw_body(ctx)
    reader = PktReader(body)
    commands, caps = [], []
    while True:
        packet = reader.next()
        if packet is None or packet[0] == "flush":
            break
        if packet[0] != "data":
            continue
        line = packet[1].decode("utf-8", "replace").rstrip("\n")
        if not commands and "\x00" in line:
            line, cap_text = line.split("\x00", 1)
            caps = cap_text.split()
        parts = line.split(" ")
        if len(parts) != 3:
            raise ValueError("malformed receive-pack command")
        commands.append((parts[0], parts[1], parts[2]))
    pack_bytes = reader.rest()

    unpack_error = None
    if pack_bytes:
        try:
            repo.odb.update(read_pack(pack_bytes, repo.odb.get))
        except Exception as err:            # a bad pack refuses every ref
            unpack_error = str(err).replace("\n", " ")

    results = []
    if unpack_error is not None:
        results = [(ref, False, "unpacker error") for _o, _n, ref in commands]
    else:
        refs_now = repo_refs(repo)
        for old, new, ref in commands:
            results.append(_apply_ref_update(repo, refs_now, old, new, ref))
        if any(ok for _ref, ok, _why in results):
            repo.updated_tick = STORE.tick()
            integrate_repo_objects(repo)

    lines = [f"unpack {unpack_error}" if unpack_error else "unpack ok"]
    for ref, ok, reason in results:
        lines.append(f"ok {ref}" if ok else f"ng {ref} {reason}")
    if "side-band-64k" in caps:
        out = bytearray()
        for line in lines:
            out += pkt_line(b"\x01" + pkt_line(line + "\n"))
        out += pkt_line(b"\x01" + PKT_FLUSH)    # the report stream's own flush
        out += PKT_FLUSH
        payload = bytes(out)
    else:
        payload = b"".join(pkt_line(line + "\n") for line in lines) + PKT_FLUSH
    send_raw(ctx, 200, payload, "application/x-git-receive-pack-result")


def _apply_ref_update(repo: Repo, refs_now: dict, old: str, new: str, ref: str):
    current = refs_now.get(ref, ZERO_OID)
    if new == ZERO_OID:                                 # delete
        if current == ZERO_OID:
            return ref, False, "reference does not exist"
        if old != current:
            return ref, False, "stale info"
        set_ref(repo, ref, None)
        refs_now.pop(ref, None)
        return ref, True, ""
    if old == ZERO_OID and current != ZERO_OID and current != new:
        return ref, False, "already exists"
    if old != ZERO_OID and old != current:
        return ref, False, "stale info"
    target = repo.odb.get(new)
    if target is None:
        return ref, False, "missing object"
    if ref.startswith("refs/heads/"):
        if target[0] != "commit":
            return ref, False, "bad object type"
        if (current != ZERO_OID and new != current
                and not is_ancestor(repo, current, new)):
            return ref, False, "non-fast-forward"
    set_ref(repo, ref, new)
    refs_now[ref] = new
    return ref, True, ""


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
