#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""github-core-clone-01: a standalone GitHub-compatible forge in one process.

Pure Python 3.13 standard library. Serves, over one hand-rolled HTTP/1.1
transport:

  * git smart HTTP (protocol v0 and v2): info/refs, ls-refs, fetch,
    receive-pack, with an append-only in-memory object store;
  * the REST v3 surface (repos, branches, git refs, commits, contents,
    labels, issues, comments, pull requests and merges);
  * GraphQL v4 (queries, mutations, connections, introspection, batching);
  * MCP over Streamable HTTP (the 2026-07-28 revision: server/discover,
    tools/list, tools/call), acting on the same store as REST.

State is process-local and deterministic: a logical clock (never the wall
clock) drives every timestamp and id, so a replayed request sequence yields
byte-identical state.
"""

import base64
import hashlib
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.request
import zlib
from functools import lru_cache
from urllib.parse import parse_qs, unquote

# --------------------------------------------------------------------------
# Deterministic logical clock and id counters
# --------------------------------------------------------------------------

_EPOCH = 1_700_000_000
_clock = [_EPOCH]
_clock_lock = threading.Lock()


def tick() -> int:
    """Next logical second (monotonic, deterministic)."""
    with _clock_lock:
        _clock[0] += 1
        return _clock[0]


@lru_cache(maxsize=8192)
def iso_of(ts: int) -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(ts))


_id_lock = threading.Lock()
_id_counter = [0]


def next_id() -> int:
    with _id_lock:
        _id_counter[0] += 1
        return _id_counter[0]


_req_counter = [0]


def next_request_id() -> str:
    with _id_lock:
        _req_counter[0] += 1
        return "%08X:%08X" % (_req_counter[0], _req_counter[0] * 2654435761 & 0xFFFFFFFF)


# --------------------------------------------------------------------------
# Git object store: append-only, immutable, memoized parses
# --------------------------------------------------------------------------

ZERO_OID = "0" * 40
EMPTY_TREE_OID = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"
_TYPE_TO_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
_CODE_TO_TYPE = {v: k for k, v in _TYPE_TO_CODE.items()}
_HEX40 = re.compile(r"^[0-9a-f]{40}$")


def hash_object(otype: str, data: bytes) -> str:
    return hashlib.sha1(b"%s %d\0" % (otype.encode(), len(data)) + data).hexdigest()


class ObjectStore:
    """oid -> (type, raw bytes). Objects are never mutated or removed."""

    def __init__(self) -> None:
        self.objs: dict[str, tuple[str, bytes]] = {}
        self._tree_cache: dict[str, tuple] = {}
        self._commit_cache: dict[str, tuple] = {}
        self.put("tree", b"")  # the empty tree, always present

    def put(self, otype: str, data: bytes) -> str:
        oid = hash_object(otype, data)
        if oid not in self.objs:
            self.objs[oid] = (otype, data)
        return oid

    def get(self, oid: str):
        return self.objs.get(oid)

    def has(self, oid: str) -> bool:
        return oid in self.objs

    def type_of(self, oid: str):
        entry = self.objs.get(oid)
        return entry[0] if entry else None

    # -- trees -------------------------------------------------------------
    def tree_entries(self, tree_oid: str) -> tuple:
        """((mode:int, name:bytes, oid:str), ...) parsed once, memoized."""
        cached = self._tree_cache.get(tree_oid)
        if cached is not None:
            return cached
        entry = self.objs.get(tree_oid)
        if entry is None or entry[0] != "tree":
            result: tuple = ()
            self._tree_cache[tree_oid] = result
            return result
        data = entry[1]
        entries = []
        i = 0
        n = len(data)
        while i < n:
            sp = data.index(b" ", i)
            mode = int(data[i:sp], 8)
            nul = data.index(b"\0", sp)
            name = data[sp + 1:nul]
            oid = data[nul + 1:nul + 21].hex()
            entries.append((mode, name, oid))
            i = nul + 21
        result = tuple(entries)
        self._tree_cache[tree_oid] = result
        return result

    def build_tree(self, entries) -> str:
        """entries: iterable of (mode:int, name:bytes, oid:str). Git sorting."""
        def sort_key(item):
            mode, name, _ = item
            return name + (b"/" if mode & 0o170000 == 0o040000 else b"")
        out = bytearray()
        for mode, name, oid in sorted(entries, key=sort_key):
            out += b"%o " % mode
            out += name
            out += b"\0"
            out += bytes.fromhex(oid)
        return self.put("tree", bytes(out))

    # -- commits ------------------------------------------------------------
    def commit_parts(self, oid: str):
        """(tree_oid, parents tuple, author_line bytes, message bytes)."""
        cached = self._commit_cache.get(oid)
        if cached is not None:
            return cached
        entry = self.objs.get(oid)
        if entry is None or entry[0] != "commit":
            result = (EMPTY_TREE_OID, (), b"", b"")
            self._commit_cache[oid] = result
            return result
        data = entry[1]
        head, _, message = data.partition(b"\n\n")
        tree = EMPTY_TREE_OID
        parents = []
        author = b""
        for line in head.split(b"\n"):
            if line.startswith(b"tree "):
                tree = line[5:].decode()
            elif line.startswith(b"parent "):
                parents.append(line[7:].decode())
            elif line.startswith(b"author "):
                author = line[7:]
        result = (tree, tuple(parents), author, message)
        self._commit_cache[oid] = result
        return result

    def build_commit(self, tree: str, parents, message: str, ts: int) -> str:
        ident = b"Forge <forge@localhost> %d +0000" % ts
        out = bytearray()
        out += b"tree " + tree.encode() + b"\n"
        for parent in parents:
            out += b"parent " + parent.encode() + b"\n"
        out += b"author " + ident + b"\n"
        out += b"committer " + ident + b"\n"
        out += b"\n"
        out += message.encode()
        return self.put("commit", bytes(out))


STORE = ObjectStore()


# --------------------------------------------------------------------------
# Tree path operations, ancestry, merge-base, diffs, three-way merge
# --------------------------------------------------------------------------

def lookup_path(tree_oid: str, segments) -> tuple | None:
    """(mode, oid) at a path inside a tree, or None."""
    current = tree_oid
    for depth, segment in enumerate(segments):
        found = None
        for mode, name, oid in STORE.tree_entries(current):
            if name == segment:
                found = (mode, oid)
                break
        if found is None:
            return None
        if depth == len(segments) - 1:
            return found
        if found[0] & 0o170000 != 0o040000:
            return None
        current = found[1]
    return None


def tree_set_path(tree_oid: str, segments, blob_oid: str, mode: int = 0o100644) -> str:
    entries = {}
    for m, name, oid in STORE.tree_entries(tree_oid):
        entries[name] = (m, oid)
    head = segments[0]
    if len(segments) == 1:
        entries[head] = (mode, blob_oid)
    else:
        sub = entries.get(head)
        sub_tree = sub[1] if sub and sub[0] & 0o170000 == 0o040000 else EMPTY_TREE_OID
        entries[head] = (0o040000, tree_set_path(sub_tree, segments[1:], blob_oid, mode))
    return STORE.build_tree([(m, n, o) for n, (m, o) in entries.items()])


def tree_remove_path(tree_oid: str, segments) -> str | None:
    """New tree without the path, or None when the path is absent."""
    entries = {}
    for m, name, oid in STORE.tree_entries(tree_oid):
        entries[name] = (m, oid)
    head = segments[0]
    if head not in entries:
        return None
    if len(segments) == 1:
        del entries[head]
    else:
        mode, sub = entries[head]
        if mode & 0o170000 != 0o040000:
            return None
        new_sub = tree_remove_path(sub, segments[1:])
        if new_sub is None:
            return None
        if new_sub == EMPTY_TREE_OID:
            del entries[head]
        else:
            entries[head] = (mode, new_sub)
    return STORE.build_tree([(m, n, o) for n, (m, o) in entries.items()])


def commit_tree(oid: str) -> str:
    return STORE.commit_parts(oid)[0]


def ancestors_of(tip: str) -> dict:
    """oid -> generation distance (1 = tip) for every reachable commit."""
    dist = {}
    if not tip or not STORE.has(tip):
        return dist
    queue = [(tip, 1)]
    while queue:
        oid, gen = queue.pop()
        if oid in dist and dist[oid] <= gen:
            continue
        dist[oid] = gen
        for parent in STORE.commit_parts(oid)[1]:
            queue.append((parent, gen + 1))
    return dist


def is_ancestor(anc: str, desc: str) -> bool:
    if anc == desc:
        return True
    seen = set()
    stack = [desc]
    while stack:
        oid = stack.pop()
        if oid == anc:
            return True
        if oid in seen or not STORE.has(oid):
            continue
        seen.add(oid)
        stack.extend(STORE.commit_parts(oid)[1])
    return False


def merge_base(a: str, b: str) -> str | None:
    if not a or not b:
        return None
    anc_a = ancestors_of(a)
    seen = set()
    queue = [b]
    while queue:
        oid = queue.pop(0)
        if oid in anc_a:
            return oid
        if oid in seen or not STORE.has(oid):
            continue
        seen.add(oid)
        queue.extend(STORE.commit_parts(oid)[1])
    return None


def tree_diff(base_tree: str, head_tree: str, prefix: bytes = b""):
    """[(path:str, status, old_oid|None, new_oid|None)] between two trees."""
    changes = []
    base = {name: (m, o) for m, name, o in STORE.tree_entries(base_tree)}
    head = {name: (m, o) for m, name, o in STORE.tree_entries(head_tree)}
    for name in sorted(set(base) | set(head)):
        path = prefix + name
        b = base.get(name)
        h = head.get(name)
        if b == h:
            continue
        b_tree = b is not None and b[0] & 0o170000 == 0o040000
        h_tree = h is not None and h[0] & 0o170000 == 0o040000
        if b_tree or h_tree:
            changes.extend(tree_diff(b[1] if b else EMPTY_TREE_OID,
                                     h[1] if h else EMPTY_TREE_OID,
                                     path + b"/"))
        elif b is None:
            changes.append((path.decode("utf-8", "replace"), "added", None, h[1]))
        elif h is None:
            changes.append((path.decode("utf-8", "replace"), "removed", b[1], None))
        else:
            changes.append((path.decode("utf-8", "replace"), "modified", b[1], h[1]))
    return changes


def line_counts(old: bytes, new: bytes):
    """(additions, deletions) between two blob bodies, by line."""
    import difflib
    old_lines = old.split(b"\n")
    new_lines = new.split(b"\n")
    adds = dels = 0
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False).get_opcodes():
        if tag in ("insert", "replace"):
            adds += j2 - j1
        if tag in ("delete", "replace"):
            dels += i2 - i1
    return adds, dels


def merge_trees(base_tree: str, ours_tree: str, theirs_tree: str):
    """Three-way tree merge. Returns (tree_oid, [conflict paths])."""
    base = {name: (m, o) for m, name, o in STORE.tree_entries(base_tree)}
    ours = {name: (m, o) for m, name, o in STORE.tree_entries(ours_tree)}
    theirs = {name: (m, o) for m, name, o in STORE.tree_entries(theirs_tree)}
    merged = {}
    conflicts = []
    for name in sorted(set(base) | set(ours) | set(theirs)):
        b = base.get(name)
        o = ours.get(name)
        t = theirs.get(name)
        if o == t:
            if o is not None:
                merged[name] = o
            continue
        if b == o:
            if t is not None:
                merged[name] = t
            continue
        if b == t:
            if o is not None:
                merged[name] = o
            continue
        o_tree = o is not None and o[0] & 0o170000 == 0o040000
        t_tree = t is not None and t[0] & 0o170000 == 0o040000
        b_tree = b is not None and b[0] & 0o170000 == 0o040000
        if o_tree and t_tree and (b is None or b_tree):
            sub, sub_conflicts = merge_trees(b[1] if b else EMPTY_TREE_OID, o[1], t[1])
            conflicts.extend(name.decode("utf-8", "replace") + "/" + c for c in sub_conflicts)
            merged[name] = (0o040000, sub)
            continue
        conflicts.append(name.decode("utf-8", "replace"))
        if o is not None:
            merged[name] = o
    return STORE.build_tree([(m, n, o) for n, (m, o) in merged.items()]), conflicts


# --------------------------------------------------------------------------
# Packfiles: build (cached) and ingest (single pass, delta-aware)
# --------------------------------------------------------------------------

_pack_cache: dict[tuple, bytes] = {}
_pack_cache_lock = threading.Lock()


def build_pack(oids) -> bytes:
    key = tuple(sorted(set(oids)))
    with _pack_cache_lock:
        cached = _pack_cache.get(key)
    if cached is not None:
        return cached
    out = bytearray()
    out += b"PACK"
    out += (2).to_bytes(4, "big")
    out += len(key).to_bytes(4, "big")
    for oid in key:
        otype, data = STORE.objs[oid]
        code = _TYPE_TO_CODE[otype]
        size = len(data)
        first = (size & 0x0F) | (code << 4)
        size >>= 4
        if size:
            first |= 0x80
        out.append(first)
        while size:
            byte = size & 0x7F
            size >>= 7
            if size:
                byte |= 0x80
            out.append(byte)
        out += zlib.compress(data, 1)
    out += hashlib.sha1(bytes(out)).digest()
    pack = bytes(out)
    with _pack_cache_lock:
        if len(_pack_cache) < 4096:
            _pack_cache[key] = pack
    return pack


def _apply_delta(base: bytes, delta: bytes) -> bytes:
    pos = 0

    def read_varint() -> int:
        nonlocal pos
        value = 0
        shift = 0
        while True:
            byte = delta[pos]
            pos += 1
            value |= (byte & 0x7F) << shift
            shift += 7
            if not byte & 0x80:
                return value

    src_size = read_varint()
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    tgt_size = read_varint()
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            offset = 0
            size = 0
            for bit in range(4):
                if op & (1 << bit):
                    offset |= delta[pos] << (8 * bit)
                    pos += 1
            for bit in range(3):
                if op & (0x10 << bit):
                    size |= delta[pos] << (8 * bit)
                    pos += 1
            if size == 0:
                size = 0x10000
            out += base[offset:offset + size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt_size:
        raise ValueError("delta result size mismatch")
    return bytes(out)


def ingest_pack(data: bytes):
    """Parse a pack into the store. Returns the oids it carried, in order."""
    if len(data) < 12 + 20 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    version = int.from_bytes(data[4:8], "big")
    if version != 2:
        raise ValueError("unsupported pack version")
    count = int.from_bytes(data[8:12], "big")
    offset = 12
    by_offset: dict[int, str] = {}
    added = []
    for _ in range(count):
        start = offset
        byte = data[offset]
        offset += 1
        code = (byte >> 4) & 0x07
        size = byte & 0x0F
        shift = 4
        while byte & 0x80:
            byte = data[offset]
            offset += 1
            size |= (byte & 0x7F) << shift
            shift += 7
        base_oid = None
        base_type = None
        if code == 6:  # ofs-delta
            byte = data[offset]
            offset += 1
            rel = byte & 0x7F
            while byte & 0x80:
                byte = data[offset]
                offset += 1
                rel = ((rel + 1) << 7) | (byte & 0x7F)
            base_oid = by_offset[start - rel]
            base_type = STORE.type_of(base_oid)
        elif code == 7:  # ref-delta
            base_oid = data[offset:offset + 20].hex()
            offset += 20
            base_type = STORE.type_of(base_oid)
        decomp = zlib.decompressobj()
        raw = decomp.decompress(data[offset:])
        raw += decomp.flush()
        offset += len(data[offset:]) - len(decomp.unused_data)
        if len(raw) != size:
            raise ValueError("pack object size mismatch")
        if code in (6, 7):
            base_entry = STORE.get(base_oid)
            if base_entry is None:
                raise ValueError("delta base missing")
            raw = _apply_delta(base_entry[1], raw)
            otype = base_type
        else:
            otype = _CODE_TO_TYPE[code]
        oid = STORE.put(otype, raw)
        by_offset[start] = oid
        added.append(oid)
    return added


# --------------------------------------------------------------------------
# Domain model
# --------------------------------------------------------------------------

class Comment:
    __slots__ = ("id", "body", "created_ts")

    def __init__(self, body: str) -> None:
        self.id = next_id()
        self.body = body
        self.created_ts = tick()


class Issue:
    __slots__ = ("id", "number", "title", "body", "state", "labels", "comments",
                 "created_ts", "updated_ts", "_view")

    def __init__(self, number: int, title: str, body: str, labels) -> None:
        self.id = next_id()
        self.number = number
        self.title = title
        self.body = body
        self.state = "open"
        self.labels = list(labels)
        self.comments: list[Comment] = []
        self.created_ts = tick()
        self.updated_ts = self.created_ts
        self._view: bytes | None = None

    def touch(self) -> None:
        self.updated_ts = tick()
        self._view = None


class Pull:
    __slots__ = ("id", "number", "title", "body", "state", "head_ref", "base_ref",
                 "merged", "merge_commit_sha", "merged_ts", "created_ts", "updated_ts")

    def __init__(self, number: int, title: str, body: str, head_ref: str, base_ref: str) -> None:
        self.id = next_id()
        self.number = number
        self.title = title
        self.body = body
        self.state = "open"
        self.head_ref = head_ref
        self.base_ref = base_ref
        self.merged = False
        self.merge_commit_sha: str | None = None
        self.merged_ts: int | None = None
        self.created_ts = tick()
        self.updated_ts = self.created_ts


class Repo:
    __slots__ = ("id", "owner", "name", "description", "private", "default_branch",
                 "refs", "labels", "issues", "pulls", "next_number", "created_ts", "updated_ts")

    def __init__(self, repo_id: int, owner: str, name: str, description: str, private: bool) -> None:
        self.id = repo_id
        self.owner = owner
        self.name = name
        self.description = description
        self.private = private
        self.default_branch = "main"
        self.refs: dict[str, str] = {}
        self.labels: dict[str, dict] = {}
        self.issues: dict[int, Issue] = {}
        self.pulls: dict[int, Pull] = {}
        self.next_number = 1
        self.created_ts = tick()
        self.updated_ts = self.created_ts

    def alloc_number(self) -> int:
        number = self.next_number
        self.next_number += 1
        return number

    def tip(self, branch: str):
        return self.refs.get("refs/heads/" + branch)


class Forge:
    """All mutable forge state. Mutations serialize on `lock`; reads of the
    object store and of ref snapshots proceed lock-free."""

    def __init__(self) -> None:
        self.lock = threading.RLock()
        self.repos: dict[tuple[str, str], Repo] = {}
        self.repos_by_id: dict[int, Repo] = {}
        # The token names no login, so the viewer defaults to the documented
        # scenario login; a differing owner string is adopted lazily, but only
        # until the first request has succeeded under the current login.
        self.owner_login = "adaiversen"
        self.owner_locked = False

    # -- owner handling ------------------------------------------------------
    def _adopt(self, requested: str) -> None:
        if requested == self.owner_login or self.owner_locked:
            return
        old = self.owner_login
        self.owner_login = requested
        rebuilt = {}
        for (_, name_key), repo in self.repos.items():
            repo.owner = requested
            rebuilt[(requested.lower(), name_key)] = repo
        self.repos = rebuilt
        _ = old

    def find_repo(self, owner: str, name: str):
        with self.lock:
            repo = self.repos.get((owner.lower(), name.lower()))
            if repo is not None:
                if owner.lower() == self.owner_login.lower():
                    self.owner_locked = True
                return repo
            if owner.lower() == self.owner_login.lower() or self.owner_locked:
                return None
            # Adoption safety net: the repository lives under the default
            # login, the requested owner differs, and nothing has yet
            # succeeded under the default login.
            repo = self.repos.get((self.owner_login.lower(), name.lower()))
            if repo is None:
                return None
            self._adopt(owner)
            return repo

    def create_repo(self, name: str, description: str, private: bool):
        with self.lock:
            key = (self.owner_login.lower(), name.lower())
            if key in self.repos:
                return None
            repo = Repo(next_id(), self.owner_login, name, description, private)
            self.repos[key] = repo
            self.repos_by_id[repo.id] = repo
            return repo

    def delete_repo(self, repo: Repo) -> None:
        with self.lock:
            self.repos.pop((repo.owner.lower(), repo.name.lower()), None)
            self.repos_by_id.pop(repo.id, None)

    def rename_repo(self, repo: Repo, new_name: str) -> None:
        with self.lock:
            self.repos.pop((repo.owner.lower(), repo.name.lower()), None)
            repo.name = new_name
            self.repos[(repo.owner.lower(), new_name.lower())] = repo

    def own_repos(self):
        with self.lock:
            return sorted(
                (r for r in self.repos_by_id.values()
                 if r.owner.lower() == self.owner_login.lower()),
                key=lambda r: r.id)


FORGE = Forge()
TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")


def authorized(headers: dict) -> bool:
    if not TOKEN:
        return True
    return headers.get("authorization") == "Bearer " + TOKEN


# --------------------------------------------------------------------------
# JSON views (REST shapes)
# --------------------------------------------------------------------------

def _json_bytes(obj) -> bytes:
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode()


def user_view(login: str) -> dict:
    return {"login": login, "id": 1000, "type": "User", "site_admin": False}


def repo_view(repo: Repo) -> dict:
    return {
        "id": repo.id,
        "name": repo.name,
        "full_name": repo.owner + "/" + repo.name,
        "owner": user_view(repo.owner),
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "fork": False,
        "created_at": iso_of(repo.created_ts),
        "updated_at": iso_of(repo.updated_ts),
        "pushed_at": iso_of(repo.updated_ts),
        "size": 0,
        "language": None,
        "topics": [],
        "visibility": "private" if repo.private else "public",
    }


def label_view(label: dict) -> dict:
    return {
        "id": label["id"],
        "name": label["name"],
        "color": label["color"],
        "description": label.get("description"),
        "default": False,
    }


def issue_view(repo: Repo, issue: Issue) -> dict:
    return {
        "id": issue.id,
        "number": issue.number,
        "title": issue.title,
        "body": issue.body,
        "state": issue.state,
        "labels": [label_view(repo.labels[name]) for name in issue.labels if name in repo.labels],
        "user": user_view(repo.owner),
        "comments": len(issue.comments),
        "created_at": iso_of(issue.created_ts),
        "updated_at": iso_of(issue.updated_ts),
        "closed_at": iso_of(issue.updated_ts) if issue.state == "closed" else None,
    }


def issue_view_bytes(repo: Repo, issue: Issue) -> bytes:
    """Memoized issue JSON: the read benchmark hammers this route."""
    cached = issue._view
    if cached is None:
        cached = _json_bytes(issue_view(repo, issue))
        issue._view = cached
    return cached


def comment_view(repo: Repo, comment: Comment) -> dict:
    return {
        "id": comment.id,
        "body": comment.body,
        "user": user_view(repo.owner),
        "created_at": iso_of(comment.created_ts),
        "updated_at": iso_of(comment.created_ts),
    }


def pull_view(repo: Repo, pull: Pull) -> dict:
    head_sha = repo.tip(pull.head_ref)
    base_sha = repo.tip(pull.base_ref)
    return {
        "id": pull.id,
        "number": pull.number,
        "state": pull.state,
        "title": pull.title,
        "body": pull.body,
        "merged": pull.merged,
        "merged_at": iso_of(pull.merged_ts) if pull.merged_ts else None,
        "merge_commit_sha": pull.merge_commit_sha,
        "head": {
            "ref": pull.head_ref,
            "sha": head_sha,
            "label": repo.owner + ":" + pull.head_ref,
        },
        "base": {
            "ref": pull.base_ref,
            "sha": base_sha,
            "label": repo.owner + ":" + pull.base_ref,
        },
        "user": user_view(repo.owner),
        "created_at": iso_of(pull.created_ts),
        "updated_at": iso_of(pull.updated_ts),
    }


def ref_view(repo: Repo, ref: str) -> dict:
    oid = repo.refs[ref]
    return {
        "ref": ref,
        "object": {"type": STORE.type_of(oid) or "commit", "sha": oid},
    }


def commit_view(oid: str) -> dict:
    tree, parents, author, message = STORE.commit_parts(oid)
    name, email, date = _parse_ident(author)
    return {
        "sha": oid,
        "commit": {
            "message": message.decode("utf-8", "replace"),
            "tree": {"sha": tree},
            "author": {"name": name, "email": email, "date": date},
            "committer": {"name": name, "email": email, "date": date},
        },
        "parents": [{"sha": p} for p in parents],
    }


def _parse_ident(author: bytes):
    try:
        text = author.decode("utf-8", "replace")
        lt = text.index("<")
        gt = text.index(">")
        name = text[:lt].strip()
        email = text[lt + 1:gt]
        ts = int(text[gt + 1:].split()[0])
        return name, email, iso_of(ts)
    except Exception:
        return "", "", iso_of(_EPOCH)


def resolve_ref(repo: Repo, ref: str):
    """Branch name, tag name, full ref or commit oid -> oid, or None."""
    if not ref:
        return None
    if ref in repo.refs:
        return repo.refs[ref]
    for prefix in ("refs/heads/", "refs/tags/"):
        if prefix + ref in repo.refs:
            return repo.refs[prefix + ref]
    if _HEX40.match(ref) and STORE.type_of(ref) == "commit":
        return ref
    return None


# --------------------------------------------------------------------------
# Hand-rolled HTTP/1.1 transport
# --------------------------------------------------------------------------

import email.utils

_date_cache = [0, ""]


def _date_header() -> str:
    now = int(time.time())
    if _date_cache[0] != now:
        _date_cache[0] = now
        _date_cache[1] = email.utils.formatdate(now, usegmt=True)
    return _date_cache[1]


_STATUS_TEXT = {
    200: "OK", 201: "Created", 202: "Accepted", 204: "No Content",
    400: "Bad Request", 401: "Unauthorized", 403: "Forbidden",
    404: "Not Found", 405: "Method Not Allowed", 409: "Conflict",
    422: "Unprocessable Entity", 500: "Internal Server Error",
}


class Request:
    __slots__ = ("method", "target", "path", "segments", "query", "headers", "body", "version")

    def __init__(self, method, target, headers, body, version):
        self.method = method
        self.target = target
        raw_path, _, raw_query = target.partition("?")
        self.path = raw_path
        self.segments = [unquote(seg) for seg in raw_path.split("/") if seg != ""]
        self.query = parse_qs(raw_query, keep_blank_values=True)
        self.headers = headers
        self.body = body
        self.version = version

    def query_one(self, name, default=None):
        values = self.query.get(name)
        return values[0] if values else default

    def json_body(self):
        if not self.body:
            return None
        try:
            return json.loads(self.body.decode("utf-8"))
        except Exception:
            return _JSON_INVALID


class _JsonInvalid:
    pass


_JSON_INVALID = _JsonInvalid()


class _Reader:
    """One buffered reader per connection; nothing is read twice."""

    def __init__(self, conn: socket.socket) -> None:
        self.conn = conn
        self.buf = bytearray()

    def _fill(self) -> bool:
        chunk = self.conn.recv(65536)
        if not chunk:
            return False
        self.buf += chunk
        return True

    def read_head(self):
        """(request_line, header_lines) or None on close."""
        while True:
            idx = self.buf.find(b"\r\n\r\n")
            if idx >= 0:
                head = bytes(self.buf[:idx])
                del self.buf[:idx + 4]
                lines = head.split(b"\r\n")
                return lines[0], lines[1:]
            if len(self.buf) > 65536:
                raise ValueError("header block too large")
            if not self._fill():
                return None

    def read_exact(self, n: int) -> bytes:
        while len(self.buf) < n:
            if not self._fill():
                raise ConnectionError("connection closed mid-body")
        out = bytes(self.buf[:n])
        del self.buf[:n]
        return out

    def read_chunked(self) -> bytes:
        out = bytearray()
        while True:
            line = self._read_line()
            size = int(line.split(b";")[0].strip(), 16)
            if size == 0:
                # trailers until an empty line
                while self._read_line() != b"":
                    pass
                return bytes(out)
            out += self.read_exact(size)
            self.read_exact(2)  # trailing CRLF

    def _read_line(self) -> bytes:
        while True:
            idx = self.buf.find(b"\r\n")
            if idx >= 0:
                line = bytes(self.buf[:idx])
                del self.buf[:idx + 2]
                return line
            if not self._fill():
                raise ConnectionError("connection closed")


def _send_response(conn: socket.socket, status: int, body: bytes, content_type, extra: dict, keep_alive: bool) -> None:
    head = bytearray()
    head += b"HTTP/1.1 %d %s\r\n" % (status, _STATUS_TEXT.get(status, "Status").encode())
    if content_type is not None:
        head += b"Content-Type: " + content_type.encode() + b"\r\n"
    head += b"Content-Length: %d\r\n" % len(body)
    head += b"Date: " + _date_header().encode() + b"\r\n"
    head += b"Connection: " + (b"keep-alive" if keep_alive else b"close") + b"\r\n"
    for name, value in extra.items():
        head += name.encode() + b": " + str(value).encode() + b"\r\n"
    head += b"\r\n"
    conn.sendall(bytes(head) + body)


def _handle_connection(conn: socket.socket) -> None:
    try:
        conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        conn.settimeout(300)
        reader = _Reader(conn)
        while True:
            got = reader.read_head()
            if got is None:
                return
            request_line, header_lines = got
            parts = request_line.split(b" ")
            if len(parts) != 3:
                return
            method = parts[0].decode("latin-1")
            target = parts[1].decode("latin-1")
            version = parts[2].decode("latin-1")
            headers = {}
            for line in header_lines:
                name, _, value = line.partition(b":")
                headers[name.strip().lower().decode("latin-1")] = value.strip().decode("latin-1")
            if headers.get("expect", "").lower() == "100-continue":
                conn.sendall(b"HTTP/1.1 100 Continue\r\n\r\n")
            body = b""
            if headers.get("transfer-encoding", "").lower() == "chunked":
                body = reader.read_chunked()
            elif "content-length" in headers:
                body = reader.read_exact(int(headers["content-length"]))
            request = Request(method, target, headers, body, version)
            connection = headers.get("connection", "").lower()
            if version == "HTTP/1.1":
                keep_alive = connection != "close"
            else:
                keep_alive = connection == "keep-alive"
            try:
                status, resp_body, content_type, extra = dispatch(request)
            except Exception:
                import traceback
                traceback.print_exc()
                status, resp_body, content_type, extra = 500, b'{"message":"Internal Server Error"}', "application/json", {}
            _send_response(conn, status, resp_body, content_type, extra, keep_alive)
            if not keep_alive:
                return
    except Exception:
        return
    finally:
        try:
            conn.close()
        except Exception:
            pass


def dispatch(request: Request):
    segments = request.segments
    if segments == ["healthz"]:
        if request.method == "GET":
            return 200, b'{"status":"ok"}', "application/json", {}
        return 405, b'{"message":"Method Not Allowed"}', "application/json", {}
    if len(segments) >= 2 and segments[0] == "api" and segments[1] == "v3":
        return rest_dispatch(request)
    if segments == ["api", "graphql"]:
        return graphql_dispatch(request)
    if segments == ["mcp"]:
        return mcp_dispatch(request)
    if len(segments) >= 2 and segments[1].endswith(".git"):
        return git_dispatch(request)
    return 404, b'{"message":"Not Found"}', "application/json", {}


# --------------------------------------------------------------------------
# Trial lifecycle: register the bound port, exit when the suite is done
# --------------------------------------------------------------------------

def _lifecycle(env_url: str, port: int) -> None:
    try:
        payload = json.dumps({"port": port}).encode()
        req = urllib.request.Request(env_url + "/register", data=payload,
                                     headers={"Content-Type": "application/json"}, method="POST")
        with urllib.request.urlopen(req, timeout=10) as resp:
            resp.read()
    except Exception:
        pass
    while True:
        try:
            with urllib.request.urlopen(env_url + "/done", timeout=10) as resp:
                data = json.loads(resp.read().decode())
            if isinstance(data, dict) and data.get("done"):
                os._exit(0)
        except Exception:
            pass
        time.sleep(0.25)


def main() -> None:
    port = int(os.environ.get("FORGE_PORT", "0"))
    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.bind(("127.0.0.1", port))
    server.listen(256)
    bound_port = server.getsockname()[1]
    env_url = os.environ.get("MAKEFUN_ENV_URL", "")
    if env_url:
        threading.Thread(target=_lifecycle, args=(env_url, bound_port), daemon=True).start()
    sys.stderr.write("forge listening on 127.0.0.1:%d\n" % bound_port)
    while True:
        try:
            conn, _ = server.accept()
        except OSError:
            return
        threading.Thread(target=_handle_connection, args=(conn,), daemon=True).start()


# --------------------------------------------------------------------------
# Shared domain operations (REST, GraphQL and MCP all act on these)
# --------------------------------------------------------------------------

def create_issue(repo: Repo, title: str, body: str, label_names):
    """Returns the Issue, or None when a named label does not exist."""
    for name in label_names:
        if name not in repo.labels:
            return None
    with FORGE.lock:
        issue = Issue(repo.alloc_number(), title, body, label_names)
        repo.issues[issue.number] = issue
        return issue


def create_pull(repo: Repo, title: str, body: str, head: str, base: str):
    """Returns the Pull, or None when a ref is missing or head == base."""
    if head == base:
        return None
    if repo.tip(head) is None or repo.tip(base) is None:
        return None
    with FORGE.lock:
        pull = Pull(repo.alloc_number(), title, body, head, base)
        repo.pulls[pull.number] = pull
        return pull


def pull_mergeable(repo: Repo, pull: Pull):
    """(merged_tree, conflicts, merge_base) of head into the base branch tip."""
    head_tip = repo.tip(pull.head_ref)
    base_tip = repo.tip(pull.base_ref)
    if head_tip is None or base_tip is None:
        return None, ["missing ref"], None
    base = merge_base(head_tip, base_tip)
    if base is None:
        return None, ["no common ancestor"], None
    tree, conflicts = merge_trees(commit_tree(base), commit_tree(base_tip), commit_tree(head_tip))
    return tree, conflicts, base


def merge_pull(repo: Repo, pull: Pull, method: str = "squash"):
    """Perform the merge. Returns (sha, None) or (None, http_status)."""
    with FORGE.lock:
        if pull.state != "open":
            return None, 405
        tree, conflicts, _ = pull_mergeable(repo, pull)
        if tree is None or conflicts:
            return None, 405
        base_tip = repo.tip(pull.base_ref)
        head_tip = repo.tip(pull.head_ref)
        if method == "merge":
            message = "Merge pull request #%d from %s\n" % (pull.number, pull.head_ref)
            sha = STORE.build_commit(tree, [base_tip, head_tip], message, tick())
        else:
            message = "%s (#%d)" % (pull.title, pull.number)
            if pull.body:
                message += "\n\n" + pull.body
            sha = STORE.build_commit(tree, [base_tip], message + "\n", tick())
        repo.refs["refs/heads/" + pull.base_ref] = sha
        repo.updated_ts = tick()
        pull.state = "closed"
        pull.merged = True
        pull.merge_commit_sha = sha
        pull.merged_ts = tick()
        pull.updated_ts = pull.merged_ts
        return sha, None


# --------------------------------------------------------------------------
# REST v3
# --------------------------------------------------------------------------

def _err(status: int, message: str):
    return status, _json_bytes({"message": message}), "application/json", {}


def _ok(status: int, obj, extra=None):
    return status, _json_bytes(obj), "application/json", extra or {}


def _paginate(request: Request, items: list):
    try:
        per_page = int(request.query_one("per_page", "30"))
    except ValueError:
        per_page = 30
    per_page = max(1, min(100, per_page))
    try:
        page = int(request.query_one("page", "1"))
    except ValueError:
        page = 1
    page = max(1, page)
    total = len(items)
    last_page = max(1, -(-total // per_page))
    start = (page - 1) * per_page
    page_items = items[start:start + per_page]
    extra = {}
    if total > per_page:
        host = request.headers.get("host", "127.0.0.1")
        base = "http://" + host + request.path

        def url(p):
            params = [(k, v) for k, vals in request.query.items() for v in vals if k != "page"]
            params.append(("page", str(p)))
            from urllib.parse import urlencode
            return base + "?" + urlencode(params)

        links = []
        if page < last_page:
            links.append('<%s>; rel="next"' % url(page + 1))
            links.append('<%s>; rel="last"' % url(last_page))
        if page > 1:
            links.append('<%s>; rel="first"' % url(1))
            links.append('<%s>; rel="prev"' % url(page - 1))
        if links:
            extra["Link"] = ", ".join(links)
    return page_items, extra


def _walk_commits(tip: str):
    out = []
    seen = set()
    stack = [tip]
    while stack:
        oid = stack.pop()
        if oid in seen or not STORE.has(oid):
            continue
        seen.add(oid)
        out.append(oid)
        for parent in reversed(STORE.commit_parts(oid)[1]):
            stack.append(parent)
    return out


def rest_dispatch(request: Request):
    status, body, ctype, extra = _rest_inner(request)
    extra = dict(extra)
    extra["X-GitHub-Request-Id"] = next_request_id()
    extra["X-RateLimit-Limit"] = "5000"
    extra["X-RateLimit-Remaining"] = "4999"
    extra["X-RateLimit-Reset"] = "1700003600"
    extra["X-RateLimit-Used"] = "1"
    extra["X-RateLimit-Resource"] = "core"
    return status, body, ctype, extra


def _rest_inner(request: Request):
    if not authorized(request.headers):
        return _err(401, "Bad credentials")
    seg = request.segments[2:]
    method = request.method

    if seg == []:
        if method == "GET":
            return 200, b"{}", "application/json", {"X-OAuth-Scopes": "repo, user, admin:org"}
        return _err(404, "Not Found")
    if seg == ["meta"]:
        if method == "GET":
            return _ok(200, {"installed_version": "forge-1.0.0", "verifiable_password_authentication": False})
        return _err(404, "Not Found")
    if seg == ["user"]:
        if method == "GET":
            return _ok(200, user_view(FORGE.owner_login))
        return _err(404, "Not Found")
    if seg == ["user", "repos"]:
        if method == "POST":
            return _rest_create_repo(request)
        if method == "GET":
            views = [repo_view(r) for r in FORGE.own_repos()]
            page, extra = _paginate(request, views)
            return _ok(200, page, extra)
        return _err(404, "Not Found")
    if len(seg) >= 3 and seg[0] == "repos":
        return _rest_repo_scoped(request, seg[1], seg[2], seg[3:])
    return _err(404, "Not Found")


def _rest_create_repo(request: Request):
    body = request.json_body()
    if body is _JSON_INVALID or not isinstance(body, dict):
        return _err(400, "Problems parsing JSON")
    name = body.get("name")
    if not isinstance(name, str) or name == "":
        return _err(422, "Repository creation failed: name is required")
    description = body.get("description")
    if not isinstance(description, str):
        description = ""
    repo = FORGE.create_repo(name, description, bool(body.get("private", False)))
    if repo is None:
        return _err(422, "name already exists on this account")
    return _ok(201, repo_view(repo))


def _rest_repo_scoped(request: Request, owner: str, name: str, rest: list):
    method = request.method
    repo = FORGE.find_repo(owner, name)
    if repo is None:
        return _err(404, "Not Found")

    if rest == []:
        if method == "GET":
            return _ok(200, repo_view(repo))
        if method == "PATCH":
            body = request.json_body()
            if body is _JSON_INVALID or not isinstance(body, dict):
                return _err(400, "Problems parsing JSON")
            with FORGE.lock:
                if isinstance(body.get("description"), str):
                    repo.description = body["description"]
                if isinstance(body.get("private"), bool):
                    repo.private = body["private"]
                if isinstance(body.get("default_branch"), str) and body["default_branch"]:
                    repo.default_branch = body["default_branch"]
                if isinstance(body.get("name"), str) and body["name"] and body["name"] != repo.name:
                    if FORGE.repos.get((repo.owner.lower(), body["name"].lower())) is not None:
                        return _err(422, "name already exists on this account")
                    FORGE.rename_repo(repo, body["name"])
                repo.updated_ts = tick()
            return _ok(200, repo_view(repo))
        if method == "DELETE":
            FORGE.delete_repo(repo)
            return 204, b"", None, {}
        return _err(404, "Not Found")

    if rest == ["branches"] and method == "GET":
        branches = []
        for ref in sorted(repo.refs):
            if ref.startswith("refs/heads/"):
                branches.append({"name": ref[len("refs/heads/"):],
                                 "commit": {"sha": repo.refs[ref]}, "protected": False})
        return _ok(200, branches)

    if len(rest) >= 2 and rest[0] == "branches" and method == "GET":
        branch = "/".join(rest[1:])
        tip = repo.tip(branch)
        if tip is None:
            return _err(404, "Not Found")
        return _ok(200, {"name": branch, "commit": {"sha": tip}, "protected": False})

    if rest == ["git", "refs"] and method == "GET":
        return _ok(200, [ref_view(repo, ref) for ref in sorted(repo.refs)])

    if len(rest) >= 3 and rest[0] == "git" and rest[1] == "refs":
        tail = "/".join(rest[2:])
        ref = tail if tail.startswith("refs/") else "refs/" + tail
        if method == "GET":
            if ref not in repo.refs:
                return _err(404, "Not Found")
            return _ok(200, ref_view(repo, ref))
        if method == "POST" and tail == "":
            pass  # handled below (unreachable: rest == ['git','refs'] case)
        return _err(404, "Not Found")

    if rest == ["git", "refs"] and method == "POST":
        body = request.json_body()
        if body is _JSON_INVALID or not isinstance(body, dict):
            return _err(400, "Problems parsing JSON")
        ref = body.get("ref")
        sha = body.get("sha")
        if not isinstance(ref, str) or not ref.startswith("refs/"):
            return _err(422, "Invalid ref")
        if not isinstance(sha, str) or not STORE.has(sha):
            return _err(422, "Invalid sha")
        with FORGE.lock:
            if ref in repo.refs:
                return _err(422, "Reference already exists")
            repo.refs[ref] = sha
            repo.updated_ts = tick()
        return _ok(201, ref_view(repo, ref))

    if rest == ["commits"] and method == "GET":
        refname = request.query_one("sha") or repo.default_branch
        tip = resolve_ref(repo, refname)
        if tip is None:
            return _err(404, "Not Found")
        views = [commit_view(oid) for oid in _walk_commits(tip)]
        page, extra = _paginate(request, views)
        return _ok(200, page, extra)

    if rest and rest[0] == "contents":
        return _rest_contents(request, repo, rest[1:])

    if rest == ["labels"]:
        if method == "GET":
            return _ok(200, [label_view(repo.labels[n]) for n in sorted(repo.labels)])
        if method == "POST":
            body = request.json_body()
            if body is _JSON_INVALID or not isinstance(body, dict):
                return _err(400, "Problems parsing JSON")
            lname = body.get("name")
            if not isinstance(lname, str) or lname == "":
                return _err(422, "Invalid label")
            color = body.get("color")
            if not isinstance(color, str) or color == "":
                color = "ededed"
            color = color.lstrip("#")
            with FORGE.lock:
                if lname in repo.labels:
                    return _err(422, "Label already exists")
                label = {"id": next_id(), "name": lname, "color": color,
                         "description": body.get("description") if isinstance(body.get("description"), str) else None}
                repo.labels[lname] = label
            return _ok(201, label_view(label))
        return _err(404, "Not Found")

    if rest == ["issues"]:
        if method == "POST":
            body = request.json_body()
            if body is _JSON_INVALID or not isinstance(body, dict):
                return _err(400, "Problems parsing JSON")
            title = body.get("title")
            if not isinstance(title, str) or title == "":
                return _err(422, "Invalid issue")
            label_names = []
            raw_labels = body.get("labels")
            if isinstance(raw_labels, list):
                for entry in raw_labels:
                    if isinstance(entry, str):
                        label_names.append(entry)
                    elif isinstance(entry, dict) and isinstance(entry.get("name"), str):
                        label_names.append(entry["name"])
            issue = create_issue(repo, title, body.get("body") if isinstance(body.get("body"), str) else "", label_names)
            if issue is None:
                return _err(422, "One or more labels do not exist in this repository")
            return 201, issue_view_bytes(repo, issue), "application/json", {}
        if method == "GET":
            state = request.query_one("state", "open")
            issues = [i for i in repo.issues.values()
                      if state == "all" or i.state == state]
            issues.sort(key=lambda i: i.number)
            if request.query_one("sort") == "created" and request.query_one("direction", "asc") == "desc":
                issues.reverse()
            views = [issue_view(repo, i) for i in issues]
            page, extra = _paginate(request, views)
            return _ok(200, page, extra)
        return _err(404, "Not Found")

    if len(rest) == 2 and rest[0] == "issues" and rest[1].isdigit():
        issue = repo.issues.get(int(rest[1]))
        if issue is None:
            return _err(404, "Not Found")
        if method == "GET":
            return 200, issue_view_bytes(repo, issue), "application/json", {}
        if method == "PATCH":
            body = request.json_body()
            if body is _JSON_INVALID or not isinstance(body, dict):
                return _err(400, "Problems parsing JSON")
            with FORGE.lock:
                if isinstance(body.get("title"), str):
                    issue.title = body["title"]
                if isinstance(body.get("body"), str):
                    issue.body = body["body"]
                if "state" in body:
                    if body["state"] not in ("open", "closed"):
                        return _err(422, "Invalid state")
                    issue.state = body["state"]
                if isinstance(body.get("labels"), list):
                    names = []
                    for entry in body["labels"]:
                        if isinstance(entry, str):
                            names.append(entry)
                        elif isinstance(entry, dict) and isinstance(entry.get("name"), str):
                            names.append(entry["name"])
                    for n in names:
                        if n not in repo.labels:
                            return _err(422, "One or more labels do not exist in this repository")
                    issue.labels = names
                issue.touch()
            return 200, issue_view_bytes(repo, issue), "application/json", {}
        return _err(404, "Not Found")

    if len(rest) == 3 and rest[0] == "issues" and rest[1].isdigit() and rest[2] == "comments":
        issue = repo.issues.get(int(rest[1]))
        if issue is None:
            return _err(404, "Not Found")
        if method == "GET":
            views = [comment_view(repo, c) for c in issue.comments]
            page, extra = _paginate(request, views)
            return _ok(200, page, extra)
        if method == "POST":
            body = request.json_body()
            if body is _JSON_INVALID or not isinstance(body, dict):
                return _err(400, "Problems parsing JSON")
            text = body.get("body")
            if not isinstance(text, str):
                return _err(422, "Invalid comment")
            with FORGE.lock:
                comment = Comment(text)
                issue.comments.append(comment)
                issue.touch()
            return _ok(201, comment_view(repo, comment))
        return _err(404, "Not Found")

    if rest == ["pulls"]:
        if method == "POST":
            body = request.json_body()
            if body is _JSON_INVALID or not isinstance(body, dict):
                return _err(400, "Problems parsing JSON")
            title = body.get("title")
            head = body.get("head")
            base = body.get("base")
            if not isinstance(title, str) or not isinstance(head, str) or not isinstance(base, str):
                return _err(422, "Invalid pull request")
            pull = create_pull(repo, title, body.get("body") if isinstance(body.get("body"), str) else "", head, base)
            if pull is None:
                return _err(422, "Invalid head or base ref")
            return _ok(201, pull_view(repo, pull))
        if method == "GET":
            state = request.query_one("state")
            pulls = list(repo.pulls.values())
            if state is None or state == "open":
                pulls = [p for p in pulls if p.state == "open"]
            elif state == "closed":
                pulls = [p for p in pulls if p.state == "closed"]
            pulls.sort(key=lambda p: p.number)
            views = [pull_view(repo, p) for p in pulls]
            page, extra = _paginate(request, views)
            return _ok(200, page, extra)
        return _err(404, "Not Found")

    if len(rest) == 2 and rest[0] == "pulls" and rest[1].isdigit():
        pull = repo.pulls.get(int(rest[1]))
        if pull is None:
            return _err(404, "Not Found")
        if method == "GET":
            return _ok(200, pull_view(repo, pull))
        return _err(404, "Not Found")

    if len(rest) == 3 and rest[0] == "pulls" and rest[1].isdigit() and rest[2] == "files" and method == "GET":
        pull = repo.pulls.get(int(rest[1]))
        if pull is None:
            return _err(404, "Not Found")
        head_tip = repo.tip(pull.head_ref)
        base_tip = repo.tip(pull.base_ref)
        if head_tip is None or base_tip is None:
            return _ok(200, [])
        base = merge_base(head_tip, base_tip)
        base_tree = commit_tree(base) if base else EMPTY_TREE_OID
        files = []
        for path, status, old_oid, new_oid in tree_diff(base_tree, commit_tree(head_tip)):
            old_data = STORE.get(old_oid)[1] if old_oid else b""
            new_data = STORE.get(new_oid)[1] if new_oid else b""
            adds, dels = line_counts(old_data, new_data)
            files.append({"filename": path, "status": status, "additions": adds,
                          "deletions": dels, "changes": adds + dels, "sha": new_oid})
        page, extra = _paginate(request, files)
        return _ok(200, page, extra)

    if len(rest) == 3 and rest[0] == "pulls" and rest[1].isdigit() and rest[2] == "merge" and method == "PUT":
        pull = repo.pulls.get(int(rest[1]))
        if pull is None:
            return _err(404, "Not Found")
        body = request.json_body()
        method_name = "squash"
        if isinstance(body, dict) and isinstance(body.get("merge_method"), str):
            method_name = body["merge_method"]
        sha, failure = merge_pull(repo, pull, method_name)
        if failure is not None:
            return _err(failure, "Pull Request is not mergeable")
        return _ok(200, {"sha": sha, "merged": True, "message": "Pull Request successfully merged"})

    return _err(404, "Not Found")


def _rest_contents(request: Request, repo: Repo, path_segments: list):
    method = request.method
    segments = [s.encode() for s in path_segments]

    if method == "GET":
        refname = request.query_one("ref") or repo.default_branch
        start = resolve_ref(repo, refname)
        if start is None:
            return _err(404, "Not Found")
        tree = commit_tree(start)
        if not segments:
            return _ok(200, _dir_listing(tree, ""))
        found = lookup_path(tree, segments)
        if found is None:
            return _err(404, "Not Found")
        mode, oid = found
        path_str = "/".join(path_segments)
        if mode & 0o170000 == 0o040000:
            return _ok(200, _dir_listing(oid, path_str))
        entry = STORE.get(oid)
        data = entry[1] if entry else b""
        return _ok(200, {
            "type": "file", "name": path_segments[-1], "path": path_str, "sha": oid,
            "size": len(data), "encoding": "base64",
            "content": base64.b64encode(data).decode(),
        })

    if method == "PUT":
        body = request.json_body()
        if body is _JSON_INVALID or not isinstance(body, dict):
            return _err(400, "Problems parsing JSON")
        if not segments:
            return _err(422, "Invalid path")
        content = body.get("content")
        if not isinstance(content, str):
            return _err(422, "content is required")
        try:
            data = base64.b64decode(re.sub(r"\s+", "", content), validate=False)
        except Exception:
            return _err(422, "content is not valid base64")
        message = body.get("message")
        if not isinstance(message, str):
            message = ""
        branch = body.get("branch")
        if not isinstance(branch, str) or branch == "":
            branch = repo.default_branch
        with FORGE.lock:
            tip = repo.tip(branch)
            if tip is not None:
                tree = commit_tree(tip)
                parents = [tip]
            elif branch != repo.default_branch and repo.tip(repo.default_branch) is not None:
                tip = repo.tip(repo.default_branch)
                tree = commit_tree(tip)
                parents = [tip]
            else:
                tree = EMPTY_TREE_OID
                parents = []
            existing = lookup_path(tree, segments)
            sha_given = body.get("sha")
            if existing is not None and existing[0] & 0o170000 != 0o040000:
                if sha_given is None:
                    return _err(422, "sha wasn't supplied")
                if sha_given != existing[1]:
                    return _err(409, "sha does not match the current file")
            elif existing is None and sha_given is not None:
                return _err(422, "sha must not be supplied when creating a file")
            mode = existing[0] if existing is not None else 0o100644
            blob_oid = STORE.put("blob", data)
            new_tree = tree_set_path(tree, segments, blob_oid, mode)
            commit = STORE.build_commit(new_tree, parents, message, tick())
            repo.refs["refs/heads/" + branch] = commit
            repo.updated_ts = tick()
            status = 200 if existing is not None else 201
            return _ok(status, {
                "content": {"type": "file", "name": path_segments[-1],
                            "path": "/".join(path_segments), "sha": blob_oid,
                            "size": len(data), "encoding": "base64"},
                "commit": {"sha": commit, "message": message},
            })

    if method == "DELETE":
        body = request.json_body()
        if body is _JSON_INVALID or not isinstance(body, dict):
            return _err(400, "Problems parsing JSON")
        if not segments:
            return _err(422, "Invalid path")
        message = body.get("message")
        if not isinstance(message, str):
            message = ""
        branch = body.get("branch")
        if not isinstance(branch, str) or branch == "":
            branch = repo.default_branch
        with FORGE.lock:
            tip = repo.tip(branch)
            if tip is None:
                return _err(404, "Not Found")
            tree = commit_tree(tip)
            existing = lookup_path(tree, segments)
            if existing is None:
                return _err(404, "Not Found")
            sha_given = body.get("sha")
            if sha_given is None:
                return _err(422, "sha wasn't supplied")
            if sha_given != existing[1]:
                return _err(409, "sha does not match the current file")
            new_tree = tree_remove_path(tree, segments)
            commit = STORE.build_commit(new_tree, [tip], message, tick())
            repo.refs["refs/heads/" + branch] = commit
            repo.updated_ts = tick()
            return _ok(200, {"content": None, "commit": {"sha": commit, "message": message}})

    return _err(404, "Not Found")


def _dir_listing(tree_oid: str, prefix: str):
    items = []
    for mode, name, oid in STORE.tree_entries(tree_oid):
        is_dir = mode & 0o170000 == 0o040000
        entry = STORE.get(oid)
        items.append({
            "type": "dir" if is_dir else "file",
            "name": name.decode("utf-8", "replace"),
            "path": (prefix + "/" if prefix else "") + name.decode("utf-8", "replace"),
            "sha": oid,
            "size": 0 if is_dir or entry is None else len(entry[1]),
        })
    return items


# --------------------------------------------------------------------------
# Git smart HTTP
# --------------------------------------------------------------------------

def _pkt(payload: bytes) -> bytes:
    return b"%04x" % (len(payload) + 4) + payload


_FLUSH = b"0000"


class _PktReader:
    def __init__(self, data: bytes) -> None:
        self.data = data
        self.pos = 0

    def read(self):
        if self.pos >= len(self.data):
            return "end", b""
        if len(self.data) - self.pos < 4:
            raise ValueError("truncated pkt-line")
        try:
            size = int(self.data[self.pos:self.pos + 4], 16)
        except ValueError:
            raise ValueError("invalid pkt-line")
        if size == 0:
            self.pos += 4
            return "flush", b""
        if size == 1:
            self.pos += 4
            return "delim", b""
        if size == 2:
            self.pos += 4
            return "end", b""
        if size < 4 or self.pos + size > len(self.data):
            raise ValueError("pkt-line overruns body")
        payload = self.data[self.pos + 4:self.pos + size]
        self.pos += size
        return "data", payload

    def rest(self) -> bytes:
        out = self.data[self.pos:]
        self.pos = len(self.data)
        return out


def _peel_to_commit(oid: str) -> str:
    seen = set()
    while STORE.type_of(oid) == "tag" and oid not in seen:
        seen.add(oid)
        data = STORE.get(oid)[1]
        for line in data.split(b"\n"):
            if line.startswith(b"object "):
                oid = line[7:].decode()
                break
        else:
            break
    return oid


def _collect_tree(tree_oid: str, acc: set) -> None:
    if tree_oid in acc:
        return
    acc.add(tree_oid)
    for mode, _name, oid in STORE.tree_entries(tree_oid):
        if mode & 0o170000 == 0o040000:
            _collect_tree(oid, acc)
        else:
            acc.add(oid)


def _sideband_packets(data: bytes) -> bytes:
    out = bytearray()
    for i in range(0, len(data), 65515):
        out += _pkt(b"\x01" + data[i:i + 65515])
    return bytes(out)


_framed_cache: dict[tuple, bytes] = {}


def _framed_pack(oids) -> bytes:
    key = tuple(sorted(set(oids)))
    cached = _framed_cache.get(key)
    if cached is None:
        cached = _sideband_packets(build_pack(key))
        if len(_framed_cache) < 4096:
            _framed_cache[key] = cached
    return cached


def _advertisement(repo: Repo, service: str) -> bytes:
    refs = dict(repo.refs)
    if service == "git-upload-pack":
        caps = "multi_ack_detailed no-done side-band-64k thin-pack ofs-delta deepen-since deepen-not agent=forge/1.0"
    else:
        caps = "report-status side-band-64k delete-refs ofs-delta agent=forge/1.0"
    default_ref = "refs/heads/" + repo.default_branch
    if default_ref in refs:
        caps += " symref=HEAD:" + default_ref
    out = bytearray()
    out += _pkt(("# service=" + service + "\n").encode())
    out += _FLUSH
    lines = []
    head_oid = refs.get(default_ref, ZERO_OID)
    if refs:
        lines.append((head_oid, "HEAD"))
        for ref in sorted(refs):
            lines.append((refs[ref], ref))
            if ref.startswith("refs/tags/") and STORE.type_of(refs[ref]) == "tag":
                lines.append((_peel_to_commit(refs[ref]), ref + "^{}"))
    else:
        lines.append((ZERO_OID, "capabilities^{}"))
    for index, (oid, name) in enumerate(lines):
        line = (oid + " " + name).encode()
        if index == 0:
            line += b"\0" + caps.encode()
        out += _pkt(line + b"\n")
    out += _FLUSH
    return bytes(out)


def _v2_advertisement() -> bytes:
    out = bytearray()
    out += _pkt(b"version 2\n")
    out += _pkt(b"agent=forge/1.0\n")
    out += _pkt(b"ls-refs=unborn\n")
    out += _pkt(b"fetch=shallow wait-for-done\n")
    out += _pkt(b"object-format=sha1\n")
    out += _FLUSH
    return bytes(out)


def _plan_fetch(wants, haves, client_shallow, depth):
    """(object set to send, boundary commits, unshallowed commits)."""
    shallow_set = set(client_shallow)
    excluded: set = set()
    if haves:
        stack = []
        for have in haves:
            htype = STORE.type_of(have)
            if htype == "commit":
                stack.append(have)
            elif htype == "tag":
                excluded.add(have)
                stack.append(_peel_to_commit(have))
            elif htype in ("tree", "blob"):
                excluded.add(have)
        seen = set()
        while stack:
            commit = stack.pop()
            if commit in seen or not STORE.has(commit):
                continue
            seen.add(commit)
            excluded.add(commit)
            _collect_tree(commit_tree(commit), excluded)
            if commit in shallow_set:
                continue
            stack.extend(STORE.commit_parts(commit)[1])
    gen: dict[str, int] = {}
    queue = []
    extra: set = set()
    for want in wants:
        wtype = STORE.type_of(want)
        if wtype == "commit":
            queue.append((want, 1))
        elif wtype == "tag":
            extra.add(want)
            queue.append((_peel_to_commit(want), 1))
        elif wtype in ("tree", "blob"):
            extra.add(want)
    while queue:
        commit, generation = queue.pop(0)
        if commit in gen and gen[commit] <= generation:
            continue
        if depth is not None and generation > depth:
            continue
        gen[commit] = generation
        if depth is not None and generation == depth:
            continue
        for parent in STORE.commit_parts(commit)[1]:
            queue.append((parent, generation + 1))
    delivered: set = set()
    for commit in gen:
        if commit in excluded:
            continue
        delivered.add(commit)
        _collect_tree(commit_tree(commit), delivered)
    delivered |= extra
    delivered -= excluded
    boundary = sorted(c for c, g in gen.items() if depth is not None and g == depth)
    unshallowed = sorted(c for c in shallow_set
                         if c in gen and (depth is None or gen[c] < depth))
    return delivered, boundary, unshallowed


def _fetch_sections(wants, haves, client_shallow, depth, version2: bool) -> bytes:
    delivered, boundary, unshallowed = _plan_fetch(wants, haves, client_shallow, depth)
    out = bytearray()
    if version2:
        ack_lines = []
        if haves:
            common = [h for h in haves if STORE.type_of(h) == "commit"]
            if common:
                ack_lines = ["ACK " + h for h in common] + ["ready"]
            else:
                ack_lines = ["NAK"]
        else:
            ack_lines = ["NAK"]
        out += _pkt(b"acknowledgments\n")
        for line in ack_lines:
            out += _pkt(line.encode() + b"\n")
        out += _FLUSH
        if depth is not None or client_shallow:
            out += _pkt(b"shallow-info\n")
            for oid in boundary:
                out += _pkt(("shallow " + oid + "\n").encode())
            for oid in unshallowed:
                out += _pkt(("unshallow " + oid + "\n").encode())
            out += _FLUSH
        out += _pkt(b"packfile\n")
        out += _framed_pack(delivered)
        out += _FLUSH
    else:
        for oid in boundary:
            out += _pkt(("shallow " + oid + "\n").encode())
        for oid in unshallowed:
            out += _pkt(("unshallow " + oid + "\n").encode())
        out += _pkt(b"NAK\n")
        out += _framed_pack(delivered)
        out += _FLUSH
    return bytes(out)


def _upload_pack(request: Request, repo: Repo):
    body = request.body
    reader = _PktReader(body)
    try:
        kind, payload = reader.read()
    except ValueError:
        return 400, b"invalid pkt-line", "text/plain", {}
    if kind == "data" and payload.startswith(b"want "):
        # Protocol v0 fetch: want lines, flush, have lines, done.
        wants = []
        haves = []
        shallow = []
        depth = None
        line = payload.rstrip(b"\n")
        while True:
            text = line.split(b"\0")[0].decode("latin-1")
            if text.startswith("want "):
                wants.append(text[5:].strip())
            elif text.startswith("deepen "):
                try:
                    depth = int(text[7:].strip())
                except ValueError:
                    pass
            if kind != "data":
                break
            try:
                kind, payload = reader.read()
            except ValueError:
                return 400, b"invalid pkt-line", "text/plain", {}
            if kind == "flush":
                break
            line = payload.rstrip(b"\n")
        while True:
            try:
                kind, payload = reader.read()
            except ValueError:
                break
            if kind != "data":
                break
            text = payload.rstrip(b"\n").decode("latin-1")
            if text == "done":
                break
            if text.startswith("have "):
                haves.append(text[5:].strip())
            elif text.startswith("shallow "):
                shallow.append(text[8:].strip())
        return 200, _fetch_sections(wants, haves, shallow, depth, False), \
            "application/x-git-upload-pack-result", {}

    # Protocol v2: command section, delim, argument section, flush.
    command = None
    args = []
    in_args = False
    pending = (kind, payload)
    while True:
        kind, payload = pending
        if kind == "delim":
            in_args = True
        elif kind in ("flush", "end"):
            break
        elif kind == "data":
            text = payload.rstrip(b"\n").decode("latin-1")
            if not in_args:
                if text.startswith("command="):
                    command = text[len("command="):]
            else:
                args.append(text)
        try:
            pending = reader.read()
        except ValueError:
            return 400, b"invalid pkt-line", "text/plain", {}

    if command == "ls-refs":
        return 200, _ls_refs(repo, args), "application/x-git-upload-pack-result", {}
    if command == "fetch":
        wants, haves, shallow = [], [], []
        depth = None
        for arg in args:
            if arg.startswith("want "):
                wants.append(arg[5:].strip())
            elif arg.startswith("have "):
                haves.append(arg[5:].strip())
            elif arg.startswith("shallow "):
                shallow.append(arg[8:].strip())
            elif arg.startswith("deepen "):
                try:
                    depth = int(arg[7:].strip())
                except ValueError:
                    pass
        return 200, _fetch_sections(wants, haves, shallow, depth, True), \
            "application/x-git-upload-pack-result", {}
    return 400, b"unknown command", "text/plain", {}


def _ls_refs(repo: Repo, args) -> bytes:
    prefixes = [a[len("ref-prefix "):] for a in args if a.startswith("ref-prefix ")]
    want_symrefs = "symrefs" in args
    want_peel = "peel" in args
    want_unborn = "unborn" in args
    refs = dict(repo.refs)

    def included(name: str) -> bool:
        return not prefixes or any(name.startswith(p) for p in prefixes)

    out = bytearray()
    default_ref = "refs/heads/" + repo.default_branch
    head_oid = refs.get(default_ref)
    if included("HEAD"):
        if head_oid is not None:
            line = head_oid + " HEAD"
            if want_symrefs:
                line += " symref-target:" + default_ref
            out += _pkt(line.encode() + b"\n")
        elif want_unborn:
            line = "unborn HEAD"
            if want_symrefs:
                line += " symref-target:" + default_ref
            out += _pkt(line.encode() + b"\n")
    for ref in sorted(refs):
        if not included(ref):
            continue
        line = refs[ref] + " " + ref
        if want_peel and STORE.type_of(refs[ref]) == "tag":
            line += " peeled:" + _peel_to_commit(refs[ref])
        out += _pkt(line.encode() + b"\n")
    out += _FLUSH
    return bytes(out)


def _receive_pack(request: Request, repo: Repo):
    reader = _PktReader(request.body)
    commands = []
    try:
        while True:
            kind, payload = reader.read()
            if kind == "flush":
                break
            if kind == "end":
                break
            if kind != "data":
                return 400, b"invalid pkt-line", "text/plain", {}
            text = payload.rstrip(b"\n").split(b"\0")[0].decode("latin-1")
            parts = text.split(" ")
            if len(parts) != 3:
                return 400, b"invalid ref update", "text/plain", {}
            commands.append((parts[0], parts[1], parts[2]))
    except ValueError:
        return 400, b"invalid pkt-line", "text/plain", {}
    pack = reader.rest()
    unpack_ok = True
    unpack_detail = ""
    if pack:
        try:
            ingest_pack(pack)
        except Exception as exc:  # a bad pack must not kill the server
            unpack_ok = False
            unpack_detail = str(exc)
    results = []
    with FORGE.lock:
        for old, new, ref in commands:
            if new == ZERO_OID:
                repo.refs.pop(ref, None)
                results.append((ref, None))
                continue
            if not unpack_ok:
                results.append((ref, "unpacker error"))
                continue
            if not STORE.has(new):
                results.append((ref, "invalid object"))
                continue
            if ref.startswith("refs/heads/") and STORE.type_of(new) != "commit":
                results.append((ref, "invalid object"))
                continue
            current = repo.refs.get(ref, ZERO_OID)
            if current != old:
                results.append((ref, "stale info"))
                continue
            if ref.startswith("refs/heads/") and current != ZERO_OID \
                    and not is_ancestor(current, new):
                results.append((ref, "non-fast-forward"))
                continue
            repo.refs[ref] = new
            repo.updated_ts = tick()
            results.append((ref, None))
    report = bytearray()
    if unpack_ok:
        report += _pkt(b"unpack ok\n")
    else:
        report += _pkt(("unpack " + (unpack_detail or "error") + "\n").encode())
    for ref, reason in results:
        if reason is None:
            report += _pkt(("ok " + ref + "\n").encode())
        else:
            report += _pkt(("ng " + ref + " " + reason + "\n").encode())
    report += _FLUSH
    body = _sideband_packets(bytes(report)) + _FLUSH
    return 200, body, "application/x-git-receive-pack-result", {}


def git_dispatch(request: Request):
    owner = request.segments[0]
    repo_name = request.segments[1][:-len(".git")]
    repo = FORGE.find_repo(owner, repo_name)
    if repo is None:
        return 404, b'{"message":"Not Found"}', "application/json", {}
    if not authorized(request.headers):
        return 401, b'{"message":"Bad credentials"}', "application/json", {}
    rest = request.segments[2:]
    if rest == ["info", "refs"] and request.method == "GET":
        service = request.query_one("service", "")
        if service not in ("git-upload-pack", "git-receive-pack"):
            return 403, b"service not available", "text/plain", {}
        if service == "git-upload-pack" and request.headers.get("git-protocol") == "version=2":
            return 200, _v2_advertisement(), "application/x-git-upload-pack-advertisement", {}
        return 200, _advertisement(repo, service), \
            "application/x-" + service + "-advertisement", {}
    if rest == ["git-upload-pack"] and request.method == "POST":
        return _upload_pack(request, repo)
    if rest == ["git-receive-pack"] and request.method == "POST":
        return _receive_pack(request, repo)
    return 404, b'{"message":"Not Found"}', "application/json", {}


# --------------------------------------------------------------------------
# GraphQL v4
# --------------------------------------------------------------------------

class _GqlError(Exception):
    pass


_GQL_TOKEN = re.compile(r"""
    (?P<ws>[\s,]+)
  | (?P<comment>\#[^\n]*)
  | (?P<name>[_A-Za-z][_0-9A-Za-z]*)
  | (?P<float>-?\d+\.\d+(?:[eE][+-]?\d+)?)
  | (?P<int>-?\d+)
  | (?P<spread>\.\.\.)
  | (?P<punct>[!$():=@\[\]{}|&])
""", re.VERBOSE)


def _gql_tokenize(text: str):
    tokens = []
    pos = 0
    while pos < len(text):
        if text.startswith('"""', pos):
            end = text.find('"""', pos + 3)
            if end < 0:
                raise _GqlError("unterminated block string")
            tokens.append(("string", text[pos + 3:end]))
            pos = end + 3
            continue
        if text[pos] == '"':
            end = pos + 1
            while end < len(text):
                if text[end] == "\\":
                    end += 2
                    continue
                if text[end] == '"':
                    break
                end += 1
            raw = text[pos:end + 1]
            try:
                tokens.append(("string", json.loads(raw)))
            except Exception:
                raise _GqlError("invalid string literal")
            pos = end + 1
            continue
        match = _GQL_TOKEN.match(text, pos)
        if match is None:
            raise _GqlError("unexpected character %r" % text[pos])
        pos = match.end()
        kind = match.lastgroup
        if kind in ("ws", "comment"):
            continue
        tokens.append((kind, match.group()))
    tokens.append(("eof", ""))
    return tokens


class _GqlParser:
    def __init__(self, text: str) -> None:
        self.tokens = _gql_tokenize(text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def expect_punct(self, value: str) -> None:
        kind, val = self.next()
        if kind != "punct" or val != value:
            raise _GqlError("expected %r, got %r" % (value, val))

    def expect_name(self) -> str:
        kind, val = self.next()
        if kind != "name":
            raise _GqlError("expected a name, got %r" % val)
        return val

    def parse_document(self):
        operations = []
        fragments = {}
        while self.peek()[0] != "eof":
            kind, val = self.peek()
            if kind == "punct" and val == "{":
                operations.append(("query", None, {}, self.parse_selection_set()))
            elif kind == "name" and val in ("query", "mutation", "subscription"):
                self.next()
                name = None
                if self.peek()[0] == "name":
                    name = self.next()[1]
                defaults = {}
                if self.peek() == ("punct", "("):
                    defaults = self.parse_variable_definitions()
                self.skip_directives()
                operations.append((val, name, defaults, self.parse_selection_set()))
            elif kind == "name" and val == "fragment":
                self.next()
                frag_name = self.expect_name()
                if self.expect_name() != "on":
                    raise _GqlError("expected 'on' in fragment definition")
                type_condition = self.expect_name()
                self.skip_directives()
                fragments[frag_name] = (type_condition, self.parse_selection_set())
            else:
                raise _GqlError("unexpected token %r" % val)
        return operations, fragments

    def parse_variable_definitions(self):
        defaults = {}
        self.expect_punct("(")
        while self.peek() != ("punct", ")"):
            self.expect_punct("$")
            name = self.expect_name()
            self.expect_punct(":")
            self.parse_type()
            if self.peek() == ("punct", "="):
                self.next()
                defaults[name] = self.parse_value()
            self.skip_directives()
        self.next()
        return defaults

    def parse_type(self) -> None:
        if self.peek() == ("punct", "["):
            self.next()
            self.parse_type()
            self.expect_punct("]")
        else:
            self.expect_name()
        if self.peek() == ("punct", "!"):
            self.next()

    def skip_directives(self) -> None:
        while self.peek() == ("punct", "@"):
            self.next()
            self.expect_name()
            if self.peek() == ("punct", "("):
                self.parse_arguments()

    def parse_selection_set(self):
        self.expect_punct("{")
        selections = []
        while self.peek() != ("punct", "}"):
            selections.append(self.parse_selection())
        self.next()
        return selections

    def parse_selection(self):
        if self.peek()[0] == "spread":
            self.next()
            if self.peek()[0] == "name" and self.peek()[1] == "on":
                self.next()
                type_condition = self.expect_name()
                self.skip_directives()
                return ("inline", type_condition, self.parse_selection_set())
            name = self.expect_name()
            self.skip_directives()
            return ("spread", name)
        name = self.expect_name()
        alias = None
        if self.peek() == ("punct", ":"):
            self.next()
            alias = name
            name = self.expect_name()
        args = {}
        if self.peek() == ("punct", "("):
            args = self.parse_arguments()
        self.skip_directives()
        selection = None
        if self.peek() == ("punct", "{"):
            selection = self.parse_selection_set()
        return ("field", alias, name, args, selection)

    def parse_arguments(self):
        args = {}
        self.expect_punct("(")
        while self.peek() != ("punct", ")"):
            name = self.expect_name()
            self.expect_punct(":")
            args[name] = self.parse_value()
        self.next()
        return args

    def parse_value(self):
        kind, val = self.next()
        if kind == "punct" and val == "$":
            return ("var", self.expect_name())
        if kind == "int":
            return int(val)
        if kind == "float":
            return float(val)
        if kind == "string":
            return val
        if kind == "name":
            if val == "true":
                return True
            if val == "false":
                return False
            if val == "null":
                return None
            return ("enum", val)
        if kind == "punct" and val == "[":
            items = []
            while self.peek() != ("punct", "]"):
                items.append(self.parse_value())
            self.next()
            return ("list", items)
        if kind == "punct" and val == "{":
            obj = {}
            while self.peek() != ("punct", "}"):
                name = self.expect_name()
                self.expect_punct(":")
                obj[name] = self.parse_value()
            self.next()
            return ("object", obj)
        raise _GqlError("unexpected value token %r" % val)


def _gql_eval(value, variables, defaults):
    if isinstance(value, tuple):
        kind = value[0]
        if kind == "var":
            if value[1] in variables:
                return variables[value[1]]
            return defaults.get(value[1])
        if kind == "enum":
            return value[1]
        if kind == "list":
            return [_gql_eval(v, variables, defaults) for v in value[1]]
        if kind == "object":
            return {k: _gql_eval(v, variables, defaults) for k, v in value[1].items()}
    return value


def _gid(type_name: str, key: str) -> str:
    return base64.b64encode(("%s:%s" % (type_name, key)).encode()).decode()


def _ungid(gid_value):
    if not isinstance(gid_value, str):
        return None, None
    try:
        text = base64.b64decode(gid_value.encode()).decode()
    except Exception:
        return None, None
    type_name, _, key = text.partition(":")
    return type_name, key


_GQL_FIELDS = {
    "Query": ["viewer", "repository", "node", "rateLimit"],
    "Mutation": ["createIssue", "closeIssue", "createPullRequest", "mergePullRequest", "addComment"],
    "User": ["id", "login", "name", "email", "url", "createdAt", "updatedAt"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner", "description",
                   "isPrivate", "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                   "hasWikiEnabled", "issue", "issues", "pullRequest", "pullRequests",
                   "createdAt", "updatedAt", "url"],
    "Issue": ["id", "number", "title", "state", "body", "author", "repository", "labels",
              "comments", "createdAt", "updatedAt", "closedAt", "url"],
    "PullRequest": ["id", "number", "title", "body", "state", "merged", "mergeable",
                    "headRefName", "baseRefName", "headRef", "baseRef", "files",
                    "repository", "author", "createdAt", "updatedAt", "mergedAt",
                    "additions", "deletions", "changedFiles"],
    "Ref": ["name", "prefix", "target"],
    "GitObject": ["id", "oid", "abbreviatedOid"],
    "Label": ["id", "name", "color", "description"],
    "IssueComment": ["id", "body", "author", "createdAt", "updatedAt"],
    "PageInfo": ["hasNextPage", "hasPreviousPage", "startCursor", "endCursor"],
    "IssueConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "PullRequestConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "IssueCommentConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "LabelConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "PullRequestFileConnection": ["nodes", "edges", "pageInfo", "totalCount"],
    "PullRequestFile": ["path", "additions", "deletions", "changeType"],
    "CreateIssuePayload": ["issue", "clientMutationId"],
    "CloseIssuePayload": ["issue", "clientMutationId"],
    "CreatePullRequestPayload": ["pullRequest", "clientMutationId"],
    "MergePullRequestPayload": ["pullRequest", "clientMutationId"],
    "AddCommentPayload": ["commentEdge", "subject", "clientMutationId"],
    "IssueCommentEdge": ["node", "cursor"],
    "__Type": ["name", "kind", "description", "fields", "enumValues", "possibleTypes",
               "inputFields", "ofType", "specifiedByURL"],
    "__Field": ["name", "description", "args", "type", "isDeprecated", "deprecationReason"],
    "__EnumValue": ["name", "description", "isDeprecated", "deprecationReason"],
    "__InputValue": ["name", "description", "type", "defaultValue"],
}

_GQL_ENUMS = {
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION"],
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "RepositoryPermission": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"],
    "OrderDirection": ["ASC", "DESC"],
    "IssueOrderField": ["CREATED_AT", "UPDATED_AT", "COMMENTS"],
}


def _gql_cursor(index: int) -> str:
    return base64.b64encode(("cursor:%d" % index).encode()).decode()


def _gql_cursor_index(value):
    if not isinstance(value, str):
        return None
    try:
        text = base64.b64decode(value.encode()).decode()
        if text.startswith("cursor:"):
            return int(text[len("cursor:"):])
    except Exception:
        pass
    return None


def _gql_connection(items, first, after):
    start = 0
    if after is not None:
        idx = _gql_cursor_index(after)
        if idx is not None:
            start = idx + 1
    if first is None:
        page = items[start:]
    else:
        page = items[start:start + int(first)]
    end = start + len(page)
    page_info = {
        "hasNextPage": end < len(items),
        "hasPreviousPage": start > 0,
        "startCursor": _gql_cursor(start) if page else None,
        "endCursor": _gql_cursor(end - 1) if page else None,
    }
    return {"nodes": page, "pageInfo": page_info, "totalCount": len(items)}


def _gql_pull_files(repo: Repo, pull: Pull):
    head_tip = repo.tip(pull.head_ref)
    base_tip = repo.tip(pull.base_ref)
    if head_tip is None or base_tip is None:
        return []
    base = merge_base(head_tip, base_tip)
    base_tree = commit_tree(base) if base else EMPTY_TREE_OID
    files = []
    for path, status, old_oid, new_oid in tree_diff(base_tree, commit_tree(head_tip)):
        old_data = STORE.get(old_oid)[1] if old_oid else b""
        new_data = STORE.get(new_oid)[1] if new_oid else b""
        adds, dels = line_counts(old_data, new_data)
        change = {"added": "ADDED", "modified": "MODIFIED", "removed": "DELETED"}[status]
        files.append({"path": path, "additions": adds, "deletions": dels, "changeType": change})
    return files


def _gql_resolve(type_name: str, payload, field: str, args: dict):
    if type_name == "Query":
        if field == "viewer":
            return ("User", FORGE.owner_login)
        if field == "repository":
            repo = FORGE.find_repo(str(args.get("owner", "")), str(args.get("name", "")))
            return ("Repository", repo) if repo else None
        if field == "node":
            return _gql_node(args.get("id"))
        if field == "rateLimit":
            return None
    if type_name == "Mutation":
        return _gql_mutation(field, args)
    if type_name == "User":
        login = payload
        if field == "login":
            return login
        if field == "id":
            return _gid("User", login)
        if field == "name":
            return login
        if field == "email":
            return ""
        if field == "url":
            return "/" + login
        if field in ("createdAt", "updatedAt"):
            return iso_of(_EPOCH)
        return None
    if type_name == "Repository":
        repo: Repo = payload
        if field == "id":
            return _gid("Repository", str(repo.id))
        if field == "databaseId":
            return repo.id
        if field == "name":
            return repo.name
        if field == "nameWithOwner":
            return repo.owner + "/" + repo.name
        if field == "owner":
            return ("User", repo.owner)
        if field == "description":
            return repo.description
        if field == "isPrivate":
            return repo.private
        if field == "defaultBranchRef":
            if repo.tip(repo.default_branch) is not None:
                return ("Ref", (repo, repo.default_branch))
            return None
        if field == "viewerPermission":
            return "ADMIN"
        if field in ("hasIssuesEnabled", "hasWikiEnabled"):
            return True
        if field == "issue":
            issue = repo.issues.get(int(args.get("number", 0)))
            return ("Issue", (repo, issue)) if issue else None
        if field == "issues":
            states = args.get("states")
            issues = list(repo.issues.values())
            if states:
                wanted = {str(s).lower() for s in states}
                issues = [i for i in issues if i.state in wanted]
            issues.sort(key=lambda i: i.number)
            order = args.get("orderBy")
            if isinstance(order, dict) and str(order.get("direction", "")).upper() == "DESC":
                issues.reverse()
            conn = _gql_connection([("Issue", (repo, i)) for i in issues],
                                   args.get("first"), args.get("after"))
            return ("IssueConnection", conn)
        if field == "pullRequest":
            pull = repo.pulls.get(int(args.get("number", 0)))
            return ("PullRequest", (repo, pull)) if pull else None
        if field == "pullRequests":
            states = args.get("states")
            pulls = list(repo.pulls.values())
            if states:
                wanted = {str(s).upper() for s in states}
                def pr_state(p):
                    return "MERGED" if p.merged else p.state.upper()
                pulls = [p for p in pulls if pr_state(p) in wanted]
            else:
                pulls = [p for p in pulls if p.state == "open"]
            pulls.sort(key=lambda p: p.number)
            conn = _gql_connection([("PullRequest", (repo, p)) for p in pulls],
                                   args.get("first"), args.get("after"))
            return ("PullRequestConnection", conn)
        if field == "createdAt":
            return iso_of(repo.created_ts)
        if field == "updatedAt":
            return iso_of(repo.updated_ts)
        if field == "url":
            return "/" + repo.owner + "/" + repo.name
        return None
    if type_name == "Issue":
        repo, issue = payload
        if field == "id":
            return _gid("Issue", "%d:%d" % (repo.id, issue.number))
        if field == "number":
            return issue.number
        if field == "title":
            return issue.title
        if field == "body":
            return issue.body
        if field == "state":
            return issue.state.upper()
        if field == "author":
            return ("User", repo.owner)
        if field == "repository":
            return ("Repository", repo)
        if field == "labels":
            nodes = [("Label", (repo, repo.labels[n])) for n in issue.labels if n in repo.labels]
            return ("LabelConnection", {"nodes": nodes, "pageInfo": None, "totalCount": len(nodes)})
        if field == "comments":
            nodes = [("IssueComment", (repo, issue, c)) for c in issue.comments]
            conn = _gql_connection(nodes, args.get("first"), args.get("after"))
            return ("IssueCommentConnection", conn)
        if field == "createdAt":
            return iso_of(issue.created_ts)
        if field == "updatedAt":
            return iso_of(issue.updated_ts)
        if field == "closedAt":
            return iso_of(issue.updated_ts) if issue.state == "closed" else None
        if field == "url":
            return "/%s/%s/issues/%d" % (repo.owner, repo.name, issue.number)
        return None
    if type_name == "PullRequest":
        repo, pull = payload
        if field == "id":
            return _gid("PullRequest", "%d:%d" % (repo.id, pull.number))
        if field == "number":
            return pull.number
        if field == "title":
            return pull.title
        if field == "body":
            return pull.body
        if field == "state":
            return "MERGED" if pull.merged else pull.state.upper()
        if field == "merged":
            return pull.merged
        if field == "mergeable":
            if pull.state != "open":
                return "UNKNOWN"
            _tree, conflicts, _base = pull_mergeable(repo, pull)
            return "CONFLICTING" if conflicts else "MERGEABLE"
        if field == "headRefName":
            return pull.head_ref
        if field == "baseRefName":
            return pull.base_ref
        if field == "headRef":
            return ("Ref", (repo, pull.head_ref))
        if field == "baseRef":
            return ("Ref", (repo, pull.base_ref))
        if field == "files":
            nodes = [("PullRequestFile", f) for f in _gql_pull_files(repo, pull)]
            conn = _gql_connection(nodes, args.get("first"), args.get("after"))
            return ("PullRequestFileConnection", conn)
        if field == "repository":
            return ("Repository", repo)
        if field == "author":
            return ("User", repo.owner)
        if field == "createdAt":
            return iso_of(pull.created_ts)
        if field == "updatedAt":
            return iso_of(pull.updated_ts)
        if field == "mergedAt":
            return iso_of(pull.merged_ts) if pull.merged_ts else None
        if field in ("additions", "deletions", "changedFiles"):
            files = _gql_pull_files(repo, pull)
            if field == "additions":
                return sum(f["additions"] for f in files)
            if field == "deletions":
                return sum(f["deletions"] for f in files)
            return len(files)
        return None
    if type_name == "Ref":
        repo, branch = payload
        if field == "name":
            return branch
        if field == "prefix":
            return "refs/heads/"
        if field == "target":
            tip = repo.tip(branch)
            return ("GitObject", tip) if tip else None
        return None
    if type_name == "GitObject":
        if field in ("id", "oid"):
            return payload
        if field == "abbreviatedOid":
            return payload[:7] if payload else None
        return None
    if type_name == "Label":
        _repo, label = payload
        if field == "id":
            return _gid("Label", str(label["id"]))
        if field == "name":
            return label["name"]
        if field == "color":
            return label["color"]
        if field == "description":
            return label.get("description")
        return None
    if type_name == "IssueComment":
        repo, _issue, comment = payload
        if field == "id":
            return _gid("IssueComment", "%d:%d:%d" % (repo.id, _issue.number, comment.id))
        if field == "body":
            return comment.body
        if field == "author":
            return ("User", repo.owner)
        if field in ("createdAt", "updatedAt"):
            return iso_of(comment.created_ts)
        return None
    if type_name in ("IssueConnection", "PullRequestConnection", "IssueCommentConnection",
                     "LabelConnection", "PullRequestFileConnection"):
        if field == "nodes":
            return payload["nodes"]
        if field == "pageInfo":
            info = payload.get("pageInfo")
            return ("PageInfo", info) if info else None
        if field == "totalCount":
            return payload.get("totalCount", len(payload["nodes"]))
        if field == "edges":
            return []
        return None
    if type_name == "PageInfo":
        return payload.get(field)
    if type_name in ("CreateIssuePayload", "CloseIssuePayload"):
        if field == "issue":
            return payload.get("issue")
        return None
    if type_name in ("CreatePullRequestPayload", "MergePullRequestPayload"):
        if field == "pullRequest":
            return payload.get("pullRequest")
        return None
    if type_name == "AddCommentPayload":
        if field == "commentEdge":
            return payload.get("commentEdge")
        if field == "subject":
            return payload.get("subject")
        return None
    if type_name == "IssueCommentEdge":
        if field == "node":
            return payload.get("node")
        if field == "cursor":
            return _gql_cursor(0)
        return None
    if type_name == "PullRequestFile":
        return payload.get(field)
    if type_name == "__Type":
        if field == "name":
            return payload
        if field == "kind":
            return "ENUM" if payload in _GQL_ENUMS else "OBJECT"
        if field == "fields":
            names = _GQL_FIELDS.get(payload)
            return [("__Field", n) for n in names] if names is not None else None
        if field == "enumValues":
            values = _GQL_ENUMS.get(payload)
            return [("__EnumValue", v) for v in values] if values is not None else None
        return None
    if type_name == "__Field":
        if field == "name":
            return payload
        if field == "args":
            return []
        if field == "isDeprecated":
            return False
        return None
    if type_name == "__EnumValue":
        if field == "name":
            return payload
        if field == "isDeprecated":
            return False
        return None
    return None


def _gql_node(gid_value):
    type_name, key = _ungid(gid_value)
    if type_name == "Repository":
        try:
            repo = FORGE.repos_by_id.get(int(key))
        except (TypeError, ValueError):
            return None
        return ("Repository", repo) if repo else None
    if type_name in ("Issue", "PullRequest"):
        try:
            repo_id, number = key.split(":")
            repo = FORGE.repos_by_id.get(int(repo_id))
            number = int(number)
        except (TypeError, ValueError):
            return None
        if repo is None:
            return None
        if type_name == "Issue":
            issue = repo.issues.get(number)
            return ("Issue", (repo, issue)) if issue else None
        pull = repo.pulls.get(number)
        return ("PullRequest", (repo, pull)) if pull else None
    if type_name == "User":
        return ("User", key)
    if type_name == "IssueComment":
        try:
            repo_id, number, comment_id = key.split(":")
            repo = FORGE.repos_by_id.get(int(repo_id))
            issue = repo.issues.get(int(number)) if repo else None
        except (TypeError, ValueError):
            return None
        if issue is None:
            return None
        for comment in issue.comments:
            if comment.id == int(comment_id):
                return ("IssueComment", (repo, issue, comment))
        return None
    return None


def _gql_repo_from_gid(gid_value) -> Repo | None:
    node = _gql_node(gid_value)
    if node is not None and node[0] == "Repository":
        return node[1]
    return None


def _gql_mutation(field: str, args: dict):
    inp = args.get("input")
    if not isinstance(inp, dict):
        raise _GqlError("mutation %s needs an input object" % field)
    if field == "createIssue":
        repo = _gql_repo_from_gid(inp.get("repositoryId"))
        if repo is None:
            raise _GqlError("repository not found")
        issue = create_issue(repo, str(inp.get("title", "")), str(inp.get("body", "") or ""), [])
        if issue is None:
            raise _GqlError("could not create issue")
        return ("CreateIssuePayload", {"issue": ("Issue", (repo, issue))})
    if field == "closeIssue":
        node = _gql_node(inp.get("issueId"))
        if node is None or node[0] != "Issue":
            raise _GqlError("issue not found")
        repo, issue = node[1]
        with FORGE.lock:
            issue.state = "closed"
            issue.touch()
        return ("CloseIssuePayload", {"issue": ("Issue", (repo, issue))})
    if field == "createPullRequest":
        repo = _gql_repo_from_gid(inp.get("repositoryId"))
        if repo is None:
            raise _GqlError("repository not found")
        pull = create_pull(repo, str(inp.get("title", "")), str(inp.get("body", "") or ""),
                           str(inp.get("headRefName", "")), str(inp.get("baseRefName", "")))
        if pull is None:
            raise _GqlError("could not create pull request")
        return ("CreatePullRequestPayload", {"pullRequest": ("PullRequest", (repo, pull))})
    if field == "mergePullRequest":
        node = _gql_node(inp.get("pullRequestId"))
        if node is None or node[0] != "PullRequest":
            raise _GqlError("pull request not found")
        repo, pull = node[1]
        method = str(inp.get("mergeMethod", "SQUASH")).lower()
        if method not in ("squash", "merge"):
            method = "squash"
        _sha, failure = merge_pull(repo, pull, method)
        if failure is not None:
            raise _GqlError("pull request is not mergeable")
        return ("MergePullRequestPayload", {"pullRequest": ("PullRequest", (repo, pull))})
    if field == "addComment":
        node = _gql_node(inp.get("subjectId"))
        if node is None or node[0] != "Issue":
            raise _GqlError("subject not found")
        repo, issue = node[1]
        with FORGE.lock:
            comment = Comment(str(inp.get("body", "")))
            issue.comments.append(comment)
            issue.touch()
        comment_obj = ("IssueComment", (repo, issue, comment))
        return ("AddCommentPayload", {
            "commentEdge": ("IssueCommentEdge", {"node": comment_obj}),
            "subject": ("Issue", (repo, issue)),
        })
    raise _GqlError("unknown mutation %s" % field)


def _gql_collect(selections, type_name: str, fragments: dict, depth: int = 0):
    """Flatten a selection set into {response key: (field, args, sub-selection)}."""
    out: dict[str, tuple] = {}
    if depth > 16:
        return out
    for sel in selections or []:
        if sel[0] == "field":
            _, alias, name, args, sub = sel
            key = alias or name
            if key in out:
                prev = out[key]
                merged = (prev[2] or []) + (sub or [])
                out[key] = (prev[0], prev[1], merged)
            else:
                out[key] = (name, args, sub)
        elif sel[0] == "inline":
            _, condition, sub = sel
            if condition == type_name:
                for k, v in _gql_collect(sub, type_name, fragments, depth + 1).items():
                    out.setdefault(k, v)
        elif sel[0] == "spread":
            frag = fragments.get(sel[1])
            if frag is not None and frag[0] == type_name:
                for k, v in _gql_collect(frag[1], type_name, fragments, depth + 1).items():
                    out.setdefault(k, v)
    return out


def _gql_exec_set(selections, type_name: str, payload, variables: dict, defaults: dict,
                  fragments: dict, errors: list):
    out = {}
    for key, (field, raw_args, sub) in _gql_collect(selections, type_name, fragments).items():
        args = {k: _gql_eval(v, variables, defaults) for k, v in raw_args.items()}
        if field == "__typename":
            out[key] = type_name
            continue
        if type_name == "Query" and field == "__type":
            name = args.get("name")
            if name in _GQL_FIELDS or name in _GQL_ENUMS:
                out[key] = _gql_complete(("__Type", name), sub, variables, defaults, fragments, errors)
            else:
                out[key] = None
            continue
        if field not in _GQL_FIELDS.get(type_name, ()):
            errors.append({"message": "Field '%s' doesn't exist on type '%s'" % (field, type_name)})
            out[key] = None
            continue
        try:
            value = _gql_resolve(type_name, payload, field, args)
        except _GqlError as exc:
            errors.append({"message": str(exc)})
            out[key] = None
            continue
        out[key] = _gql_complete(value, sub, variables, defaults, fragments, errors)
    return out


def _gql_complete(value, sub, variables, defaults, fragments, errors):
    if value is None:
        return None
    if isinstance(value, tuple) and len(value) == 2 and isinstance(value[0], str) \
            and value[0] in _GQL_FIELDS:
        return _gql_exec_set(sub, value[0], value[1], variables, defaults, fragments, errors)
    if isinstance(value, list):
        return [_gql_complete(v, sub, variables, defaults, fragments, errors) for v in value]
    return value


def _gql_execute(document: str, variables: dict, operation_name):
    try:
        operations, fragments = _GqlParser(document).parse_document()
    except _GqlError as exc:
        return {"errors": [{"message": str(exc)}]}
    chosen = None
    for op in operations:
        if operation_name is None or op[1] == operation_name:
            chosen = op
            break
    if chosen is None:
        return {"errors": [{"message": "operation not found"}]}
    op_type, _name, defaults, selections = chosen
    root = "Mutation" if op_type == "mutation" else "Query"
    errors: list = []
    data = _gql_exec_set(selections, root, None, variables or {}, defaults, fragments, errors)
    result = {"data": data}
    if errors:
        result["errors"] = errors
    return result


def graphql_dispatch(request: Request):
    if request.method != "POST":
        return 405, b'{"message":"Method Not Allowed"}', "application/json", {}
    if not authorized(request.headers):
        return 401, b'{"message":"Bad credentials"}', "application/json", {}
    try:
        body = json.loads(request.body.decode("utf-8"))
    except Exception:
        return 400, b'{"errors":[{"message":"Invalid JSON body"}]}', "application/json", {}
    if isinstance(body, list):
        results = []
        for entry in body:
            if isinstance(entry, dict):
                results.append(_gql_execute(str(entry.get("query", "")),
                                            entry.get("variables") or {},
                                            entry.get("operationName")))
            else:
                results.append({"errors": [{"message": "Invalid operation"}]})
        return 200, _json_bytes(results), "application/json", {}
    if isinstance(body, dict):
        result = _gql_execute(str(body.get("query", "")), body.get("variables") or {},
                              body.get("operationName"))
        return 200, _json_bytes(result), "application/json", {}
    return 400, b'{"errors":[{"message":"Invalid request body"}]}', "application/json", {}


# --------------------------------------------------------------------------
# MCP (Model Context Protocol, Streamable HTTP, revision 2026-07-28)
# --------------------------------------------------------------------------

_MCP_SERVER_INFO = {"name": "forge", "version": "1.0.0"}

_MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a new repository owned by the authenticated user.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "The repository name."},
                "description": {"type": "string", "description": "A short description."},
                "private": {"type": "boolean", "description": "Whether the repository is private."},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Get a repository by owner and name.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner."},
                "repo": {"type": "string", "description": "The repository name."},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "list_repos",
        "description": "List the repositories owned by the authenticated user.",
        "inputSchema": {"type": "object", "properties": {}},
    },
    {
        "name": "create_issue",
        "description": "Create an issue in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner."},
                "repo": {"type": "string", "description": "The repository name."},
                "title": {"type": "string", "description": "The issue title."},
                "body": {"type": "string", "description": "The issue body."},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "list_issues",
        "description": "List the issues of a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner."},
                "repo": {"type": "string", "description": "The repository name."},
                "state": {"type": "string", "description": "open, closed or all."},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "get_issue",
        "description": "Get one issue of a repository by its number.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner."},
                "repo": {"type": "string", "description": "The repository name."},
                "issue_number": {"type": "integer", "description": "The issue number."},
            },
            "required": ["owner", "repo", "issue_number"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Open a pull request from a head branch into a base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner."},
                "repo": {"type": "string", "description": "The repository name."},
                "title": {"type": "string", "description": "The pull request title."},
                "body": {"type": "string", "description": "The pull request body."},
                "head": {"type": "string", "description": "The head branch."},
                "base": {"type": "string", "description": "The base branch."},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Merge a pull request by its number.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "The repository owner."},
                "repo": {"type": "string", "description": "The repository name."},
                "pull_number": {"type": "integer", "description": "The pull request number."},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]

_MCP_TOOLS_BY_NAME = {tool["name"]: tool for tool in _MCP_TOOLS}


class _ToolError(Exception):
    pass


def _mcp_repo(args) -> Repo:
    repo = FORGE.find_repo(str(args.get("owner", "")), str(args.get("repo", "")))
    if repo is None:
        raise _ToolError("repository not found")
    return repo


def _mcp_call_tool(name: str, args: dict):
    if name == "create_repo":
        repo = FORGE.create_repo(str(args["name"]),
                                 str(args.get("description", "") or ""),
                                 bool(args.get("private", False)))
        if repo is None:
            repo = FORGE.find_repo(FORGE.owner_login, str(args["name"]))
        return repo_view(repo)
    if name == "get_repo":
        return repo_view(_mcp_repo(args))
    if name == "list_repos":
        return {"repositories": [repo_view(r) for r in FORGE.own_repos()]}
    if name == "create_issue":
        repo = _mcp_repo(args)
        issue = create_issue(repo, str(args["title"]), str(args.get("body", "") or ""), [])
        if issue is None:
            raise _ToolError("could not create issue")
        return issue_view(repo, issue)
    if name == "list_issues":
        repo = _mcp_repo(args)
        state = str(args.get("state", "open"))
        issues = [i for i in repo.issues.values() if state == "all" or i.state == state]
        issues.sort(key=lambda i: i.number)
        return {"issues": [issue_view(repo, i) for i in issues]}
    if name == "get_issue":
        repo = _mcp_repo(args)
        issue = repo.issues.get(int(args["issue_number"]))
        if issue is None:
            raise _ToolError("issue not found")
        return issue_view(repo, issue)
    if name == "create_pull_request":
        repo = _mcp_repo(args)
        pull = create_pull(repo, str(args["title"]), str(args.get("body", "") or ""),
                           str(args["head"]), str(args["base"]))
        if pull is None:
            raise _ToolError("could not create pull request")
        return pull_view(repo, pull)
    if name == "merge_pull_request":
        repo = _mcp_repo(args)
        pull = repo.pulls.get(int(args["pull_number"]))
        if pull is None:
            raise _ToolError("pull request not found")
        _sha, failure = merge_pull(repo, pull, "squash")
        if failure is not None:
            raise _ToolError("pull request is not mergeable")
        return pull_view(repo, pull)
    raise _ToolError("unknown tool")


def _mcp_result(req_id, result):
    return 200, _json_bytes({"jsonrpc": "2.0", "id": req_id, "result": result}), \
        "application/json", {}


def _mcp_error(req_id, code: int, message: str, status: int = 200):
    return status, _json_bytes({"jsonrpc": "2.0", "id": req_id,
                                "error": {"code": code, "message": message}}), \
        "application/json", {}


def _mcp_handle(msg: dict):
    method = msg.get("method")
    params = msg.get("params")
    if not isinstance(params, dict):
        params = {}
    if "id" not in msg:
        return 202, b"", None, {}
    req_id = msg["id"]
    if method == "server/discover":
        return _mcp_result(req_id, {
            "supportedVersions": ["2026-07-28", "2025-11-25", "2025-06-18"],
            "capabilities": {"tools": {}},
            "serverInfo": dict(_MCP_SERVER_INFO),
            "_meta": {"io.modelcontextprotocol/serverInfo": dict(_MCP_SERVER_INFO)},
        })
    if method == "initialize":
        return _mcp_result(req_id, {
            "protocolVersion": params.get("protocolVersion", "2025-11-25"),
            "capabilities": {"tools": {}},
            "serverInfo": dict(_MCP_SERVER_INFO),
        })
    if method == "ping":
        return _mcp_result(req_id, {})
    if method == "tools/list":
        return _mcp_result(req_id, {"tools": _MCP_TOOLS})
    if method == "tools/call":
        name = params.get("name")
        arguments = params.get("arguments")
        if not isinstance(arguments, dict):
            arguments = {}
        tool = _MCP_TOOLS_BY_NAME.get(name) if isinstance(name, str) else None
        if tool is None:
            return _mcp_error(req_id, -32602, "unknown tool: %s" % (name,))
        missing = [p for p in tool["inputSchema"].get("required", [])
                   if arguments.get(p) is None]
        if missing:
            return _mcp_error(req_id, -32602,
                              "missing required argument(s): %s" % ", ".join(missing))
        try:
            result_obj = _mcp_call_tool(name, arguments)
        except _ToolError as exc:
            return _mcp_result(req_id, {
                "content": [{"type": "text", "text": str(exc)}],
                "isError": True,
            })
        return _mcp_result(req_id, {
            "content": [{"type": "text", "text": json.dumps(result_obj)}],
            "structuredContent": result_obj,
            "isError": False,
        })
    return _mcp_error(req_id, -32601, "method not found: %s" % (method,))


def mcp_dispatch(request: Request):
    if request.method == "DELETE":
        return 200, b"{}", "application/json", {}
    if request.method != "POST":
        return 405, b'{"message":"Method Not Allowed"}', "application/json", {}
    if not authorized(request.headers):
        return 401, b'{"message":"Bad credentials"}', "application/json", {}
    try:
        msg = json.loads(request.body.decode("utf-8"))
    except Exception:
        return _mcp_error(None, -32700, "Parse error", status=400)
    if isinstance(msg, list):
        results = []
        for entry in msg:
            if isinstance(entry, dict) and "id" in entry:
                _status, body, _ctype, _extra = _mcp_handle(entry)
                results.append(json.loads(body))
        return 200, _json_bytes(results), "application/json", {}
    if not isinstance(msg, dict):
        return _mcp_error(None, -32600, "Invalid Request", status=400)
    return _mcp_handle(msg)


if __name__ == "__main__":
    main()
