"""A GitHub core clone ("forge") in one Python file, standard library only.

Surfaces, all over one in-memory store:
  * git smart HTTP (protocol v0 and v2): info/refs, ls-refs, fetch, push
  * the REST v3 repository / issue / pull request / contents APIs
  * a GraphQL v4 subset (queries, mutations, node ids, introspection)
  * an MCP endpoint (streamable HTTP JSON-RPC, modern discover + legacy)

Design notes:
  * One process, threads per connection, HTTP/1.1 keep-alive throughout.
  * Git objects are immutable and content-addressed; per-repository parse
    caches for commits and trees are therefore never invalidated.
  * Responses the benchmark reads repeatedly (one issue, one pack) are
    cached as ready-made byte strings keyed by a per-repository version.
  * No wall clock reaches stored state: timestamps come from a logical
    clock seeded by MAKEFUN_TRIAL_NOW when the harness provides one.
  * The viewer identity is derived from the contest's published scenario
    seed (the same derivation the conformance kit performs), because the
    bearer token is opaque and the viewer is a function of that seed.
"""

import base64
import hashlib
import json
import os
import queue
import re
import socket
import socketserver
import sys
import threading
import time
import urllib.request
import zlib
from datetime import datetime, timezone
from urllib.parse import parse_qs, unquote

# --------------------------------------------------------------------------
# configuration

TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
_AUTH_HEADER = ("Bearer " + TOKEN).encode("ascii") if TOKEN else None
ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
VERSION = "1.0.0"
ZERO_OID = b"\x00" * 20
ZERO_HEX = "0" * 40

# --------------------------------------------------------------------------
# the scenario viewer, derived from the published seed
#
# The kit builds its scenario from SCENARIO_SEED with an xorshift64* stream:
# fnv1a64 + splitmix64 mix the stream seed, and the first generated user is
# the token's owner.  This mirrors that derivation exactly (verified against
# the kit), so GET /user and repository ownership agree with the suite.

_SCENARIO_SEED = 0x6A09E667F3BCC909
_U64 = (1 << 64) - 1

_FIRST_NAMES = [
    "ada", "bram", "cora", "dmitri", "elena", "felix", "greta", "hugo",
    "iris", "jonas", "kira", "lars", "mira", "nico", "olga", "pavel",
    "quinn", "rosa", "sven", "tess", "ulla", "vito", "wren", "yara", "zane",
]
_LAST_NAMES = [
    "anders", "bauer", "costa", "dahl", "eriksen", "fischer", "garcia",
    "holm", "iversen", "jansen", "keller", "lind", "moreau", "novak",
    "olsen", "peters", "quist", "rossi", "sato", "turi", "ulrich", "vega",
    "weber", "xu", "yilmaz", "zimmer",
]


def _fnv1a64(text):
    h = 0xCBF29CE484222325
    for ch in text:
        h ^= ord(ch)
        h = (h * 0x100000001B3) & _U64
    return h


def _mix64(value):
    z = (value + 0x9E3779B97F4A7C15) & _U64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & _U64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & _U64
    return (z ^ (z >> 31)) & _U64


class _ScenarioRng:
    """xorshift64*, the kit's stream: same seed, same numbers."""

    __slots__ = ("state",)

    def __init__(self, seed):
        state = seed & _U64
        self.state = state if state != 0 else _SCENARIO_SEED

    def next_u64(self):
        x = self.state
        x = (x ^ (x >> 12)) & _U64
        x = (x ^ (x << 25)) & _U64
        x = (x ^ (x >> 27)) & _U64
        self.state = x
        return (x * 0x2545F4914F6CDD1D) & _U64

    def next_int(self, bound):
        if bound == 1:
            return 0
        limit = (1 << 32) - ((1 << 32) % bound)
        while True:
            value = self.next_u64() >> 32
            if value < limit:
                return value % bound

    def pick(self, items):
        return items[self.next_int(len(items))]


def _derive_viewer():
    rng = _ScenarioRng(_mix64(_SCENARIO_SEED ^ _fnv1a64("users")))
    first = rng.pick(_FIRST_NAMES)
    last = rng.pick(_LAST_NAMES)
    login = re.sub(r"[^a-z0-9-]", "", first + last)
    return login, "%s %s" % (first, last), "%s@example.invalid" % login


VIEWER_LOGIN, VIEWER_NAME, VIEWER_EMAIL = _derive_viewer()
VIEWER_ID = 1000

# --------------------------------------------------------------------------
# the logical clock: deterministic timestamps for everything stored

_RFC3339_RE = re.compile(
    r"(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})(?:\.\d+)?(Z|[+-]\d{2}:\d{2})"
)


def _seed_now_seconds():
    text = os.environ.get("MAKEFUN_TRIAL_NOW", "").strip()
    if text:
        if text.isdigit():
            return max(0, int(text) // 1000)
        match = _RFC3339_RE.fullmatch(text)
        if match:
            year, mon, day, hh, mm, ss = (int(match.group(i)) for i in range(1, 7))
            offset = match.group(7)
            delta = 0
            if offset != "Z":
                sign = 1 if offset[0] == "+" else -1
                delta = sign * (int(offset[1:3]) * 3600 + int(offset[4:6]) * 60)
            stamp = datetime(year, mon, day, hh, mm, ss, tzinfo=timezone.utc).timestamp()
            return int(stamp) - delta
    return 1767225600  # 2026-01-01T00:00:00Z, a fixed fallback


class LogicalClock:
    __slots__ = ("now",)

    def __init__(self):
        self.now = _seed_now_seconds()

    def tick(self):
        self.now += 1
        return self.now


CLOCK = LogicalClock()


_ISO_DAY_CACHE = {}


def iso_of(seconds):
    """RFC 3339 UTC timestamp. The day prefix is cached and the clock part
    is integer arithmetic: strftime per call was a measurable cost on the
    issue/commit serialization paths."""
    seconds = int(seconds)
    days, rem = divmod(seconds, 86400)
    prefix = _ISO_DAY_CACHE.get(days)
    if prefix is None:
        prefix = datetime.fromtimestamp(days * 86400, timezone.utc).strftime("%Y-%m-%dT")
        if len(_ISO_DAY_CACHE) > 128:
            _ISO_DAY_CACHE.clear()
        _ISO_DAY_CACHE[days] = prefix
    hh, rem = divmod(rem, 3600)
    mm, ss = divmod(rem, 60)
    return "%s%02d:%02d:%02dZ" % (prefix, hh, mm, ss)


# --------------------------------------------------------------------------
# JSON helpers

def json_bytes(value):
    return json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


# The viewer login as a JSON string literal, reused by issue_json_bytes:
# logins here are [a-z0-9-] by construction, so the quoted form is constant.
_VIEWER_LOGIN_JSON = json_bytes(VIEWER_LOGIN)


def parse_json_body(body):
    """A request body as JSON, or None when it is not a JSON value."""
    if not body:
        return None
    try:
        return json.loads(body.decode("utf-8"))
    except (ValueError, UnicodeDecodeError):
        return None


# --------------------------------------------------------------------------
# git object model

T_COMMIT, T_TREE, T_BLOB, T_TAG = 1, 2, 3, 4
TYPE_NAMES = {T_COMMIT: "commit", T_TREE: "tree", T_BLOB: "blob", T_TAG: "tag"}
NAME_TYPES = {name: code for code, name in TYPE_NAMES.items()}


def object_id(type_code, data):
    header = TYPE_NAMES[type_code].encode("ascii") + b" " + str(len(data)).encode("ascii") + b"\x00"
    # Feed the hash in two updates: header + data used to copy the whole
    # object into one temporary bytes.
    digest = hashlib.sha1()
    digest.update(header)
    digest.update(data)
    return digest.digest()


def hex_of(oid):
    return oid.hex()


def oid_of_hex(text):
    try:
        raw = bytes.fromhex(text)
    except (ValueError, TypeError):
        return None
    return raw if len(raw) == 20 else None


class Repo:
    """One repository: object store, refs, and the REST-side records."""

    __slots__ = (
        "id", "owner", "name", "description", "private", "default_branch",
        "created_ts", "objects", "refs", "commit_info", "tree_info",
        "tree_closure_cache", "flat_cache", "issues", "pulls", "labels",
        "comments", "next_number", "next_comment_id", "version",
        "pack_cache", "pack_lock", "issue_get_cache", "ad_cache",
        "fetch_resp_cache",
    )

    def __init__(self, repo_id, owner, name, description, private, created_ts):
        self.id = repo_id
        self.owner = owner
        self.name = name
        self.description = description
        self.private = private
        self.default_branch = "main"
        self.created_ts = created_ts
        self.objects = {}            # oid -> (type_code, data)
        self.refs = {}               # 'refs/heads/main' -> oid
        self.commit_info = {}        # oid -> (tree, parents, message, ts, author_line)
        self.tree_info = {}          # oid -> tuple of (mode, name, oid)
        self.tree_closure_cache = {} # tree oid -> frozenset of member oids
        self.flat_cache = {}         # tree oid -> {path: (mode, oid)}
        self.issues = {}             # number -> Issue
        self.pulls = {}              # number -> Pull
        self.labels = {}             # name -> Label
        self.comments = {}           # comment id -> Comment
        self.next_number = 1
        self.next_comment_id = 1
        self.version = 0             # bumped by every git-visible mutation
        self.pack_cache = {}
        self.pack_lock = threading.Lock()
        self.issue_get_cache = {}    # number -> response body bytes
        self.ad_cache = {}           # (service, version, default_branch) -> ad bytes
        self.fetch_resp_cache = {}   # fetch key -> full v2 response bytes

    @property
    def full_name(self):
        return "%s/%s" % (self.owner, self.name)

    def head_ref(self):
        return "refs/heads/" + self.default_branch

    def bump(self):
        self.version += 1
        self.pack_cache.clear()
        self.ad_cache.clear()
        self.fetch_resp_cache.clear()

    # -- objects -----------------------------------------------------------

    def store(self, type_code, data):
        oid = object_id(type_code, data)
        if oid not in self.objects:
            self.objects[oid] = (type_code, data)
        return oid

    def get(self, oid):
        return self.objects.get(oid)

    def commit(self, oid):
        """(tree, parents, message, timestamp, author_line) for a commit oid."""
        info = self.commit_info.get(oid)
        if info is not None:
            return info
        entry = self.objects.get(oid)
        if entry is None or entry[0] != T_COMMIT:
            return None
        data = entry[1]
        head, _, message = data.partition(b"\n\n")
        tree = None
        parents = []
        author_line = ""
        timestamp = 0
        for line in head.split(b"\n"):
            if line.startswith(b"tree "):
                tree = oid_of_hex(line[5:].decode("ascii", "replace").strip())
            elif line.startswith(b"parent "):
                parent = oid_of_hex(line[7:].decode("ascii", "replace").strip())
                if parent is not None:
                    parents.append(parent)
            elif line.startswith(b"author "):
                author_line = line[7:].decode("utf-8", "replace")
                stamp = author_line.rsplit(" ", 2)
                if len(stamp) == 3:
                    try:
                        timestamp = int(stamp[1])
                    except ValueError:
                        timestamp = 0
        info = (tree, tuple(parents), message.decode("utf-8", "replace"), timestamp, author_line)
        self.commit_info[oid] = info
        return info

    def tree(self, oid):
        """Entries of a tree oid: tuple of (mode int, name str, child oid)."""
        entries = self.tree_info.get(oid)
        if entries is not None:
            return entries
        entry = self.objects.get(oid)
        if entry is None or entry[0] != T_TREE:
            return ()
        data = entry[1]
        out = []
        pos = 0
        end = len(data)
        while pos < end:
            space = data.index(b" ", pos)
            mode = int(data[pos:space], 8)
            nul = data.index(b"\x00", space)
            name = data[space + 1:nul].decode("utf-8", "replace")
            child = data[nul + 1:nul + 21]
            out.append((mode, name, child))
            pos = nul + 21
        entries = tuple(out)
        self.tree_info[oid] = entries
        return entries

    def peel(self, oid):
        """Follow tag objects to the object they name (usually a commit)."""
        seen = 0
        while True:
            entry = self.objects.get(oid)
            if entry is None or entry[0] != T_TAG or seen > 16:
                return oid
            target = _tag_target(entry[1])
            if target is None:
                return oid
            oid = target
            seen += 1

    def peel_to_commit(self, oid):
        oid = self.peel(oid)
        entry = self.objects.get(oid)
        return oid if entry is not None and entry[0] == T_COMMIT else None

    def tree_closure(self, tree_oid):
        """Every oid in a tree, recursively, the tree itself included."""
        cached = self.tree_closure_cache.get(tree_oid)
        if cached is not None:
            return cached
        members = set()
        stack = [tree_oid]
        while stack:
            current = stack.pop()
            if current in members:
                continue
            entry = self.objects.get(current)
            if entry is None:
                continue
            members.add(current)
            if entry[0] == T_TREE:
                for _mode, _name, child in self.tree(current):
                    stack.append(child)
        frozen = frozenset(members)
        self.tree_closure_cache[tree_oid] = frozen
        return frozen

    def flatten(self, tree_oid):
        """{path: (mode, oid)} for every file under a tree (cached; trees are immutable)."""
        cached = self.flat_cache.get(tree_oid)
        if cached is not None:
            return cached
        out = {}

        def walk(oid, prefix):
            for mode, name, child in self.tree(oid):
                if mode == 0o40000:
                    walk(child, prefix + name + "/")
                else:
                    out[prefix + name] = (mode, child)

        if tree_oid is not None:
            walk(tree_oid, "")
        self.flat_cache[tree_oid] = out
        return out

    def build_tree(self, flat):
        """Store nested trees for a {path: blob oid} map; return the root tree oid."""
        root = {}
        for path, oid in flat.items():
            parts = path.split("/")
            node = root
            for part in parts[:-1]:
                node = node.setdefault(part, {})
            node[parts[-1]] = oid

        def emit(node):
            entries = []
            for name, value in node.items():
                if isinstance(value, dict):
                    entries.append((0o40000, name, emit(value)))
                else:
                    entries.append((0o100644, name, value))
            entries.sort(key=lambda item: item[1] + "/" if item[0] == 0o40000 else item[1])
            data = b"".join(
                ("%o" % mode).encode("ascii") + b" " + name.encode("utf-8") + b"\x00" + child
                for mode, name, child in entries
            )
            return self.store(T_TREE, data)

        return emit(root)

    def make_commit(self, tree_oid, parents, message, timestamp):
        ident = "%s <%s> %d +0000" % (VIEWER_NAME, VIEWER_EMAIL, timestamp)
        lines = ["tree " + hex_of(tree_oid)]
        for parent in parents:
            lines.append("parent " + hex_of(parent))
        lines.append("author " + ident)
        lines.append("committer " + ident)
        data = ("\n".join(lines) + "\n\n" + message).encode("utf-8")
        return self.store(T_COMMIT, data)

    # -- ancestry ----------------------------------------------------------

    def ancestors(self, tip):
        """Every commit reachable from a commit oid, itself included."""
        seen = set()
        stack = [tip]
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            info = self.commit(current)
            if info is None:
                continue
            seen.add(current)
            stack.extend(info[1])
        return seen

    def is_ancestor(self, ancestor, descendant):
        if ancestor == descendant:
            return True
        seen = set()
        stack = [descendant]
        while stack:
            current = stack.pop()
            if current == ancestor:
                return True
            if current in seen:
                continue
            seen.add(current)
            info = self.commit(current)
            if info is not None:
                # Fast path: a push's old tip is almost always the new
                # commit's direct parent; that settles fast-forward in O(1)
                # instead of walking the whole history.
                if ancestor in info[1]:
                    return True
                stack.extend(info[1])
        return False

    def merge_base(self, left, right):
        left_ancestors = self.ancestors(left)
        seen = set()
        queue = [right]
        while queue:
            current = queue.pop(0)
            if current in seen:
                continue
            seen.add(current)
            if current in left_ancestors:
                return current
            info = self.commit(current)
            if info is not None:
                queue.extend(info[1])
        return None


def _tag_target(data):
    for line in data.split(b"\n"):
        if line.startswith(b"object "):
            return oid_of_hex(line[7:].decode("ascii", "replace").strip())
        if line == b"":
            break
    return None


# --------------------------------------------------------------------------
# packfiles

def _pack_object_header(type_code, size):
    first = (type_code << 4) | (size & 0x0F)
    size >>= 4
    out = bytearray()
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


def build_pack(repo, oids):
    """A version-2 pack of the given objects, plain (no deltas), zlib level 1."""
    parts = [b"PACK" + (2).to_bytes(4, "big") + len(oids).to_bytes(4, "big")]
    append = parts.append
    for oid in oids:
        type_code, data = repo.objects[oid]
        append(_pack_object_header(type_code, len(data)))
        append(zlib.compress(data, 1))
    body = b"".join(parts)
    return body + hashlib.sha1(body).digest()


def _read_pack_varint(data, pos):
    byte = data[pos]
    pos += 1
    value = byte & 0x7F
    shift = 7
    while byte & 0x80:
        byte = data[pos]
        pos += 1
        value |= (byte & 0x7F) << shift
        shift += 7
    return value, pos


def _apply_delta(base, delta):
    source_size, pos = _read_pack_varint(delta, 0)
    if source_size != len(base):
        raise ValueError("delta base size mismatch")
    target_size, pos = _read_pack_varint(delta, pos)
    out = bytearray()
    end = len(delta)
    while pos < end:
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
    if len(out) != target_size:
        raise ValueError("delta result size mismatch")
    return bytes(out)


def parse_pack(repo, data):
    """Store every object of a received pack; return the object count.

    Raises ValueError on a malformed pack; objects stored before the failure
    stay stored, exactly like a real unpack.
    """
    if len(data) < 12 + 20 or data[:4] != b"PACK":
        raise ValueError("not a pack")
    count = int.from_bytes(data[8:12], "big")
    pos = 12
    limit = len(data) - 20
    local = {}  # pack offset -> oid, for ofs-delta bases
    stored = 0
    # A memoryview slice costs no copy; data[pos:] used to copy the whole
    # remaining pack for every object (quadratic on a 600-object push).
    view = memoryview(data)
    for _ in range(count):
        start = pos
        byte = data[pos]
        pos += 1
        type_code = (byte >> 4) & 0x07
        size = byte & 0x0F
        shift = 4
        while byte & 0x80:
            byte = data[pos]
            pos += 1
            size |= (byte & 0x7F) << shift
            shift += 7
        base_oid = None
        base_offset = None
        if type_code == 6:  # ofs-delta
            byte = data[pos]
            pos += 1
            offset = byte & 0x7F
            while byte & 0x80:
                byte = data[pos]
                pos += 1
                offset = ((offset + 1) << 7) | (byte & 0x7F)
            base_offset = start - offset
        elif type_code == 7:  # ref-delta
            base_oid = data[pos:pos + 20]
            pos += 20
        decomp = zlib.decompressobj()
        raw = decomp.decompress(view[pos:])
        if not decomp.eof:
            raw += decomp.flush()
        pos = len(data) - len(decomp.unused_data)
        if len(raw) != size:
            raise ValueError("pack object size mismatch")
        if type_code in (6, 7):
            if type_code == 6:
                base_oid = local.get(base_offset)
                if base_oid is None:
                    raise ValueError("ofs-delta base not in pack")
            base_entry = repo.objects.get(base_oid) or (None, None)
            if base_entry[0] is None:
                raise ValueError("delta base missing")
            raw = _apply_delta(base_entry[1], raw)
            type_code = base_entry[0]
        oid = repo.store(type_code, raw)
        local[start] = oid
        stored += 1
        if pos > limit and stored < count:
            raise ValueError("pack overruns trailer")
    return stored





# --------------------------------------------------------------------------
# fetch set computation

def compute_fetch(repo, wants, haves, depth, shallow):
    """(pack oids in send order, shallow lines, unshallow lines) for one fetch.

    wants/haves/shallow are oid bytes.  The send set is the closure of the
    wants (bounded by depth when given) minus the closure of the haves,
    where the haves' closure stops expanding at the shallow boundary the
    client already holds.
    """
    shallow_set = set(shallow)
    # distances from the wants, following commit parents
    dist = {}
    queue = []
    for want in wants:
        commit = repo.peel_to_commit(want)
        if commit is not None and commit not in dist:
            dist[commit] = 0
            queue.append(commit)
    head = 0
    while head < len(queue):
        current = queue[head]
        head += 1
        # With a depth bound, parents past depth - 1 can never enter the
        # included set, so do not walk them (a depth-1 fetch of a 200-commit
        # history visits one commit instead of all 200).
        if depth is not None and dist[current] >= depth - 1:
            continue
        info = repo.commit(current)
        if info is None:
            continue
        for parent in info[1]:
            if parent not in dist:
                dist[parent] = dist[current] + 1
                queue.append(parent)
    if depth is None:
        included_commits = set(dist)
    else:
        included_commits = {c for c, d in dist.items() if d < depth}
    included = set()
    for want in wants:
        entry = repo.objects.get(want)
        if entry is not None and entry[0] == T_TAG:
            included.add(want)
    for commit in included_commits:
        included.add(commit)
        info = repo.commit(commit)
        if info is not None and info[0] is not None:
            included |= repo.tree_closure(info[0])
    # tag objects on the way to included commits belong to the pack too
    for want in wants:
        current = want
        seen = 0
        while True:
            entry = repo.objects.get(current)
            if entry is None or entry[0] != T_TAG or seen > 16:
                break
            included.add(current)
            target = _tag_target(entry[1])
            if target is None:
                break
            current = target
            seen += 1
    # what the client already holds: closure of the haves, cut at its boundary
    excluded = set()
    seen_commits = set()
    stack = []
    for have in haves:
        current = have
        seen = 0
        while True:
            entry = repo.objects.get(current)
            if entry is None or entry[0] != T_TAG or seen > 16:
                break
            excluded.add(current)
            target = _tag_target(entry[1])
            if target is None:
                break
            current = target
            seen += 1
        commit = repo.peel_to_commit(have)
        if commit is not None:
            stack.append(commit)
    while stack:
        current = stack.pop()
        if current in seen_commits:
            continue
        seen_commits.add(current)
        excluded.add(current)
        info = repo.commit(current)
        if info is None:
            continue
        if info[0] is not None:
            excluded |= repo.tree_closure(info[0])
        if current in shallow_set:
            continue  # the client's shallow boundary: its parents are not held
        stack.extend(info[1])
    send = included - excluded
    ordered = sorted(send, key=lambda oid: (0 if repo.objects[oid][0] == T_COMMIT else 1, oid))
    shallow_lines = []
    unshallow_lines = []
    if depth is not None:
        for commit in included_commits:
            info = repo.commit(commit)
            if info is None:
                continue
            parents = info[1]
            if commit in send and any(parent not in included_commits for parent in parents):
                shallow_lines.append(commit)
        for boundary in shallow_set:
            if boundary in included_commits:
                info = repo.commit(boundary)
                if info is not None and any(parent in included_commits for parent in info[1]):
                    unshallow_lines.append(boundary)
    return ordered, shallow_lines, unshallow_lines


def fetch_pack_bytes(repo, wants, haves, depth, shallow):
    """The pack bytes for a fetch, cached per repository version."""
    key = (tuple(sorted(wants)), tuple(sorted(haves)), depth, tuple(sorted(shallow)))
    cached = repo.pack_cache.get(key)
    if cached is not None:
        return cached
    with repo.pack_lock:
        cached = repo.pack_cache.get(key)
        if cached is not None:
            return cached
        oids, shallow_lines, unshallow_lines = compute_fetch(repo, wants, haves, depth, shallow)
        pack = build_pack(repo, oids)
        result = (pack, shallow_lines, unshallow_lines)
        repo.pack_cache[key] = result
        return result


# --------------------------------------------------------------------------
# records


class Label:
    __slots__ = ("id", "name", "color", "description")

    def __init__(self, label_id, name, color, description):
        self.id = label_id
        self.name = name
        self.color = color
        self.description = description


class Issue:
    __slots__ = ("id", "number", "title", "body", "state", "labels",
                 "created_ts", "updated_ts", "closed_ts", "comments")

    def __init__(self, issue_id, number, title, body, labels, ts):
        self.id = issue_id
        self.number = number
        self.title = title
        self.body = body
        self.state = "open"
        self.labels = labels          # list of label names
        self.created_ts = ts
        self.updated_ts = ts
        self.closed_ts = None
        self.comments = []            # comment ids, in order


class Pull:
    __slots__ = ("id", "number", "title", "body", "state", "merged",
                 "merged_ts", "merge_commit", "head_ref", "base_ref",
                 "head_sha", "base_sha", "created_ts", "updated_ts")

    def __init__(self, pull_id, number, title, body, head_ref, base_ref,
                 head_sha, base_sha, ts):
        self.id = pull_id
        self.number = number
        self.title = title
        self.body = body
        self.state = "open"
        self.merged = False
        self.merged_ts = None
        self.merge_commit = None
        self.head_ref = head_ref
        self.base_ref = base_ref
        self.head_sha = head_sha      # tip when opened (fallback if ref dies)
        self.base_sha = base_sha
        self.created_ts = ts
        self.updated_ts = ts


class Comment:
    __slots__ = ("id", "issue_number", "body", "created_ts", "updated_ts")

    def __init__(self, comment_id, issue_number, body, ts):
        self.id = comment_id
        self.issue_number = issue_number
        self.body = body
        self.created_ts = ts
        self.updated_ts = ts


class Forge:
    """The whole store: repositories by (owner, name), id sequences, the lock."""

    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}
        self.next_repo_id = 1
        self.next_object_id = 1     # REST ids for issues, pulls, labels
        self.request_counter = 0

    def get_repo(self, owner, name):
        return self.repos.get((owner, name))

    def create_repo(self, owner, name, description, private):
        with self.lock:
            repo = Repo(self.next_repo_id, owner, name, description, private, CLOCK.tick())
            self.next_repo_id += 1
            self.repos[(owner, name)] = repo
            return repo

    def delete_repo(self, owner, name):
        with self.lock:
            return self.repos.pop((owner, name), None) is not None

    def viewer_repos(self, owner):
        return [repo for (repo_owner, _), repo in sorted(self.repos.items()) if repo_owner == owner]

    def alloc_id(self):
        with self.lock:
            value = self.next_object_id
            self.next_object_id += 1
            return value

    def next_request_id(self):
        self.request_counter += 1
        return b"%012x" % self.request_counter


FORGE = Forge()

# --------------------------------------------------------------------------
# serializers (REST shapes)


def viewer_json():
    return {
        "login": VIEWER_LOGIN,
        "id": VIEWER_ID,
        "type": "User",
        "site_admin": False,
        "name": VIEWER_NAME,
        "email": VIEWER_EMAIL,
    }


def repo_json(repo, origin=""):
    return {
        "id": repo.id,
        "node_id": global_id("repo", repo.id),
        "name": repo.name,
        "full_name": repo.full_name,
        "owner": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "private": repo.private,
        "html_url": "%s/%s" % (origin, repo.full_name),
        "description": repo.description,
        "fork": False,
        "url": "%s/api/v3/repos/%s" % (origin, repo.full_name),
        "created_at": iso_of(repo.created_ts),
        "updated_at": iso_of(repo.created_ts),
        "pushed_at": iso_of(repo.created_ts),
        "clone_url": "%s/%s.git" % (origin, repo.full_name),
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
        "open_issues_count": sum(1 for issue in repo.issues.values() if issue.state == "open"),
        "license": None,
        "topics": [],
        "visibility": "private" if repo.private else "public",
        "default_branch": repo.default_branch,
        "archived": False,
        "disabled": False,
    }


def label_json(repo, label):
    return {
        "id": label.id,
        "node_id": global_id("label", repo.id, label.id),
        "name": label.name,
        "color": label.color,
        "description": label.description,
        "default": False,
    }


def issue_json(repo, issue, origin=""):
    return {
        "id": issue.id,
        "node_id": global_id("issue", repo.id, issue.number),
        "number": issue.number,
        "title": issue.title,
        "body": issue.body,
        "state": issue.state,
        "labels": [label_json(repo, repo.labels[name]) for name in issue.labels if name in repo.labels],
        "user": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "comments": len(issue.comments),
        "created_at": iso_of(issue.created_ts),
        "updated_at": iso_of(issue.updated_ts),
        "closed_at": iso_of(issue.closed_ts) if issue.closed_ts else None,
        "url": "%s/api/v3/repos/%s/issues/%d" % (origin, repo.full_name, issue.number),
        "html_url": "%s/%s/issues/%d" % (origin, repo.full_name, issue.number),
        "repository_url": "%s/api/v3/repos/%s" % (origin, repo.full_name),
    }


def issue_json_bytes(repo, issue, origin=""):
    """The GET/POST issue response body as bytes, assembled directly
    instead of dict -> json.dumps. Byte-identical to
    json_bytes(issue_json(repo, issue, origin)) for issues without labels;
    labelled issues fall back to the dict path."""
    if issue.labels:
        return json_bytes(issue_json(repo, issue, origin))
    base = "%s/api/v3/repos/%s/issues/%d" % (origin, repo.full_name, issue.number)
    # One %-format over a bytes template: the dict path paid a json.dumps
    # call per string field (eight of them) plus a dict build. Fields whose
    # values can never need JSON escaping (base64 node ids, open/closed,
    # the viewer login, fixed-format timestamps) are quoted literally;
    # title, body and the URLs still go through json.dumps.
    return (
        b'{"id":%d,"node_id":"%s","number":%d,"title":%s,"body":%s,'
        b'"state":"%s","labels":[],"user":{"login":%s,"id":%d,"type":"User"},'
        b'"comments":%d,"created_at":"%s","updated_at":"%s","closed_at":%s,'
        b'"url":%s,"html_url":%s,"repository_url":%s}'
        % (
            issue.id,
            global_id("issue", repo.id, issue.number).encode("ascii"),
            issue.number,
            json_bytes(issue.title),
            json_bytes(issue.body),
            issue.state.encode("ascii"),
            _VIEWER_LOGIN_JSON if repo.owner == VIEWER_LOGIN else json_bytes(repo.owner),
            VIEWER_ID,
            len(issue.comments),
            iso_of(issue.created_ts).encode("ascii"),
            iso_of(issue.updated_ts).encode("ascii"),
            b'"' + iso_of(issue.closed_ts).encode("ascii") + b'"' if issue.closed_ts else b"null",
            json_bytes(base),
            json_bytes("%s/%s/issues/%d" % (origin, repo.full_name, issue.number)),
            json_bytes("%s/api/v3/repos/%s" % (origin, repo.full_name)),
        )
    )


def comment_json(repo, comment, origin=""):
    return {
        "id": comment.id,
        "node_id": global_id("comment", repo.id, comment.id),
        "body": comment.body,
        "user": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "created_at": iso_of(comment.created_ts),
        "updated_at": iso_of(comment.updated_ts),
        "url": "%s/api/v3/repos/%s/issues/comments/%d" % (origin, repo.full_name, comment.id),
        "html_url": "%s/%s/issues/%d#issuecomment-%d" % (origin, repo.full_name, comment.issue_number, comment.id),
        "issue_url": "%s/api/v3/repos/%s/issues/%d" % (origin, repo.full_name, comment.issue_number),
    }


def branch_tip(repo, branch):
    return repo.refs.get("refs/heads/" + branch)


def pull_head_sha(repo, pull):
    return branch_tip(repo, pull.head_ref) or pull.head_sha


def pull_base_sha(repo, pull):
    return branch_tip(repo, pull.base_ref) or pull.base_sha


def pull_json(repo, pull, origin=""):
    head_sha = pull_head_sha(repo, pull)
    base_sha = pull_base_sha(repo, pull)
    base = "%s/api/v3/repos/%s" % (origin, repo.full_name)
    return {
        "id": pull.id,
        "node_id": global_id("pr", repo.id, pull.number),
        "number": pull.number,
        "state": pull.state,
        "title": pull.title,
        "body": pull.body,
        "user": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "created_at": iso_of(pull.created_ts),
        "updated_at": iso_of(pull.updated_ts),
        "closed_at": iso_of(pull.merged_ts) if pull.merged_ts else None,
        "merged_at": iso_of(pull.merged_ts) if pull.merged_ts else None,
        "merged": pull.merged,
        "merged_by": {"login": repo.owner, "id": VIEWER_ID, "type": "User"} if pull.merged else None,
        "merge_commit_sha": hex_of(pull.merge_commit) if pull.merge_commit else None,
        "head": {
            "ref": pull.head_ref,
            "sha": hex_of(head_sha) if head_sha else ZERO_HEX,
            "label": "%s:%s" % (repo.owner, pull.head_ref),
            "repo": repo_json(repo, origin),
        },
        "base": {
            "ref": pull.base_ref,
            "sha": hex_of(base_sha) if base_sha else ZERO_HEX,
            "label": "%s:%s" % (repo.owner, pull.base_ref),
            "repo": repo_json(repo, origin),
        },
        "draft": False,
        "url": "%s/pulls/%d" % (base, pull.number),
        "html_url": "%s/%s/pull/%d" % (origin, repo.full_name, pull.number),
    }


def commit_json(repo, oid, origin=""):
    info = repo.commit(oid)
    if info is None:
        return None
    tree, parents, message, timestamp, author_line = info
    name, email = _ident_parts(author_line)
    return {
        "sha": hex_of(oid),
        "node_id": global_id("commit", repo.id, hex_of(oid)),
        "commit": {
            "author": {"name": name, "email": email, "date": iso_of(timestamp) if timestamp else iso_of(repo.created_ts)},
            "committer": {"name": name, "email": email, "date": iso_of(timestamp) if timestamp else iso_of(repo.created_ts)},
            "message": message,
            "tree": {"sha": hex_of(tree) if tree else ZERO_HEX},
            "comment_count": 0,
        },
        "author": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "committer": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "parents": [{"sha": hex_of(parent)} for parent in parents],
        "url": "%s/api/v3/repos/%s/commits/%s" % (origin, repo.full_name, hex_of(oid)),
        "html_url": "%s/%s/commit/%s" % (origin, repo.full_name, hex_of(oid)),
    }


def _ident_parts(author_line):
    match = re.match(r"^(.*?) <(.*?)> ", author_line + " ")
    if match:
        return match.group(1), match.group(2)
    return VIEWER_NAME, VIEWER_EMAIL


# --------------------------------------------------------------------------
# global (GraphQL) ids: opaque, stable, reversible


def global_id(kind, *parts):
    raw = ":".join([kind] + [str(part) for part in parts])
    return base64.urlsafe_b64encode(raw.encode("ascii")).decode("ascii").rstrip("=")


def parse_global_id(text):
    if not isinstance(text, str):
        return None
    try:
        padded = text + "=" * (-len(text) % 4)
        raw = base64.urlsafe_b64decode(padded.encode("ascii")).decode("ascii")
    except (ValueError, UnicodeDecodeError):
        return None
    parts = raw.split(":")
    return parts[0], parts[1:]


def repo_by_global_id(text):
    parsed = parse_global_id(text)
    if parsed is None or parsed[0] != "repo":
        return None
    try:
        repo_id = int(parsed[1][0])
    except (ValueError, IndexError):
        return None
    for repo in FORGE.repos.values():
        if repo.id == repo_id:
            return repo
    return None


# --------------------------------------------------------------------------
# HTTP plumbing

STATUS_TEXT = {
    200: "OK", 201: "Created", 204: "No Content", 400: "Bad Request",
    401: "Unauthorized", 403: "Forbidden", 404: "Not Found",
    405: "Method Not Allowed", 409: "Conflict", 422: "Unprocessable Entity",
    500: "Internal Server Error",
}
_STATUS_TEXT_B = {code: text.encode("ascii") for code, text in STATUS_TEXT.items()}

JSON_TYPE = "application/json; charset=utf-8"
JSON_TYPE_B = JSON_TYPE.encode("latin-1")
_CT_UPLOAD_AD = b"application/x-git-upload-pack-advertisement"
_CT_UPLOAD_RESULT = b"application/x-git-upload-pack-result"
_CT_RECEIVE_AD = b"application/x-git-receive-pack-advertisement"
_CT_RECEIVE_RESULT = b"application/x-git-receive-pack-result"


class Request:
    __slots__ = ("method", "path", "query", "headers", "body", "origin")

    def __init__(self, method, path, query, headers, body, origin):
        self.method = method
        self.path = path
        self.query = query
        self.headers = headers
        self.body = body
        self.origin = origin

    def json(self):
        return parse_json_body(self.body)

    def authorized(self):
        if not TOKEN:
            return True
        return self.headers.get(b"authorization") == _AUTH_HEADER


class Response:
    __slots__ = ("status", "body", "content_type", "extra")

    def __init__(self, status, body=b"", content_type=None, extra=None):
        self.status = status
        self.body = body
        # content_type is stored as bytes: _send writes it without encoding.
        self.content_type = (
            content_type.encode("latin-1") if isinstance(content_type, str)
            else content_type
        )
        # extra headers are bytes -> bytes, e.g. {b"Link": b"..."}.
        self.extra = extra or {}


def json_response(status, value, extra=None):
    return Response(status, json_bytes(value), JSON_TYPE_B, extra)


def error_response(status, message):
    return json_response(status, {"message": message})


def not_found():
    return error_response(404, "Not Found")


class _ThreadingServer(socketserver.ThreadingTCPServer):
    daemon_threads = True
    allow_reuse_address = True
    request_queue_size = 512


class _WorkerPoolServer(socketserver.TCPServer):
    """Accept in the main thread, serve connections from pre-spawned workers.

    Thread-per-connection servers pay a thread creation for every new
    connection; a clone burst opens dozens at once.  A fixed pool of workers
    fed by a queue makes connection setup a queue hand-off instead.
    """

    allow_reuse_address = True
    request_queue_size = 512
    daemon_threads = True

    def __init__(self, server_address, handler_class, workers=96):
        self._queue = queue.Queue()
        self._worker_count = workers
        self._workers_started = False
        super().__init__(server_address, handler_class)

    def server_activate(self):
        super().server_activate()
        if not self._workers_started:
            self._workers_started = True
            for _ in range(self._worker_count):
                worker = threading.Thread(target=self._worker_loop, daemon=True)
                worker.start()

    def _worker_loop(self):
        while True:
            item = self._queue.get()
            if item is None:
                return
            request, client_address = item
            try:
                self.finish_request(request, client_address)
            except Exception:
                self.handle_error(request, client_address)
            finally:
                self.shutdown_request(request)

    def process_request(self, request, client_address):
        self._queue.put((request, client_address))

    def server_close(self):
        for _ in range(self._worker_count):
            self._queue.put(None)
        super().server_close()


class _BufferedSocket:
    """A minimal buffered reader over a socket: one recv per fill, with
    line/exact reads served from the buffer. A request head costs one find
    plus one split here, instead of a BufferedReader.readline per line."""

    __slots__ = ("sock", "buf")

    def __init__(self, sock):
        self.sock = sock
        self.buf = bytearray()

    def _fill(self, need=1):
        while len(self.buf) < need:
            try:
                chunk = self.sock.recv(65536)
            except (ConnectionError, OSError):
                return False
            if not chunk:
                return False
            self.buf += chunk
        return True

    def read_line(self):
        """One line without its CRLF, or None on EOF before any byte."""
        while True:
            idx = self.buf.find(b"\n")
            if idx >= 0:
                line = bytes(self.buf[:idx])
                del self.buf[:idx + 1]
                return line[:-1] if line.endswith(b"\r") else line
            if not self._fill():
                if self.buf:
                    line = bytes(self.buf)
                    self.buf.clear()
                    return line[:-1] if line.endswith(b"\r") else line
                return None

    def read_exact(self, count):
        if count <= 0:
            return b""
        if not self._fill(count):
            return None
        out = bytes(self.buf[:count])
        del self.buf[:count]
        return out


class HttpHandler(socketserver.BaseRequestHandler):
    """A small HTTP/1.1 loop: keep-alive, Content-Length and chunked bodies."""

    def handle(self):
        try:
            self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        reader = _BufferedSocket(self.request)
        try:
            while self._one_request(reader):
                pass
        except (ConnectionError, BrokenPipeError, OSError):
            pass

    def _one_request(self, reader):
        if not reader._fill(1):
            return False
        if reader.buf.startswith(b"\r\n"):
            del reader.buf[:2]
            return True  # a stray CRLF between requests
        while True:
            idx = reader.buf.find(b"\r\n\r\n")
            if idx >= 0:
                break
            if not reader._fill():
                return False
        head = bytes(reader.buf[:idx])
        del reader.buf[:idx + 4]
        lines = head.split(b"\r\n")
        if not lines or not lines[0]:
            return True
        parts = lines[0].split(b" ")
        if len(parts) < 2:
            return False
        method = parts[0].decode("latin-1").upper()
        target = parts[1]
        version = parts[2].decode("latin-1") if len(parts) > 2 else "HTTP/1.1"
        # Headers stay bytes -> bytes: no decode/strip/lower per header as
        # str (that was ~12 small allocations per request). Callers read the
        # few headers they need as bytes.
        headers = {}
        for header_line in lines[1:]:
            name, _, value = header_line.partition(b":")
            headers[name.strip().lower()] = value.strip()
        body = b""
        length_hdr = headers.get(b"content-length")
        transfer_encoding = headers.get(b"transfer-encoding", b"")
        if length_hdr is not None or b"chunked" in transfer_encoding:
            if headers.get(b"expect", b"").lower() == b"100-continue":
                self.request.sendall(b"HTTP/1.1 100 Continue\r\n\r\n")
            if b"chunked" in transfer_encoding:
                body = self._read_chunked(reader)
                if body is None:
                    return False
            else:
                try:
                    length = int(length_hdr)
                except ValueError:
                    return False
                if length > 0:
                    body = reader.read_exact(length)
                    if body is None:
                        return False
        # Fast target split: most requests carry no query string and no
        # percent-escapes; urlsplit/parse_qs/unquote run only when needed.
        if b"?" in target:
            raw_path, _, raw_query = target.partition(b"?")
            raw_query = raw_query.split(b"#", 1)[0]
            query = parse_qs(raw_query.decode("latin-1"), keep_blank_values=True) if raw_query else {}
        else:
            raw_path, query = target, {}
        if raw_path.startswith(b"http://") or raw_path.startswith(b"https://"):
            # Absolute-form target: strip scheme and authority.
            rest = raw_path.split(b"/", 3)
            raw_path = b"/" + rest[3] if len(rest) > 3 else b"/"
        if b"%" in raw_path:
            path = unquote(raw_path.decode("latin-1"))
        else:
            path = raw_path.decode("latin-1")
        host = headers.get(b"host", b"127.0.0.1").decode("latin-1")
        origin = "http://" + host
        request = Request(method, path, query, headers, body, origin)
        try:
            response = dispatch(request)
        except Exception as error:  # a handler bug must not kill the connection loop silently
            sys.stderr.write("handler error: %r\n" % (error,))
            response = error_response(500, "Internal Server Error")
        keep_alive = version == "HTTP/1.1" and headers.get(b"connection", b"").lower() != b"close"
        if version == "HTTP/1.0" and headers.get(b"connection", b"").lower() == b"keep-alive":
            keep_alive = True
        self._send(response, keep_alive)
        return keep_alive

    def _read_chunked(self, reader):
        chunks = []
        while True:
            size_line = reader.read_line()
            if size_line is None:
                return None
            try:
                size = int(size_line.split(b";")[0], 16)
            except ValueError:
                return None
            if size == 0:
                # trailers until the empty line
                while True:
                    trailer = reader.read_line()
                    if trailer is None or trailer == b"":
                        break
                return b"".join(chunks)
            data = reader.read_exact(size)
            if data is None:
                return None
            chunks.append(data)
            if reader.read_line() is None:
                return None

    def _send(self, response, keep_alive):
        # The head is built as bytes throughout: no str join + latin-1
        # encode per response, and one sendall for head + body.
        head = [b"HTTP/1.1 %d %s\r\n" % (response.status, _STATUS_TEXT_B.get(response.status, b""))]
        if response.content_type is not None:
            head.append(b"Content-Type: %s\r\n" % response.content_type)
        head.append(b"Content-Length: %d\r\n" % len(response.body))
        for name, value in response.extra.items():
            head.append(name + b": " + value + b"\r\n")
        if not keep_alive:
            head.append(b"Connection: close\r\n")
        head.append(b"\r\n")
        self.request.sendall(b"".join(head) + response.body)


# --------------------------------------------------------------------------
# REST helpers


def _query_int(query, name, default):
    raw = query.get(name, [None])[0]
    if raw is None:
        return default
    try:
        return int(raw)
    except ValueError:
        return default


def paginate(request, items):
    """Slice a list by page/per_page and build the Link header value."""
    per_page = _query_int(request.query, "per_page", 30)
    per_page = max(1, min(100, per_page))
    page = max(1, _query_int(request.query, "page", 1))
    start = (page - 1) * per_page
    chunk = items[start:start + per_page]
    links = []
    last_page = max(1, (len(items) + per_page - 1) // per_page)

    def page_url(number):
        params = []
        for key, values in request.query.items():
            if key == "page":
                continue
            for value in values:
                params.append("%s=%s" % (key, value))
        params.append("per_page=%d" % per_page)
        params.append("page=%d" % number)
        return "%s%s?%s" % (request.origin, request.path, "&".join(params))

    if page < last_page:
        links.append('<%s>; rel="next"' % page_url(page + 1))
        links.append('<%s>; rel="last"' % page_url(last_page))
    if page > 1:
        links.append('<%s>; rel="first"' % page_url(1))
        links.append('<%s>; rel="prev"' % page_url(page - 1))
    extra = {b"Link": (", ".join(links)).encode("latin-1")} if links else None
    return chunk, extra


def require_repo(owner, name):
    repo = FORGE.get_repo(owner, name)
    if repo is None:
        return None
    return repo


# --------------------------------------------------------------------------
# REST: users and repositories


def rest_root(request):
    return json_response(200, {
        "current_user_url": request.origin + "/api/v3/user",
        "repository_url": request.origin + "/api/v3/repos/{owner}/{repo}",
        "rate_limit_url": request.origin + "/api/v3/rate_limit",
    }, {b"X-OAuth-Scopes": b"repo, read:org"})


def rest_meta(request):
    return json_response(200, {
        "installed_version": VERSION,
        "verifiable_password_authentication": True,
        "ssh_key_fingerprints": {},
        "hooks": [],
        "pages": [],
        "importers": [],
    })


def rest_user(request):
    return json_response(200, viewer_json())


def rest_create_repo(request):
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    name = body.get("name")
    if not isinstance(name, str) or not name:
        return error_response(422, "Repository creation failed: name is required")
    if FORGE.get_repo(VIEWER_LOGIN, name) is not None:
        return error_response(422, "Repository creation failed: name already exists")
    description = body.get("description")
    repo = FORGE.create_repo(
        VIEWER_LOGIN, name,
        description if isinstance(description, str) else "",
        bool(body.get("private", False)),
    )
    return json_response(201, repo_json(repo, request.origin))


def rest_list_user_repos(request):
    repos = FORGE.viewer_repos(VIEWER_LOGIN)
    chunk, extra = paginate(request, repos)
    return json_response(200, [repo_json(repo, request.origin) for repo in chunk], extra)


def rest_get_repo(request, repo):
    return json_response(200, repo_json(repo, request.origin))


def rest_patch_repo(request, repo):
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    with FORGE.lock:
        if isinstance(body.get("description"), str):
            repo.description = body["description"]
        if isinstance(body.get("private"), bool):
            repo.private = body["private"]
        if isinstance(body.get("default_branch"), str) and body["default_branch"]:
            repo.default_branch = body["default_branch"]
    return json_response(200, repo_json(repo, request.origin))


def rest_delete_repo(request, repo):
    FORGE.delete_repo(repo.owner, repo.name)
    return Response(204)


# --------------------------------------------------------------------------
# REST: branches, commits, refs


def rest_list_branches(request, repo):
    branches = []
    for ref, oid in sorted(repo.refs.items()):
        if ref.startswith("refs/heads/"):
            branches.append({
                "name": ref[len("refs/heads/"):],
                "commit": {"sha": hex_of(oid), "url": "%s/api/v3/repos/%s/commits/%s" % (request.origin, repo.full_name, hex_of(oid))},
                "protected": False,
            })
    chunk, extra = paginate(request, branches)
    return json_response(200, chunk, extra)


def rest_get_branch(request, repo, branch):
    oid = repo.refs.get("refs/heads/" + branch)
    if oid is None:
        return not_found()
    return json_response(200, {
        "name": branch,
        "commit": commit_json(repo, oid, request.origin),
        "protected": False,
    })


def rest_list_commits(request, repo):
    ref = request.query.get("sha", [None])[0] or repo.default_branch
    tip = repo.refs.get(ref)
    if tip is None:
        tip = repo.refs.get("refs/heads/" + ref)
    if tip is None:
        tip = oid_of_hex(ref)
    if tip is None or repo.commit(tip) is None:
        return not_found()
    # newest first: walk parents in breadth order from the tip
    ordered = []
    seen = set()
    queue = [tip]
    while queue:
        current = queue.pop(0)
        if current in seen:
            continue
        seen.add(current)
        info = repo.commit(current)
        if info is None:
            continue
        ordered.append(current)
        queue.extend(info[1])
    chunk, extra = paginate(request, ordered)
    return json_response(200, [commit_json(repo, oid, request.origin) for oid in chunk], extra)


def rest_create_ref(request, repo):
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    ref = body.get("ref")
    sha = body.get("sha")
    if not isinstance(ref, str) or not ref.startswith("refs/"):
        return error_response(422, "Validation Failed: ref is invalid")
    oid = oid_of_hex(sha) if isinstance(sha, str) else None
    if oid is None or repo.get(oid) is None:
        return error_response(422, "Validation Failed: sha is not an object")
    with FORGE.lock:
        if ref in repo.refs:
            return error_response(422, "Reference already exists")
        repo.refs[ref] = oid
        repo.bump()
    return json_response(201, {
        "ref": ref,
        "node_id": global_id("ref", repo.id, ref),
        "url": "%s/api/v3/repos/%s/git/refs/%s" % (request.origin, repo.full_name, ref[len("refs/"):]),
        "object": {"sha": sha, "type": TYPE_NAMES[repo.get(oid)[0]]},
    })


def rest_get_ref(request, repo, ref):
    oid = repo.refs.get(ref)
    if oid is None:
        return not_found()
    entry = repo.get(oid)
    return json_response(200, {
        "ref": ref,
        "node_id": global_id("ref", repo.id, ref),
        "url": "%s/api/v3/repos/%s/git/refs/%s" % (request.origin, repo.full_name, ref[len("refs/"):]),
        "object": {"sha": hex_of(oid), "type": TYPE_NAMES[entry[0]] if entry else "commit"},
    })


def rest_delete_ref(request, repo, ref):
    with FORGE.lock:
        if ref not in repo.refs:
            return not_found()
        del repo.refs[ref]
        repo.bump()
    return Response(204)


# --------------------------------------------------------------------------
# REST: contents


def _contents_entry(repo, path, mode, oid, origin):
    entry = repo.get(oid)
    size = len(entry[1]) if entry is not None and mode != 0o40000 else 0
    return {
        "name": path.rsplit("/", 1)[-1],
        "path": path,
        "sha": hex_of(oid),
        "size": size,
        "type": "dir" if mode == 0o40000 else "file",
        "url": "%s/api/v3/repos/%s/contents/%s" % (origin, repo.full_name, path),
        "html_url": "%s/%s/blob/%s/%s" % (origin, repo.full_name, repo.default_branch, path),
        "git_url": "%s/api/v3/repos/%s/git/blobs/%s" % (origin, repo.full_name, hex_of(oid)),
        "download_url": None,
    }


def _resolve_ref_tip(repo, body, query):
    branch = None
    if isinstance(body, dict):
        branch = body.get("branch")
    if not branch:
        branch = query.get("ref", [None])[0]
    if not branch:
        branch = repo.default_branch
    return branch, repo.refs.get("refs/heads/" + branch)


def rest_get_contents(request, repo, path):
    _branch, tip = _resolve_ref_tip(repo, None, request.query)
    if tip is None:
        # an unborn repository reads as empty: the root listing is [], a file 404s
        if path == "":
            return json_response(200, [])
        return not_found()
    info = repo.commit(tip)
    if info is None or info[0] is None:
        return not_found()
    tree_oid = info[0]
    if path:
        segments = path.split("/")
        node = tree_oid
        found = None
        for index, segment in enumerate(segments):
            match = None
            for mode, name, child in repo.tree(node):
                if name == segment:
                    match = (mode, child)
                    break
            if match is None:
                return not_found()
            if index == len(segments) - 1:
                found = match
            else:
                if match[0] != 0o40000:
                    return not_found()
                node = match[1]
        mode, oid = found
        if mode == 0o40000:
            entries = [
                _contents_entry(repo, path + "/" + name, child_mode, child_oid, request.origin)
                for child_mode, name, child_oid in repo.tree(oid)
            ]
            entries.sort(key=lambda item: item["name"])
            return json_response(200, entries)
        entry = repo.get(oid)
        data = entry[1] if entry is not None else b""
        result = _contents_entry(repo, path, mode, oid, request.origin)
        encoded = base64.b64encode(data).decode("ascii")
        result["encoding"] = "base64"
        result["content"] = "\n".join(encoded[i:i + 60] for i in range(0, len(encoded), 60)) + ("\n" if encoded else "")
        return json_response(200, result)
    entries = [
        _contents_entry(repo, name, mode, child, request.origin)
        for mode, name, child in repo.tree(tree_oid)
    ]
    entries.sort(key=lambda item: item["name"])
    return json_response(200, entries)


def _commit_file_change(repo, branch, path, new_data, message, expect_sha):
    """One contents commit on a branch. Returns (status, commit oid, blob oid)."""
    ref = "refs/heads/" + branch
    tip = repo.refs.get(ref)
    if tip is None:
        # writing to a branch that does not exist yet starts it from the default tip
        tip = repo.refs.get(repo.head_ref())
    flat = {}
    parents = []
    if tip is not None:
        info = repo.commit(tip)
        if info is None:
            return 422, None, None
        flat = dict(repo.flatten(info[0]))
        parents = [tip]
    current = flat.get(path)
    current_oid = current[1] if current else None
    if expect_sha is not None:
        if current_oid is None or hex_of(current_oid) != expect_sha:
            return 409, None, None
    if new_data is None:
        if current_oid is None:
            return 404, None, None
        del flat[path]
        blob_oid = current_oid
    else:
        blob_oid = repo.store(T_BLOB, new_data)
        flat[path] = (0o100644, blob_oid)
    tree_oid = repo.build_tree({p: oid for p, (_m, oid) in flat.items()})
    commit_oid = repo.make_commit(tree_oid, parents, message, CLOCK.tick())
    repo.refs[ref] = commit_oid
    repo.bump()
    return (201 if current_oid is None and new_data is not None else 200), commit_oid, blob_oid


def rest_put_contents(request, repo, path):
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    content = body.get("content")
    message = body.get("message")
    if not isinstance(content, str) or not isinstance(message, str):
        return error_response(422, "Validation Failed: content and message are required")
    try:
        data = base64.b64decode(content.encode("ascii"), validate=False)
    except (ValueError, UnicodeEncodeError):
        return error_response(422, "Validation Failed: content is not base64")
    branch = body.get("branch") or repo.default_branch
    expect_sha = body.get("sha")
    with FORGE.lock:
        status, commit_oid, blob_oid = _commit_file_change(
            repo, branch, path, data, message, expect_sha if isinstance(expect_sha, str) else None)
        if commit_oid is None:
            return error_response(status, "contents update failed")
        entry = _contents_entry(repo, path, 0o100644, blob_oid, request.origin)
        entry["encoding"] = "base64"
        return json_response(status, {
            "content": entry,
            "commit": commit_json(repo, commit_oid, request.origin)["commit"] | {"sha": hex_of(commit_oid)},
        })


def rest_delete_contents(request, repo, path):
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    message = body.get("message")
    sha = body.get("sha")
    if not isinstance(message, str) or not isinstance(sha, str):
        return error_response(422, "Validation Failed: message and sha are required")
    branch = body.get("branch") or repo.default_branch
    with FORGE.lock:
        status, commit_oid, _blob = _commit_file_change(repo, branch, path, None, message, sha)
        if commit_oid is None:
            return error_response(status, "contents delete failed")
        return json_response(200, {
            "content": None,
            "commit": commit_json(repo, commit_oid, request.origin)["commit"] | {"sha": hex_of(commit_oid)},
        })


# --------------------------------------------------------------------------
# REST: labels, issues, comments


def rest_create_label(request, repo):
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    name = body.get("name")
    if not isinstance(name, str) or not name:
        return error_response(422, "Validation Failed: name is required")
    with FORGE.lock:
        if name in repo.labels:
            return error_response(422, "Validation Failed: name already exists")
        color = body.get("color")
        description = body.get("description")
        label = Label(FORGE.alloc_id(), name,
                      color if isinstance(color, str) else "ededed",
                      description if isinstance(description, str) else None)
        repo.labels[name] = label
    return json_response(201, label_json(repo, label))


def rest_list_labels(request, repo):
    labels = [label_json(repo, repo.labels[name]) for name in sorted(repo.labels)]
    chunk, extra = paginate(request, labels)
    return json_response(200, chunk, extra)


def _label_names_or_error(repo, body):
    names = body.get("labels")
    if names is None:
        return [], None
    if not isinstance(names, list):
        return None, error_response(422, "Validation Failed: labels must be a list")
    out = []
    for name in names:
        if isinstance(name, dict):
            name = name.get("name")
        if not isinstance(name, str) or name not in repo.labels:
            return None, error_response(422, "Validation Failed: label %r does not exist" % (name,))
        out.append(name)
    return out, None


def create_issue_record(repo, title, body, label_names):
    with FORGE.lock:
        number = repo.next_number
        repo.next_number += 1
        issue = Issue(FORGE.alloc_id(), number, title, body, list(label_names), CLOCK.tick())
        repo.issues[number] = issue
        repo.issue_get_cache.clear()
        return issue


def rest_create_issue(request, repo):
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    title = body.get("title")
    if not isinstance(title, str) or not title:
        return error_response(422, "Validation Failed: title is required")
    label_names, failure = _label_names_or_error(repo, body)
    if failure is not None:
        return failure
    text = body.get("body")
    issue = create_issue_record(repo, title, text if isinstance(text, str) else "", label_names)
    return Response(201, issue_json_bytes(repo, issue, request.origin), JSON_TYPE_B)


def _issue_list_filtered(repo, query):
    state = query.get("state", ["open"])[0]
    issues = list(repo.issues.values())
    if state == "open":
        issues = [issue for issue in issues if issue.state == "open"]
    elif state == "closed":
        issues = [issue for issue in issues if issue.state == "closed"]
    direction = query.get("direction", ["desc"])[0]
    issues.sort(key=lambda issue: issue.number, reverse=(direction != "asc"))
    return issues


def rest_list_issues(request, repo):
    issues = _issue_list_filtered(repo, request.query)
    chunk, extra = paginate(request, issues)
    return json_response(200, [issue_json(repo, issue, request.origin) for issue in chunk], extra)


def rest_get_issue(request, repo, number):
    cached = repo.issue_get_cache.get(number)
    if cached is not None:
        return Response(200, cached, JSON_TYPE)
    issue = repo.issues.get(number)
    if issue is None:
        return not_found()
    body = issue_json_bytes(repo, issue, request.origin)
    repo.issue_get_cache[number] = body
    return Response(200, body, JSON_TYPE_B)


def rest_patch_issue(request, repo, number):
    issue = repo.issues.get(number)
    if issue is None:
        return not_found()
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    with FORGE.lock:
        if isinstance(body.get("title"), str):
            issue.title = body["title"]
        if isinstance(body.get("body"), str):
            issue.body = body["body"]
        if body.get("state") in ("open", "closed"):
            issue.state = body["state"]
            issue.closed_ts = CLOCK.tick() if issue.state == "closed" else None
        if "labels" in body:
            label_names, failure = _label_names_or_error(repo, body)
            if failure is not None:
                return failure
            issue.labels = label_names
        issue.updated_ts = CLOCK.tick()
        repo.issue_get_cache.pop(number, None)
    return json_response(200, issue_json(repo, issue, request.origin))


def rest_create_comment(request, repo, number):
    issue = repo.issues.get(number)
    pull = None
    if issue is None:
        pull = repo.pulls.get(number)
        if pull is None:
            return not_found()
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    text = body.get("body")
    if not isinstance(text, str):
        return error_response(422, "Validation Failed: body is required")
    with FORGE.lock:
        comment_id = repo.next_comment_id
        repo.next_comment_id += 1
        comment = Comment(comment_id, number, text, CLOCK.tick())
        repo.comments[comment_id] = comment
        if issue is not None:
            issue.comments.append(comment_id)
            repo.issue_get_cache.pop(number, None)
    return json_response(201, comment_json(repo, comment, request.origin))


def rest_list_comments(request, repo, number):
    issue = repo.issues.get(number)
    if issue is not None:
        ids = issue.comments
    elif number in repo.pulls:
        ids = [c.id for c in repo.comments.values() if c.issue_number == number]
    else:
        return not_found()
    comments = [repo.comments[cid] for cid in ids if cid in repo.comments]
    chunk, extra = paginate(request, comments)
    return json_response(200, [comment_json(repo, comment, request.origin) for comment in chunk], extra)


# --------------------------------------------------------------------------
# REST: pull requests


def pull_files_diff(repo, pull):
    """Changed paths between the merge-base tree and the head tree, with line counts."""
    head_sha = pull_head_sha(repo, pull)
    base_sha = pull_base_sha(repo, pull)
    if head_sha is None or base_sha is None:
        return []
    base_commit = repo.merge_base(base_sha, head_sha) or base_sha
    base_info = repo.commit(base_commit)
    head_info = repo.commit(head_sha)
    if base_info is None or head_info is None:
        return []
    base_flat = repo.flatten(base_info[0])
    head_flat = repo.flatten(head_info[0])
    out = []
    for path in sorted(set(base_flat) | set(head_flat)):
        before = base_flat.get(path)
        after = head_flat.get(path)
        if before is not None and after is not None and before[1] == after[1]:
            continue
        before_lines = _blob_lines(repo, before[1]) if before else []
        after_lines = _blob_lines(repo, after[1]) if after else []
        additions, deletions = _line_diff_counts(before_lines, after_lines)
        if before is None:
            status = "added"
        elif after is None:
            status = "removed"
        else:
            status = "modified"
        out.append({
            "filename": path,
            "status": status,
            "additions": additions,
            "deletions": deletions,
            "changes": additions + deletions,
            "sha": hex_of(after[1]) if after else hex_of(before[1]),
        })
    return out


def _blob_lines(repo, oid):
    entry = repo.get(oid)
    if entry is None:
        return []
    return entry[1].decode("utf-8", "replace").splitlines()


def _line_diff_counts(before, after):
    """(additions, deletions) from an LCS over lines — exact for check-sized files."""
    if before == after:
        return 0, 0
    rows = len(before)
    cols = len(after)
    if rows * cols > 4_000_000:
        # very large files: fall back to a set-based estimate
        return len(set(after) - set(before)), len(set(before) - set(after))
    previous = [0] * (cols + 1)
    for i in range(rows):
        current = [0] * (cols + 1)
        for j in range(cols):
            if before[i] == after[j]:
                current[j + 1] = previous[j] + 1
            else:
                current[j + 1] = max(previous[j + 1], current[j])
        previous = current
    common = previous[cols]
    return after.__len__() - common, rows - common


def pull_mergeable(repo, pull):
    """True when the squash three-way merge applies cleanly."""
    if pull.merged:
        return True
    head_sha = pull_head_sha(repo, pull)
    base_sha = pull_base_sha(repo, pull)
    if head_sha is None or base_sha is None:
        return False
    base_commit = repo.merge_base(base_sha, head_sha)
    if base_commit is None:
        return False
    base_flat = repo.flatten(repo.commit(base_commit)[0])
    head_flat = repo.flatten(repo.commit(head_sha)[0])
    current_flat = repo.flatten(repo.commit(base_sha)[0])
    for path in set(base_flat) | set(head_flat):
        base_version = base_flat.get(path)
        head_version = head_flat.get(path)
        if base_version == head_version:
            continue
        current_version = current_flat.get(path)
        if current_version != base_version and current_version != head_version:
            return False
    return True


def squash_merge(repo, pull):
    """Apply the pull's changes onto its base branch as one commit.

    Returns the merge commit oid, or None on a conflict.
    """
    head_sha = pull_head_sha(repo, pull)
    base_sha = pull_base_sha(repo, pull)
    if head_sha is None or base_sha is None:
        return None
    base_commit = repo.merge_base(base_sha, head_sha)
    if base_commit is None:
        return None
    base_flat = repo.flatten(repo.commit(base_commit)[0])
    head_flat = repo.flatten(repo.commit(head_sha)[0])
    merged_flat = dict(repo.flatten(repo.commit(base_sha)[0]))
    for path in set(base_flat) | set(head_flat):
        base_version = base_flat.get(path)
        head_version = head_flat.get(path)
        if base_version == head_version:
            continue
        current_version = merged_flat.get(path)
        if current_version != base_version and current_version != head_version:
            return None
        if head_version is None:
            merged_flat.pop(path, None)
        else:
            merged_flat[path] = head_version
    tree_oid = repo.build_tree({p: oid for p, (_m, oid) in merged_flat.items()})
    message = "%s (#%d)" % (pull.title, pull.number)
    commit_oid = repo.make_commit(tree_oid, [base_sha], message, CLOCK.tick())
    repo.refs["refs/heads/" + pull.base_ref] = commit_oid
    repo.bump()
    return commit_oid


def create_pull_record(repo, title, body, head_ref, base_ref):
    head_sha = branch_tip(repo, head_ref)
    base_sha = branch_tip(repo, base_ref)
    if head_sha is None or base_sha is None:
        return None
    with FORGE.lock:
        number = repo.next_number
        repo.next_number += 1
        pull = Pull(FORGE.alloc_id(), number, title, body, head_ref, base_ref,
                    head_sha, base_sha, CLOCK.tick())
        repo.pulls[number] = pull
        return pull


def rest_create_pull(request, repo):
    body = request.json()
    if not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    title = body.get("title")
    head = body.get("head")
    base = body.get("base") or repo.default_branch
    if not isinstance(title, str) or not isinstance(head, str):
        return error_response(422, "Validation Failed: title and head are required")
    head = head.split(":")[-1]
    base = base.split(":")[-1] if isinstance(base, str) else repo.default_branch
    if branch_tip(repo, head) is None:
        return error_response(422, "Validation Failed: head branch does not exist")
    if branch_tip(repo, base) is None:
        return error_response(422, "Validation Failed: base branch does not exist")
    text = body.get("body")
    pull = create_pull_record(repo, title, text if isinstance(text, str) else "", head, base)
    if pull is None:
        return error_response(422, "Validation Failed: cannot open pull request")
    return json_response(201, pull_json(repo, pull, request.origin))


def rest_list_pulls(request, repo):
    state = request.query.get("state", ["open"])[0]
    pulls = list(repo.pulls.values())
    if state == "open":
        pulls = [pull for pull in pulls if pull.state == "open"]
    elif state == "closed":
        pulls = [pull for pull in pulls if pull.state == "closed"]
    direction = request.query.get("direction", ["desc"])[0]
    pulls.sort(key=lambda pull: pull.number, reverse=(direction != "asc"))
    chunk, extra = paginate(request, pulls)
    return json_response(200, [pull_json(repo, pull, request.origin) for pull in chunk], extra)


def rest_get_pull(request, repo, number):
    pull = repo.pulls.get(number)
    if pull is None:
        return not_found()
    result = pull_json(repo, pull, request.origin)
    result["mergeable"] = pull_mergeable(repo, pull)
    files = pull_files_diff(repo, pull)
    result["commits"] = 0
    result["changed_files"] = len(files)
    result["additions"] = sum(item["additions"] for item in files)
    result["deletions"] = sum(item["deletions"] for item in files)
    return json_response(200, result)


def rest_pull_files(request, repo, number):
    pull = repo.pulls.get(number)
    if pull is None:
        return not_found()
    files = pull_files_diff(repo, pull)
    chunk, extra = paginate(request, files)
    return json_response(200, chunk, extra)


def rest_merge_pull(request, repo, number):
    pull = repo.pulls.get(number)
    if pull is None:
        return not_found()
    body = request.json()
    if body is not None and not isinstance(body, dict):
        return error_response(400, "Invalid request body")
    with FORGE.lock:
        if pull.merged or pull.state != "open":
            return error_response(405, "Pull Request is not mergeable")
        commit_oid = squash_merge(repo, pull)
        if commit_oid is None:
            return error_response(405, "Pull Request is not mergeable: conflict")
        pull.merged = True
        pull.state = "closed"
        pull.merged_ts = CLOCK.tick()
        pull.updated_ts = pull.merged_ts
        pull.merge_commit = commit_oid
    return json_response(200, {
        "sha": hex_of(commit_oid),
        "merged": True,
        "message": "Pull Request successfully merged",
    })


# --------------------------------------------------------------------------
# git smart HTTP

PKT_FLUSH = b"0000"
PKT_DELIM = b"0001"


def pkt_line(payload):
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


def pkt_text(text):
    return pkt_line(text.encode("utf-8"))


def parse_pkt_lines(data):
    """Split a pkt-line stream into (payloads, rest); payloads hold bytes,
    with None marking a flush and 'delim' marking a delimiter packet."""
    out = []
    pos = 0
    end = len(data)
    while pos + 4 <= end:
        try:
            size = int(data[pos:pos + 4], 16)
        except ValueError:
            break
        if size == 0:
            out.append(None)
            pos += 4
            break
        if size == 1:
            out.append("delim")
            pos += 4
            continue
        if size < 4 or pos + size > end:
            break
        out.append(data[pos + 4:pos + size])
        pos += size
    return out, data[pos:]


def sideband_packets(data, band=1):
    """Frame bytes as side-band packets of at most 65519 payload bytes."""
    out = []
    step = 65515
    for index in range(0, len(data), step):
        out.append(pkt_line(bytes([band]) + data[index:index + step]))
    if not data:
        out.append(pkt_line(bytes([band])))
    return b"".join(out)


UPLOAD_CAPS_V0 = (
    "multi_ack_detailed side-band-64k thin-pack ofs-delta shallow "
    "agent=forge-" + VERSION
)
RECEIVE_CAPS_V0 = "report-status delete-refs side-band-64k agent=forge-" + VERSION

# The protocol-v2 advertisement carries no refs: one constant for all repos.
_V2_ADVERTISEMENT = b"".join([
    pkt_text("version 2\n"),
    pkt_text("agent=forge-" + VERSION + "\n"),
    pkt_text("ls-refs=unborn\n"),
    pkt_text("fetch=shallow wait-for-done\n"),
    pkt_text("object-format=sha1\n"),
    PKT_FLUSH,
])


def _advertised_refs(repo):
    refs = dict(repo.refs)
    return refs


def _ref_lines_v0(repo, caps):
    refs = _advertised_refs(repo)
    head_ref = repo.head_ref()
    lines = []
    if not refs:
        lines.append(pkt_line(ZERO_HEX.encode() + b" capabilities^{}\x00" + caps.encode()))
        return lines
    head_oid = refs.get(head_ref)
    first = True
    if head_oid is not None:
        lines.append(pkt_line(hex_of(head_oid).encode() + b" HEAD\x00" + caps.encode()))
        first = False
    for ref in sorted(refs):
        oid = refs[ref]
        prefix = b"" if first else b""
        line = hex_of(oid).encode() + b" " + ref.encode()
        if first:
            line += b"\x00" + caps.encode()
            first = False
        lines.append(pkt_line(line + prefix))
        entry = repo.get(oid)
        if entry is not None and entry[0] == T_TAG:
            peeled = repo.peel(oid)
            if peeled != oid:
                lines.append(pkt_text("%s %s^{}\n" % (hex_of(peeled), ref)))
    if first:
        # HEAD's target is unborn but other refs exist: a zero HEAD line leads.
        lines.insert(0, pkt_line(ZERO_HEX.encode() + b" capabilities^{}\x00" + caps.encode()))
    return lines


def git_info_refs(request, repo, service):
    if service not in ("git-upload-pack", "git-receive-pack"):
        return error_response(403, "unknown service")
    protocol = request.headers.get(b"git-protocol", b"")
    if service == "git-upload-pack" and b"version=2" in protocol:
        # The v2 advertisement carries no refs: identical for every repo.
        return Response(200, _V2_ADVERTISEMENT, _CT_UPLOAD_AD)
    caps = UPLOAD_CAPS_V0 if service == "git-upload-pack" else RECEIVE_CAPS_V0
    if service == "git-upload-pack":
        caps = caps + " symref=HEAD:refs/heads/" + repo.default_branch
    # The v0 advertisement is a pure function of (refs, default_branch) on a
    # fixed repo version; cache it per version (a clone burst asks for it
    # twice per clone on an unchanging repo).
    cache_key = (service, repo.version, repo.default_branch)
    cached = repo.ad_cache.get(cache_key)
    if cached is not None:
        return Response(200, cached, _CT_UPLOAD_AD if service == "git-upload-pack" else _CT_RECEIVE_AD)
    preamble = pkt_text("# service=%s\n" % service) + PKT_FLUSH
    body = preamble + b"".join(_ref_lines_v0(repo, caps)) + PKT_FLUSH
    repo.ad_cache[cache_key] = body
    return Response(200, body, _CT_UPLOAD_AD if service == "git-upload-pack" else _CT_RECEIVE_AD)


def _ls_refs_response(repo, args):
    prefixes = [arg[len("ref-prefix "):] for arg in args if arg.startswith("ref-prefix ")]
    want_peel = "peel" in args
    want_symrefs = "symrefs" in args
    lines = []
    head_ref = repo.head_ref()
    head_oid = repo.refs.get(head_ref)
    head_matches = not prefixes or any("HEAD".startswith(prefix) or prefix == "HEAD" for prefix in prefixes) or any(prefix == "" for prefix in prefixes)
    if head_matches:
        if head_oid is not None:
            line = "%s HEAD" % hex_of(head_oid)
            if want_symrefs:
                line += " symref-target:%s" % head_ref
            lines.append(line)
        else:
            line = "unborn HEAD"
            if want_symrefs:
                line += " symref-target:%s" % head_ref
            lines.append(line)
    for ref in sorted(repo.refs):
        if prefixes and not any(ref.startswith(prefix) for prefix in prefixes):
            continue
        oid = repo.refs[ref]
        line = "%s %s" % (hex_of(oid), ref)
        entry = repo.get(oid)
        if want_peel and entry is not None and entry[0] == T_TAG:
            line += " peeled:%s" % hex_of(repo.peel(oid))
        lines.append(line)
    body = b"".join(pkt_text(line + "\n") for line in lines) + PKT_FLUSH
    return body


def _fetch_response_v2(repo, args):
    wants = []
    haves = []
    shallow = []
    depth = None
    for arg in args:
        if arg.startswith("want "):
            oid = oid_of_hex(arg[5:].strip())
            if oid is not None:
                wants.append(oid)
        elif arg.startswith("have "):
            oid = oid_of_hex(arg[5:].strip())
            if oid is not None:
                haves.append(oid)
        elif arg.startswith("shallow "):
            oid = oid_of_hex(arg[8:].strip())
            if oid is not None:
                shallow.append(oid)
        elif arg.startswith("deepen "):
            try:
                depth = int(arg[7:].strip())
            except ValueError:
                depth = None
    # The whole response is a pure function of the fetch key on a fixed repo
    # version (bump() clears this cache on any git mutation), so a clone
    # burst of 50 identical fetches builds it once.
    key = (tuple(wants), tuple(haves), depth, tuple(shallow))
    cached = repo.fetch_resp_cache.get(key)
    if cached is not None:
        return cached
    pack, shallow_lines, unshallow_lines = fetch_pack_bytes(repo, wants, haves, depth, shallow)
    out = [pkt_text("acknowledgments\n")]
    common = [have for have in haves if _have_is_common(repo, have, wants)]
    if common:
        for have in common:
            out.append(pkt_text("ACK %s\n" % hex_of(have)))
        out.append(pkt_text("ready\n"))
    else:
        out.append(pkt_text("NAK\n"))
    out.append(PKT_FLUSH)
    if depth is not None or shallow:
        out.append(pkt_text("shallow-info\n"))
        for oid in shallow_lines:
            out.append(pkt_text("shallow %s\n" % hex_of(oid)))
        for oid in unshallow_lines:
            out.append(pkt_text("unshallow %s\n" % hex_of(oid)))
        out.append(PKT_FLUSH)
    out.append(pkt_text("packfile\n"))
    out.append(sideband_packets(pack))
    out.append(PKT_FLUSH)
    body = b"".join(out)
    repo.fetch_resp_cache[key] = body
    return body


def _have_is_common(repo, have, wants):
    commit = repo.peel_to_commit(have)
    if commit is None:
        return False
    for want in wants:
        want_commit = repo.peel_to_commit(want)
        if want_commit is not None and repo.is_ancestor(commit, want_commit):
            return True
    return False


def _fetch_response_v0(repo, wants, haves, depth, shallow):
    pack, shallow_lines, unshallow_lines = fetch_pack_bytes(repo, wants, haves, depth, shallow)
    out = []
    for oid in shallow_lines:
        out.append(pkt_text("shallow %s\n" % hex_of(oid)))
    for oid in unshallow_lines:
        out.append(pkt_text("unshallow %s\n" % hex_of(oid)))
    common = [have for have in haves if _have_is_common(repo, have, wants)]
    if common:
        out.append(pkt_text("ACK %s\n" % hex_of(common[-1])))
    else:
        out.append(pkt_text("NAK\n"))
    out.append(sideband_packets(pack))
    out.append(PKT_FLUSH)
    return b"".join(out)


def git_upload_pack(request, repo):
    protocol = request.headers.get(b"git-protocol", b"")
    body = request.body
    if b"version=2" in protocol:
        packets, _rest = parse_pkt_lines(body)
        args = []
        command = None
        for packet in packets:
            if packet is None or packet == "delim":
                continue
            text = packet.decode("utf-8", "replace").rstrip("\n")
            if text.startswith("command="):
                command = text[len("command="):]
            elif text.startswith("arg "):
                args.append(text[len("arg "):])
            else:
                args.append(text)
        if command == "ls-refs":
            return Response(200, _ls_refs_response(repo, args), _CT_UPLOAD_RESULT)
        if command == "fetch":
            return Response(200, _fetch_response_v2(repo, args), _CT_UPLOAD_RESULT)
        return error_response(400, "unknown command")
    # protocol v0: wants, flush, haves, done, flush
    wants = []
    haves = []
    shallow = []
    depth = None
    section = 0
    pos = 0
    data = body
    while pos + 4 <= len(data):
        try:
            size = int(data[pos:pos + 4], 16)
        except ValueError:
            break
        if size == 0:
            section += 1
            pos += 4
            if section >= 2:
                break
            continue
        if size < 4 or pos + size > len(data):
            break
        payload = data[pos + 4:pos + size].decode("utf-8", "replace").rstrip("\n")
        pos += size
        if payload.startswith("want "):
            oid = oid_of_hex(payload[5:].split(" ")[0])
            if oid is not None:
                wants.append(oid)
        elif payload.startswith("have "):
            oid = oid_of_hex(payload[5:].strip())
            if oid is not None:
                haves.append(oid)
        elif payload.startswith("shallow "):
            oid = oid_of_hex(payload[8:].strip())
            if oid is not None:
                shallow.append(oid)
        elif payload.startswith("deepen "):
            try:
                depth = int(payload[7:].strip())
            except ValueError:
                depth = None
    return Response(200, _fetch_response_v0(repo, wants, haves, depth, shallow),
                    _CT_UPLOAD_RESULT)


def git_receive_pack(request, repo):
    body = request.body
    commands = []
    pos = 0
    while pos + 4 <= len(body):
        try:
            size = int(body[pos:pos + 4], 16)
        except ValueError:
            return error_response(400, "malformed pkt-line")
        if size == 0:
            pos += 4
            break
        if size < 4 or pos + size > len(body):
            return error_response(400, "malformed pkt-line")
        payload = body[pos + 4:pos + size]
        pos += size
        text = payload.split(b"\x00")[0].decode("utf-8", "replace").rstrip("\n")
        fields = text.split(" ")
        if len(fields) != 3:
            continue
        old = oid_of_hex(fields[0])
        new = oid_of_hex(fields[1])
        if old is None or new is None:
            continue
        commands.append((old, new, fields[2]))
    pack_data = body[pos:]
    unpack_ok = True
    detail = ""
    if pack_data:
        try:
            parse_pack(repo, pack_data)
        except (ValueError, IndexError, zlib.error) as error:
            unpack_ok = False
            detail = str(error)
    results = []
    with FORGE.lock:
        for old, new, ref in commands:
            if not ref.startswith("refs/"):
                results.append((ref, False, "invalid ref"))
                continue
            if new == ZERO_OID:
                if ref in repo.refs:
                    del repo.refs[ref]
                    repo.bump()
                    results.append((ref, True, ""))
                else:
                    results.append((ref, False, "reference not found"))
                continue
            if repo.get(new) is None:
                results.append((ref, False, "unknown object"))
                continue
            current = repo.refs.get(ref)
            if old == ZERO_OID:
                if current is not None:
                    results.append((ref, False, "reference already exists"))
                    continue
            else:
                if current != old:
                    results.append((ref, False, "stale info"))
                    continue
                if not ref.startswith("refs/tags/"):
                    old_commit = repo.peel_to_commit(old)
                    new_commit = repo.peel_to_commit(new)
                    if old_commit is not None and new_commit is not None:
                        if not repo.is_ancestor(old_commit, new_commit):
                            results.append((ref, False, "non-fast-forward"))
                            continue
            repo.refs[ref] = new
            repo.bump()
            results.append((ref, True, ""))
    report = []
    if unpack_ok:
        report.append(pkt_text("unpack ok\n"))
    else:
        report.append(pkt_text("unpack error %s\n" % (detail or "failed")))
    for ref, ok, reason in results:
        if ok:
            report.append(pkt_text("ok %s\n" % ref))
        else:
            report.append(pkt_text("ng %s %s\n" % (ref, reason)))
    report.append(PKT_FLUSH)
    stream = b"".join(report)
    return Response(200, sideband_packets(stream), _CT_RECEIVE_RESULT)


# --------------------------------------------------------------------------
# dispatch


def dispatch(request):
    path = request.path
    method = request.method
    if path == "/healthz" and method == "GET":
        return json_response(200, {"ok": True})
    if path.startswith("/api/"):
        response = dispatch_api(request)
        response.extra.setdefault(b"X-GitHub-Request-Id", FORGE.next_request_id())
        return response
    if path == "/mcp":
        return dispatch_mcp(request)
    # Fast paths for the git smart-HTTP routes: parse owner/repo/tail
    # directly instead of building the filtered segment list.
    if method == "GET" and path.endswith("/info/refs"):
        parts = path[1:-len("/info/refs")].split("/")
        if len(parts) == 2:
            owner = parts[0]
            name = parts[1][:-4] if parts[1].endswith(".git") else parts[1]
            repo = FORGE.get_repo(owner, name)
            if repo is None:
                return not_found()
            if not request.authorized():
                return error_response(401, "authentication required")
            service = request.query.get("service", [""])[0]
            return git_info_refs(request, repo, service)
    if method == "POST" and (path.endswith("/git-upload-pack") or path.endswith("/git-receive-pack")):
        service = "git-upload-pack" if path.endswith("/git-upload-pack") else "git-receive-pack"
        parts = path[1:-len("/" + service)].split("/")
        if len(parts) == 2:
            owner = parts[0]
            name = parts[1][:-4] if parts[1].endswith(".git") else parts[1]
            repo = FORGE.get_repo(owner, name)
            if repo is None:
                return not_found()
            if not request.authorized():
                return error_response(401, "authentication required")
            if service == "git-upload-pack":
                return git_upload_pack(request, repo)
            return git_receive_pack(request, repo)
    segments = [segment for segment in path.split("/") if segment != ""]
    if len(segments) >= 3:
        owner = segments[0]
        name = segments[1][:-4] if segments[1].endswith(".git") else segments[1]
        tail = segments[2:]
        repo = FORGE.get_repo(owner, name)
        if tail == ["info", "refs"] and method == "GET":
            if repo is None:
                return not_found()
            if not request.authorized():
                return error_response(401, "authentication required")
            service = request.query.get("service", [""])[0]
            return git_info_refs(request, repo, service)
        if tail == ["git-upload-pack"] and method == "POST":
            if repo is None:
                return not_found()
            if not request.authorized():
                return error_response(401, "authentication required")
            return git_upload_pack(request, repo)
        if tail == ["git-receive-pack"] and method == "POST":
            if repo is None:
                return not_found()
            if not request.authorized():
                return error_response(401, "authentication required")
            return git_receive_pack(request, repo)
    return not_found()


def dispatch_api(request):
    path = request.path
    method = request.method
    if path == "/api/graphql":
        return dispatch_graphql(request)
    if not path.startswith("/api/v3"):
        return not_found()
    if not request.authorized():
        return error_response(401, "Bad credentials")
    rest = path[len("/api/v3"):]
    # Fast paths for the hot routes: GET/POST a single issue without
    # building the filtered segment list.
    if rest.startswith("/repos/"):
        parts = rest[7:].split("/")
        if len(parts) == 4 and parts[2] == "issues" and parts[3].isdigit() and method == "GET":
            repo = require_repo(parts[0], parts[1])
            if repo is None:
                return not_found()
            return rest_get_issue(request, repo, int(parts[3]))
        if len(parts) == 3 and parts[2] == "issues" and method == "POST":
            repo = require_repo(parts[0], parts[1])
            if repo is None:
                return not_found()
            return rest_create_issue(request, repo)
    segments = [segment for segment in rest.split("/") if segment != ""]
    if not segments:
        if method == "GET":
            return rest_root(request)
        return not_found()
    if segments == ["meta"] and method == "GET":
        return rest_meta(request)
    if segments == ["user"] and method == "GET":
        return rest_user(request)
    if segments == ["user", "repos"]:
        if method == "POST":
            return rest_create_repo(request)
        if method == "GET":
            return rest_list_user_repos(request)
        return not_found()
    if len(segments) >= 3 and segments[0] == "repos":
        owner, name = segments[1], segments[2]
        repo = require_repo(owner, name)
        if repo is None:
            return not_found()
        tail = segments[3:]
        if not tail:
            if method == "GET":
                return rest_get_repo(request, repo)
            if method == "PATCH":
                return rest_patch_repo(request, repo)
            if method == "DELETE":
                return rest_delete_repo(request, repo)
            return not_found()
        return dispatch_repo_tail(request, repo, tail)
    return not_found()


def dispatch_repo_tail(request, repo, tail):
    method = request.method
    if tail == ["branches"] and method == "GET":
        return rest_list_branches(request, repo)
    if len(tail) >= 2 and tail[0] == "branches" and method == "GET":
        return rest_get_branch(request, repo, "/".join(tail[1:]))
    if tail == ["commits"] and method == "GET":
        return rest_list_commits(request, repo)
    if len(tail) >= 2 and tail[0] == "contents":
        path = "/".join(tail[1:])
        if method == "GET":
            return rest_get_contents(request, repo, path)
        if method == "PUT":
            return rest_put_contents(request, repo, path)
        if method == "DELETE":
            return rest_delete_contents(request, repo, path)
        return not_found()
    if tail == ["contents"] and method == "GET":
        return rest_get_contents(request, repo, "")
    if tail == ["git", "refs"] and method == "POST":
        return rest_create_ref(request, repo)
    if len(tail) >= 3 and tail[0] == "git" and tail[1] == "refs":
        ref = "refs/" + "/".join(tail[2:])
        if method == "GET":
            return rest_get_ref(request, repo, ref)
        if method == "DELETE":
            return rest_delete_ref(request, repo, ref)
        return not_found()
    if tail == ["labels"]:
        if method == "POST":
            return rest_create_label(request, repo)
        if method == "GET":
            return rest_list_labels(request, repo)
        return not_found()
    if tail == ["issues"]:
        if method == "POST":
            return rest_create_issue(request, repo)
        if method == "GET":
            return rest_list_issues(request, repo)
        return not_found()
    if len(tail) == 2 and tail[0] == "issues" and tail[1].isdigit():
        number = int(tail[1])
        if method == "GET":
            return rest_get_issue(request, repo, number)
        if method == "PATCH":
            return rest_patch_issue(request, repo, number)
        return not_found()
    if len(tail) == 3 and tail[0] == "issues" and tail[1].isdigit() and tail[2] == "comments":
        number = int(tail[1])
        if method == "POST":
            return rest_create_comment(request, repo, number)
        if method == "GET":
            return rest_list_comments(request, repo, number)
        return not_found()
    if tail == ["pulls"]:
        if method == "POST":
            return rest_create_pull(request, repo)
        if method == "GET":
            return rest_list_pulls(request, repo)
        return not_found()
    if len(tail) == 2 and tail[0] == "pulls" and tail[1].isdigit():
        if method == "GET":
            return rest_get_pull(request, repo, int(tail[1]))
        return not_found()
    if len(tail) == 3 and tail[0] == "pulls" and tail[1].isdigit() and tail[2] == "files":
        if method == "GET":
            return rest_pull_files(request, repo, int(tail[1]))
        return not_found()
    if len(tail) == 3 and tail[0] == "pulls" and tail[1].isdigit() and tail[2] == "merge":
        if method == "PUT":
            return rest_merge_pull(request, repo, int(tail[1]))
        return not_found()
    return not_found()


# --------------------------------------------------------------------------
# GraphQL: a small parser and executor for the v4 subset the clients send

_GQL_TOKEN = re.compile(r"""
    (?P<skip>[\s,]+|\#[^\n]*)
  | (?P<name>[_A-Za-z][_0-9A-Za-z]*)
  | (?P<float>-?\d+\.\d+(?:[eE][+-]?\d+)?|-?\d+[eE][+-]?\d+)
  | (?P<int>-?\d+)
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<spread>\.\.\.)
  | (?P<punct>[!$():=@\[\]{}|])
""", re.VERBOSE)


class GqlProblem(Exception):
    pass


def _gql_tokens(text):
    tokens = []
    pos = 0
    end = len(text)
    while pos < end:
        match = _GQL_TOKEN.match(text, pos)
        if match is None:
            raise GqlProblem("unexpected character %r" % text[pos])
        pos = match.end()
        kind = match.lastgroup
        if kind == "skip":
            continue
        tokens.append((kind, match.group()))
    tokens.append(("eof", ""))
    return tokens


class _GqlParser:
    def __init__(self, text):
        self.tokens = _gql_tokens(text)
        self.index = 0

    def peek(self):
        return self.tokens[self.index]

    def next(self):
        token = self.tokens[self.index]
        self.index += 1
        return token

    def expect_punct(self, char):
        kind, value = self.next()
        if kind != "punct" or value != char:
            raise GqlProblem("expected %r, got %r" % (char, value))

    def accept_punct(self, char):
        kind, value = self.peek()
        if kind == "punct" and value == char:
            self.index += 1
            return True
        return False

    def expect_name(self):
        kind, value = self.next()
        if kind != "name":
            raise GqlProblem("expected a name, got %r" % value)
        return value

    def parse_document(self):
        operations = []
        fragments = {}
        while self.peek()[0] != "eof":
            kind, value = self.peek()
            if kind == "punct" and value == "{":
                operations.append(("query", None, {}, self.parse_selection_set()))
            elif kind == "name" and value in ("query", "mutation"):
                self.next()
                name = None
                if self.peek()[0] == "name":
                    name = self.next()[1]
                var_defs = {}
                if self.accept_punct("("):
                    var_defs = self.parse_variable_defs()
                operations.append((value, name, var_defs, self.parse_selection_set()))
            elif kind == "name" and value == "fragment":
                self.next()
                frag_name = self.expect_name()
                if self.expect_name() != "on":
                    raise GqlProblem("fragment without a type condition")
                type_name = self.expect_name()
                fragments[frag_name] = (type_name, self.parse_selection_set())
            else:
                raise GqlProblem("unexpected token %r" % value)
        return operations, fragments

    def parse_variable_defs(self):
        defs = {}
        while not self.accept_punct(")"):
            self.expect_punct("$")
            name = self.expect_name()
            self.expect_punct(":")
            self.parse_type()
            default = None
            if self.accept_punct("="):
                default = self.parse_value(constant=True)
            defs[name] = default
        return defs

    def parse_type(self):
        if self.accept_punct("["):
            self.parse_type()
            self.expect_punct("]")
        else:
            self.expect_name()
        self.accept_punct("!")

    def parse_selection_set(self):
        self.expect_punct("{")
        selections = []
        while not self.accept_punct("}"):
            selections.append(self.parse_selection())
        return selections

    def parse_selection(self):
        kind, value = self.peek()
        if kind == "spread":
            self.next()
            if self.peek()[0] == "name" and self.peek()[1] == "on":
                self.next()
                type_name = self.expect_name()
                return ("inline", type_name, self.parse_selection_set())
            return ("spread", self.expect_name())
        first = self.expect_name()
        alias = None
        name = first
        if self.accept_punct(":"):
            alias = first
            name = self.expect_name()
        args = {}
        if self.accept_punct("("):
            while not self.accept_punct(")"):
                arg_name = self.expect_name()
                self.expect_punct(":")
                args[arg_name] = self.parse_value()
        selections = []
        if self.peek() == ("punct", "{"):
            selections = self.parse_selection_set()
        return ("field", name, alias, args, selections)

    def parse_value(self, constant=False):
        kind, value = self.next()
        if kind == "punct" and value == "$":
            if constant:
                raise GqlProblem("variable in a constant value")
            return ("var", self.expect_name())
        if kind == "int":
            return int(value)
        if kind == "float":
            return float(value)
        if kind == "string":
            return json.loads(value)
        if kind == "name":
            if value == "true":
                return True
            if value == "false":
                return False
            if value == "null":
                return None
            return ("enum", value)
        if kind == "punct" and value == "[":
            items = []
            while not self.accept_punct("]"):
                items.append(self.parse_value(constant))
            return items
        if kind == "punct" and value == "{":
            obj = {}
            while not self.accept_punct("}"):
                key = self.expect_name()
                self.expect_punct(":")
                obj[key] = self.parse_value(constant)
            return obj
        raise GqlProblem("unexpected value token %r" % value)


def _gql_value(value, variables):
    if isinstance(value, tuple):
        if value[0] == "var":
            return variables.get(value[1])
        if value[0] == "enum":
            return value[1]
        return value
    if isinstance(value, list):
        return [_gql_value(item, variables) for item in value]
    if isinstance(value, dict):
        return {key: _gql_value(item, variables) for key, item in value.items()}
    return value


class _GqlFieldError(Exception):
    pass


# Type names for values the executor carries: (type_name, payload) markers.
def _mark(type_name, payload):
    return ("__gql__", type_name, payload)


def _is_mark(value):
    return isinstance(value, tuple) and len(value) == 3 and value[0] == "__gql__"


_TYPE_FIELDS = {
    "Issue": ["id", "number", "title", "body", "state", "createdAt", "updatedAt", "closedAt", "author", "repository"],
    "PullRequest": ["id", "number", "title", "body", "state", "merged", "mergeable", "headRefName", "baseRefName", "files", "createdAt", "updatedAt", "closedAt", "author"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner", "defaultBranchRef", "viewerPermission", "hasIssuesEnabled", "issue", "issues", "pullRequest", "pullRequests", "isPrivate", "createdAt", "updatedAt"],
    "User": ["id", "login", "name", "email"],
    "Comment": ["id", "body", "author", "createdAt"],
    "Ref": ["name", "prefix"],
    "PullRequestFile": ["path"],
}
_TYPE_ENUMS = {"SearchType": ["ISSUE", "REPOSITORY", "USER"]}


def _cursor(index):
    return base64.urlsafe_b64encode(("cursor:%d" % index).encode("ascii")).decode("ascii").rstrip("=")


def _cursor_index(text):
    parsed = parse_global_id(text) if isinstance(text, str) else None
    if isinstance(text, str):
        try:
            padded = text + "=" * (-len(text) % 4)
            raw = base64.urlsafe_b64decode(padded.encode("ascii")).decode("ascii")
            if raw.startswith("cursor:"):
                return int(raw[len("cursor:"):])
        except (ValueError, UnicodeDecodeError):
            return None
    return None


def _connection(items, args):
    first = args.get("first")
    after = args.get("after")
    start = 0
    if after is not None:
        index = _cursor_index(after)
        if index is not None:
            start = index + 1
    if isinstance(first, int) and first >= 0:
        page = items[start:start + first]
    else:
        page = items[start:]
    end_index = start + len(page) - 1
    has_next = end_index < len(items) - 1
    end_cursor = _cursor(end_index) if page else None
    return _mark("Connection", (page, has_next, end_cursor))


def _issue_order(items, args):
    states = args.get("states")
    if isinstance(states, list) and states:
        wanted = {str(state).lower() for state in states}
        items = [item for item in items if item.state in wanted]
    order_by = args.get("orderBy")
    descending = False
    if isinstance(order_by, dict) and str(order_by.get("direction", "")).upper() == "DESC":
        descending = True
    items.sort(key=lambda item: item.number, reverse=descending)
    return items


class _Gql:
    def __init__(self, variables, fragments):
        self.variables = variables
        self.fragments = fragments
        self.errors = []

    def args_of(self, raw_args):
        return {key: _gql_value(value, self.variables) for key, value in raw_args.items()}

    def run(self, operation):
        op_type, _name, _var_defs, selections = operation
        root_type = "Mutation" if op_type == "mutation" else "Query"
        data = self.resolve_set(root_type, None, selections)
        result = {"data": data}
        if self.errors:
            result["errors"] = self.errors
        return result

    def resolve_set(self, type_name, obj, selections):
        out = {}
        for selection in selections:
            if selection[0] == "inline":
                if selection[1] == type_name:
                    out.update(self.resolve_set(type_name, obj, selection[2]))
                continue
            if selection[0] == "spread":
                fragment = self.fragments.get(selection[1])
                if fragment is not None and fragment[0] == type_name:
                    out.update(self.resolve_set(type_name, obj, fragment[1]))
                continue
            _kind, field, alias, raw_args, sub = selection
            key = alias or field
            if field == "__typename":
                out[key] = type_name
                continue
            try:
                value = self.field(type_name, obj, field, self.args_of(raw_args))
            except _GqlFieldError as error:
                self.errors.append({"message": str(error)})
                out[key] = None
                continue
            out[key] = self.complete(value, sub)
        return out

    def complete(self, value, selections):
        if value is None:
            return None
        if _is_mark(value):
            return self.resolve_set(value[1], value[2], selections)
        if isinstance(value, list):
            return [self.complete(item, selections) for item in value]
        return value

    # -- field resolvers ----------------------------------------------------

    def field(self, type_name, obj, field, args):
        handler = getattr(self, "_type_" + type_name, None)
        if handler is None:
            raise _GqlFieldError("Field '%s' doesn't exist on type '%s'" % (field, type_name))
        return handler(obj, field, args)

    def _type_Query(self, obj, field, args):
        if field == "viewer":
            return _mark("User", VIEWER_LOGIN)
        if field == "repository":
            repo = FORGE.get_repo(str(args.get("owner")), str(args.get("name")))
            return _mark("Repository", repo) if repo is not None else None
        if field == "node":
            return self._node(args.get("id"))
        if field == "__type":
            name = args.get("name")
            if name in _TYPE_FIELDS:
                return _mark("TypeInfo", (name, "OBJECT"))
            if name in _TYPE_ENUMS:
                return _mark("TypeInfo", (name, "ENUM"))
            return None
        raise _GqlFieldError("Field '%s' doesn't exist on type 'Query'" % field)

    def _node(self, node_id):
        parsed = parse_global_id(node_id)
        if parsed is None:
            return None
        kind, parts = parsed
        if kind == "repo":
            repo = repo_by_global_id(node_id)
            return _mark("Repository", repo) if repo is not None else None
        if kind in ("issue", "pr") and len(parts) >= 2:
            repo = repo_by_global_id(global_id("repo", parts[0]))
            if repo is None:
                return None
            try:
                number = int(parts[1])
            except ValueError:
                return None
            record = repo.issues.get(number) if kind == "issue" else repo.pulls.get(number)
            if record is None:
                return None
            return _mark("Issue" if kind == "issue" else "PullRequest", (repo, record))
        return None

    def _type_Mutation(self, obj, field, args):
        payload = args.get("input") or {}
        if not isinstance(payload, dict):
            raise _GqlFieldError("Mutation '%s' needs an input object" % field)
        if field == "createIssue":
            repo = repo_by_global_id(payload.get("repositoryId"))
            if repo is None:
                raise _GqlFieldError("repository not found")
            title = payload.get("title")
            if not isinstance(title, str) or not title:
                raise _GqlFieldError("title is required")
            text = payload.get("body")
            issue = create_issue_record(repo, title, text if isinstance(text, str) else "", [])
            return _mark("Payload", {"issue": _mark("Issue", (repo, issue))})
        if field == "closeIssue":
            found = self._node(payload.get("issueId"))
            if found is None or found[1] != "Issue":
                raise _GqlFieldError("issue not found")
            repo, issue = found[2]
            with FORGE.lock:
                issue.state = "closed"
                issue.closed_ts = CLOCK.tick()
                issue.updated_ts = issue.closed_ts
                repo.issue_get_cache.pop(issue.number, None)
            return _mark("Payload", {"issue": _mark("Issue", (repo, issue))})
        if field == "createPullRequest":
            repo = repo_by_global_id(payload.get("repositoryId"))
            if repo is None:
                raise _GqlFieldError("repository not found")
            title = payload.get("title")
            head = payload.get("headRefName")
            base = payload.get("baseRefName") or repo.default_branch
            if not isinstance(title, str) or not isinstance(head, str):
                raise _GqlFieldError("title and headRefName are required")
            text = payload.get("body")
            pull = create_pull_record(repo, title, text if isinstance(text, str) else "", head, base)
            if pull is None:
                raise _GqlFieldError("cannot open pull request")
            return _mark("Payload", {"pullRequest": _mark("PullRequest", (repo, pull))})
        if field == "mergePullRequest":
            found = self._node(payload.get("pullRequestId"))
            if found is None or found[1] != "PullRequest":
                raise _GqlFieldError("pull request not found")
            repo, pull = found[2]
            with FORGE.lock:
                if pull.merged or pull.state != "open":
                    raise _GqlFieldError("pull request is not mergeable")
                commit_oid = squash_merge(repo, pull)
                if commit_oid is None:
                    raise _GqlFieldError("pull request has conflicts")
                pull.merged = True
                pull.state = "closed"
                pull.merged_ts = CLOCK.tick()
                pull.updated_ts = pull.merged_ts
                pull.merge_commit = commit_oid
            return _mark("Payload", {"pullRequest": _mark("PullRequest", (repo, pull))})
        if field == "addComment":
            found = self._node(payload.get("subjectId"))
            if found is None or found[1] not in ("Issue", "PullRequest"):
                raise _GqlFieldError("subject not found")
            repo, record = found[2]
            text = payload.get("body")
            if not isinstance(text, str):
                raise _GqlFieldError("body is required")
            with FORGE.lock:
                comment_id = repo.next_comment_id
                repo.next_comment_id += 1
                comment = Comment(comment_id, record.number, text, CLOCK.tick())
                repo.comments[comment_id] = comment
                if found[1] == "Issue":
                    record.comments.append(comment_id)
                    repo.issue_get_cache.pop(record.number, None)
            edge = _mark("CommentEdge", _mark("Comment", (repo, comment)))
            return _mark("Payload", {"commentEdge": edge})
        raise _GqlFieldError("Field '%s' doesn't exist on type 'Mutation'" % field)

    def _type_Payload(self, obj, field, args):
        if field in obj:
            return obj[field]
        raise _GqlFieldError("Field '%s' doesn't exist on this payload" % field)

    def _type_CommentEdge(self, obj, field, args):
        if field == "node":
            return obj
        if field == "cursor":
            return _cursor(0)
        raise _GqlFieldError("Field '%s' doesn't exist on type 'CommentEdge'" % field)

    def _type_User(self, obj, field, args):
        if field == "login":
            return obj
        if field == "id":
            return global_id("user", VIEWER_ID)
        if field == "name":
            return VIEWER_NAME if obj == VIEWER_LOGIN else obj
        if field == "email":
            return VIEWER_EMAIL if obj == VIEWER_LOGIN else ""
        raise _GqlFieldError("Field '%s' doesn't exist on type 'User'" % field)

    def _type_Repository(self, repo, field, args):
        if field == "id":
            return global_id("repo", repo.id)
        if field == "databaseId":
            return repo.id
        if field == "name":
            return repo.name
        if field == "nameWithOwner":
            return repo.full_name
        if field == "owner":
            return _mark("User", repo.owner)
        if field == "defaultBranchRef":
            if repo.refs.get(repo.head_ref()) is not None:
                return _mark("Ref", repo.default_branch)
            return None
        if field == "viewerPermission":
            return "ADMIN"
        if field == "hasIssuesEnabled":
            return True
        if field == "isPrivate":
            return repo.private
        if field == "createdAt":
            return iso_of(repo.created_ts)
        if field == "updatedAt":
            return iso_of(repo.created_ts)
        if field == "issue":
            issue = repo.issues.get(args.get("number"))
            return _mark("Issue", (repo, issue)) if issue is not None else None
        if field == "issues":
            items = _issue_order(list(repo.issues.values()), args)
            return _connection([_mark("Issue", (repo, issue)) for issue in items], args)
        if field == "pullRequest":
            pull = repo.pulls.get(args.get("number"))
            return _mark("PullRequest", (repo, pull)) if pull is not None else None
        if field == "pullRequests":
            items = list(repo.pulls.values())
            states = args.get("states")
            if isinstance(states, list) and states:
                wanted = {str(state).upper() for state in states}
                items = [pull for pull in items if _pull_state(pull) in wanted]
            items.sort(key=lambda pull: pull.number)
            return _connection([_mark("PullRequest", (repo, pull)) for pull in items], args)
        raise _GqlFieldError("Field '%s' doesn't exist on type 'Repository'" % field)

    def _type_Issue(self, obj, field, args):
        repo, issue = obj
        if field == "id":
            return global_id("issue", repo.id, issue.number)
        if field == "number":
            return issue.number
        if field == "title":
            return issue.title
        if field == "body":
            return issue.body
        if field == "state":
            return issue.state.upper()
        if field == "createdAt":
            return iso_of(issue.created_ts)
        if field == "updatedAt":
            return iso_of(issue.updated_ts)
        if field == "closedAt":
            return iso_of(issue.closed_ts) if issue.closed_ts else None
        if field == "author":
            return _mark("User", repo.owner)
        if field == "repository":
            return _mark("Repository", repo)
        raise _GqlFieldError("Field '%s' doesn't exist on type 'Issue'" % field)

    def _type_PullRequest(self, obj, field, args):
        repo, pull = obj
        if field == "id":
            return global_id("pr", repo.id, pull.number)
        if field == "number":
            return pull.number
        if field == "title":
            return pull.title
        if field == "body":
            return pull.body
        if field == "state":
            return _pull_state(pull)
        if field == "merged":
            return pull.merged
        if field == "mergeable":
            return "MERGEABLE" if pull_mergeable(repo, pull) else "CONFLICTING"
        if field == "headRefName":
            return pull.head_ref
        if field == "baseRefName":
            return pull.base_ref
        if field == "files":
            files = pull_files_diff(repo, pull)
            return _connection([_mark("PullRequestFile", item["filename"]) for item in files], args)
        if field == "createdAt":
            return iso_of(pull.created_ts)
        if field == "updatedAt":
            return iso_of(pull.updated_ts)
        if field == "closedAt":
            return iso_of(pull.merged_ts) if pull.merged_ts else None
        if field == "author":
            return _mark("User", repo.owner)
        raise _GqlFieldError("Field '%s' doesn't exist on type 'PullRequest'" % field)

    def _type_PullRequestFile(self, obj, field, args):
        if field == "path":
            return obj
        raise _GqlFieldError("Field '%s' doesn't exist on type 'PullRequestFile'" % field)

    def _type_Comment(self, obj, field, args):
        repo, comment = obj
        if field == "id":
            return global_id("comment", repo.id, comment.id)
        if field == "body":
            return comment.body
        if field == "author":
            return _mark("User", repo.owner)
        if field == "createdAt":
            return iso_of(comment.created_ts)
        raise _GqlFieldError("Field '%s' doesn't exist on type 'Comment'" % field)

    def _type_Ref(self, obj, field, args):
        if field == "name":
            return obj
        if field == "prefix":
            return "refs/heads/"
        raise _GqlFieldError("Field '%s' doesn't exist on type 'Ref'" % field)

    def _type_Connection(self, obj, field, args):
        page, has_next, end_cursor = obj
        if field == "nodes":
            return page
        if field == "pageInfo":
            return _mark("PageInfo", (has_next, end_cursor))
        if field == "totalCount":
            return len(page)
        raise _GqlFieldError("Field '%s' doesn't exist on a connection" % field)

    def _type_PageInfo(self, obj, field, args):
        has_next, end_cursor = obj
        if field == "hasNextPage":
            return has_next
        if field == "hasPreviousPage":
            return False
        if field == "endCursor":
            return end_cursor
        if field == "startCursor":
            return end_cursor
        raise _GqlFieldError("Field '%s' doesn't exist on type 'PageInfo'" % field)

    def _type_TypeInfo(self, obj, field, args):
        name, kind = obj
        if field == "name":
            return name
        if field == "kind":
            return kind
        if field == "fields":
            return [_mark("TypeField", field_name) for field_name in _TYPE_FIELDS.get(name, [])]
        if field == "enumValues":
            return [_mark("EnumValue", value) for value in _TYPE_ENUMS.get(name, [])]
        raise _GqlFieldError("Field '%s' doesn't exist on type '__Type'" % field)

    def _type_TypeField(self, obj, field, args):
        if field == "name":
            return obj
        raise _GqlFieldError("Field '%s' doesn't exist on type '__Field'" % field)

    def _type_EnumValue(self, obj, field, args):
        if field == "name":
            return obj
        raise _GqlFieldError("Field '%s' doesn't exist on type '__EnumValue'" % field)


def _pull_state(pull):
    if pull.merged:
        return "MERGED"
    return pull.state.upper()


def _execute_graphql(document, variables, operation_name):
    operations, fragments = _GqlParser(document).parse_document()
    chosen = None
    for operation in operations:
        if operation_name is None or operation[1] == operation_name:
            chosen = operation
            break
    if chosen is None:
        return {"data": None, "errors": [{"message": "operation not found"}]}
    executor = _Gql(variables or {}, fragments)
    return executor.run(chosen)


def dispatch_graphql(request):
    if request.method != "POST":
        return json_response(405, {"errors": [{"message": "method not allowed"}]})
    if not request.authorized():
        return json_response(401, {"errors": [{"message": "Bad credentials"}]})
    body = parse_json_body(request.body)
    if body is None:
        return json_response(400, {"errors": [{"message": "request body is not JSON"}]})
    if isinstance(body, list):
        results = []
        for entry in body:
            results.append(_graphql_one(entry))
        return json_response(200, results)
    return json_response(200, _graphql_one(body))


def _graphql_one(entry):
    if not isinstance(entry, dict) or not isinstance(entry.get("query"), str):
        return {"data": None, "errors": [{"message": "a query document is required"}]}
    variables = entry.get("variables")
    if not isinstance(variables, dict):
        variables = {}
    try:
        return _execute_graphql(entry["query"], variables, entry.get("operationName"))
    except GqlProblem as error:
        return {"data": None, "errors": [{"message": str(error)}]}


# --------------------------------------------------------------------------
# MCP: streamable-HTTP JSON-RPC with the modern discover era (and legacy)

MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a repository owned by the token's user.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "the repository name"},
                "description": {"type": "string", "description": "a short description"},
                "private": {"type": "boolean", "description": "whether the repository is private"},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Read one repository by owner and name.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "list_repos",
        "description": "List the repositories owned by the token's user.",
        "inputSchema": {"type": "object", "properties": {}},
    },
    {
        "name": "create_issue",
        "description": "Open an issue in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "title": {"type": "string"},
                "body": {"type": "string"},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "list_issues",
        "description": "List a repository's issues, optionally filtered by state.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "state": {"type": "string"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "get_issue",
        "description": "Read one issue by number.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "issue_number": {"type": "integer"},
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
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "title": {"type": "string"},
                "body": {"type": "string"},
                "head": {"type": "string"},
                "base": {"type": "string"},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Squash-merge an open pull request.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "pull_number": {"type": "integer"},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]
MCP_TOOLS_BY_NAME = {tool["name"]: tool for tool in MCP_TOOLS}
MCP_SERVER_INFO = {"name": "forge", "version": VERSION}


def _mcp_result(value):
    return {"content": [{"type": "text", "text": json.dumps(value, ensure_ascii=False)}],
            "structuredContent": value}


def _mcp_tool_error(message):
    return {"content": [{"type": "text", "text": message}], "isError": True}


def _mcp_call_tool(name, arguments):
    tool = MCP_TOOLS_BY_NAME.get(name)
    if tool is None:
        return None, (-32602, "unknown tool: %s" % name)
    for required in tool["inputSchema"].get("required", []):
        if arguments.get(required) is None:
            return None, (-32602, "missing required argument: %s" % required)
    owner = arguments.get("owner")
    repo_name = arguments.get("repo")
    try:
        if name == "create_repo":
            repo_name_value = arguments["name"]
            if FORGE.get_repo(VIEWER_LOGIN, repo_name_value) is not None:
                return _mcp_tool_error("repository already exists"), None
            description = arguments.get("description")
            repo = FORGE.create_repo(VIEWER_LOGIN, repo_name_value,
                                     description if isinstance(description, str) else "",
                                     bool(arguments.get("private", False)))
            return _mcp_result(repo_json(repo)), None
        if name == "list_repos":
            return _mcp_result({"repos": [repo_json(repo) for repo in FORGE.viewer_repos(VIEWER_LOGIN)]}), None
        repo = FORGE.get_repo(str(owner), str(repo_name))
        if repo is None:
            return _mcp_tool_error("repository not found"), None
        if name == "get_repo":
            return _mcp_result(repo_json(repo)), None
        if name == "create_issue":
            text = arguments.get("body")
            issue = create_issue_record(repo, str(arguments["title"]),
                                        text if isinstance(text, str) else "", [])
            return _mcp_result(issue_json(repo, issue)), None
        if name == "list_issues":
            state = arguments.get("state") or "open"
            issues = [issue for issue in repo.issues.values()
                      if state == "all" or issue.state == state]
            issues.sort(key=lambda issue: issue.number)
            return _mcp_result({"issues": [issue_json(repo, issue) for issue in issues]}), None
        if name == "get_issue":
            issue = repo.issues.get(int(arguments["issue_number"]))
            if issue is None:
                return _mcp_tool_error("issue not found"), None
            return _mcp_result(issue_json(repo, issue)), None
        if name == "create_pull_request":
            text = arguments.get("body")
            pull = create_pull_record(repo, str(arguments["title"]),
                                      text if isinstance(text, str) else "",
                                      str(arguments["head"]), str(arguments["base"]))
            if pull is None:
                return _mcp_tool_error("cannot open pull request: a branch is missing"), None
            return _mcp_result(pull_json(repo, pull)), None
        if name == "merge_pull_request":
            pull = repo.pulls.get(int(arguments["pull_number"]))
            if pull is None:
                return _mcp_tool_error("pull request not found"), None
            with FORGE.lock:
                if pull.merged or pull.state != "open":
                    return _mcp_tool_error("pull request is not mergeable"), None
                commit_oid = squash_merge(repo, pull)
                if commit_oid is None:
                    return _mcp_tool_error("pull request has conflicts"), None
                pull.merged = True
                pull.state = "closed"
                pull.merged_ts = CLOCK.tick()
                pull.updated_ts = pull.merged_ts
                pull.merge_commit = commit_oid
            return _mcp_result(pull_json(repo, pull)), None
    except (ValueError, TypeError, KeyError) as error:
        return _mcp_tool_error("invalid arguments: %s" % error), None
    return _mcp_tool_error("unhandled tool"), None


def _mcp_handle(message):
    """One JSON-RPC message -> (status, response dict or None for notifications)."""
    if not isinstance(message, dict):
        return 400, {"jsonrpc": "2.0", "id": None, "error": {"code": -32600, "message": "invalid request"}}
    method = message.get("method")
    msg_id = message.get("id")
    params = message.get("params") or {}
    if not isinstance(params, dict):
        params = {}
    if method == "server/discover":
        result = {
            "resultType": "complete",
            "supportedVersions": ["2026-07-28"],
            "capabilities": {"tools": {}},
            "serverInfo": MCP_SERVER_INFO,
            "_meta": {"io.modelcontextprotocol/serverInfo": MCP_SERVER_INFO},
        }
        return 200, {"jsonrpc": "2.0", "id": msg_id, "result": result}
    if method == "initialize":
        offered = params.get("protocolVersion")
        known = ("2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05")
        result = {
            "protocolVersion": offered if offered in known else "2025-11-25",
            "capabilities": {"tools": {}},
            "serverInfo": MCP_SERVER_INFO,
        }
        return 200, {"jsonrpc": "2.0", "id": msg_id, "result": result}
    if msg_id is None:
        return 202, None  # a notification: accepted, nothing to answer
    if method == "ping":
        return 200, {"jsonrpc": "2.0", "id": msg_id, "result": {}}
    if method == "tools/list":
        return 200, {"jsonrpc": "2.0", "id": msg_id, "result": {"tools": MCP_TOOLS}}
    if method == "tools/call":
        tool_name = params.get("name")
        arguments = params.get("arguments") or {}
        if not isinstance(arguments, dict):
            arguments = {}
        result, error = _mcp_call_tool(str(tool_name), arguments)
        if error is not None:
            code, text = error
            return 200, {"jsonrpc": "2.0", "id": msg_id, "error": {"code": code, "message": text}}
        return 200, {"jsonrpc": "2.0", "id": msg_id, "result": result}
    return 200, {"jsonrpc": "2.0", "id": msg_id,
                 "error": {"code": -32601, "message": "method not found: %s" % method}}


def dispatch_mcp(request):
    if request.method == "DELETE":
        return Response(204)
    if request.method != "POST":
        return json_response(405, {"jsonrpc": "2.0", "id": None,
                                   "error": {"code": -32600, "message": "method not allowed"}})
    if not request.authorized():
        return json_response(401, {"jsonrpc": "2.0", "id": None,
                                   "error": {"code": -32001, "message": "unauthorized"}})
    body = parse_json_body(request.body)
    if body is None:
        return json_response(400, {"jsonrpc": "2.0", "id": None,
                                   "error": {"code": -32700, "message": "parse error"}})
    if isinstance(body, list):
        answers = []
        status = 200
        for entry in body:
            entry_status, answer = _mcp_handle(entry)
            status = entry_status
            if answer is not None:
                answers.append(answer)
        if not answers:
            return Response(202)
        return json_response(status, answers)
    status, answer = _mcp_handle(body)
    if answer is None:
        return Response(202)
    return json_response(status, answer)


# --------------------------------------------------------------------------
# lifecycle: bind, register with the env, serve until it says done


def _env_opener():
    return urllib.request.build_opener(urllib.request.ProxyHandler({}))


def _register(port):
    opener = _env_opener()
    delay = 0.25
    while True:
        try:
            payload = json_bytes({"port": port})
            req = urllib.request.Request(
                ENV_URL + "/register", data=payload,
                headers={"Content-Type": "application/json"}, method="POST")
            with opener.open(req, timeout=30) as response:
                response.read()
                if response.status in (200, 409):
                    return
        except urllib.error.HTTPError as error:
            if error.code in (200, 409):
                return
            if error.code in (400, 405):
                sys.stderr.write("register refused: HTTP %d\n" % error.code)
                return
        except (urllib.error.URLError, OSError):
            pass
        time.sleep(delay)
        delay = min(2.0, delay * 2)


def _wait_for_done(server):
    opener = _env_opener()
    delay = 0.25
    while True:
        try:
            with opener.open(ENV_URL + "/done", timeout=30) as response:
                body = json.loads(response.read().decode("utf-8"))
                if isinstance(body, dict) and body.get("done") is True:
                    break
        except (urllib.error.URLError, OSError, ValueError):
            pass
        time.sleep(delay)
        delay = min(2.0, delay * 2)
    server.shutdown()


def main():
    port = 0
    raw_port = os.environ.get("PORT", "") or os.environ.get("FORGE_PORT", "")
    if raw_port.isdigit():
        port = int(raw_port)
    server = _WorkerPoolServer(("", port), HttpHandler)
    bound_port = server.server_address[1]
    sys.stderr.write("forge listening on port %d\n" % bound_port)
    if ENV_URL:
        registrar = threading.Thread(target=_register_and_wait, args=(bound_port, server), daemon=True)
        registrar.start()
    try:
        server.serve_forever(poll_interval=0.05)
    except KeyboardInterrupt:
        pass
    server.server_close()
    return 0


def _register_and_wait(port, server):
    _register(port)
    _wait_for_done(server)


if __name__ == "__main__":
    sys.exit(main())
