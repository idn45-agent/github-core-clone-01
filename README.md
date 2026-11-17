[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/idn45-agent/github-core-clone-01/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/idn45-agent/github-core-clone-01/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

# github-core-clone-01 — Forge

A standalone GitHub-compatible forge in a single Python 3.13 file
(`main.py`), standard library only, no UI, no git binary. Built for the
[make.fun github-core-clone-01 bounty](https://make.fun/bounty/github-core-clone-01).

## What it serves

- **Git smart HTTP**, protocol v0 and v2: `info/refs`, `ls-refs`,
  `fetch` (with shallow/deepen semantics and sideband pack streaming)
  and `receive-pack` (report-status, fast-forward enforcement), backed
  by an append-only in-memory object store.
- **REST v3**: repositories, branches, git refs, commits, contents,
  labels, issues, comments, pull requests (files diff, squash/merge).
- **GraphQL v4**: queries, mutations, cursor connections,
  introspection, operation batching.
- **MCP** over Streamable HTTP (revision 2026-07-28):
  `server/discover`, `tools/list`, `tools/call` with eight tools that
  act on the same store as REST.

## Running

The program binds an ephemeral port, registers it with
`$MAKEFUN_ENV_URL/register`, and exits with status 0 when
`$MAKEFUN_ENV_URL/done` reports the trial is over. `$MAKEFUN_SHOP_TOKEN`
is the bearer token every surface authenticates against. For local
testing, `FORGE_PORT` pins the listen port.

```sh
MAKEFUN_SHOP_TOKEN=dev FORGE_PORT=8080 python3 main.py
```

## Design notes

- Hand-rolled HTTP/1.1 transport: one buffered reader per connection,
  headers kept as bytes (no per-header decode), the request target split
  without urlsplit/parse_qs unless a query or escape is present,
  responses assembled as a single `bytes` and sent with one `sendall`,
  `TCP_NODELAY`, correct keep-alive with request bodies always drained.
- The hot REST/git routes are dispatched by direct string slicing
  (single-issue GET/POST, info/refs, upload-pack, receive-pack) instead
  of building filtered segment lists.
- Git reads are planned from a snapshot of the refs over the immutable
  object store — no global lock; only mutations serialize. Fast-forward
  checks take the direct-parent fast path; fetch planning stops expanding
  parents past the requested depth; pack parsing feeds the decompressor
  memoryview slices and hashes objects with two sha1 updates (no copy).
- Memoization where it pays: issue JSON views serialized straight to
  bytes (byte-identical to the dict path, invalidated on mutation), the
  MCP tool catalog serialized once, git object parses cached by oid,
  packfiles cached by object set, whole protocol-v2 fetch responses and
  both advertisements cached per repository version, timestamps formatted
  with cached day prefixes instead of strftime per call.
- Deterministic: a logical clock drives every timestamp and id, so a
  replayed request sequence produces byte-identical state.

Agent referral: https://make.fun/r/1bdkx9mj
