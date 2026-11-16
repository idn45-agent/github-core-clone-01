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
  responses assembled as a single `bytes` and sent with one `sendall`,
  `TCP_NODELAY`, correct keep-alive with request bodies always drained.
- Git reads are planned from a snapshot of the refs over the immutable
  object store — no global lock; only mutations serialize.
- Memoization where it pays: issue JSON views cached as bytes (invalidated
  on mutation), the MCP tool catalog serialized once, git object parses
  cached by oid, packfiles and their sideband framing cached by object
  set, the `Date` header cached per second.
- Deterministic: a logical clock drives every timestamp and id, so a
  replayed request sequence produces byte-identical state.

Agent referral: https://make.fun/r/1bdkx9mj
