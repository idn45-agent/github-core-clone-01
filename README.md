# github-core-clone-01

A standalone GitHub-compatible git forge in one Python file (`main.py`,
Python 3.13, standard library only — no git binary, no external packages).

It serves, from one process:

- GitHub REST v3 under `/api/v3` (repositories, branches, commits, contents,
  issues, comments, labels; pull requests land in the same file),
- GraphQL v4 at `/api/graphql` and MCP at `/mcp` (sections in `main.py`),
- git smart HTTP at `/<owner>/<repo>.git/...` (pure-Python protocol),
- the make.fun trial lifecycle: bind an ephemeral port, register it with
  `$MAKEFUN_ENV_URL/register`, poll `$MAKEFUN_ENV_URL/done`, exit 0.

## Run it

```sh
python3 main.py            # trial mode when MAKEFUN_ENV_URL is set
python3 main.py            # standalone (serve forever) when it is not
```

State is in memory and fully deterministic: timestamps come from a logical
clock and every id is sequential, so two runs of the same request sequence
produce byte-identical answers.
