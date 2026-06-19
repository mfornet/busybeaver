# Lean Busy Beaver

[![CI](https://github.com/mfornet/busybeaver/actions/workflows/ci.yml/badge.svg)](https://github.com/mfornet/busybeaver/actions/workflows/ci.yml)

This project contains an attempt at formalising results regarding Busy Beavers.

The objective is to merge deciders and their proof of correctness.

More broadly, the project should rely as little as possible on
specific numbers of states and symbols. The idea is to have an
executable that allows querying and computing busy beaver values, as
well as a playground to play with TMs.

# Using the project

You will need to have `lake` installed:
```
lake exe beaver -h
```

Follow the help from here.

For an individual machine, `decide` stops after the first definite result:

```bash
lake exe beaver decide 0RB---_1LA1LB
```

Pass `--all` to keep running later deciders after a result is found. To classify
machine codes already written to a holdout log, use `audit`:

```bash
lake exe beaver audit holdouts.txt --limit 100
```

## Codex + Lean MCP

To register [`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp) with Codex for this repo:

```bash
ci/lean_mcp.sh register
```

This does three things:
1. Runs `lake build` in this project.
2. Registers a Codex MCP server named `lean-lsp`.
3. Pins `LEAN_PROJECT_PATH` to this repo so Lean tools resolve here.

Check the resulting MCP config:

```bash
ci/lean_mcp.sh status
```

For debugging, you can run the MCP server directly:

```bash
ci/lean_mcp.sh serve
```

Manual equivalent:

```bash
codex mcp add lean-lsp --env "LEAN_PROJECT_PATH=$(pwd)" -- uvx lean-lsp-mcp
```

## Codex Local Environment

Codex worktrees run in separate directories and get their own local `.lake` state by default. For this Lean project, the expensive part is the dependency checkout and build cache under `.lake/packages`, especially mathlib.

This repo includes a Codex local environment at [`.codex/environments/environment.toml`](/Users/mnaeraxr/Documents/projects/busy-beaver-research/busybeaver/.codex/environments/environment.toml). Its setup step delegates to [ci/codex_lean_setup.sh](./ci/codex_lean_setup.sh), which reuses or migrates `.lake/packages` from a shared cache root and then runs `lake build` in the current worktree.

Recommended shared cache location:

```bash
CODEX_LEAN_CACHE_ROOT=$HOME/.codex/cache/busybeaver-lean
```

What this gives you:

1. New worktrees reuse the same dependency checkout and build cache.
2. Only the repo-local code in the current worktree needs to rebuild.
3. You can reset the cache later by deleting the shared cache root.

## Configuration file

The binary admits a configuration file for the deciders, in JSON, the
configuration is an array of decider parameters, which can be
repeated.

Available deciders include:
- Bounded exploration: `{ "explore": <number> }`
- Loop1 translated-loop detection: `{ "loop1": <number> }`
- Translated cyclers: `{ "translatedCycler": <number> }`
- Cyclers: `{ "cycler": <number> }`
- Backwards reasoning: `{ "backwardsReasoning": <number> }`
- NGram CPS: `{ "nGramCPS": { "n": <number>, "bound": <number> } }`
- History-augmented NGram CPS:
  `{ "nGramCPSHistory": { "history": <number>, "left": <number>, "right": <number>, "bound": <number> } }`
- LRU-augmented NGram CPS:
  `{ "nGramCPSLRU": { "left": <number>, "right": <number>, "bound": <number> } }`
- Repeated Word List:
  `{ "repWL": { "len": <number>, "threshold": <number>, "maxT": <number>, "bound": <number> } }`
- BB5 generated hardcoded table: `"bb5TableExecutable"`
- BB5 generated full table alias: `"bb5TableAll"`

When no configuration file is passed, the executable uses a size-aware default:
`BB(3,2)` includes the history-augmented NGram CPS pass needed to close the
known holdouts, `BB(4,2)` uses the complete Coq-style pipeline, `BB(5,2)` uses
the Coq NGram pipeline plus the generated hardcoded table, and other larger runs
use a lighter development default.

The larger-run development default is equivalent to:
```json
[
  { "explore": 130 },
  { "translatedCycler": 300 },
  { "cycler": 300 },
  { "nGramCPS": { "n": 1, "bound": 100 } },
  { "nGramCPS": { "n": 2, "bound": 200 } },
  { "nGramCPS": { "n": 3, "bound": 400 } }
]
```

For `BB(3,2)`, the default additionally appends:
```json
{ "nGramCPSHistory": { "history": 2, "left": 2, "right": 2, "bound": 1600 } }
```

For `BB(4,2)`, the default follows the exact `S(4)` pipeline from the Coq proof:
loop detection with bound `107`, the standard NGram CPS passes, the fixed-history
and LRU NGram CPS passes, and finally RepWL with `{ "len": 4, "threshold": 3,
"maxT": 320, "bound": 10000 }`.

For `BB(5,2)`, the default uses bounded exploration passes for partial-machine
expansion; the Loop1, NGram CPS, LRU, and RepWL passes from the Coq BB5
pipeline for which Lean has executable equivalents; and `"bb5TableExecutable"`.
The generated table contains all 8,228 hardcoded Coq rows, including custom
NGram, RepWL, halt, Loop1, FAR, WFAR, and sporadic entries.

# Architecture of the project

The library/proofs are contained in [Busybeaver](./Busybeaver/):

- [Basic.lean](./Busybeaver/Basic.lean) contains the base definition of Turing machines
- [Problem.lean](./Busybeaver/Problem.lean) contains the definition of the busy beaver problem
- [TM](./Busybeaver/TM/) holds the machine abstractions: `Model/` is the
  opaque higher-level machine interface and `Table/` is the base tabular
  machine. Both provide a `Reachability.lean` and a `ClosedSet.lean`; the
  latter defines a tool to prove non-halting based on [Closed
  Sets](https://wiki.bbchallenge.org/wiki/Closed_Set) and exposes the very
  convenient `closed_set` tactic
  ([TM/Table/ClosedSet.lean](./Busybeaver/TM/Table/ClosedSet.lean)).
- [Enumerate](./Busybeaver/Enumerate/) contains everything related to
  justify the machine enumeration algorithm, and especially
  [Alg.lean](./Busybeaver/Enumerate/Alg.lean) contains a
  [TNF](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form)
  enumeration algorithm along with formal proofs.
- [Deciders](./Busybeaver/Deciders/) contains the code of deciders,
  designed as proof-carrying functions. These include cyclers, translated
  cyclers, backwards reasoning, bounded exploration, NGram CPS (with
  History/LRU variants), RepWL, FAR/WFAR, Loop1, and the generated BB5
  table.

# Acknowledgment

I am heavily inspired by the following Coq formalisation of the problem: [busycoq](https://github.com/meithecatte/busycoq).

# Contributing

Development happens on [GitHub](https://github.com/mfornet/busybeaver).
Fork the repository, branch off `main`, and open a pull request with your
changes. CI runs `lake build` on every push and pull request.
