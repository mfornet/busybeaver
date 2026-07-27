# A Lean proof of BB(5)

[![CI](https://github.com/mfornet/busybeaver/actions/workflows/ci.yml/badge.svg)](https://github.com/mfornet/busybeaver/actions/workflows/ci.yml)

This repository contains a Lean 4 formalization of the five-state, two-symbol
Busy Beaver result:

> **BB(5) = 47,176,870**

Here `BB(5)` is the maximum number of transitions made before halting by a
halting five-state, two-symbol Turing machine started on a blank tape. The Lean
library internally counts steps to the pre-halt configuration, so its
corresponding theorem is `Busybeaver 4 1 = 47,176,869`; the theorem
`BBTheorems.bb5_literature` states the standard value above.

The proof combines a verified tree-normal-form enumeration with proof-carrying
halting and non-halting deciders. It ports the deciders, hardcoded table, and
sporadic-machine arguments from
[Coq-BB5](https://github.com/ccz181078/Coq-BB5), while retaining general
Turing-machine and enumeration infrastructure for other state and symbol
counts.

## Reproduce and verify

Install [elan](https://github.com/leanprover/elan), clone this repository, and
run commands from its root. The pinned toolchain is in
[`lean-toolchain`](./lean-toolchain); Lake fetches the exact dependencies
recorded in [`lake-manifest.json`](./lake-manifest.json).

Choose the check appropriate to your time and trust requirements:

| Check | Command | What it establishes |
| --- | --- | --- |
| Fast CI scope | `lake build Busybeaver.CLI Busybeaver.Enumerate.Impl` | Elaborates the reusable verified implementation, without selecting the expensive Skelet #1 proof backend. |
| Native Skelet #1 | `lake build Skelet1Fast` | Checks the complete Skelet #1 argument using Lean's compiled evaluator. A cold build took about 30 minutes on the development machine. |
| Kernel-only Skelet #1 | `scripts/verify_skelet1.sh "$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu)"` | Generates a deterministic, resumable certificate and checks it with the Lean kernel. This is intentionally very expensive. |
| Concrete BB(5) value theorem | `lake build BBTheorems.BB5` | Runs the complete enumeration and decider pipeline and proves the value theorem. Expect hours; this uses `native_decide`. |

Ordinary GitHub Actions run the fast scope. The separate
[`skelet1-native.yml`](./.github/workflows/skelet1-native.yml) workflow runs the
native Skelet #1 check nightly and on demand. See
[Verification and trust](#verification-and-trust) below before interpreting
these checks.

## Using the executable

The default `beaver` executable selects the native Skelet #1 backend. Its first
build may therefore take roughly as long as `Skelet1Fast`.

```bash
lake exe beaver --help
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

### Codex + Lean MCP

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

### Codex local environment

Codex worktrees run in separate directories and get their own local `.lake` state by default. For this Lean project, the expensive part is the dependency checkout and build cache under `.lake/packages`, especially mathlib.

This repo includes a Codex local environment at
[`.codex/environments/environment.toml`](./.codex/environments/environment.toml).
Its setup step delegates to [ci/codex_lean_setup.sh](./ci/codex_lean_setup.sh),
which reuses or migrates `.lake/packages` from a shared cache root and then runs
`lake build` in the current worktree.

Recommended shared cache location:

```bash
CODEX_LEAN_CACHE_ROOT=$HOME/.codex/cache/busybeaver-lean
```

What this gives you:

1. New worktrees reuse the same dependency checkout and build cache.
2. Only the repo-local code in the current worktree needs to rebuild.
3. You can reset the cache later by deleting the shared cache root.

### Configuration file

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

## Verification and trust

The concrete values `BB(2,2)` … `BB(5,2)` are stated as Lean theorems in the
[BBTheorems](./BBTheorems/) library (for example,
`BBTheorems.bb4 : Busybeaver 3 1 = 106`,
with a `_literature` companion in the convention that counts the halting
transition, `Busybeaver 3 1 + 1 = 107`). Each theorem instantiates
`Busybeaver.BBCompute.correct_complete` with the CLI's decider pipeline and
discharges the "no undecided machines" hypothesis by `native_decide`.

Because `BBCompute` uses well-founded recursion, the kernel cannot evaluate it,
so these theorems necessarily trust the compiled evaluator (`native_decide`).
They are therefore **not part of the default build** — `lake build` skips them.
Build them explicitly:

```bash
lake build BBTheorems        # everything (BB5 evaluates the full pipeline: hours)
lake build BBTheorems.BB4    # a single value (minutes)
```

The root module prints `#print axioms` for each theorem on build. In addition to
Lean's standard logical axioms (`propext`, `Classical.choice`, and
`Quot.sound`), the value theorems use the axiom introduced by `native_decide`.
The BB(5) theorem also includes the native-evaluation axioms selected by the
hardcoded table's expensive certificates. No source proof is replaced by
`sorry`.

### Skelet #1 verification backends

The BB5 table, decider pipeline, and CLI share one implementation and accept a
small proof-backend value for the expensive Skelet #1 non-halting theorem.
Choose the backend through an explicit Lake target:

```bash
lake build Skelet1Fast       # compiled native evaluation
lake build beaver            # CLI using the native backend
scripts/verify_skelet1.sh 12 # generate and check the kernel-only certificate
lake build beaverKernel      # kernel CLI, after the certificate is generated
```

`Skelet1Fast` is suitable for routine verification and is run nightly (and on
demand) by GitHub Actions. Its proof trusts Lean's native evaluator through the
axiom introduced by `native_decide`, but contains no `sorry`. On the development
machine used for this proof, a cold check took about 30 minutes; a cached build
including the CLI link took under 4 seconds.

`Skelet1Kernel` uses no native-evaluation axiom: it checks the generated,
resumable checkpoint certificate using only Lean's kernel. A fresh run is
intentionally very expensive; use `scripts/verify_skelet1.sh N` to verify it
with `N` parallel workers and preserve completed checkpoints. The generated
certificate sources are intentionally ignored by Git: only the compact,
deterministic generator is committed. Once generated and cached,
`lake build Skelet1Kernel` and `lake build beaverKernel` reuse the checked
modules.

## Architecture

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

## Acknowledgments

Much of the BB5 formalisation builds on [Coq-BB5](https://github.com/ccz181078/Coq-BB5),
the Coq proof that `BB(5) = 47,176,870`, from which the deciders, the hardcoded
machine table, and the sporadic-machine arguments are ported.

## Citation

This work is described in the paper [*Determination of the fifth Busy Beaver
value*](https://arxiv.org/abs/2509.12337) (arXiv:2509.12337):

```bibtex
@misc{busybeaver5,
  title         = {Determination of the fifth Busy Beaver value},
  author        = {{The bbchallenge Collaboration} and Blanchard, Justin and Briggs, Daniel and Deka, Konrad and Fenner, Nathan and Forster, Yannick and Georgiev, Georgi and House, Matthew L. and Hunter, Rachel and Iijil and K{\k{a}}dzio{\l}ka, Maja and Kropitz, Pavel and Ligocki, Shawn and mxdys and Na{\'s}ciszewski, Mateusz and savask and St{\'e}rin, Tristan and Xu, Chris and Yuen, Jason and Zimmermann, Th{\'e}o},
  year          = {2025},
  eprint        = {2509.12337},
  archivePrefix = {arXiv},
  primaryClass  = {cs.LO},
  url           = {https://arxiv.org/abs/2509.12337}
}
```
