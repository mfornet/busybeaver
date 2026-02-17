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

## Blueprint workflow

This repository now includes a Lean blueprint scaffold under
[`blueprint/src`](./blueprint/src).

Install `leanblueprint`:

```bash
python3 -m pip install --user leanblueprint
```

Then build the blueprint website:

```bash
leanblueprint checkdecls
leanblueprint web
```

The generated site is written to `blueprint/web`.
To build the PDF, run:

```bash
leanblueprint pdf
```

For a single command that runs the local project checks plus website build:

```bash
ci/blueprint.sh
```

To publish from GitHub Actions, enable Pages once in repository settings:
`Settings -> Pages -> Build and deployment -> Source: GitHub Actions`.

## Configuration file

The binary admits a configuration file for the deciders, in JSON, the
configuration is an array of decider parameters, which can be
repeated.

There are two deciders currently:
- Translated cyclers: `{ "translatedCycler": <number> }`
- Cyclers: `{ "cycler": <number> }`

An example configuration file (which is equivalent to the default
configuration):
```json
[
  { "translatedCycler" :  200 },
  { "cycler" : 100 }
]
```

# Architecture of the project

The library/proofs are contained in [Busybeaver](./Busybeaver/):

- [Basic.lean](./Busybeaver/Basic.lean) contains the base definition of Turing machines
- [Reachability.lean](./Busybeaver/Reachability.lean) contains many definitions related to reachability in TMs
- [Problem.lean](./Busybeaver/Problem.lean) contains the definition of the busy beaver problem
- [ClosedSet.lean](./Busybeaver/ClosedSet.lean) defines a tool to prove non-halting based on [Closed Sets](https://wiki.bbchallenge.org/wiki/Closed_Set). It also provides the very convenient `closed_set` tactic, to call within the proofs.
- [Partial.lean](./Busybeaver/Partial.lean) defines TMs steps on finite tapes.
- [Enumerate](./Busybeaver/Enumerate/) contains everything related to
  justify the machine enumeration algorithm, and especially
  [Alg.lean](./Busybeaver/Enumerate/Alg.lean) contains a
  [TNF](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form)
  enumeration algorithm along with formal proofs.
- [Deciders](./Busybeaver/Deciders/) contains the code of deciders.
  They are designed as proof-carrying functions. Currently we have:
  [cyclers](./Busybeaver/Deciders/Cyclers.lean) and [translated
  cyclers](./Busybeaver/Deciders/TranslatedCyclers.lean).
- [blueprint/src](./blueprint/src) contains the Lean blueprint content
  and LaTeX entrypoints used by `leanblueprint`.

# TODOs

You can find the ongoing tasks and goals [here](https://todo.sr.ht/~vigoux/busybeaver).

# Acknowledgment

I am heavily inspired by the following Coq formalisation of the problem: [busycoq](https://github.com/meithecatte/busycoq).

# Contibuting

This project follows the `sr.ht` workflow, we recommend to [setup git to
send emails](https://git-send-email.io). Note that it is not required
to create a `sr.ht` account to contribute, simply clone the repo and
make your changes.

To setup for this specific repo, a `lake` script is provided:

```
lake script run gitconfig
```

After running this command, and assuming that you are working off the
`master` branch, it should be sufficient to:

1. `git send-email master`
2. Annotate the patch set, the first annotation will be the cover
   letter, that describes broadly your changes
3. Wait for a review !

If you need to make changes and resubmit a patch, you can do that
using:
```bash
# Replace 2 by the version of the patchset
git send-email -v2 master
```

For additional guidelines about how to contribute and send patches, we
recommend reading [aerc's contributing guidelines](https://git.sr.ht/~rjarry/aerc/tree/master/item/CONTRIBUTING.md).
