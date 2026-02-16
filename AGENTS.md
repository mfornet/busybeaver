# AGENTS.md

## Goal
- Prove busy beaver results in Lean 4 with proof-carrying deciders and verified enumeration.

## Start-Of-Session Checklist
1. Run `lake build`.
1. Scan debt: `rg -n "\bsorry\b" Busybeaver`.
1. If reducing debt: fix easy/local obligations first, then harder global proofs.

## Core Commands
- `lake build`
- `lake exe beaver -h`
- `lake script run gitconfig`

## High-Value File Map
- `Busybeaver/Basic.lean`: core TM definitions and indexing lemmas.
- `Busybeaver/Reachability.lean`: multistep/reachability lemmas.
- `Busybeaver/ClosedSet.lean`: non-halting framework (`closed_set` tactic).
- `Busybeaver/Deciders/*.lean`: proof-carrying deciders.
- `Busybeaver/Enumerate/Alg.lean`, `Busybeaver/Enumerate/Impl.lean`: enumeration algorithm and implementation equivalence.

## Proof Triage Rules
- Easy: `Fin` bounds, `simp`/`rw` cleanup, fold/map congruences, linter-only simplifications.
- Hard: semantic bridge lemmas across different step systems, long state-evolution inductions with new invariants.
- If user says skip nontrivial proofs, leave hard lemmas untouched and continue elsewhere.

## Working Style
1. Solve one lemma cluster at a time.
1. Rebuild after each nontrivial edit.
1. Prefer stable local `have` lemmas over brittle `conv` patterns.
1. Do not change theorem/API shape unless required.

## Lean Conventions
- Follow Mathlib style: https://leanprover-community.github.io/contribute/style.html
- 2-space indentation.
- Prefer `fun a ↦ b`.
- Use `@[simp]` only for stable simplifying lemmas.

## Warning Policy
- Fix easy warnings (`simpa`→`simp`, unused simp args) if behavior is unchanged.
- Do not perform large refactors only to silence linters unless asked.

## Commits
- Conventional commits: `feat:`, `fix:`, `perf:`, `refactor:`, `chore:`.
