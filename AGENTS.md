# Repository Guidelines

This Lean 4 project aims to formally prove busy beaver values BB(n) for small n (1-5). It provides proof-carrying deciders and a TNF enumeration algorithm with correctness proofs.

## Project Structure

```
Busybeaver/           # Main library
├── Basic.lean        # Core Turing machine definitions
├── Problem.lean      # Busy beaver problem definition
├── Reachability.lean # TM reachability lemmas
├── ClosedSet.lean    # Non-halting proofs via closed sets
├── Partial.lean      # Finite tape stepping
├── Deciders/         # Proof-carrying decider implementations
│   ├── Cyclers.lean
│   └── TranslatedCyclers.lean
└── Enumerate/        # TNF enumeration with proofs
    └── Alg.lean      # Main enumeration algorithm
bin/                  # Executable entry points
Main.lean             # CLI entry point for `beaver` executable
```

## Build & Development Commands

| Command                     | Description                             |
| --------------------------- | --------------------------------------- |
| `lake build`                | Build the library and executables       |
| `lake exe beaver -h`        | Run the main CLI tool                   |
| `lake script run gitconfig` | Configure git for contribution workflow |

This project depends on Mathlib (stable branch). Lake will fetch dependencies automatically.

## Coding Style

- Follow standard [Mathlib conventions](https://leanprover-community.github.io/contribute/style.html)
- Use 2-space indentation
- Prefer `fun a ↦ b` syntax (configured in lakefile)
- Name theorems descriptively: `lemma Finset.mem_fold_union`
- Use `@[simp]` for simplification lemmas

## Commit Conventions

Use [Conventional Commits](https://www.conventionalcommits.org/) with these prefixes:

- `feat:` — New features or proofs
- `fix:` — Bug fixes
- `perf:` — Performance improvements
- `refactor:` — Code restructuring
- `chore:` — Maintenance tasks

Optional scope in parentheses: `feat(ui): add horizontal movement`

## Architecture Notes

Deciders are designed as **proof-carrying functions**: they return both a decision and a correctness proof. When adding new deciders, follow the pattern in `Busybeaver/Deciders/`.

For non-halting proofs, use the `closed_set` tactic from `ClosedSet.lean`.
