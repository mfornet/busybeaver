# Project Docs

This folder stores all valuable project information: plans, progress notes,
session logs, architectural decisions, and reference material.

## Index

| File | Description |
|------|-------------|
| [bb5-proof-overview.md](./bb5-proof-overview.md) | How BB(5) = 47,176,870 was proved: enumeration strategy, deciders, sporadic machines, and pointers to the PDF and Coq submodule |

## How to Use and Maintain Docs

- **Add a new doc** when you learn something non-obvious about the project,
  make a significant architectural decision, or complete a work session with
  notable progress.
- **Keep docs focused**: one topic per file, named clearly.
- **Link from here**: add every new file to the index table above.
- **Session logs**: name them `sessions/YYYY-MM-DD-<topic>.md`. Capture what
  was attempted, what succeeded, what was left as debt.
- **Architectural decisions**: name them `adr/NNN-<title>.md` (ADR format).
  Record the context, the decision, and the consequences.
- **Do not let docs go stale**: if you change architecture or learn that
  something documented is wrong, update the doc in the same commit.
