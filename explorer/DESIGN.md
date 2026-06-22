# Busy Beaver Explorer — Design

A public website + API that shows the state of the Lean Busy Beaver formalization as a
machine explorer: every TNF-enumerated machine, what was decided, and what remains in the
holdout set. You can paste an arbitrary machine, see it rewritten to canonical Tree Normal
Form, explore its behavior, and see the exact command that decides it in the Lean project.

## Decisions (from the design interview)

- **Full materialization, whole ladder BB(2,2)→BB(5,2).** One row per enumerated machine
  (~10⁸ at 5 states). Every read path is a point lookup (by code) or a **keyset** range scan
  (by enumeration ordinal) — never `OFFSET`. Aggregates live in summary tables.
- **The DB is a downstream projection of the Lean enumerator.** Data flows one way:
  `Lean (enumerator + deciders) → admin CLI → Postgres → public API → website`. The DB is
  authoritative *for the explorer only*; the Lean verifier never reads it, and the DB can be
  rebuilt from the Lean binary at any commit.
- **Each decided machine stores its exact deciding `(decider, config)`** so the site can show a
  reproducible `lake exe beaver decide <code> --config <one-decider.json>` command, plus a
  `pipeline_hash` for drift detection.
- **Ingestion bypasses HTTP** — the admin CLI connects straight to Postgres and `COPY`-loads.
  There is a single **public read-only** API; securing writes = securing the DB credentials.
- **Interactive computations run client-side in TypeScript** (`@bb/core`): parsing, simulation,
  and TNF canonicalization. This is the only way the explorer feels instant. The canonicalizer
  is pinned to Lean's output by a **conformance test** over real `beaver enumerate` codes.

## Components

```
explorer/
  packages/core/   @bb/core — TS: parse, serialize, simulate, TNF-canonicalize, decider commands
  web/             Vite + React static site (GitHub Pages); imports @bb/core
  api/             FastAPI + asyncpg, read-only, keyset-paginated, cache headers
  ingest/          Python CLI: runs `lake exe beaver enumerate`, COPY-loads Postgres
  db/schema.sql    machines + summary tables, indexes, refresh_summaries()
```

The Lean CLI gains one subcommand, `enumerate`, which streams every TNF leaf as
`code⟨tab⟩verdict⟨tab⟩steps⟨tab⟩deciderJSON` in DFS order (the stable ordinal).

## TNF canonicalization (the correctness-critical piece)

The enumerator (`Busybeaver/Enumerate/`) fills the first halting transition reached during
simulation, introducing new states/symbols in **min-unused order**. A machine is in TNF when:

1. its first executed transition (state A reading blank) moves **right** — seeds are
   `0RB…`/`1RB…`, and left/right is reduced by reflection;
2. states are numbered in order of first being **targeted** during the run;
3. non-blank symbols are numbered in order of first being **written**;
4. transitions on cells never reached from the start are `halt` (`---`).

`@bb/core`'s `canonicalize` reproduces this (optional reflection + a single simulation that
assigns labels in introduction order; unreached cells become halt). The produced code is the
database key, so an arbitrary pasted machine resolves to its stored verdict. Because the
canonical TNF code *is* the lookup key, the TS port must match Lean byte-for-byte — enforced
by `packages/core/test/conformance.test.ts` over a committed fixture of real Lean codes
(regenerated in CI / by ingestion from `beaver enumerate`).

## Snappiness budget

- Landing page: served from `size_summary` (also exportable to a static `summary.json`).
- Browse: keyset pagination on `(states, symbols, ordinal)`; `Cache-Control` allows CDN reuse.
- Machine page: simulation, canonicalization, and the space-time diagram are all client-side;
  only the verdict lookup hits the API.

## Operating it

1. `psql < db/schema.sql`
2. `bb-ingest ingest --dsn $BB_DSN --repo /path/to/busybeaver --sizes 2x2,3x2,4x2,5x2`
3. Run the API: `BB_DSN=… uvicorn bb_api.main:app` (behind a reverse proxy / CDN).
4. The web deploys to GitHub Pages on push to `main` (`.github/workflows/explorer.yml`),
   built with `VITE_API_BASE` pointing at the API and `VITE_BASE` at the Pages path.
