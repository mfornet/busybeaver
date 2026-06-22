# Busy Beaver Explorer

A public machine explorer for the [Lean Busy Beaver](https://github.com/mfornet/busybeaver)
formalization: browse every TNF-enumerated machine, see what the formal deciders settled and
what remains a holdout, paste any machine to rewrite it to Tree Normal Form, watch its
behavior, and copy the exact command that decides it in the Lean project.

See [DESIGN.md](./DESIGN.md) for the architecture and the decisions behind it.

## Layout

| Path             | What it is                                                                    |
| ---------------- | ----------------------------------------------------------------------------- |
| `packages/core`  | `@bb/core` — TypeScript: parse, serialize, simulate, TNF-canonicalize a TM    |
| `web`            | Vite + React static site (GitHub Pages)                                        |
| `api`            | FastAPI + asyncpg, public **read-only** API over Postgres                      |
| `ingest`         | Python admin CLI: `lake exe beaver enumerate` → `COPY` into Postgres           |
| `db/schema.sql`  | Postgres schema (machines + summaries + `refresh_summaries()`)                 |

## Quick start (local)

```bash
# 1. Core + web
cd explorer
pnpm install
pnpm --filter @bb/core test          # unit + TNF conformance
pnpm --filter web dev                 # http://localhost:5173 (set VITE_API_BASE)

# 2. Database
createdb bb && psql bb -f db/schema.sql

# 3. Ingest (needs the Lean repo built: `lake build`)
cd ingest && uv venv && uv pip install -e .
BB_DSN=postgresql:///bb bb-ingest ingest --repo /path/to/busybeaver --sizes 2x2,3x2

# 4. API
cd ../api && uv venv && uv pip install -e .
BB_DSN=postgresql:///bb uvicorn bb_api.main:app --reload
```

## The Lean side

Ingestion drives one new subcommand added to the Lean CLI:

```bash
lake exe beaver enumerate <states> <symbols> <out.tsv> [--config cfg.json]
```

It streams every enumerated TNF machine as `code⟨tab⟩verdict⟨tab⟩steps⟨tab⟩deciderJSON`,
in DFS order (the stable enumeration ordinal). The explorer database is exactly this stream,
loaded into Postgres.

## Conformance

The TypeScript canonicalizer must produce byte-identical TNF codes to the Lean enumerator,
because that code is the database lookup key. `packages/core/test/fixtures/tnf-codes.txt`
holds real `beaver enumerate` codes; `conformance.test.ts` asserts each is a fixed point of
`canonicalize`. Regenerate the fixture from a fresh export with:

```bash
bb-ingest gen-conformance --file export_4_2.tsv \
  --out packages/core/test/fixtures/tnf-codes.txt --sample 5000 --stride 100
```
