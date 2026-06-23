-- Busy Beaver explorer — Postgres schema.
--
-- Design notes (see explorer/DESIGN.md):
--   * Full materialization: one row per TNF-enumerated machine across the ladder
--     BB(2,2)..BB(5,2). The 5-state size alone is ~10^8 rows, so every read path is a
--     point lookup (by code) or a keyset range scan (by enumeration ordinal) — never OFFSET.
--   * The DB is a downstream projection of the Lean enumerator (`lake exe beaver export`).
--     It is authoritative for the explorer only; the Lean verifier never reads it.
--   * Each decided machine stores the exact deciding decider as JSON so the website can show
--     a reproducible `lake exe beaver decide <code> --config <one-decider.json>` command.
--   * Aggregates live in summary tables refreshed after ingestion, so the landing page and
--     filters never scan the big table.

BEGIN;

-- Canonical verdict vocabulary. 'nonhalt' = proven not to halt by any decider (not
-- necessarily a periodic cycler). Mirrored by the API, the TS client, and Main.lean.
CREATE TYPE verdict AS ENUM ('halt', 'nonhalt', 'undecided');

-- One row per enumerated machine.
CREATE TABLE machines (
    -- Canonical TNF code, e.g. '1RB1LC_1RC1RB_...'. This is the lookup key produced by the
    -- TypeScript canonicalizer for arbitrary pasted machines.
    code            TEXT        NOT NULL,
    states          SMALLINT    NOT NULL,          -- Lean l+1
    symbols         SMALLINT    NOT NULL,          -- Lean s+1
    -- Position in the deterministic DFS enumeration for this size (stable ordinal).
    ordinal         BIGINT      NOT NULL,
    verdict         verdict     NOT NULL,
    steps           BIGINT,                        -- halting step count, NULL unless verdict='halt'
    -- Winning decider as Lean DeciderConfig JSON (NULL for holdouts):
    --   "bb5TableExecutable" | {"cycler": 300} | {"repWL": {...}} | ...
    decider         JSONB,
    -- Top-level decider kind, denormalized for cheap filtering/grouping
    -- ('cycler','repWL','nGramCPSHistory','bb5TableExecutable', ...; NULL for holdouts).
    decider_kind    TEXT,
    -- Hash of the decider pipeline version used at ingestion, for drift detection.
    pipeline_hash   TEXT        NOT NULL,
    ingested_at     TIMESTAMPTZ NOT NULL DEFAULT now(),

    PRIMARY KEY (code),
    CHECK (states >= 1 AND symbols >= 1),
    CHECK ((verdict = 'halt') = (steps IS NOT NULL)),
    CHECK ((verdict = 'undecided') = (decider IS NULL))
);

-- Keyset pagination + size browse: WHERE states=? AND symbols=? AND ordinal > ? ORDER BY ordinal.
CREATE UNIQUE INDEX machines_size_ordinal ON machines (states, symbols, ordinal);

-- Filtered browse by verdict, still keyset-paginated by ordinal.
CREATE INDEX machines_size_verdict_ordinal ON machines (states, symbols, verdict, ordinal);

-- Filtered browse by deciding technique.
CREATE INDEX machines_size_decider_ordinal
    ON machines (states, symbols, decider_kind, ordinal)
    WHERE decider_kind IS NOT NULL;

-- Fast holdout listing (small set, hot path).
CREATE INDEX machines_holdouts
    ON machines (states, symbols, ordinal)
    WHERE verdict = 'undecided';

-- Per-size rollup. Powers the landing page (also exported to static JSON) and size headers.
CREATE TABLE size_summary (
    states        SMALLINT    NOT NULL,
    symbols       SMALLINT    NOT NULL,
    total         BIGINT      NOT NULL,
    n_halt        BIGINT      NOT NULL,
    n_nonhalt     BIGINT      NOT NULL,
    n_undecided   BIGINT      NOT NULL,
    max_steps     BIGINT,                          -- BB(states,symbols) when n_undecided = 0
    decided_fully BOOLEAN     NOT NULL,            -- n_undecided = 0
    pipeline_hash TEXT,
    refreshed_at  TIMESTAMPTZ NOT NULL DEFAULT now(),
    PRIMARY KEY (states, symbols)
);

-- Per-size, per-technique counts. Powers the "how machines were decided" breakdown chart.
CREATE TABLE decider_summary (
    states       SMALLINT NOT NULL,
    symbols      SMALLINT NOT NULL,
    decider_kind TEXT     NOT NULL,
    n            BIGINT   NOT NULL,
    PRIMARY KEY (states, symbols, decider_kind)
);

-- Provenance: one row per ingestion run, for auditing and drift detection.
CREATE TABLE ingest_runs (
    id            BIGSERIAL   PRIMARY KEY,
    states        SMALLINT    NOT NULL,
    symbols       SMALLINT    NOT NULL,
    pipeline_hash TEXT        NOT NULL,
    config        JSONB,                            -- the decider pipeline used
    git_commit    TEXT,                             -- Lean repo commit the export came from
    rows_loaded   BIGINT,
    started_at    TIMESTAMPTZ NOT NULL DEFAULT now(),
    finished_at   TIMESTAMPTZ,
    note          TEXT
);

-- Recompute summary tables from `machines`. Run after each ingestion (see ingest CLI).
--
-- Scope to a single size by passing (p_states, p_symbols); ingestion loads one size at a
-- time, so this avoids re-scanning the whole table (dominated by the ~10^8 BB(5,2) rows) on
-- every per-size load. Pass NULL for both to rebuild every size (full manual refresh).
CREATE OR REPLACE FUNCTION refresh_summaries(
    p_states  SMALLINT DEFAULT NULL,
    p_symbols SMALLINT DEFAULT NULL
) RETURNS void LANGUAGE plpgsql AS $$
BEGIN
    INSERT INTO size_summary AS ss
        (states, symbols, total, n_halt, n_nonhalt, n_undecided, max_steps, decided_fully,
         pipeline_hash, refreshed_at)
    SELECT
        states, symbols,
        count(*),
        count(*) FILTER (WHERE verdict = 'halt'),
        count(*) FILTER (WHERE verdict = 'nonhalt'),
        count(*) FILTER (WHERE verdict = 'undecided'),
        max(steps),
        bool_and(verdict <> 'undecided'),
        max(pipeline_hash),
        now()
    FROM machines
    WHERE (p_states IS NULL OR states = p_states)
      AND (p_symbols IS NULL OR symbols = p_symbols)
    GROUP BY states, symbols
    ON CONFLICT (states, symbols) DO UPDATE SET
        total = EXCLUDED.total,
        n_halt = EXCLUDED.n_halt,
        n_nonhalt = EXCLUDED.n_nonhalt,
        n_undecided = EXCLUDED.n_undecided,
        max_steps = EXCLUDED.max_steps,
        decided_fully = EXCLUDED.decided_fully,
        pipeline_hash = EXCLUDED.pipeline_hash,
        refreshed_at = EXCLUDED.refreshed_at;

    DELETE FROM decider_summary
    WHERE (p_states IS NULL OR states = p_states)
      AND (p_symbols IS NULL OR symbols = p_symbols);
    INSERT INTO decider_summary (states, symbols, decider_kind, n)
    SELECT states, symbols, decider_kind, count(*)
    FROM machines
    WHERE decider_kind IS NOT NULL
      AND (p_states IS NULL OR states = p_states)
      AND (p_symbols IS NULL OR symbols = p_symbols)
    GROUP BY states, symbols, decider_kind;
END;
$$;

COMMIT;
