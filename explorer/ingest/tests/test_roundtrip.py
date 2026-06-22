"""End-to-end ingestion test against a throwaway Postgres cluster.

Spins up a temporary PG instance, applies the schema, loads a synthetic export stream,
and asserts the rows + refreshed summaries are correct. Run via `python -m tests.test_roundtrip`
from explorer/ingest with psycopg installed (see run_tests.sh).
"""

from __future__ import annotations

import io
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import psycopg

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from bb_ingest.ingest import load_rows, pipeline_hash  # noqa: E402
from bb_ingest.parse import parse_stream  # noqa: E402

SCHEMA = Path(__file__).resolve().parents[2] / "db" / "schema.sql"

# Synthetic export: 2 halts (one champion, one fast), 1 non-halter, 1 holdout.
SAMPLE = "\n".join([
    "1RB1LB_1LA---\thalt\t6\t{\"explore\":130}",
    "0RB---_1LA---\thalt\t3\t{\"explore\":130}",
    "1RB0RB_1LB1LA\tnonhalt\t\t{\"cycler\":300}",
    "1RB1RB_1LB1LA\tundecided\t\t",
]) + "\n"


def main() -> int:
    tmp = Path(tempfile.mkdtemp(prefix="bbpgtest."))
    pgdata = tmp / "data"
    sock = tmp / "sock"
    sock.mkdir(parents=True)
    subprocess.run(["initdb", "-D", str(pgdata), "-U", "postgres", "--auth=trust"],
                   check=True, capture_output=True)
    subprocess.run(
        ["pg_ctl", "-D", str(pgdata), "-o", f"-k {sock} -p 5455 -c listen_addresses=''",
         "-l", str(tmp / "log"), "start"], check=True, capture_output=True)
    try:
        time.sleep(2)
        dsn = f"host={sock} port=5455 user=postgres dbname=postgres"
        with psycopg.connect(dsn) as conn:
            conn.execute(SCHEMA.read_text())
            conn.commit()
            rows = list(parse_stream(io.StringIO(SAMPLE)))
            n = load_rows(conn, rows, states=2, symbols=2,
                          phash=pipeline_hash("abc123", None), config=None, commit="abc123")
            assert n == 4, n

            counts = dict(conn.execute(
                "SELECT verdict, count(*) FROM machines GROUP BY verdict").fetchall())
            assert counts == {"halt": 2, "nonhalt": 1, "undecided": 1}, counts

            summary = conn.execute(
                "SELECT total, n_halt, n_nonhalt, n_undecided, max_steps, decided_fully "
                "FROM size_summary WHERE states=2 AND symbols=2").fetchone()
            assert summary == (4, 2, 1, 1, 6, False), summary

            kinds = dict(conn.execute(
                "SELECT decider_kind, n FROM decider_summary ORDER BY decider_kind").fetchall())
            assert kinds == {"cycler": 1, "explore": 2}, kinds

            # Holdout must have NULL decider/steps; constraints enforce this on load.
            hold = conn.execute(
                "SELECT steps, decider FROM machines WHERE verdict='undecided'").fetchone()
            assert hold == (None, None), hold

            # Idempotent reload (replace=True) keeps counts stable.
            n2 = load_rows(conn, list(parse_stream(io.StringIO(SAMPLE))), 2, 2,
                           pipeline_hash("abc123", None), None, "abc123")
            assert n2 == 4
            total = conn.execute("SELECT count(*) FROM machines").fetchone()[0]
            assert total == 4, total
        print("INGEST ROUNDTRIP OK")
        return 0
    finally:
        subprocess.run(["pg_ctl", "-D", str(pgdata), "stop"], capture_output=True)
        subprocess.run(["rm", "-rf", str(tmp)])


if __name__ == "__main__":
    raise SystemExit(main())
