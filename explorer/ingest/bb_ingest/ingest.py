"""Run the Lean export and bulk-load results into Postgres."""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
from pathlib import Path
from typing import Iterable, Optional

import psycopg

from .parse import MachineRow, parse_stream

COPY_COLUMNS = (
    "code",
    "states",
    "symbols",
    "ordinal",
    "verdict",
    "steps",
    "decider",
    "decider_kind",
    "pipeline_hash",
)


def git_commit(repo: Path) -> Optional[str]:
    try:
        out = subprocess.run(
            ["git", "-C", str(repo), "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, check=True,
        )
        return out.stdout.strip()
    except Exception:
        return None


def pipeline_hash(commit: Optional[str], config: object) -> str:
    """Drift token: stable while the Lean deciders (commit) and config are unchanged."""
    payload = json.dumps({"commit": commit, "config": config}, sort_keys=True)
    return hashlib.sha256(payload.encode()).hexdigest()[:16]


def run_export(
    repo: Path, states: int, symbols: int, out_path: Path, config: Optional[Path] = None
) -> None:
    """Invoke `lake exe beaver enumerate <states> <symbols> <out>` in the Lean repo."""
    cmd = ["lake", "exe", "beaver", "enumerate", str(states), str(symbols), str(out_path)]
    if config is not None:
        cmd += ["--config", str(config)]
    subprocess.run(cmd, cwd=str(repo), check=True)


def load_rows(
    conn: psycopg.Connection,
    rows: Iterable[MachineRow],
    states: int,
    symbols: int,
    phash: str,
    config: object,
    commit: Optional[str],
    *,
    replace: bool = True,
) -> int:
    """COPY rows for one size into `machines`, then refresh summaries. Returns row count."""
    n = 0
    with conn.cursor() as cur:
        run_id = cur.execute(
            """INSERT INTO ingest_runs (states, symbols, pipeline_hash, config, git_commit)
               VALUES (%s, %s, %s, %s, %s) RETURNING id""",
            (states, symbols, phash, json.dumps(config) if config is not None else None, commit),
        ).fetchone()[0]

        if replace:
            cur.execute(
                "DELETE FROM machines WHERE states = %s AND symbols = %s", (states, symbols)
            )

        copy_sql = f"COPY machines ({', '.join(COPY_COLUMNS)}) FROM STDIN"
        with cur.copy(copy_sql) as copy:
            copy.set_types(
                ["text", "int2", "int2", "int8", "text", "int8", "jsonb", "text", "text"]
            )
            for r in rows:
                copy.write_row(
                    (
                        r.code, r.states, r.symbols, r.ordinal, r.verdict, r.steps,
                        psycopg.types.json.Jsonb(r.decider) if r.decider is not None else None,
                        r.decider_kind, phash,
                    )
                )
                n += 1

        # Scope the recompute to the size just loaded — refreshing all sizes here would
        # re-scan the whole table (dominated by BB(5,2)) on every per-size ingest.
        cur.execute("SELECT refresh_summaries(%s, %s)", (states, symbols))
        cur.execute(
            "UPDATE ingest_runs SET finished_at = now(), rows_loaded = %s WHERE id = %s",
            (n, run_id),
        )
    conn.commit()
    return n


def ingest_size(
    dsn: str,
    repo: Path,
    states: int,
    symbols: int,
    *,
    config: Optional[Path] = None,
    export_path: Optional[Path] = None,
    keep_export: bool = False,
) -> int:
    """End-to-end: export from Lean, parse, and load one size class into Postgres."""
    out = export_path or Path(tempfile.gettempdir()) / f"bb_export_{states}_{symbols}.tsv"
    run_export(repo, states, symbols, out, config)
    commit = git_commit(repo)
    config_json = json.loads(config.read_text()) if config else None
    phash = pipeline_hash(commit, config_json)
    with psycopg.connect(dsn) as conn:
        with out.open() as fh:
            n = load_rows(
                conn, parse_stream(fh), states, symbols, phash, config_json, commit
            )
    if not keep_export and export_path is None:
        out.unlink(missing_ok=True)
    return n


def load_export_file(
    dsn: str, export_path: Path, states: int, symbols: int, *, commit: Optional[str] = None
) -> int:
    """Load an already-generated export file (e.g. produced on a build machine)."""
    phash = pipeline_hash(commit, None)
    with psycopg.connect(dsn) as conn, export_path.open() as fh:
        return load_rows(conn, parse_stream(fh), states, symbols, phash, None, commit)
