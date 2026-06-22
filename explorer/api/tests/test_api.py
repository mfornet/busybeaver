"""API smoke test against a throwaway Postgres cluster (no external services).

Spins up temp PG, applies the schema, inserts sample machines, then drives the FastAPI app
in-process via httpx ASGITransport and checks the read endpoints + keyset pagination.
Run with `python -m tests.test_api` from explorer/api with deps installed (see run_tests.sh).
"""

from __future__ import annotations

import asyncio
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path

import asyncpg

SCHEMA = Path(__file__).resolve().parents[2] / "db" / "schema.sql"

SAMPLE = [
    # code, states, symbols, ordinal, verdict, steps, decider(json|None), kind
    ("1RB1LB_1LA---", 2, 2, 0, "halt", 6, {"explore": 130}, "explore"),
    ("0RB---_1LA---", 2, 2, 1, "halt", 3, {"explore": 130}, "explore"),
    ("1RB0RB_1LB1LA", 2, 2, 2, "nonhalt", None, {"cycler": 300}, "cycler"),
    ("1RB1RB_1LB1LA", 2, 2, 3, "undecided", None, None, None),
]


async def seed(dsn: str) -> None:
    con = await asyncpg.connect(dsn)
    try:
        await con.execute(SCHEMA.read_text())
        await con.executemany(
            "INSERT INTO machines (code, states, symbols, ordinal, verdict, steps, decider, "
            "decider_kind, pipeline_hash) VALUES ($1,$2,$3,$4,$5,$6,$7,$8,'test')",
            [
                (c, st, sy, o, v, steps, json.dumps(d) if d is not None else None, k)
                for (c, st, sy, o, v, steps, d, k) in SAMPLE
            ],
        )
        await con.execute("SELECT refresh_summaries()")
    finally:
        await con.close()


async def run_checks(dsn: str) -> None:
    os.environ["BB_DSN"] = dsn
    from httpx import ASGITransport, AsyncClient

    import bb_api.main as m

    transport = ASGITransport(app=m.app)
    async with m.lifespan(m.app):
        async with AsyncClient(transport=transport, base_url="http://t") as c:
            r = await c.get("/api/health")
            assert r.status_code == 200 and r.json()["status"] == "ok"

            r = await c.get("/api/summary")
            body = r.json()
            assert r.headers["cache-control"].startswith("public")
            size = next(s for s in body["sizes"] if s["states"] == 2 and s["symbols"] == 2)
            assert (size["total"], size["n_halt"], size["n_nonhalt"], size["n_undecided"]) == (4, 2, 1, 1)
            assert size["max_steps"] == 6 and size["decided_fully"] is False

            r = await c.get("/api/sizes/2/2/summary")
            assert {d["decider_kind"]: d["n"] for d in r.json()["deciders"]} == {
                "explore": 2, "cycler": 1
            }

            # Full list.
            r = await c.get("/api/machines", params={"states": 2, "symbols": 2})
            page = r.json()
            assert [mm["ordinal"] for mm in page["machines"]] == [0, 1, 2, 3]
            assert page["next_cursor"] is None

            # Keyset pagination: limit 2 -> cursor 1 -> next page starts at ordinal 2.
            r = await c.get("/api/machines", params={"states": 2, "symbols": 2, "limit": 2})
            page = r.json()
            assert [mm["ordinal"] for mm in page["machines"]] == [0, 1]
            assert page["next_cursor"] == 1
            r = await c.get("/api/machines",
                            params={"states": 2, "symbols": 2, "limit": 2, "after_ordinal": 1})
            assert [mm["ordinal"] for mm in r.json()["machines"]] == [2, 3]

            # Verdict filter.
            r = await c.get("/api/machines",
                            params={"states": 2, "symbols": 2, "verdict": "undecided"})
            holds = r.json()["machines"]
            assert len(holds) == 1 and holds[0]["code"] == "1RB1RB_1LB1LA"
            assert holds[0]["decider"] is None

            # Single machine: decider JSON round-trips as a structured object.
            r = await c.get("/api/machines/1RB0RB_1LB1LA")
            assert r.json()["decider"] == {"cycler": 300}

            r = await c.get("/api/machines/nope_nope")
            assert r.status_code == 404
    print("API SMOKE OK")


def main() -> int:
    tmp = Path(tempfile.mkdtemp(prefix="bbapitest."))
    pgdata, sock = tmp / "data", tmp / "sock"
    sock.mkdir(parents=True)
    subprocess.run(["initdb", "-D", str(pgdata), "-U", "postgres", "--auth=trust"],
                   check=True, capture_output=True)
    subprocess.run(
        ["pg_ctl", "-D", str(pgdata), "-o", f"-k {sock} -p 5456 -c listen_addresses=''",
         "-l", str(tmp / "log"), "start"], check=True, capture_output=True)
    try:
        time.sleep(2)
        dsn = f"postgresql://postgres@/postgres?host={sock}&port=5456"
        asyncio.run(seed(dsn))
        asyncio.run(run_checks(dsn))
        return 0
    finally:
        subprocess.run(["pg_ctl", "-D", str(pgdata), "stop"], capture_output=True)
        subprocess.run(["rm", "-rf", str(tmp)])


if __name__ == "__main__":
    raise SystemExit(main())
