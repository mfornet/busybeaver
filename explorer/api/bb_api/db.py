"""asyncpg access layer. All queries hit indexes; lists use keyset pagination (no OFFSET)."""

from __future__ import annotations

import json
from typing import Any, Optional

import asyncpg


def _machine(row: asyncpg.Record) -> dict[str, Any]:
    decider = row["decider"]
    if isinstance(decider, str):
        # asyncpg returns jsonb as text unless a codec is set; decode here.
        decider = json.loads(decider)
    return {
        "code": row["code"],
        "states": row["states"],
        "symbols": row["symbols"],
        "ordinal": row["ordinal"],
        "verdict": row["verdict"],
        "steps": row["steps"],
        "decider": decider,
        "decider_kind": row["decider_kind"],
    }


async def create_pool(dsn: str, *, mn: int, mx: int) -> asyncpg.Pool:
    return await asyncpg.create_pool(dsn, min_size=mn, max_size=mx)


async def fetch_summary(pool: asyncpg.Pool) -> dict[str, list[dict[str, Any]]]:
    async with pool.acquire() as con:
        sizes = await con.fetch(
            "SELECT states, symbols, total, n_halt, n_nonhalt, n_undecided, max_steps, "
            "decided_fully FROM size_summary ORDER BY states, symbols"
        )
        deciders = await con.fetch(
            "SELECT states, symbols, decider_kind, n FROM decider_summary "
            "ORDER BY states, symbols, n DESC"
        )
    return {
        "sizes": [dict(r) for r in sizes],
        "deciders": [dict(r) for r in deciders],
    }


async def fetch_size_detail(
    pool: asyncpg.Pool, states: int, symbols: int
) -> Optional[dict[str, Any]]:
    async with pool.acquire() as con:
        summary = await con.fetchrow(
            "SELECT states, symbols, total, n_halt, n_nonhalt, n_undecided, max_steps, "
            "decided_fully FROM size_summary WHERE states=$1 AND symbols=$2",
            states, symbols,
        )
        if summary is None:
            return None
        deciders = await con.fetch(
            "SELECT states, symbols, decider_kind, n FROM decider_summary "
            "WHERE states=$1 AND symbols=$2 ORDER BY n DESC",
            states, symbols,
        )
    return {"summary": dict(summary), "deciders": [dict(r) for r in deciders]}


async def fetch_machine(pool: asyncpg.Pool, code: str) -> Optional[dict[str, Any]]:
    async with pool.acquire() as con:
        row = await con.fetchrow(
            "SELECT code, states, symbols, ordinal, verdict, steps, decider, decider_kind "
            "FROM machines WHERE code=$1",
            code,
        )
    return _machine(row) if row else None


async def fetch_machines(
    pool: asyncpg.Pool,
    *,
    states: int,
    symbols: int,
    verdict: Optional[str],
    decider_kind: Optional[str],
    after_ordinal: int,
    limit: int,
) -> tuple[list[dict[str, Any]], Optional[int]]:
    """Keyset page within a size, ordered by ordinal. Optional verdict/decider filters.

    Returns (rows, next_cursor); next_cursor is the last ordinal or None at the end.
    """
    clauses = ["states=$1", "symbols=$2", "ordinal > $3"]
    params: list[Any] = [states, symbols, after_ordinal]
    if verdict is not None:
        params.append(verdict)
        clauses.append(f"verdict=${len(params)}")
    if decider_kind is not None:
        params.append(decider_kind)
        clauses.append(f"decider_kind=${len(params)}")
    params.append(limit + 1)  # fetch one extra to detect "more"
    sql = (
        "SELECT code, states, symbols, ordinal, verdict, steps, decider, decider_kind "
        "FROM machines WHERE " + " AND ".join(clauses) +
        f" ORDER BY ordinal LIMIT ${len(params)}"
    )
    async with pool.acquire() as con:
        rows = await con.fetch(sql, *params)
    machines = [_machine(r) for r in rows[:limit]]
    next_cursor = machines[-1]["ordinal"] if len(rows) > limit and machines else None
    return machines, next_cursor
