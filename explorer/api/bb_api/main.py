"""FastAPI app: public, read-only, snappy.

Every endpoint is a point lookup or a keyset range scan over indexed columns, and sets a
long Cache-Control so a CDN/browser can serve repeat reads without touching Postgres.
"""

from __future__ import annotations

from contextlib import asynccontextmanager
from typing import Optional

from fastapi import Depends, FastAPI, HTTPException, Query, Response
from fastapi.middleware.cors import CORSMiddleware
from fastapi.middleware.gzip import GZipMiddleware

from . import db
from .models import VERDICTS, Machine, MachinePage, SizeDetail, Summary
from .settings import settings


@asynccontextmanager
async def lifespan(app: FastAPI):
    if not settings.dsn:
        raise RuntimeError("BB_DSN is not set")
    app.state.pool = await db.create_pool(
        settings.dsn, mn=settings.pool_min, mx=settings.pool_max
    )
    try:
        yield
    finally:
        await app.state.pool.close()


app = FastAPI(title="Busy Beaver Explorer API", version="0.0.0", lifespan=lifespan)
app.add_middleware(GZipMiddleware, minimum_size=512)
app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.cors_origins,
    allow_methods=["GET"],
    allow_headers=["*"],
)


def _cache(resp: Response) -> None:
    resp.headers["Cache-Control"] = (
        f"public, max-age={settings.cache_seconds}, "
        f"stale-while-revalidate={settings.cache_seconds * 12}"
    )


def get_pool():
    return app.state.pool


@app.get("/api/health")
async def health(pool=Depends(get_pool)) -> dict[str, str]:
    async with pool.acquire() as con:
        await con.execute("SELECT 1")
    return {"status": "ok"}


@app.get("/api/summary", response_model=Summary)
async def summary(resp: Response, pool=Depends(get_pool)) -> Summary:
    _cache(resp)
    return Summary(**await db.fetch_summary(pool))


@app.get("/api/sizes/{states}/{symbols}/summary", response_model=SizeDetail)
async def size_detail(
    states: int, symbols: int, resp: Response, pool=Depends(get_pool)
) -> SizeDetail:
    _cache(resp)
    detail = await db.fetch_size_detail(pool, states, symbols)
    if detail is None:
        raise HTTPException(404, f"no data for BB({states},{symbols})")
    return SizeDetail(**detail)


@app.get("/api/machines", response_model=MachinePage)
async def list_machines(
    resp: Response,
    states: int = Query(..., ge=1),
    symbols: int = Query(..., ge=1),
    verdict: Optional[str] = Query(None, pattern=f"^({'|'.join(VERDICTS)})$"),
    decider_kind: Optional[str] = Query(None, max_length=64),
    after_ordinal: int = Query(-1, ge=-1),
    limit: int = Query(100, ge=1),
    pool=Depends(get_pool),
) -> MachinePage:
    _cache(resp)
    limit = min(limit, settings.max_page)
    machines, cursor = await db.fetch_machines(
        pool, states=states, symbols=symbols, verdict=verdict,
        decider_kind=decider_kind, after_ordinal=after_ordinal, limit=limit,
    )
    return MachinePage(machines=[Machine(**m) for m in machines], next_cursor=cursor)


@app.get("/api/machines/{code}", response_model=Machine)
async def machine(code: str, resp: Response, pool=Depends(get_pool)) -> Machine:
    _cache(resp)
    row = await db.fetch_machine(pool, code)
    if row is None:
        raise HTTPException(404, f"machine {code} not found")
    return Machine(**row)
