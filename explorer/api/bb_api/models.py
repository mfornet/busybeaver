"""Pydantic response models."""

from __future__ import annotations

from typing import Any, Optional

from pydantic import BaseModel

# Canonical verdict vocabulary. Mirrors the `verdict` ENUM in db/schema.sql (the cross-language
# source of truth), the ingest parser's VERDICTS, and the TS client's VERDICTS.
VERDICTS = ("halt", "nonhalt", "undecided")


class Machine(BaseModel):
    code: str
    states: int
    symbols: int
    ordinal: int
    verdict: str
    steps: Optional[int] = None
    decider: Optional[Any] = None  # Lean DeciderConfig JSON (string or object)
    decider_kind: Optional[str] = None


class MachinePage(BaseModel):
    machines: list[Machine]
    # Keyset cursor: pass back as `after_ordinal` to fetch the next page. None at end.
    next_cursor: Optional[int] = None


class SizeSummary(BaseModel):
    states: int
    symbols: int
    total: int
    n_halt: int
    n_nonhalt: int
    n_undecided: int
    max_steps: Optional[int] = None
    decided_fully: bool


class DeciderCount(BaseModel):
    states: int
    symbols: int
    decider_kind: str
    n: int


class Summary(BaseModel):
    sizes: list[SizeSummary]
    deciders: list[DeciderCount]


class SizeDetail(BaseModel):
    summary: SizeSummary
    deciders: list[DeciderCount]
