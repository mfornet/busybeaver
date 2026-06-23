"""Parse the `lake exe beaver enumerate` stream into machine rows."""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Iterator, Optional

# Canonical verdict vocabulary. Mirrors the `verdict` ENUM in db/schema.sql (the cross-language
# source of truth), the API's query validator, and the TS client's VERDICTS.
VERDICTS = ("halt", "nonhalt", "undecided")


@dataclass(frozen=True)
class MachineRow:
    code: str
    states: int
    symbols: int
    ordinal: int
    verdict: str  # one of VERDICTS
    steps: Optional[int]
    decider: Optional[dict | str]  # parsed DeciderConfig JSON, or None for holdouts
    decider_kind: Optional[str]


def decider_kind(decider: object) -> Optional[str]:
    """Top-level kind of a Lean DeciderConfig JSON value.

    A decider is either a bare string ("bb5TableExecutable") or a single-key object
    ({"repWL": {...}}, {"cycler": 300}, ...). Returns None for an absent decider.
    """
    if decider is None:
        return None
    if isinstance(decider, str):
        return decider
    if isinstance(decider, dict) and len(decider) == 1:
        return next(iter(decider))
    raise ValueError(f"unrecognized decider JSON: {decider!r}")


def shape_from_code(code: str) -> tuple[int, int]:
    """Infer (states, symbols) from a machine code, e.g. '1RB1LB_1LA---' -> (2, 2)."""
    groups = code.split("_")
    states = len(groups)
    symbols = len(groups[0]) // 3
    return states, symbols


def parse_stream(lines: Iterator[str]) -> Iterator[MachineRow]:
    """Yield one MachineRow per non-empty export line. Ordinal = 0-based line index."""
    ordinal = 0
    for raw in lines:
        line = raw.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 4:
            raise ValueError(f"malformed export line (want 4 tab fields): {line!r}")
        code, verdict, steps_s, decider_s = parts
        if verdict not in VERDICTS:
            raise ValueError(f"unknown verdict {verdict!r} on line: {line!r}")
        states, symbols = shape_from_code(code)
        steps = int(steps_s) if steps_s else None
        decider = json.loads(decider_s) if decider_s else None
        yield MachineRow(
            code=code,
            states=states,
            symbols=symbols,
            ordinal=ordinal,
            verdict=verdict,
            steps=steps,
            decider=decider,
            decider_kind=decider_kind(decider),
        )
        ordinal += 1
