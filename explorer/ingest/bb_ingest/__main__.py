"""bb-ingest CLI.

Examples:
  # Enumerate BB(2,2)..BB(5,2) from the Lean repo and load into Postgres.
  bb-ingest ingest --dsn "$BB_DSN" --repo /path/to/busybeaver --sizes 2x2,3x2,4x2,5x2

  # Load a pre-generated export file.
  bb-ingest load --dsn "$BB_DSN" --states 2 --symbols 2 --file export_2_2.tsv

  # Write a TNF-conformance fixture for the TS core test from an export file.
  bb-ingest gen-conformance --file export_4_2.tsv --out ../packages/core/test/fixtures/tnf-codes.txt --sample 2000
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

from .ingest import ingest_size, load_export_file


def _parse_sizes(spec: str) -> list[tuple[int, int]]:
    out = []
    for tok in spec.split(","):
        tok = tok.strip()
        if not tok:
            continue
        a, b = tok.lower().split("x")
        out.append((int(a), int(b)))
    return out


def _default_dsn(arg: str | None) -> str:
    dsn = arg or os.environ.get("BB_DSN")
    if not dsn:
        sys.exit("error: provide --dsn or set BB_DSN (e.g. postgresql://user:pw@host/bb)")
    return dsn


def cmd_ingest(args: argparse.Namespace) -> int:
    dsn = _default_dsn(args.dsn)
    repo = Path(args.repo).resolve()
    config = Path(args.config).resolve() if args.config else None
    for states, symbols in _parse_sizes(args.sizes):
        print(f"[ingest] BB({states},{symbols}) — exporting + loading...", flush=True)
        n = ingest_size(
            dsn, repo, states, symbols, config=config,
            export_path=Path(args.export_dir) / f"export_{states}_{symbols}.tsv"
            if args.export_dir else None,
            keep_export=args.keep_export,
        )
        print(f"[ingest] BB({states},{symbols}) — loaded {n:,} machines", flush=True)
    return 0


def cmd_load(args: argparse.Namespace) -> int:
    dsn = _default_dsn(args.dsn)
    n = load_export_file(
        dsn, Path(args.file), args.states, args.symbols, commit=args.commit
    )
    print(f"[load] loaded {n:,} machines for BB({args.states},{args.symbols})")
    return 0


def cmd_gen_conformance(args: argparse.Namespace) -> int:
    from .parse import parse_stream

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    codes: list[str] = []
    with Path(args.file).open() as fh:
        for i, row in enumerate(parse_stream(fh)):
            # Stride applies on its own; --sample (when > 0) caps the total kept.
            if i % max(1, args.stride) != 0:
                continue
            codes.append(row.code)
            if args.sample and len(codes) >= args.sample:
                break
    header = "# TNF codes generated from `lake exe beaver enumerate` — TS conformance fixture\n"
    out.write_text(header + "\n".join(codes) + "\n")
    print(f"[gen-conformance] wrote {len(codes):,} codes to {out}")
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="bb-ingest", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    pi = sub.add_parser("ingest", help="export from Lean + load into Postgres")
    pi.add_argument("--dsn")
    pi.add_argument("--repo", required=True, help="path to the busybeaver Lean repo")
    pi.add_argument("--sizes", default="2x2,3x2,4x2,5x2", help="comma list like 2x2,5x2")
    pi.add_argument("--config", help="decider config JSON (default: size-aware Lean default)")
    pi.add_argument("--export-dir", help="keep export TSVs in this directory")
    pi.add_argument("--keep-export", action="store_true")
    pi.set_defaults(func=cmd_ingest)

    pl = sub.add_parser("load", help="load a pre-generated export file")
    pl.add_argument("--dsn")
    pl.add_argument("--file", required=True)
    pl.add_argument("--states", type=int, required=True)
    pl.add_argument("--symbols", type=int, required=True)
    pl.add_argument("--commit")
    pl.set_defaults(func=cmd_load)

    pg = sub.add_parser("gen-conformance", help="write TS conformance fixture from an export file")
    pg.add_argument("--file", required=True)
    pg.add_argument("--out", required=True)
    pg.add_argument("--sample", type=int, default=0, help="max codes (0 = all)")
    pg.add_argument("--stride", type=int, default=1, help="take every Nth code when sampling")
    pg.set_defaults(func=cmd_gen_conformance)

    args = p.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
