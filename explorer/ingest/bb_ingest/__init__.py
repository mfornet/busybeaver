"""Admin-side ingestion for the Busy Beaver explorer.

Pipeline: `lake exe beaver enumerate` streams every TNF-enumerated machine as
`code<TAB>verdict<TAB>steps<TAB>deciderJSON`; we parse it, derive the decider kind and a
pipeline-version hash, and COPY-bulk-load into Postgres. The CLI is the only writer; the
public API reads the same tables read-only.
"""

__all__ = ["__version__"]
__version__ = "0.0.0"
