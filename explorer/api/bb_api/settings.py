"""Environment-driven configuration for the API."""

from __future__ import annotations

import os
from dataclasses import dataclass, field


def _origins() -> list[str]:
    raw = os.environ.get(
        "BB_CORS_ORIGINS",
        # Default to the GitHub Pages origin + local dev.
        "http://localhost:5173,http://127.0.0.1:5173",
    )
    return [o.strip() for o in raw.split(",") if o.strip()]


@dataclass(frozen=True)
class Settings:
    dsn: str = field(default_factory=lambda: os.environ.get("BB_DSN", ""))
    cors_origins: list[str] = field(default_factory=_origins)
    pool_min: int = int(os.environ.get("BB_POOL_MIN", "2"))
    pool_max: int = int(os.environ.get("BB_POOL_MAX", "10"))
    # Cache lifetime for read responses (the DB only changes on ingestion).
    cache_seconds: int = int(os.environ.get("BB_CACHE_SECONDS", "300"))
    max_page: int = int(os.environ.get("BB_MAX_PAGE", "500"))


settings = Settings()
