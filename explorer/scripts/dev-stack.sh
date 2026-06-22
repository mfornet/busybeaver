#!/usr/bin/env bash
#
# One-command local dev stack for the Busy Beaver explorer.
#
#   bash explorer/scripts/dev-stack.sh
#
# Brings up a throwaway Postgres, applies the schema, enumerates + ingests a few sizes
# straight from the Lean binary, starts the read-only API, and starts the web dev server.
# Ctrl-C tears everything down and deletes the temp database.
#
# Env overrides:
#   SIZES=2x2,3x2,4x2   sizes to enumerate + ingest (default: 2x2,3x2)
#   BB_DSN=postgres://… use your own Postgres instead of a throwaway one
#   PORT_API / PORT_WEB ports (default 8099 / 5173)
set -euo pipefail

export PATH="$HOME/.elan/bin:$PATH"   # make `lake` available in non-interactive shells
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
EXP="$ROOT/explorer"
SIZES="${SIZES:-2x2,3x2}"
PORT_API="${PORT_API:-8099}"
PORT_WEB="${PORT_WEB:-5173}"

API_PID=""; WEB_PID=""; PGTMP=""; OWN_PG=0

# Recursively kill a process and all its descendants (pnpm spawns a vite subtree).
kill_tree() {
  local pid="$1" child
  [ -n "$pid" ] || return 0
  for child in $(pgrep -P "$pid" 2>/dev/null); do kill_tree "$child"; done
  kill "$pid" 2>/dev/null || true
}

cleanup() {
  trap - EXIT INT TERM   # avoid re-entry
  echo; echo "[dev-stack] shutting down…"
  kill_tree "$WEB_PID"
  kill_tree "$API_PID"
  if [ "$OWN_PG" = 1 ] && [ -n "$PGTMP" ]; then
    pg_ctl -D "$PGTMP/data" stop -m fast >/dev/null 2>&1 || true
    rm -rf "$PGTMP"
  fi
}
trap cleanup EXIT INT TERM

# --- Postgres -------------------------------------------------------------------------
if [ -z "${BB_DSN:-}" ]; then
  OWN_PG=1
  PGTMP="$(mktemp -d "${TMPDIR:-/tmp}/bb-dev.XXXX")"
  echo "[dev-stack] starting throwaway Postgres in $PGTMP"
  initdb -D "$PGTMP/data" -U postgres --auth=trust >/dev/null
  pg_ctl -D "$PGTMP/data" \
    -o "-p 5459 -c listen_addresses=127.0.0.1 -c unix_socket_directories=$PGTMP" \
    -l "$PGTMP/log" start >/dev/null
  sleep 2
  export BB_DSN="postgresql://postgres@127.0.0.1:5459/postgres"
fi
echo "[dev-stack] applying schema"
psql "$BB_DSN" -v ON_ERROR_STOP=1 -q -f "$EXP/db/schema.sql"

# --- Ingest from the Lean binary ------------------------------------------------------
echo "[dev-stack] enumerating + ingesting sizes: $SIZES (this runs the Lean deciders)"
cd "$EXP/ingest"
[ -d .venv ] || uv venv >/dev/null
VIRTUAL_ENV="$EXP/ingest/.venv" uv pip install -q 'psycopg[binary]>=3.2'
"$EXP/ingest/.venv/bin/python" -m bb_ingest ingest --dsn "$BB_DSN" --repo "$ROOT" --sizes "$SIZES"

# --- API ------------------------------------------------------------------------------
echo "[dev-stack] starting API on http://127.0.0.1:$PORT_API"
cd "$EXP/api"
[ -d .venv ] || uv venv >/dev/null
VIRTUAL_ENV="$EXP/api/.venv" uv pip install -q 'fastapi>=0.115' 'asyncpg>=0.30' 'pydantic>=2.9' 'uvicorn[standard]>=0.32'
BB_DSN="$BB_DSN" BB_CORS_ORIGINS="http://localhost:$PORT_WEB,http://127.0.0.1:$PORT_WEB" \
  "$EXP/api/.venv/bin/python" -m uvicorn bb_api.main:app \
  --host 127.0.0.1 --port "$PORT_API" >"$EXP/.api.log" 2>&1 &
API_PID=$!

# --- Web ------------------------------------------------------------------------------
echo "[dev-stack] starting web on http://127.0.0.1:$PORT_WEB"
cd "$EXP"
pnpm install --silent
VITE_API_BASE="http://127.0.0.1:$PORT_API" \
  pnpm --filter web exec vite --host 127.0.0.1 --port "$PORT_WEB" --strictPort \
  >"$EXP/.web.log" 2>&1 &
WEB_PID=$!

sleep 3
echo
echo "  ───────────────────────────────────────────────"
echo "   Web:  http://127.0.0.1:$PORT_WEB"
echo "   API:  http://127.0.0.1:$PORT_API/api/summary"
echo "   logs: explorer/.api.log  explorer/.web.log"
echo "   Ctrl-C to stop and clean up."
echo "  ───────────────────────────────────────────────"
wait
