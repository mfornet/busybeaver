#!/usr/bin/env sh
set -eu

if ! command -v leanblueprint >/dev/null 2>&1; then
  echo "leanblueprint was not found in PATH."
  echo "Install it with: python3 -m pip install --user leanblueprint"
  exit 1
fi

# Ensure we use the plasTeX executable bundled with the active leanblueprint tool.
LB_EXE="$(command -v leanblueprint)"
LB_PY="$(head -n 1 "$LB_EXE" | sed 's/^#!//')"
if [ -x "$LB_PY" ]; then
  LB_DIR="$(dirname "$LB_PY")"
else
  LB_DIR="$(dirname "$LB_EXE")"
fi
PATH="$LB_DIR:$PATH"

# Optional speedup; allow offline/local runs without failing early.
lake exe cache get || true
lake build Busybeaver
leanblueprint web
leanblueprint checkdecls
