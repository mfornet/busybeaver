#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"

usage() {
  cat <<EOF
Usage:
  ci/lean_mcp.sh register [server-name]
  ci/lean_mcp.sh serve
  ci/lean_mcp.sh status [server-name]

Commands:
  register   Add or replace a Codex MCP server that runs lean-lsp-mcp.
  serve      Run lean-lsp-mcp directly for this repo (stdio transport).
  status     Show the Codex MCP config for this server.

Defaults:
  server-name: lean-lsp
EOF
}

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "Missing required command: ${cmd}" >&2
    exit 1
  fi
}

cmd_register() {
  local name="${1:-lean-lsp}"
  require_cmd codex
  require_cmd uvx
  require_cmd lake

  echo "Building project first (recommended for Lean MCP startup speed)..."
  (cd "${repo_root}" && lake build)

  if codex mcp get "${name}" >/dev/null 2>&1; then
    echo "Removing existing Codex MCP server: ${name}"
    codex mcp remove "${name}"
  fi

  echo "Registering Codex MCP server '${name}' -> uvx lean-lsp-mcp"
  codex mcp add "${name}" \
    --env "LEAN_PROJECT_PATH=${repo_root}" \
    --env "LEAN_LOG_LEVEL=ERROR" \
    -- uvx lean-lsp-mcp

  echo "Done. Verify with:"
  echo "  codex mcp get ${name}"
  echo "Then restart your Codex session to pick up the MCP server."
}

cmd_serve() {
  require_cmd uvx
  require_cmd lake
  export LEAN_PROJECT_PATH="${repo_root}"
  echo "Starting lean-lsp-mcp with LEAN_PROJECT_PATH=${LEAN_PROJECT_PATH}"
  exec uvx lean-lsp-mcp
}

cmd_status() {
  local name="${1:-lean-lsp}"
  require_cmd codex
  codex mcp get "${name}"
}

main() {
  local subcmd="${1:-}"
  case "${subcmd}" in
    register)
      shift
      cmd_register "$@"
      ;;
    serve)
      shift
      cmd_serve "$@"
      ;;
    status)
      shift
      cmd_status "$@"
      ;;
    -h|--help|help)
      usage
      ;;
    *)
      usage >&2
      exit 1
      ;;
  esac
}

main "$@"
