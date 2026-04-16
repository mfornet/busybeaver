#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source_tree_root="${CODEX_SOURCE_TREE_PATH:-$(cd "${script_dir}/.." && pwd)}"
worktree_root="${CODEX_WORKTREE_PATH:-${source_tree_root}}"

shared_root="${CODEX_LEAN_CACHE_ROOT:-${HOME}/.codex/cache/busybeaver-lean}"
shared_packages="${shared_root}/lake-packages"
local_lake_dir="${worktree_root}/.lake"
local_packages="${local_lake_dir}/packages"
lock_dir="${shared_root}/.setup.lock"

mkdir -p "${shared_root}"
mkdir -p "${local_lake_dir}"

while ! mkdir "${lock_dir}" 2>/dev/null; do
  sleep 1
done
trap 'rmdir "${lock_dir}"' EXIT

if [ -L "${local_packages}" ]; then
  current_target="$(readlink "${local_packages}")"
  if [ "${current_target}" != "${shared_packages}" ]; then
    rm "${local_packages}"
  fi
fi

if [ -d "${local_packages}" ] && [ ! -L "${local_packages}" ]; then
  if [ -e "${shared_packages}" ]; then
    if find "${shared_packages}" -mindepth 1 -maxdepth 1 -print -quit >/dev/null 2>&1; then
      rm -rf "${local_packages}"
    else
      rmdir "${shared_packages}"
      mv "${local_packages}" "${shared_packages}"
    fi
  else
    mv "${local_packages}" "${shared_packages}"
  fi
fi

mkdir -p "${shared_packages}"
ln -sfn "${shared_packages}" "${local_packages}"

echo "Shared Lake package cache: ${shared_packages}"
echo "Lake workspace packages symlinked from: ${local_packages}"

if command -v lake >/dev/null 2>&1; then
  (cd "${worktree_root}" && lake build)
else
  echo "Skipping lake build because 'lake' is not on PATH." >&2
fi
