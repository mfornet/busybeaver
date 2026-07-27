#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "$0")/.." && pwd)"
cert_dir="$repo_dir/Skelet1Cert"

count_files() {
  find "$1" -maxdepth 1 -type f -name "$2" 2>/dev/null | wc -l | tr -d ' '
}

if [[ -f "$cert_dir/All.lean" ]] &&
   [[ "$(count_files "$cert_dir/Pack" 'P*.lean')" == 21396 ]] &&
   [[ "$(count_files "$cert_dir/LocalAnchor" 'A*.lean')" == 856 ]] &&
   [[ "$(count_files "$cert_dir/LocalSegment" 'S*.lean')" == 856 ]] &&
   [[ "$(count_files "$cert_dir/LocalJoin" 'J*.lean')" == 27 ]]; then
  echo "Skelet #1 generated certificate sources already present"
  exit 0
fi

echo "Generating Skelet #1 kernel certificate sources"
lake build skelet1prof
profiler="$repo_dir/.lake/build/bin/skelet1prof"

"$profiler" emitall 1024 "$cert_dir"
"$profiler" pack 85584 4 "$cert_dir"
"$profiler" emitlocalanchors 85584 100 1024 "$cert_dir"
"$profiler" emitchainlocal 85584 100 "$cert_dir" 4

# The packed modules contain the checkpoint data needed by Lean. The unpacked
# C*.lean intermediates are regenerable and would otherwise double local disk use.
find "$cert_dir" -maxdepth 1 -type f -name 'C*.lean' -delete

echo "Generated Skelet #1 certificate sources in $cert_dir"
