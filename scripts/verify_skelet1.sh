#!/usr/bin/env bash
set -euo pipefail

workers="${1:-10}"
if ! [[ "$workers" =~ ^[1-9][0-9]*$ ]]; then
  echo "usage: $0 [positive-worker-count]" >&2
  exit 2
fi

repo_dir="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_dir"
started_at=$SECONDS

"$repo_dir/scripts/generate_skelet1.sh"

# Build the small shared semantics once through Lake, then invoke Lean directly
# for the computational modules.  This avoids generating unused C/metadata
# artifacts and gives us an explicit memory-safe concurrency bound.
lake -q build +Busybeaver.Deciders.Skelet.Skelet1:olean
lean_bin="$(lake env which lean)"
export LEAN_PATH="$(lake env printenv LEAN_PATH)"

pack_count=21396
pack_out="$repo_dir/.lake/build/lib/lean/Skelet1Cert/Pack"
mkdir -p "$pack_out"

echo "Verifying $pack_count packed Skelet #1 checkpoints with $workers workers"
pids=()
for ((worker = 0; worker < workers; worker++)); do
  (
    rebuilt=0
    for ((i = worker; i < pack_count; i += workers)); do
      src="$repo_dir/Skelet1Cert/Pack/P${i}.lean"
      out="$pack_out/P${i}.olean"
      if [[ ! -f "$out" || "$src" -nt "$out" ]]; then
        "$lean_bin" "$src" -o "$out"
        ((rebuilt += 1))
        if ((rebuilt % 100 == 0)); then
          echo "checkpoint worker $worker: rebuilt $rebuilt modules"
        fi
      fi
    done
  ) &
  pids+=("$!")
done

status=0
for pid in "${pids[@]}"; do
  if ! wait "$pid"; then
    status=1
  fi
done
if ((status != 0)); then
  echo "A checkpoint worker failed" >&2
  exit "$status"
fi

anchor_count=856
anchor_out="$repo_dir/.lake/build/lib/lean/Skelet1Cert/LocalAnchor"
mkdir -p "$anchor_out"
echo "Verifying $anchor_count shallow local anchors with $workers workers"
pids=()
for ((worker = 0; worker < workers; worker++)); do
  (
    for ((i = worker; i < anchor_count; i += workers)); do
      src="$repo_dir/Skelet1Cert/LocalAnchor/A${i}.lean"
      out="$anchor_out/A${i}.olean"
      if [[ ! -f "$out" || "$src" -nt "$out" ]]; then
        "$lean_bin" "$src" -o "$out"
      fi
    done
  ) &
  pids+=("$!")
done

status=0
for pid in "${pids[@]}"; do
  if ! wait "$pid"; then
    status=1
  fi
done
if ((status != 0)); then
  echo "A local anchor failed" >&2
  exit "$status"
fi

segment_count=856
segment_workers=$workers
if ((segment_workers > 8)); then
  # Segment elaboration itself uses several cores, unlike checkpoint
  # evaluation. Eight outer workers overlap its long single-core reduction
  # phases while staying well below the memory limit on this machine.
  segment_workers=8
fi
segment_out="$repo_dir/.lake/build/lib/lean/Skelet1Cert/LocalSegment"
mkdir -p "$segment_out"
echo "Verifying $segment_count independent local segments with $segment_workers workers"
pids=()
for ((worker = 0; worker < segment_workers; worker++)); do
  (
    for ((i = worker; i < segment_count; i += segment_workers)); do
      src="$repo_dir/Skelet1Cert/LocalSegment/S${i}.lean"
      out="$segment_out/S${i}.olean"
      if [[ ! -f "$out" || "$src" -nt "$out" ]]; then
        "$lean_bin" "$src" -o "$out"
      fi
    done
  ) &
  pids+=("$!")
done

status=0
for pid in "${pids[@]}"; do
  if ! wait "$pid"; then
    status=1
  fi
done
if ((status != 0)); then
  echo "A composition segment failed" >&2
  exit "$status"
fi

join_count=27
join_out="$repo_dir/.lake/build/lib/lean/Skelet1Cert/LocalJoin"
mkdir -p "$join_out"
echo "Verifying $join_count independent joins with $segment_workers workers"
pids=()
for ((worker = 0; worker < segment_workers; worker++)); do
  (
    for ((i = worker; i < join_count; i += segment_workers)); do
      src="$repo_dir/Skelet1Cert/LocalJoin/J${i}.lean"
      out="$join_out/J${i}.olean"
      if [[ ! -f "$out" || "$src" -nt "$out" ]]; then
        "$lean_bin" "$src" -o "$out"
      fi
    done
  ) &
  pids+=("$!")
done

status=0
for pid in "${pids[@]}"; do
  if ! wait "$pid"; then
    status=1
  fi
done
if ((status != 0)); then
  echo "A composition join failed" >&2
  exit "$status"
fi

"$lean_bin" "$repo_dir/Skelet1Cert/All.lean" \
  -o "$repo_dir/.lake/build/lib/lean/Skelet1Cert/All.olean"
"$lean_bin" "$repo_dir/Busybeaver/Deciders/Skelet/Skelet1Final.lean" \
  -o "$repo_dir/.lake/build/lib/lean/Busybeaver/Deciders/Skelet/Skelet1Final.olean"
"$lean_bin" "$repo_dir/Busybeaver/Deciders/BB5Table.lean" \
  -o "$repo_dir/.lake/build/lib/lean/Busybeaver/Deciders/BB5Table.olean"
"$lean_bin" "$repo_dir/Busybeaver/Deciders/Skelet/Skelet1Backend.lean" \
  -o "$repo_dir/.lake/build/lib/lean/Busybeaver/Deciders/Skelet/Skelet1Backend.olean"
"$lean_bin" "$repo_dir/Busybeaver/Deciders/Skelet/Skelet1Kernel.lean" \
  -o "$repo_dir/.lake/build/lib/lean/Busybeaver/Deciders/Skelet/Skelet1Kernel.olean"
"$lean_bin" "$repo_dir/Busybeaver/Deciders/BB5TableKernel.lean" \
  -o "$repo_dir/.lake/build/lib/lean/Busybeaver/Deciders/BB5TableKernel.olean"
"$lean_bin" "$repo_dir/Skelet1Kernel.lean" \
  -o "$repo_dir/.lake/build/lib/lean/Skelet1Kernel.olean"

echo "Skelet #1 kernel backend and BB5 table verified successfully in $((SECONDS - started_at)) seconds"
