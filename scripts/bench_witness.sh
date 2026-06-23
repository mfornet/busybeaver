#!/usr/bin/env bash
#
# Witness-store regression guard for `beaver`.
#
# Checks three things on a from-scratch BB(4,2) run:
#   1. Correctness — the --trusted re-run reports the SAME value as generation.
#   2. Generation is fast        (< GEN_LIMIT_MS, default 30000 — a 12-core-dev target).
#   3. --trusted is ~instant     (< TRUSTED_LIMIT_MS, default 1000 — hardware-independent,
#                                 it is a single cached-row read).
#
# Exits non-zero (printing FAIL) on any violation, so it can run in CI.
# Tune via env: GEN_LIMIT_MS, TRUSTED_LIMIT_MS, ARGS (e.g. ARGS="3 2").
# CI runs on slower hardware than a dev box, so set a generous GEN_LIMIT_MS there;
# correctness and the trusted bound stay meaningful regardless of core count.
set -euo pipefail

GEN_LIMIT_MS=${GEN_LIMIT_MS:-30000}
TRUSTED_LIMIT_MS=${TRUSTED_LIMIT_MS:-1000}
ARGS=${ARGS:-"4 2"}

DB="$(mktemp -u).db"
cleanup() { rm -f "$DB" "$DB-wal" "$DB-shm"; }
trap cleanup EXIT

echo "Building beaver…"
lake build beaver >/dev/null

ms()  { grep -oE 'In: [0-9]+ms' | grep -oE '[0-9]+'; }
val() { awk '/Busybeaver\(/ {v=$NF} END {print v}'; }   # last token of the result line

echo "Generating witness (beaver $ARGS)…"
# shellcheck disable=SC2086
gen_out=$(lake exe beaver $ARGS --witness "$DB" 2>/dev/null)
echo "Trusted re-run (beaver $ARGS --trusted)…"
# shellcheck disable=SC2086
trusted_out=$(lake exe beaver $ARGS --trusted --witness "$DB" 2>/dev/null)

gen_ms=$(echo "$gen_out" | ms)
trusted_ms=$(echo "$trusted_out" | ms)
gen_val=$(echo "$gen_out" | val)
trusted_val=$(echo "$trusted_out" | val)

echo
echo "value:    generate=$gen_val  trusted=$trusted_val"
echo "generate: ${gen_ms}ms   (limit ${GEN_LIMIT_MS}ms)"
echo "trusted:  ${trusted_ms}ms   (limit ${TRUSTED_LIMIT_MS}ms)"

fail=0
if [ -z "$gen_val" ] || [ "$gen_val" != "$trusted_val" ]; then
  echo "FAIL: trusted value ($trusted_val) does not match generated value ($gen_val)"; fail=1
fi
if [ "$gen_ms" -ge "$GEN_LIMIT_MS" ]; then echo "FAIL: generation exceeded ${GEN_LIMIT_MS}ms"; fail=1; fi
if [ "$trusted_ms" -ge "$TRUSTED_LIMIT_MS" ]; then echo "FAIL: trusted exceeded ${TRUSTED_LIMIT_MS}ms"; fail=1; fi
[ "$fail" -eq 0 ] && echo "PASS"
exit "$fail"
