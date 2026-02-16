#!/usr/bin/env bash
set -euo pipefail

report_path="${1:-sorry-report.txt}"

collect_paths=()
for p in Busybeaver Main.lean Busybeaver.lean bin; do
  if [ -e "$p" ]; then
    collect_paths+=("$p")
  fi
done

{
  echo "# Sorry report"
  echo "Generated (UTC): $(date -u +'%Y-%m-%dT%H:%M:%SZ')"
  echo
  echo "## Raw token matches (rg -n '\\bsorry\\b')"
  if rg -n '\bsorry\b' "${collect_paths[@]}"; then
    :
  else
    echo "No raw `sorry` tokens found."
  fi
  echo
  echo "## Elaborator warnings (kind=hasSorry)"

  has_sorry_count=0
  while IFS= read -r file; do
    while IFS= read -r line; do
      if [[ "$line" != *'"kind":"hasSorry"'* ]]; then
        continue
      fi

      pos="$(echo "$line" | sed -n 's/.*"pos":{"column":\([0-9][0-9]*\),"line":\([0-9][0-9]*\)}.*/\2:\1/p')"
      msg="$(echo "$line" | sed -n 's/.*"data":"\([^"]*\)".*/\1/p')"

      if [ -n "$pos" ]; then
        echo "${file}:${pos}: ${msg}"
      else
        echo "${file}: ${msg}"
      fi
      has_sorry_count=$((has_sorry_count + 1))
    done < <(lake env lean "$file" --json 2>/dev/null || true)
  done < <(rg --files -g '*.lean' "${collect_paths[@]}" | sort -u)

  if [ "$has_sorry_count" -eq 0 ]; then
    echo "No elaborator `hasSorry` warnings found."
  fi
  echo
  echo "Total hasSorry warnings: ${has_sorry_count}"
} > "$report_path"

echo "Wrote ${report_path}"
