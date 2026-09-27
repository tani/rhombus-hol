#!/usr/bin/env bash
set -euo pipefail

# Builds the standard library and reports:
#   - whether it builds
#   - whether every theorem without `~sorry` has a completed proof
#     (this is the same check: `raco make` elaborates every theorem, and a
#     failed waterfall proof fails the build, so build success already
#     means every non-`~sorry` theorem is proved)
#   - how many theorems still carry `~sorry`

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
stdlib_dir="$repo_root/rhombus-hol-stdlib"
stdlib_src="$stdlib_dir/rhombus/hol/stdlib"

build_log="$(mktemp)"
trap 'rm -f "$build_log"' EXIT

build_ok=1
if ! (cd "$stdlib_dir" && raco make rhombus/hol/stdlib.rhm) >"$build_log" 2>&1
then
  build_ok=0
fi

if [ "$build_ok" -eq 1 ]
then
  echo "BUILD: ok"
  echo "PROOFS: complete (every theorem without ~sorry was proved by the waterfall)"
else
  echo "BUILD: FAILED"
  echo "PROOFS: unknown (build did not finish; see errors below)"
  echo "--- raco make output ---"
  cat "$build_log"
fi

echo
echo "SORRY: $(grep -rho '~sorry' "$stdlib_src"/*.rhm | wc -l) remaining"
grep -rc '~sorry' "$stdlib_src"/*.rhm | while IFS=: read -r file count
do
  [ "$count" -gt 0 ] && printf '  %s: %s\n' "$(basename "$file")" "$count"
done

exit $((1 - build_ok))
