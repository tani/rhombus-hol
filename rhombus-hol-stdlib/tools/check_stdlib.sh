#!/usr/bin/env bash
set -euo pipefail

# Builds the standard library and reports:
#   - whether it builds (fast syntax/type check via `raco make`)
#   - whether every theorem without `~sorry` actually has a completed HOL
#     proof (a real check: instantiating `stdlib.rhm`'s `hol_theory`
#     submodule, which is where the waterfall proof / kernel axiom admission
#     actually runs -- `raco make` alone does NOT run this: it only
#     type-checks each theorem's statement and options, so it would happily
#     "pass" a theorem whose proof search fails. See tools/verify_theory.rkt.)
#   - how many theorems still carry `~sorry`

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
stdlib_dir="$repo_root/rhombus-hol-stdlib"
stdlib_src="$stdlib_dir/rhombus/hol/stdlib"
verify_script="$repo_root/rhombus-hol-stdlib/tools/verify_theory.rkt"

build_log="$(mktemp)"
theory_log="$(mktemp)"
trap 'rm -f "$build_log" "$theory_log"' EXIT

build_ok=1
if ! (cd "$stdlib_dir" && raco make rhombus/hol/stdlib.rhm) >"$build_log" 2>&1
then
  build_ok=0
fi

if [ "$build_ok" -eq 1 ]
then
  echo "BUILD: ok"
else
  echo "BUILD: FAILED"
  echo "--- raco make output ---"
  cat "$build_log"
fi

proofs_ok=0
if [ "$build_ok" -eq 1 ]
then
  if racket "$verify_script" "$stdlib_dir/rhombus/hol/stdlib.rhm" >"$theory_log" 2>&1
  then
    proofs_ok=1
    echo "PROOFS: complete (hol_theory instantiated: every theorem without ~sorry was proved by the waterfall)"
  else
    echo "PROOFS: FAILED"
    echo "--- theory check output ---"
    cat "$theory_log"
  fi
else
  echo "PROOFS: unknown (build did not finish; see errors above)"
fi

echo
echo "SORRY: $(grep -rho '~sorry' "$stdlib_src"/*.rhm | wc -l) remaining"
grep -rc '~sorry' "$stdlib_src"/*.rhm | while IFS=: read -r file count
do
  [ "$count" -gt 0 ] && printf '  %s: %s\n' "$(basename "$file")" "$count"
done

exit $((1 - build_ok * proofs_ok))
