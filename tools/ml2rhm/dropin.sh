#!/bin/bash
# tools/ml2rhm/dropin.sh GENERATED-DIR MODULE...
# Compiles each generated module in place of rhombus/hol's, one at a time, in
# a scratch copy of the repository. Exits non-zero if any fails to compile.
set -u
gen=$(cd "$1" && pwd); shift
repo=$(cd "$(dirname "$0")/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$repo/rhombus" "$work/"
status=0
for m in "$@"; do
  target=rhombus/hol/$m.rhm
  [ "$m" = preterm ] && target=rhombus/hol/private/type_inference.rhm
  [ "$m" = printer ] && target=rhombus/hol/private/theory_support.rhm
  src=$gen/${target#rhombus/hol/}
  cp "$work/$target" "$work/orig.rhm"
  cp "$src" "$work/$target"
  if out=$(cd "$work" && raco make "$target" 2>&1); then
    echo "ok    $m"
  else
    echo "FAIL  $m: $(echo "$out" | head -1)"
    status=1
  fi
  cp "$work/orig.rhm" "$work/$target"
done
exit $status
