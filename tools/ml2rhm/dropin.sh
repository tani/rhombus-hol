#!/bin/bash
# tools/ml2rhm/dropin.sh GENERATED-DIR MODULE...
# Compiles each generated module in place of rhombus/hol's, in a scratch copy
# of the repository per module, DROPIN_JOBS (default: all cores) at a time.
# The repository's modules must be compiled first (raco make define.rhm);
# only the replaced module is compiled. Exits non-zero if any fails.
set -u
gen=$(cd "$1" && pwd); shift
repo=$(cd "$(dirname "$0")/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export gen repo work

one() {
  m=$1
  target=rhombus/hol/$m.rhm
  dir=$work/$m
  mkdir -p "$dir"
  # hard links share the compiled dependencies; the replaced file is
  # removed first, so that the repository's copy is never written to
  cp -al "$repo/rhombus" "$dir/" 2>/dev/null || cp -r "$repo/rhombus" "$dir/"
  rm -f "$dir/$target"
  cp "$gen/${target#rhombus/hol/}" "$dir/$target"
  if out=$(cd "$dir" && raco make "$target" 2>&1); then
    echo "ok    $m" > "$work/$m.result"
  else
    echo "FAIL  $m: $(echo "$out" | head -1)" > "$work/$m.result"
  fi
  rm -rf "$dir"
}
export -f one

printf '%s\n' "$@" | xargs -P "${DROPIN_JOBS:-$(nproc)}" -I{} bash -c 'one {}'

status=0
for m in "$@"; do
  cat "$work/$m.result"
  grep -q '^FAIL' "$work/$m.result" && status=1
done
exit $status
