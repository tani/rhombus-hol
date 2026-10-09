#!/bin/sh
# Regenerate rhombus/hol/tests/golden/hol_light.tsv.gz (the logical state)
# and printed.tsv.gz (the printer's output) from HOL Light.
#
# Usage: tools/hol_light_golden/generate.sh /path/to/hol-light
#
# The checkout must be at the pinned revision and built with `make`
# (OCaml 4.14 with camlp5, zarith and findlib). Loading hol.ml takes a few
# minutes. The output is the logical state after the standard load sequence;
# Rhombus/HOL only compares against it and never imports it.
set -eu

PINNED=cba9198db76e9dfb89cbd653df9412d01f65b22a
HOL=$(cd "$1" && pwd)
HERE=$(cd "$(dirname "$0")" && pwd)
OUT="$HERE/../../rhombus/hol/tests/golden/hol_light.tsv.gz"
PRINTED="$HERE/../../rhombus/hol/tests/golden/printed.tsv.gz"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

REV=$(git -C "$HOL" rev-parse HEAD)
if [ "$REV" != "$PINNED" ]; then
  echo "hol-light checkout is at $REV, expected $PINNED" >&2
  exit 1
fi

# Candidate theorem names: column-0 bindings of the ported modules. Names
# that are not theorems at the toplevel are skipped by dump.ml; the
# database.ml theorem list is added there as well.
MODULES="fusion basics nets equal bool drule tactics itab simp theorems
  ind_defs class trivia canon meson firstorder metis thecops quot impconv
  pair compute nums recursion arith wf calc_num normalizer grobner ind_types
  lists realax calc_int realarith real calc_rat int sets iterate cart define"
for m in $MODULES; do
  sed -n "s/^\(let\|and\)  *\(rec  *\)\{0,1\}\([A-Za-z_][A-Za-z0-9_']*\).*/\3/p" "$HOL/$m.ml"
done | sort -u > "$WORK/names.txt"

printf '#use "%s/dump.ml";;\n#use "%s/printed.ml";;\n' "$HERE" "$HERE" |
  (cd "$HOL" && LINE_EDITOR=env HOL_GOLDEN_NAMES="$WORK/names.txt" \
     HOL_GOLDEN_OUT="$WORK/hol_light.tsv" HOL_PRINTED_OUT="$WORK/printed.tsv" \
     ./hol.sh > "$WORK/hol.log" 2>&1)

if ! grep -q '^thm' "$WORK/hol_light.tsv"; then
  tail -20 "$WORK/hol.log" >&2
  exit 1
fi
gzip -9 -n -c "$WORK/hol_light.tsv" > "$OUT"
gzip -9 -n -c "$WORK/printed.tsv" > "$PRINTED"
cut -f1 "$WORK/hol_light.tsv" | sort | uniq -c
