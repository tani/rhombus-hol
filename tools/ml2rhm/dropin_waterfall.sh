#!/bin/bash
# tools/ml2rhm/dropin_waterfall.sh GENERATED-DIR
# Replaces rhombus/hol/Boyer_Moore/ (the hand-written translation of HOL
# Light's Boyer-Moore waterfall prover) with the generated modules, in a
# scratch copy of the repository, and runs tests/upstream/boyer_moore.rhm on
# them. Exits non-zero if they do not compile or the test fails.
set -eu
gen=$(cd "$1/Boyer_Moore" && pwd)
repo=$(cd "$(dirname "$0")/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r "$repo/rhombus" "$work/"
dir=$work/rhombus/hol/Boyer_Moore
rm -rf "$dir"
mkdir -p "$dir"
cp -r "$gen"/. "$dir/"
# the test's bytecode was compiled against the hand-written modules
rm -rf "$work/rhombus/hol/tests/upstream/compiled"
cd "$work/rhombus/hol"
raco make -j 4 Boyer_Moore/*.rhm Boyer_Moore/testset/*.rhm tests/upstream/boyer_moore.rhm
raco test tests/upstream/boyer_moore.rhm
