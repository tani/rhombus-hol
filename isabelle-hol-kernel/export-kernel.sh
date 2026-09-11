#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
theory_dir="$repo_root/isabelle-hol-kernel"
production="$repo_root/rhombus-hol-kernel/rhombus/hol/kernel_generated.rhm"
out_dir="$(mktemp -d)"
trap 'rm -rf "$out_dir"' EXIT

nix develop "$repo_root" --command \
  isabelle build -D "$theory_dir" -o quick_and_dirty=false Rhombus_HOL_Kernel
nix develop "$repo_root" --command \
  isabelle export -d "$theory_dir" -n -p 2 -O "$out_dir" \
    -x 'Rhombus_HOL_Kernel.Rhombus_HOL_Code:code/rhombus_hol_kernel.rhm' \
    Rhombus_HOL_Kernel

exported="$out_dir/rhombus_hol_kernel.rhm"
case "${1:-}" in
  "") install -m 0644 "$exported" "$production" ;;
  --check) cmp "$exported" "$production" ;;
  *) printf 'usage: %s [--check]\n' "$0" >&2; exit 2 ;;
esac
