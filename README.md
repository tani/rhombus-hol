# Rhombus/HOL

A direct Rhombus reimplementation of the HOL Light proof engine.

The repository is intentionally split at the HOL Light engine/frontend
boundary. The proof engine follows HOL Light closely; the surface language
above it will be implemented natively with Rhombus macros.

## Layout

```text
rhombus/hol/
  fusion.rhm
  basics.rhm
  nets.rhm
  equal.rhm
  bool.rhm
  drule.rhm
  tactics.rhm
  itab.rhm
  simp.rhm
  private/
    compat.rhm
    atoms_map.rhm
    term_hash.rhm
    hash_runtime.rkt
  tests/

differential/
  tests/
  upstream/

.github/workflows/
  ci.yml
  differential.yml
```

The files directly under `rhombus/hol/` correspond to the HOL Light engine
modules. `private/` contains mechanical support needed to reproduce OCaml/HOL
Light behavior; it is not part of the intended public API.

The source-to-source port stops at:

```text
fusion.ml
basics.ml
nets.ml
equal.ml
bool.ml
drule.ml
tactics.ml
itab.ml
simp.ml
```

HOL Light's `parser.ml`, `preterm.ml`, and `printer.ml` are deliberately
not ported. Parsing, elaboration, notation, quotation, and presentation will be
implemented using Rhombus syntax and macro facilities.

## Verification

The engine differential harness checks the pinned HOL Light implementation on
3,912 cases (1,296 kernel and 2,616 upper-layer cases), including 164 OCaml hash
compatibility cases. The `atoms` implementation preserves HOL Light's exact
list order through its original Patricia-map insertion/fold and OCaml hashing.
The common engine suite has 3,748 cases when `HOL_ENGINE_ONLY=1` is set.
Removed frontend operations are outside this engine boundary.

The harness is under `differential/`. It imports the live Rhombus
implementation; there is no duplicate port tree.

```sh
python3 differential/tests/run.py
python3 differential/tests/run_upper.py
```

The full differential suite is manual-only in GitHub Actions so ordinary CI
remains fast.

## Build

```sh
raco pkg install --auto --batch --no-docs --no-setup --skip-installed \
  --name rhombus-hol "$PWD"
raco make rhombus/hol/simp.rhm
raco test rhombus/hol/tests
```

## Provenance

HOL Light-derived engine code and the OCaml-derived hash support retain their
upstream notices and license terms. See `THIRD_PARTY_NOTICES` and
`THIRD_PARTY_LICENSES/`.

## Local private-core benchmark

```sh
python3 benchmarks/private_core.py /path/to/baseline /path/to/experiment
```

Apply the same current differential harness to both checkouts first. The runner
measures three cold `equal.rhm` compiles, both complete differential harnesses,
and three compiled warm runs of each generated probe. It records elapsed time,
child maximum RSS, exit status, and exact differential mismatches.
See `benchmarks/results.json` for the historical comparison before the
`atoms` compatibility restoration. Those timings describe the fully reduced
variant and are not measurements of the current partially restored variant.
