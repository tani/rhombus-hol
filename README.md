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
    ordered_map.rhm
    term_hash.rhm
    hash_runtime.rkt
    surface_state.rhm
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

The restored `fusion/basics/nets/equal` core was differentially checked
against the pinned HOL Light implementation on 3,914 generated cases:

- 1,296 kernel cases
- 2,618 upper-layer cases

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

HOL Light-derived engine code and the two OCaml-derived private support modules
retain their upstream notices and license terms. See `THIRD_PARTY_NOTICES`
and `THIRD_PARTY_LICENSES/`.
