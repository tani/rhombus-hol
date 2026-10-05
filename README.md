# Rhombus/HOL

A direct Rhombus translation of the HOL Light proof engine and standard theories.

The repository is intentionally split at the HOL Light engine/frontend
boundary. The proof engine and standard theories follow HOL Light; the surface language
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
  theorems.rhm
  ind_defs.rhm
  class.rhm
  ... standard theories through define.rhm
  private/
    compat.rhm
    atoms_map.rhm
    term_hash.rhm
    hash_runtime.rhm
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

The source-to-source port includes the engine sequence:

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

It extends through the standard load sequence ending at `define.ml`: basic
theorems, classical logic, inductive definitions, first-order automation,
natural numbers and recursion, arithmetic, inductive types and lists, reals
and integers, sets, iteration, and Cartesian products.

HOL Light's text parser and printer are not the frontend. Literal theory
quotations expand offline to public term/type constructors; runtime modules
replay the original proofs. Private type-inference algorithms support Metis
reconstruction, and a small Rhombus-native type-description frontend supports
inductive declarations. General parsing, elaboration, notation, quotation,
and presentation belong to the Rhombus syntax and macro frontend.

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

The standard theory harness compares each exported theorem with the pinned
OCaml original. Only bound term names and polymorphic type-variable names are
normalized; hypotheses, conclusions, constants, and free term names must agree.
It rejects kernel axioms outside the original ETA_AX, SELECT_AX, and INFINITY_AX.
All 2,979 exported theorems across the 34 standard modules match the original,
and all proofs replay in the Rhombus kernel. Local engine tests also pass
(25 tests). See [tools/translate/verification.json](tools/translate/verification.json)
for the saved module coverage and checks,
and [tools/translate/README.md](tools/translate/README.md) for generation and
full-theory verification commands. Expected theorems are never runtime axioms.

## Build

```sh
raco pkg install --auto --batch --no-docs --no-setup --skip-installed \
  --name rhombus-hol "$PWD"
raco make --disable-inline rhombus/hol/define.rhm
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
