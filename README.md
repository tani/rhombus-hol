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
    compat.rhm            lib.ml helpers
    theory_support.rhm    remaining OCaml stdlib/lib.ml support
    data_types.rhm        options and variant comparison view
    atoms_map.rhm         Patricia term maps (generated from lib.ml)
    term_hash.rhm, hash_runtime.rhm, ocaml_random.rhm
    type_inference.rhm, type_specification.rhm, quoted_ast.rhm
    declarations.rhm, proof_syntax.rhm, variant_base.rhm
  tests/

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

The Rhombus modules replay the translated standard-theory proofs through the
kernel. HOL Light's original proof rules are preserved; expected theorems are
never runtime axioms.

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

## Build and check

Requires Racket 9.3 or later with `rhombus-lib`.

```sh
raco make -j 4 rhombus/hol/*.rhm          # compile every module
racket rhombus/hol/tests/fusion.rhm       # also tests/bool.rhm, tests/engine.rhm
racket rhombus/hol/define.rhm             # replays every standard-theory proof
```

The standard-theory modules (after `simp.rhm`) were generated from the pinned
HOL Light sources. OCaml tuples are Rhombus lists (`[a, b]`), OCaml lists are
`PairList`, and record types are classes.


## Generated source style

The translated modules use ordinary indentation, scoped names, descriptive
payload fields, shared variant/record declarations, and compact typed term
syntax. Multi-argument functions use explicit unary stages, such as
`fun(x): fun(y): x + y`, and callers apply each stage separately.

Standard proofs use the existing combinators through small infix operators.
These forms are defined in `rhombus/hol/private/`; they introduce no new proof
rules.
