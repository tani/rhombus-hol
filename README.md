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
  lib.rhm                 lib.ml (list utilities, finite partial functions)
  private/
    ocaml.rhm             OCaml runtime: exceptions, polymorphic compare,
                          Hashtbl.hash, Random
    theory_support.rhm    parser.ml/printer.ml pieces: pattern combinators,
                          interface state, diagnostic printing
    data_types.rhm        options and variant comparison view
    hol_quote.rhm         `hol:` / `hol_type:` quotation macros
    type_inference.rhm, type_specification.rhm
    declarations.rhm, proof_syntax.rhm, variant_base.rhm
  tests/

```

The files directly under `rhombus/hol/` correspond to HOL Light modules:
`lib.rhm` and the engine and theory modules. `private/` contains mechanical support needed to reproduce OCaml/HOL
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
quotations are written in the Rhombus-native `hol:` quotation, whose macros
elaborate them at compile time into public term/type constructors; runtime
modules replay the original proofs. For example, HOL Light's
`` `!x:A. x = x` `` is `hol: forall x :: A: x == x`. A HOL name that is not a
Rhombus identifier is an escaped identifier (`#{+}`, `#{|x'|}`), and an infix
operator name on its own is that name (`#{+}(m, n)`). `(NAME :: type)` is a name at
exactly that type: a second instance of a constant, a variable hidden by a binder
of the same name, or `!` and `-`, which are also prefix forms. Private type-inference algorithms support Metis
reconstruction, and a small Rhombus-native type-description frontend supports
inductive declarations. General parsing, elaboration, notation, quotation,
and presentation belong to the Rhombus syntax and macro frontend.

### Quotation design

Type inference for theory quotations happens offline, in HOL Light itself
(`tools/hol_light_golden/quote.ml`), and `to_hol.py` writes the result into the
sources with every constant type and every variable name explicit. `hol:`
therefore performs no inference at compile time: it checks the declared types
and builds kernel constructors. This keeps the compile step cheap (about
4 minutes for all theories, against about 12 when the macro inferred types) and
keeps the quoted terms identical to HOL Light's. Names are never renamed:
those that are not Rhombus identifiers (`x'`, `<<`, `PAIR'`) are escaped
identifiers, and a constant used at a different type than its declaration is
written with that type at the use.

A change to the quotation layer is accepted only when `theories` still passes:
it replays every proof and compares each theorem, constant and definition
with the pinned HOL Light state (`tests/golden/hol_light.rhm`). Do not make
that audit optional, and do not rewrite quotations in bulk without replaying
the proofs.

## Verification

The Rhombus modules replay the translated standard-theory proofs through the
kernel. HOL Light's original proof rules are preserved; expected theorems are
never runtime axioms.

## Build

```sh
raco pkg install --auto --batch --no-docs --no-setup --skip-installed \
  --name rhombus-hol "$PWD"
raco make --disable-inline rhombus/hol/define.rhm
raco test rhombus/hol/tests/*.rhm
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

The slower suites replay the whole standard theory sequence (several minutes
each) and run in the CI `theories` job:

```sh
raco test -j 4 rhombus/hol/tests/golden/hol_light.rhm rhombus/hol/tests/upstream/*.rhm
```

- `tests/golden/hol_light.rhm` compares every type, constant, axiom,
  definition and toplevel theorem with the logical state of the pinned HOL
  Light after `define.ml`, recorded in `tests/golden/hol_light.tsv.gz`.
- `tests/upstream/` ports HOL Light's `UnitTests/basic_tests.ml` and
  `Examples/{dickson,lagrange_lemma}.ml`.

The data comes from `tools/hol_light_golden/` and is only compared against.

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
