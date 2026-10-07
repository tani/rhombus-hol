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
infer types and expand directly into public term/type constructor calls; runtime
modules replay the original proofs. For example, HOL Light's
`` `!x:A. x = x` `` is `hol: forall x :: A: x == x`. A polymorphic constant
has one declared type scheme and is instantiated separately at each occurrence:

```rhombus
hol:
  const IN :: A -> (A -> bool) -> bool
  var x
  var s
  var ss
  IN(x, s) && IN(s, ss)
```

Free and bound variables are monomorphic within a quotation and may omit type
annotations. Inference is first-order, occurs-checked, and local to macro
expansion; it does not load theories. Explicit variable annotations are rigid.
Unconstrained types become fresh HOL type variables. Numerals still require
`(n :: num)`, `(n :: int)` or `(n :: real)`. Ambiguous overloaded arithmetic
requires an annotation, such as `(x :: num)`. No coercions are inserted.

Bound names need no HOL Light spelling aliases. Symbolic names use escaped
identifiers; `const.#{=}` explicitly refers to a declared equality constant,
and `const.IN` or `var.x` select declarations under a shadowing binder. Only
unusual declaration names, such as a name containing a newline, need `as`.
Every constructed constant is checked against the runtime kernel declaration.
Generated constructor calls are composed as parsed syntax, so nested quotations
do not repeatedly pass through Rhombus expression parsing.
Private type-inference algorithms support Metis
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
raco test rhombus/hol/tests/fast.rhm
```

## Provenance

HOL Light-derived engine code and the OCaml-derived hash support retain their
upstream notices and license terms. See `THIRD_PARTY_NOTICES` and
`THIRD_PARTY_LICENSES/`.

## Build and check

Requires Racket 9.3 or later with `rhombus-lib`.

```sh
raco make -j 4 rhombus/hol/*.rhm          # compile every module
raco test rhombus/hol/tests/fast.rhm       # kernel, frontend and engine contracts
raco test rhombus/hol/tests/all.rhm        # one standard-theory load, all suites
```

The CI `theories` job uses `tests/all.rhm` as a single-process runner. It replays
the standard theories once, verifies the exact three axiom statements, then
runs the kernel/frontend/engine contracts and upstream examples in sequence.
It checks that no suite adds or replaces an axiom. Example definitions are
conservative context extensions; the runner deliberately shares mutable state
and must not be parallelized internally.

The historical HOL Light audit is optional. It runs before examples extend the
context, and shares the same standard-theory load:

```sh
HOL_TEST_AUDIT=1 raco test rhombus/hol/tests/all.rhm
```

- `tests/golden/hol_light.rhm` compares the recorded types, constants, axioms,
  definition and toplevel theorem with the logical state of the pinned HOL
  Light after `define.ml`, recorded in `tests/golden/hol_light.tsv.gz`.
- `tests/support/reference.rkt` parses the historical encoding into typed trees,
  compares binders by scope and hypotheses without regard to order, and keeps
  separate bijections for type variables, free variables and generated constants.
  Ordinary constants retain their identity, including the numeral constant `_0`.
- `tests/upstream/` ports HOL Light's `UnitTests/basic_tests.ml` and
  `Examples/{dickson,lagrange_lemma}.ml`. Example contracts check their explicit
  goals and empty hypotheses directly, without large theorem-printer strings.
- `tests/kernel.rhm` exercises primitive inference rules, rejected side
  conditions, capture-avoiding substitution and a bounded typed-term grammar.
- `tests/inference_errors.rhm` checks that invalid quotations fail during
  expansion rather than during proof execution.

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
