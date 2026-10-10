# Rhombus/HOL

A direct Rhombus translation of the HOL Light proof engine and standard theories.

The proof engine and standard theories follow HOL Light, including its
quotation parser: theory quotations are HOL Light text inside `@hol|{...}|`.

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
  printer.rhm             printer.ml (character classes, parse status
                          tables, interface state, the printer)
  preterm.rhm             preterm.ml (preterms, type inference)
  parser.rhm              parser.ml (lexer, type and term parsers)
  lib.rhm                 lib.ml (list utilities, finite partial functions)
  Boyer_Moore/            Boyer_Moore/*.ml: the Boyer-Moore waterfall prover
                          (boyer-moore.rhm loads it, make.rhm is the
                          evaluation script, testset/ its conjectures)
  private/
    ocaml.rhm             OCaml runtime: exceptions, options, polymorphic
                          compare, Hashtbl.hash, int_of_string, Random,
                          Stdlib functions under their OCaml names
    format.rhm            OCaml's Format (the pretty-printing engine)
    hol_quote.rhm         `@hol|{...}|` quotation macro
    declarations.rhm      variant and record declarations
    proof_syntax.rhm      then_tac / then_list / or_tac / then_conv / or_conv
  tests/

```

The files directly under `rhombus/hol/` correspond to HOL Light modules:
one file per HOL Light file, with the same name. `private/` contains mechanical support needed to reproduce OCaml/HOL
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

Quotations are written in HOL Light's own syntax inside `@hol|{...}|`; for
example HOL Light's `` `!x:A. x = x` `` is `@hol|{!x:A. x = x}|`, and
`` `:num->bool` `` is `@hol|{:num->bool}|`. As in HOL Light, the text is read
when it is evaluated, by the direct translation of `parser.ml` and
`preterm.ml`, against the binders, infixes, overloadings and constants of the
theories loaded at that moment; the result is built with the public kernel
constructors and every proof is replayed. The raw `|{ }|` text keeps
backslashes and braces literal, so quotations are copied from the HOL Light
sources unchanged. Terms, types, theorems and goals print as in HOL Light:
`printer.rhm` is a translation of `printer.ml` on a translation of OCaml's
`Format`, checked against HOL Light's output for every theorem
(`tests/golden/printer.rhm`).

### Checking quotations

`HOL_QUOTE_CHECK=1` prints every term a quotation elaborates to
(`HOLCHECK` lines, site and term as JSON). A change to the parser, type
inference or quotation layer is accepted only when `theories` still passes:
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

`tools/literalness/measure.py /path/to/hol-light` reports, per module, how
closely the port follows the pinned HOL Light source (identifiers and
quotations in the same order, toplevel definitions found and in order). The
CI `literalness` job fails when a logic-layer module drops below
`tools/literalness/baseline.json`; see AGENTS.md for the layers.

The standard-theory modules (after `simp.rhm`) were generated from the pinned
HOL Light sources, with each quotation's text taken from them. OCaml tuples
are Rhombus lists (`[a, b]`), OCaml lists are `PairList`, and record types are
classes.


## Boyer-Moore waterfall

`rhombus/hol/Boyer_Moore/` is a hand-written direct translation of HOL
Light's `Boyer_Moore/` library, the waterfall prover described in
P. Papapanagiotou and J. Fleuriot, "The Boyer-Moore Waterfall Model
Revisited" (arXiv:1808.03810), which builds on R. J. Boulton's HOL88 code.
It is not `tools/ml2rhm` output. Clauses pour over a list of heuristics
(tautology, clausal form, setify, substitution, simplification, equality
and cross-fertilization, generalization, irrelevance); the clauses left in
the pool are proved by induction and poured again. `FILTERED_WATERFALL`
adds the paper's termination heuristics (the heuristic warehouse,
`max_var_depth`), `generalize_heuristic_ext`/`_aderhold` the generalization
techniques with the counterexample checker of `counterexample.rhm`.
Every heuristic returns a proof function, and the result is a kernel
theorem.

```rhombus
import: "rhombus/hol/Boyer_Moore/boyer-moore.rhm" open

// Tell the prover about definitions and rewrite rules, as make.ml's bm_reset.
new_def(ADD)
new_rewrite_rule(ADD)
BOYER_MOORE_FINAL(PairList [])(@hol|{m + n = n + m}|)   // |- m + n = n + m
prove([@hol|{!m n. m + n = n + m}|, REPEAT(GEN_TAC) then_tac BMF_TAC(PairList [])])
```

The entry points are those of `main.ml`: `BOYER_MOORE`, `BOYER_MOORE_EXT`,
`BOYER_MOORE_RE`, `BOYER_MOORE_GEN`, `BOYER_MOORE_FINAL`,
`BOYER_MOORE_MESON` (conversions to theorems) and the tactics
`BOYER_MOORE_TAC`, `BMF_TAC`, `BMG_TAC`, `BM_SAFE_TAC`, `BMF_NOEQ_TAC`,
`BM_SIMPLIFY_TAC`, `BM_INDUCT_TAC`. `make.rhm` translates upstream's
evaluation script (`bm_reset`, `bm_test`, the `BM`/`BME`/`BMF` shortcuts)
and `testset/` its 119 arithmetic and 48 list conjectures;
`tests/upstream/boyer_moore.rhm` (CI `theories` job) runs it.

## Generated source style

The translated modules use ordinary indentation, scoped names, descriptive
payload fields, shared variant/record declarations, and HOL Light quotation
text. Multi-argument functions use explicit unary stages, such as
`fun(x): fun(y): x + y`, and callers apply each stage separately.

Standard proofs use the existing combinators through small infix operators.
These forms are defined in `rhombus/hol/private/`; they introduce no new proof
rules.

## Generating from HOL Light

`tools/ml2rhm` translates HOL Light's OCaml sources to Rhombus in the style
of this port, with a `parser-tools` lexer and LALR parser for HOL Light's
OCaml dialect. It translates every OCaml file of the pinned checkout, and all
45 ported modules compile in place of the hand-maintained ones. See
`tools/ml2rhm/README.md`.
