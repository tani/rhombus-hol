# ml2rhm: HOL Light to Rhombus

`ml2rhm` translates HOL Light's OCaml sources to Rhombus in the style of
`rhombus/hol`. It is written in Racket with `parser-tools`:

- `lexer.rkt`: `parser-tools/lex` lexer for the OCaml dialect HOL Light is
  read in. It follows camlp5 with HOL Light's `pa_j`: `` `...` `` quotations,
  the JRH identifier rule (a capital followed only by lower-case characters is
  a constructor, `TAUT` and `REFL_TAC` are values; `unset_jrh_lexer` turns
  the rule off), and the infix words `o`, `upto`, `F_F`, `THEN`, `THENL`,
  `ORELSE`, `THENC`, `ORELSEC`, `THEN_TCL`, `ORELSE_TCL`.
- `grammar.rkt`: `parser-tools/yacc` LALR grammar after OCaml's own
  `parser.mly`, with the HOL infix level between the comparisons and `^`, as
  in `pa_j`, and camlp5's `fun x, y -> e`. The remaining shift/reduce
  conflicts resolve to the shift that OCaml takes.
- `ast.rkt`: the syntax tree.
- `emit.rkt`: the Rhombus writer.
- `main.rkt`: the driver, which also computes imports.

```sh
racket tools/ml2rhm/main.rkt --out OUT HOL-LIGHT-DIR            # every file
racket tools/ml2rhm/main.rkt --out OUT HOL-LIGHT-DIR itab.ml    # some files
racket tools/ml2rhm/coverage.rkt HOL-LIGHT-DIR                  # parse report
python3 tools/ml2rhm/compare.py HOL-LIGHT-DIR OUT                # vs rhombus/hol
tools/ml2rhm/dropin.sh OUT bool drule ...                        # compile in place
tools/ml2rhm/dropin_waterfall.sh OUT                             # Boyer_Moore/ in place, tested
```

`dropin.sh` compiles each generated module in place of the hand-maintained
one, in a scratch copy of the repository. The CI job `ml2rhm` runs all of
these against the pinned HOL Light.

## Results

- All 569 OCaml files of the pinned checkout translate.
- On the 45 modules of the port, the generated code scores 97.6% literal
  (`tools/literalness`; the hand-maintained modules score 95.0%) and is 88%
  token-similar to the hand-maintained modules.
- All 45 compile in place of the hand-maintained module (`dropin.sh`, run by
  the CI job `ml2rhm`).
- The 19 files of `Boyer_Moore/` (with `testset/`) replace the hand-written
  translation together and pass `tests/upstream/boyer_moore.rhm`
  (`dropin_waterfall.sh`, run by the CI job `ml2rhm`). The test imports the
  modules it uses by name: the generated `boyer-moore.rhm` loads the others,
  it does not re-export them.

The output mirrors the checkout: `Library/card.ml` becomes
`OUT/Library/card.rhm`, and `printer.ml` becomes `OUT/printer.rhm`, as in
`rhombus/hol`. printer.ml's `include Format` imports and re-exports
`private/format.rhm`'s `Format`, so later modules take `pp_print_string` and
the rest from the printer, as in HOL Light.

## Translation

The output follows the conventions of the hand-maintained modules:

| OCaml | Rhombus |
|---|---|
| `let f x y = e` | `fun f(x):` / `fun(y):` (one stage per parameter) |
| `let x = e` | `def x = e`, or `def x:` with a block |
| `let x = e in b`, `e1; e2` | block lines `let x = e`, `e1` |
| `let rec f x = ... in` | local `fun f(x): ...` |
| `(a, b)`, `[a; b]`, `h :: t` | `[a, b]`, `PairList [a, b]`, `PairList.cons(h, t)` |
| `ref e`, `!r`, `r := e` | `Box(e)`, `r.value`, `r.value := e` |
| `` `p /\ q` ``, `` `:num` `` | `@hol\|{p /\ q}\|`, `@hol\|{:num}\|` |
| `A THEN B`, `A ORELSE B`, `c1 THENC c2` | `A then_tac B`, `A or_tac B`, `c1 then_conv c2` |
| `f o g`, `x \|-> y`, `m -- n`, `l1 @ l2` | `o(f)(g)`, `fpf_define(x)(y)`, `range(m)(n)`, `append(l1)(l2)` |
| `a = b`, `a <> b`, `a == b`, `s ^ t` | `a == b`, `a != b`, `a === b`, `s +& t` |
| `match e with p -> a \| q when g -> b` | `match e` / `\| p: a` / `\| q when g: b` |
| `try e with Failure _ -> h` | `try:` / `e` / `~catch Failure(_): h` |
| `if c then a else b` | `if c \| a \| b`, or `(if c \| a \| b)` at the end of a line that other lines of a branch follow |
| `C (a, b)` for `C of t * u`, `C (a, b)` for `C of (t * u)` | `C(a, b)`, `C([a, b])` |
| `(+) a b`, `(+) 1` | `a + b`, `(fun(x): fun(y): x + y)(1)` |
| `open Printf` (a Stdlib module of `private/ocaml.rhm`) | its names as `Printf.printf` |
| `type t = A \| B of u` | `variant t:` / `A()` / `B(u)` |
| `type r = {f: u}` | `record R(f)` |
| `exception E of string` | `class E(message)` |
| `module M = struct ... end` | `namespace M:` |
| `x'` | `x_prime` |

Source parentheses around operator expressions are kept. A long chain of one
operator breaks once per operator, with a trailing `\`. Comments between
definitions are kept as `//` lines. A name defined twice gets
`module_NAME_vK` for the earlier definitions. A case `p1 | p2 -> e` whose
patterns bind variables becomes one case per alternative, since Rhombus
or-patterns bind none.

Imports are computed. A file sees the modules HOL Light loads before it: the
sequence of `hol_lib.ml`, then its `needs` closure. A file that a loader of
its directory loads from a list, with `needs`/`loads`/`loadt` or with
`load_on_path` over a literal list of names (`Boyer_Moore/boyer-moore.ml`,
`IsabelleLight/isalight.ml`), also sees the files listed before it, and what
the loader's own loader loaded first; the loading statement itself becomes no
code, as `loads` does. Each free name is
imported, as an `only:` list, from the latest earlier module that defines it.
OCaml Stdlib names come from `private/ocaml.rhm`, which provides them under
their OCaml names (`not`, `max`, `Printf.sprintf`, `OCamlString.sub`,
`OCamlArray.make`, ...). When a module also defines a name it uses before
its own definition, the import is qualified (`IndTypes.list_INDUCT`).

## Limits

- Of 572 files, 569 parse. The three others are not HOL Light OCaml:
  `Mizarlight/pa_f.ml` is a camlp5 extension in revised syntax, and two
  `RichterHilbertAxiomGeometry` files are Mizar-style proof texts.
- Constructor arities come from the declarations of the module and of the
  modules loaded before it; inside a `module ... struct` or `let module`, its
  own declarations come first, and `M.C` uses the arity declared in `M`.
- OCaml keeps constructors and modules apart; Rhombus does not. A constructor
  or exception named like a module of the same file is renamed `NameValue`,
  as in the port (metis.ml's `Atom` beside `module Atom`).
- Functors are expanded where they are applied, `Map.Make` and `Set.Make`
  from the vendored OCaml 4.14.1 `stdlib/map.ml` and `stdlib/set.ml`
  (definitions that need `Seq` are left out). `include M` of a namespace of
  the same file re-exports M's values, constructors and exceptions.
- `let ... and ...` becomes sequential bindings; a right-hand side that
  refers to a shadowed outer name is not detected.
- Comments inside a definition are dropped.
