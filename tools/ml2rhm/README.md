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
```

`dropin.sh` compiles each generated module in place of the hand-maintained
one, in a scratch copy of the repository. The CI job `ml2rhm` runs all of
these against the pinned HOL Light.

## Results

- All 569 OCaml files of the pinned checkout translate.
- On the 44 modules of the port, the generated code scores 97.6% literal
  (`tools/literalness`; the hand-maintained modules score 95.0%) and is 88%
  token-similar to the hand-maintained modules.
- 38 of the 44 compile in place of the hand-maintained module. The six that
  do not are:
  - `equal`, `tactics`, `metis` and `thecops`, which call printer functions
    that the port does not have;
  - `lib`, which uses `Printexc` and file I/O;
  - `impconv`, whose `let module Tset = struct ... end in` defines names its
    enclosing block already binds.

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
| `if c then a else b` | `if c \| a \| b` |
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
sequence of `hol_lib.ml`, then its `needs` closure. Each free name is
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
  modules loaded before it; a module that redeclares a constructor name
  (compute.ml's `Const`) uses its own arity throughout.
- `let ... and ...` becomes sequential bindings; a right-hand side that
  refers to a shadowed outer name is not detected.
- Comments inside a definition are dropped.
