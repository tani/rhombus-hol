# Rhombus/HOL frontend

A Rhombus language for programs that are also HOL definitions. A module
written with the frontend's forms runs as ordinary Rhombus code; a separate
check turns the same declarations into HOL Light definitions in the port's
kernel and proves its theorems with an extended Boyer-Moore waterfall. There
are no tactics: a theorem is proved automatically or not at all, with hints in
an optional `proof:` block.

```rhombus
#lang rhombus
import:
  rhombus/frontend/main open   // or a relative path to main.rhm

datatype Tree(?a)
| Leaf
| Node(left :: Tree(?a), value :: ?a, right :: Tree(?a))

function mirror(t :: Tree(?a)) :: Tree(?a):
  match t
  | Leaf: Leaf
  | Node(l, x, r): Node(mirror(r), x, mirror(l))

theorem mirror_mirror(t :: Tree(?a)):
  mirror(mirror(t)) == t
proof:
  induct: t
```

Run it: `racket file.rhm` (theorems do nothing at run time).
Check it: `racket rhombus/frontend/check.rhm file.rhm ...`, which prints
each declaration's HOL theorem or why it failed and exits with status 1 when
anything failed. `FRONTEND_TRACE=1` also prints the HOL Light text of each
declaration; `FRONTEND_TRACE=raise` lets the first error escape.

## Forms

- `datatype Name(?a, ...)` followed by `| Ctor(field :: type, ...)` lines.
  Further types of a mutually recursive group follow as `and Name(...)` groups.
  A field may use an earlier datatype applied to this one (a nested type).
  Executable: one class per constructor (fields by name, `==` structural); a
  constructor without fields is a value.
- `function name(x :: type, ...) :: type: body`, and `and name(...)` groups for
  mutual recursion. The body is an expression; `let x = e` lines may come
  before it.
- `theorem name(x :: type, ...): statement`, a Bool expression whose
  parameters are read universally.
- `proof:` after a form, with lines `use: name ...` (theorems or functions to
  use as rewrite rules), `disable: name ...` (rules to leave out), and
  `induct: x` (the variable of the first induction).

Types: `Nat` (HOL's `num`), `Bool`, type variables `?a`, datatypes.
Expressions: variables, Nat literals, `#true`/`#false`, calls, `+ - * div mod`
(`-` truncates at 0, `x div 0 = 0`, `x mod 0 = x`, as in HOL), comparisons
`== != < <= > >=` (not chained), `&& || ! ==>`, `if c | a | b`, `match`.
Patterns: `_`, variables, `Ctor(p, ...)`, a capitalized name (a constructor
without fields), `0`, `p + 1`.

## How it works

| file | role |
|---|---|
| `ir.rhm` | declarations, types, expressions and patterns as values |
| `parse.rhm` | shrubbery to IR, at expansion time |
| `main.rhm` | the forms: executable code from the IR, plus a run-time record of the IR |
| `runtime.rhm` | the record (`declare`), datatype values, Nat operations |
| `logic.rhm` | IR to HOL Light text, read by `../hol/parser.rhm`: `define_type`, `define` / `new_recursive_definition`, Boyer-Moore proofs |
| `check.rhm` | instantiates modules and runs `logic.rhm` over their records |
| `bm/` | the extended Boyer-Moore prover |

A `match` on a parameter becomes one equation per constructor (Nat: `0`,
`SUC n`), the form of a HOL Light pattern-matching definition; `let` is
inlined; a literal `n > 1` gets the rewrite `n = SUC (n - 1)` (`num_CONV`).
Each proved theorem becomes a rewrite rule for later theorems.

`bm/` started from `tools/ml2rhm`'s translation of HOL Light's `Boyer_Moore/`
and is edited freely; `rhombus/hol/Boyer_Moore/` stays the literal port. The
extensions so far: shells for types made by `define_type` (`define_shell`),
an induction variable hint, per-proof `use`/`disable` rules (`bm/bm.rhm`).

## Limits (next steps)

- No Boyer-Moore shell, hence no induction, for mutual or nested types: their
  functions are defined, theorems about them are not proved yet.
- `match` only on a function parameter, without nested patterns; Nat literal
  patterns other than `0`.
- `inductive` (inductive predicates with intro/induct/cases rules) is not
  implemented yet.
- Loading the HOL theories for a check takes a few minutes.
