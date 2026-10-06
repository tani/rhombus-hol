# Direct theory translation

Reference: HOL Light commit `cba9198db76e9dfb89cbd653df9412d01f65b22a`.
The original source files are under `differential/upstream`.

`ast.ml` reads the compiler AST produced by the original HOL Light Camlp5
extension. `translate.py` preserves definitions, curried calls, branches,
pattern matching, exceptions, and proof scripts. Literal quotations use typed
Rhombus macro syntax, for example:

```rhombus
hol_term(Forall("x", Tvar("A"), Eq(Tvar("A"), Ref("x"), Ref("x"))))
```

The macro in `private/quoted_ast.rhm` serializes this syntax at expansion time;
it is never expanded as nested constructor calls. `Forall`, `Eq`, and other
shorthands restore exact constant signatures, while `Ref` restores a bound
variable's original name and type. Unrecognized constants and types stay
explicit. Runtime terms still use the public kernel constructors.
Runtime code
never imports a recorded theorem or adds an axiom to replace a proof.

`record_quotes.ml` runs only inside the original OCaml oracle. It records
inferred quotations and exported theorems for comparison. Unevaluated literal
quotations are read after their source module loads. Repeated quotations must
agree up to bound-variable and polymorphic type-variable renaming.

Compressed compiler ASTs, quotation records, and source SHA-256 values are
saved in `data/`; generation can use them without OCaml. To regenerate oracle
data, set `HOL_LIGHT_SOURCE` to a checkout of the pinned reference with
`pa_j.cmo` built. Requirements: OCaml 4.14, Num, Camlp5 8.02, camlp-streams.
`CAMLP5_RUNNER`, `CAMLP5_LIB`, and `HOL_PORT_STAGE` select local tools/paths.

```sh
export HOL_PORT_STAGE=/tmp/hol-port
python3 tools/translate/prepare.py
ocaml -w -a "$HOL_PORT_STAGE/bootstrap.ml"
python3 tools/translate/translate.py \
  bool simp theorems ind_defs class trivia canon meson firstorder metis \
  thecops quot impconv pair compute nums recursion arith wf calc_num \
  normalizer grobner ind_types lists realax calc_int realarith real \
  calc_rat int sets iterate cart define
HOL_THEORY_TIMEOUT=600 python3 differential/tests/check_foundations.py --all
```

Generation fails on unsupported syntax or missing/context-dependent
quotations. Compilation and theorem comparison must follow generation.
`HOL_PORT_TRACE=1` adds temporary initialization traces; regenerate without it
before committing runtime modules.

`translate.py` also regenerates the private finite-partial-function operations
and type-inference support. `prepare_stdlib.py` selects the unchanged OCaml
4.14.1 Map.Make/Set.Make AVL value groups and their dependencies. Each concrete
functor application specializes these groups with the original comparator.
This preserves tree shape and stateful predicate traversal, including Metis's
random model callbacks. The original OCaml sources and licenses are in `stdlib/`.

Mechanical adaptations include immutable record updates, OCaml tuples as
Rhombus lists (pairs included; OCaml lists are `PairList`), and shared
exception/option representations. Arguments follow Rhombus evaluation order;
the port does not restore OCaml's right-to-left operand evaluation. Local
values use `let`; recursive functions use `fun`.

`private/curried.rhm` implements variadic staged application:

```rhombus
curried fun add(x, y): x + y
// Both add(1)(2) and add(1, 2) return 3.
```

Every unary stage executes as its argument arrives. A partial application
shares the state allocated in its completed stages; a completed application
returns its result unchanged. Extra arguments apply to a function result.
The generator flattens consecutive lambdas into these declarations. For
shadowed parameter names it retains the explicit staged declaration. Lambdas
separated by computation keep that computation at its original stage. Calls
are grouped only when their callee has a known staged arity and later
argument expressions are pure. Arbitrary callbacks retain unary calls.

`variant` declarations derive comparison tags from original constructor order;
`record` declarations derive comparison views and immutable `port_update`.
`tools/translate/fields.py` records payload names from the pinned source; a
missing layout fails generation. Constructor and field order never change.
Kernel constructors retain their separate private, opaque implementation.

Nested modules use their own scope for short names. Redefined or conflicting
bindings keep short suffixes. Public namespace names use export renames so
they do not create local bindings that capture references to parent scopes.
Imported names are opened selectively only when
no original binding can capture them; namespace aliases remain qualified.
Proof operators (`then_tac`, `then_list`, `or_tac`, `then_conv`, `or_conv`)
expand the original combinators, retaining the original expression tree.
The generator formats long calls and branches with indentation and uses
`PairList [a, b, & tail]` instead of chains of list constructors.

`Hashtbl` is a Rhombus `MutableMap` from each key to its stack of bindings
(`add` shadows, `remove` restores); `fold` visits bindings newest first.
Bucket iteration order is not an OCaml-compatible API. The source AVL functors preserve tree structure; Patricia term maps retain
the original traversal. Set predicates and Map.exists retain their recorded
callback traces. Map.merge has a preexisting evaluation-order difference: its
callbacks run in ascending key order here, versus descending order in OCaml.
The `check_stdlib.py` oracle still reports that difference without changing
its expected trace. It is also present in the checkout before this readability
refactor.

The theories replay their original proof scripts. Timing and Format diagnostic
output are compatibility stubs; they are not a HOL text printer. Internal
pretype/type-inference algorithms serve Metis reconstruction and declaration
metadata. The inductive type-description API is a small Rhombus-native frontend.
There is no runtime HOL term text parser. The native string helpers are used on
the standard theories' ASCII text; a general OCaml byte-string frontend is
outside this port.

Checks:

```sh
python3 differential/tests/check_runtime.py
python3 differential/tests/check_stdlib.py
python3 differential/tests/check_translation.py
HOL_THEORY_TIMEOUT=600 python3 differential/tests/check_foundations.py --all
python3 tools/translate/snapshot.py
```

The theorem comparator normalizes only bound term names and polymorphic type
variable names. It compares every hypothesis and conclusion and rejects any
kernel axiom outside ETA_AX, SELECT_AX, and INFINITY_AX. Saved expected theorems
are read only by the differential harness, never by runtime theory modules.

Saved verification: all 2,979 exported theorems in the 34 standard modules
match the pinned original. See [verification.json](verification.json). The
engine also passes 3,912 differential cases and 58 local tests. The generated
translation regressions add seven checks against inherited binding capture,
included nested namespaces, and curried declarations whose original names
contain apostrophes.
