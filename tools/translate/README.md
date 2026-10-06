# Direct theory translation

Reference: HOL Light commit `cba9198db76e9dfb89cbd653df9412d01f65b22a`.
The original source files are under `differential/upstream`.

`ast.ml` reads the compiler AST produced by the original HOL Light Camlp5
extension. `translate.py` preserves definitions, curried calls, branches,
pattern matching, exceptions, and proof scripts. Literal quotations become
compact JSON data containing their offline-inferred, typed constructor ASTs.
`private/quoted_ast.rhm` materializes those data through the existing public
kernel term/type constructors. This avoids compiling thousands of repeated
nested constructor expressions. JSON strings are normalized to immutable
Rhombus strings before constructor matching. Runtime code
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

Mechanical adaptations include curried calls, immutable record maps with
declared field order, OCaml tuples as Rhombus lists (pairs included; OCaml lists are `PairList`),
record types as classes with a `port_update` method, and shared exception/option representations. Effectful
arguments and constructor fields preserve OCaml's right-to-left evaluation;
simultaneous value bindings preserve their left-to-right evaluation. Unit
callbacks accept one unit value and are bridged to the existing zero-argument
native engine functions. Local values use `let`; recursive functions use `fun`. Translated modules are
imported under capitalized namespaces (`Fusion`, `Tactics`, ...). A top-level
value defined once keeps its HOL Light name; nested modules and redefinitions
use module-prefixed names. Generated files start with a DO NOT EDIT header.

`Hashtbl` is a Rhombus `MutableMap` from each key to its stack of bindings
(`add` shadows, `remove` restores); `fold` visits bindings newest first.
Bucket iteration order is not an OCaml-compatible API. The source AVL functors and the
Patricia term maps preserve the traversal required by the standard proofs.

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
HOL_THEORY_TIMEOUT=600 python3 differential/tests/check_foundations.py --all
python3 tools/translate/snapshot.py
```

The theorem comparator normalizes only bound term names and polymorphic type
variable names. It compares every hypothesis and conclusion and rejects any
kernel axiom outside ETA_AX, SELECT_AX, and INFINITY_AX. Saved expected theorems
are read only by the differential harness, never by runtime theory modules.

Saved verification: all 2,979 exported theorems in the 34 standard modules
match the pinned original. See [verification.json](verification.json). The
engine also passes 3,912 differential cases and 25 local tests.
