# Rhombus/HOL Language Specification

## Status and scope

This is the normative specification for the `#lang rhombus/hol` surface
language. The frontend, derived prover, executable lowering, and standard
library specified here are implemented in `rhombus-hol-prover` and
`rhombus-hol-stdlib`, built over the verified kernel in `rhombus-hol-kernel`.
This document remains the normative reference for the language's required
behavior: where the implementation and this specification disagree on a
point this document covers, that is an implementation defect to fix, not a
specification to relax.

This document specifies the language layer, the logical effect of declarations,
and the required trust and execution boundaries. It does **not** specify a
standard library of proved datatypes and functions. Library types such as
`List.of` and `Integer` appear only as examples of syntax the language must
support. `String` is the sole exception: section 7.5 fixes its representation
because string literal syntax depends on it.

The governing design rule is a largest clean intersection of Rhombus and HOL:
use normal Rhombus syntax when it has a direct total HOL meaning; lower surface
sugar to ordinary HOL terms; do not add a kernel primitive when lambda,
application, equality, definitions, and derived datatype or recursion machinery
already suffice.

## 1. Module model

A `#lang rhombus/hol` module is an ordinary Rhombus module that may contain
logical declarations. A logical declaration is read from one source expansion
in two ways:

- **Logical reading.** It extends an immutable HOL theory with derived
  constants, definitions, datatype theorems, or a checked theorem.
- **Executable reading.** Where defined, it emits ordinary Rhombus code. A
  datatype emits classes; a `function` emits a Rhombus function. Types and
  proof-only constructs are erased.

Both readings consume the same normalized Core representation. A construct must
not be parsed once for logic and reconstructed independently for runtime.

Proofs and termination checks run while the module is compiled. A theorem that
cannot be proved, a function that cannot be shown total, or an ill-formed
logical declaration is a compile-time error with the remaining goals or
obligation. At runtime, logical proofs do not execute.

Only the declaration forms in this document receive a logical reading. Ordinary
Rhombus `fun`, `def`, `class`, `operator`, and all other ordinary forms retain
their ordinary Rhombus meaning and have no implicit theorem-prover effect. In
particular, `fun` is never a logical definition; the distinct keyword
`function` is required for a declaration with both readings.

Logical declarations are module-body forms. A user declaration macro may expand
to them, preserving source expansion order, but the resulting declaration must
ultimately occur in a module body, not in a `block`, `fun`, or method body.

## 2. Theories, imports, and scope

A theory is an immutable value with a lineage stamp. A theorem belongs to the
theory in which it was proved. Kernel rules may combine only theorems on one
extension chain; theorems from sibling theories are rejected.

An ordinary Rhombus import of a `#lang rhombus/hol` module imports both halves:

```rhombus
import:
  "list_proofs.rhm" open
```

- Runtime bindings are imported by normal Rhombus import semantics.
- The importing module adopts the exported `hol_theory` value itself, including
  its transitive imports, declarations, theorem objects, and overload registry.
  It does not reparse or reassert a textual description of that theory.
- An ordinary module with no `hol_theory` submodule remains an ordinary import.

Theory imports must precede the importing module's own logical declarations.
Multiple theory imports must appear in dependency order. Importing an unrelated
sibling theory is an error: a module has one linear theory lineage, not a merge
of independently extended worlds. If an import names a theory in a module-path
form the frontend cannot inspect, it is an error rather than silently losing the
logical import.

A preceding logical declaration is in scope for all later logical declarations.
A declaration name is not in scope within its own body unless that declaration
form explicitly supports recursion.

## 3. Types

```text
Type ::= Id
       | Id.of(Type, ...)
       | ?a
       | Type -> Type
       | (Type)
       | Boolean
```

- `Id` names a declared nullary type constructor.
- `Id.of(T, ...)` applies a parameterized type constructor. A declaration
  `datatype List.of(?a)` binds `List.of`, not a bare `List` type.
- `?a`, `?b`, and so on are type variables. A top-level function or definition
  is implicitly polymorphic in every type variable in its declared type; there
  is no type-level `forall` syntax.
- `A -> B -> C` means `A -> (B -> C)`.
- `Boolean` is the proposition type and has the same meaning in both logical
  and executable readings.

Elaboration unifies types before producing a kernel term. Overload resolution
uses that type information, but the kernel term and generated runtime code
contain the selected implementation directly and contain no overload node or
runtime type test.

## 4. Declaration forms

### 4.1 `datatype`

```rhombus
datatype TypeName
| Constructor()
| Constructor(field :: Type, ...)

datatype TypeName.of(?a, ...)
| Constructor()
| Constructor(field :: Type, ...)
```

The block spelling is equivalent, and `()` may be omitted for a nullary
constructor in the declaration head. Expressions and patterns use constructor
application syntax, such as `zero()`.

```rhombus
datatype List.of(?a)
| Nil()
| Cons(head :: ?a, tail :: List.of(?a))
```

A datatype declaration must be strictly positive: the datatype being declared
must not occur to the left of an arrow in one of its own fields. It must be
inhabited; in particular, a recursive datatype needs a non-recursive
constructor. Duplicate type parameters, constructors, and undeclared type
variables in fields are errors.

Its logical reading derives, without a per-declaration axiom:

- constructor constants;
- injectivity theorems for constructor fields;
- distinctness theorems for different constructors;
- a cases/exhaustiveness theorem and an induction theorem;
- constructor discriminator functions `is_Constructor`;
- field selector functions `Constructor_field` and their equations;
- guarded destructor-elimination equations; and
- for a recursive datatype, a derived well-founded subterm relation
  `TypeName_lt`.

The derived equations enter the rewrite database. They make constructor tests,
selector applications, and pattern-defined functions reduce during proofs.

The executable reading emits one ordinary Rhombus class per constructor, with a
shared interface for matching, structural equality, readable printing, fields,
and constructor calls. It does not introduce a distinct runtime representation
unrelated to the logical declaration.

#### Mutually recursive datatypes

```rhombus
datatype.together:
  datatype Expr
  | lit(value :: Nat)
  | app(args :: Args)
  datatype Args
  | anil()
  | acons(head :: Expr, tail :: Args)
```

A `datatype.together:` block declares a family of datatypes simultaneously:
a constructor field may be at any member of the family. Every member must
declare the same type parameters, every constructor name in the family must
be distinct, and each member must be inhabited by values the family's own
constructors build. A single `datatype` declaration is the one-member case of
this form, and the two spellings share one implementation.

A family is read as one ordinary self-recursive datatype -- the union of every
member's constructors, with a field at a member replaced by the union type --
with each member carved out of it as the set of values its own constructors
build. Those membership predicates are the least ones closed under the
constructors, which is `inductive`'s construction, so a family needs no
representation, no definition principle and no trusted operation that a single
datatype does not.

Each member derives everything a single declaration derives, stated about its
own constructors: injectivity, distinctness, cases, discriminators, selectors,
destructor elimination, structural induction whose hypotheses are about its own
recursive fields, and its subterm relation when it has one. The family's joint
induction, whose hypotheses may be about any member, is retained by name as
`<Member1>_..._union_induct` and requested in a proof with `~use:`.

The family's union type also gives the whole family one well-founded order,
which is what a `function.together:` recursion over it descends in.

### 4.2 `function`

```rhombus
function name(arg :: Type, ...) :: ResultType:
  body

function name(arg :: Type, ...) :: ResultType
| (pattern, ...): body
| ...

proof:
  ~measure: expression
```

`function` declares a total function with both readings. Its result type is
explicit. The body must use the pure total body grammar in section 5.

The two clause spellings normalize to one ordered pattern matrix. The matrix
must be exhaustive, and every row must win for some input shape after preceding
rows have priority. Overlap is allowed; first matching row wins in both logical
and executable readings. An unreachable row is an error.

For a non-recursive function, the frontend compiles the checked pattern matrix
to a closed decision-tree term and conservatively defines it. For a recursive
function, it derives the same clausal equations through well-founded recursion
only after the termination check in section 8 succeeds. One theorem per winning
clause is registered as a rewrite rule.

The executable reading emits a Rhombus `fun` over the same ordered clauses, with
HOL type annotations erased. The emitted function is required to agree with the
same normalized Core decision tree used by the logical reading.

A recursive definition is never assumed. It is either derived from an accepted
well-founded order or rejected.

#### Mutually recursive functions

```rhombus
function.together:
  function a_size(a :: Args) :: Nat
  | (anil()): zero()
  | (acons(e, r)): plus(e_size(e), a_size(r))
  function e_size(e :: Expr) :: Nat
  | (lit(n)): succ(zero())
  | (app(a)): succ(a_size(a))
```

A `function.together:` block declares a family of functions simultaneously:
a member's body may call any member of the family. Every member declares each
parameter type and its result type, since the members are elaborated against
each other rather than inferred from their bodies, and all members use the
same type variables. A member of a family is called with all of its arguments.
A single `function` declaration is the one-member case of this form.

A family is read as one ordinary function over a tagged argument: a domain
datatype with one constructor per member carrying that member's parameters,
and, when the members' result types differ, a result datatype tagging them the
same way. That combined function is derived by the well-founded machinery an
ordinary recursive `function` already uses, and each member is then the
non-recursive definition that tags its arguments and reads the result back.
Each member's clausal equations are derived from the combined function's and
registered as rewrite rules, so a proof sees the members, never the encoding.

A recursive call in a family leaves the member that made it, so the descent
order has to span the family. Either every member supplies a
`proof: ~measure: expression` into one common declared datatype, or none does
and the family descends structurally: one argument column per member, at a
common recursive datatype -- or at the union type of a datatype family, which
is what relates values of different members of it -- such that every call
between members reaches a strict subterm. A family that does neither is
rejected, exactly as a single function that terminates for no visible reason
is.

A member's `proof:` block is the ordinary one: it sits adjacent to that
member inside the block and carries exactly one `~measure:`. The members'
measures are read as one measure over the tag, so they must land in the same
type, and a measure may not call a member of its own family: it justifies the
family's definition and so cannot use it.

The executable reading is one Rhombus `fun` per member, calling each other
directly; the tagging is logical only.

### 4.3 `definition`

```rhombus
definition name(arg :: Type, ...) :: ResultType:
  expression
```

`definition` introduces a logical, non-recursive constant when an executable
Rhombus function is neither supplied nor required.

```rhombus
definition id(x :: ?a) :: ?a:
  x

definition chosen(p :: ?a -> Boolean) :: ?a:
  select (x :: ?a): p(x)
```

A declaration with arguments `x1, ..., xn` and body `e` introduces the fresh
constant

```text
name : T1 -> ... -> Tn -> ResultType
```

and the theorem

```text
|- name = \x1. ... \xn. e
```

The frontend elaborates `e` using the logical expression policy, lambda-binds
the declared arguments, and makes one `new_basic_definition` call. It does not
call `new_constant` first. The kernel atomically installs the constant and its
definition theorem; the theorem is an oriented rewrite rule for later logical
declarations and proofs.

`definition` has no executable reading. It emits no Rhombus binding, cannot be
called from ordinary Rhombus code, an executable `function` body, or
`quickcheck`, and has no runtime fallback.

The following are static errors:

- a name already present in the current theory;
- a body whose lambda-abstracted type differs from the declared type;
- a body that is not closed after abstraction;
- a body with a type variable absent from the declared type;
- a reference to the definition being declared; and
- pattern clauses, `proof:`, a measure, or any executable-definition option.

Thus `definition` has no termination check: it cannot introduce recursion. It
is the appropriate form for specification-level or choice-based HOL constants.
Use `function` when an executable meaning is required.

### 4.4 `inductive`

```rhombus
inductive name(Type, ...)
| rule_name: proposition
| ...

inductive.together:
  inductive name(Type, ...)
  | rule_name: proposition
  | ...
  inductive name(Type, ...)
  | rule_name: proposition
  | ...
```

`inductive` introduces the least predicates closed under the given rules. Each
head lists one predicate's argument types; each rule is a closed proposition
about the predicates being declared, so it quantifies over its own variables.

```rhombus
inductive spine(Tree)
| spine_leaf: spine(leaf())
| spine_node: forall (r :: Tree): spine(r) ==> spine(node(leaf(), r))
```

A rule has the form

```text
forall y1 ... ym. Q1 ==> ... ==> Qj ==> name(a1, ..., an)
```

and the declaration introduces one constant
`name : T1 -> ... -> Tn -> Boolean` per head, each with a single definition

```text
|- name_j = \x1. ... \xn. !P1 ... Pm. R1[P] ==> ... ==> Rk[P] ==> Pj x1 ... xn
```

where `Ri[P]` is rule `i` with each declared name replaced by the
corresponding quantified `Pj`: predicate `j` is the `j`-th component of the
intersection of every predicate family the rules are closed under. Each is one
`new_basic_definition` call, so `inductive` adds no axiom and no new
definition principle.

Predicates declared in one `inductive.together:` block are mutually
recursive: the block's rules are shared, so all of them are premises of every
definition and a rule may conclude with any of the declared predicates. A
single `inductive` is this same construction with a one-element family.

From those definitions the declaration derives, by kernel rules only:

- one introduction theorem per rule, named by the rule, stating `Ri[name]`;
- `name_induct` per predicate, stating
  `!P1 ... Pm. R1[P] ==> ... ==> Rk[P] ==> !x. name_j x ==> Pj x`; and
- `name_cases` per predicate, stating that membership came from some rule
  concluding with that predicate: `!x. name_j x ==> (D1 or ... or Dr)`, where
  `Di` is `?y1 ... ym. Q1 and ... and Qj and x1 = a1 and ... and xn = an` for
  such a rule `i`. A predicate with no rules gets `!x. name_j x ==> false`.

The derived theorems are retained by name, exactly as a `theorem` is, and are
requested in a later proof with `~use:`. Neither the definition nor the derived
theorems enter the rewriter, so the automation never unfolds the fixed point on
its own.

The rules must describe a monotone operator, which is what makes the least
predicate closed under them and the introduction theorems derivable. The
following are static errors:

- a rule that does not conclude with a declared predicate applied to its
  arguments;
- an occurrence of a declared predicate in a negative position of a premise,
  that is under `not` or to the left of a nested `==>`;
- an occurrence of a declared predicate that is not applied to arguments,
  including one passed to another function or compared with `===`;
- an occurrence of a declared predicate inside a rule's own arguments;
- the same predicate name declared twice in one family; and
- a rule name, `name_induct` or `name_cases` that is already a theorem in the
  current theory.

`inductive` has no executable reading: like `definition`, it emits no Rhombus
binding.

### 4.5 `theorem` and `proof`

```rhombus
theorem name:
  proposition

proof:
  ~induct: variable
  ~split: proposition
  ~choose: expression
  ~use: [theorem, ...]
  ~skip: [stage, ...]
  ~disable: [rule, ...]
  ~limit: nonnegative_integer
  ~extensionality: variable
```

A theorem is elaborated as a Boolean HOL term and proved during compilation.
Its successful theorem object is retained under `name`, but it is **not** added
to the global rewrite database merely because it exists. A later proof enables
it explicitly with `~use`; adding an unrelated theorem must not silently change
automation.

The `proof:` block is optional. Its options only control proof search; none can
admit a false proposition.

- `~induct:` chooses the induction variable once.
- `~split:` adds a Boolean case split; it may repeat.
- `~choose:` supplies an existential witness; it may repeat.
- `~use:` enables listed theorem(s) for this proof only; it may repeat in source
  order.
- `~disable:` disables selected rewrite rule(s) for this proof only.
- `~skip:` skips selected named waterfall stages for this proof only.
- `~limit:` sets the nonnegative proof-step limit once.
- `~extensionality:` names a fresh variable and reduces an equality of functions
  (including predicate-encoded sets) to its pointwise equality. It is a
  compile-time error for any other goal shape.

### 4.6 `notation`

```rhombus
notation left operator right:
  ~order: hol_addition
  target_function
```

`notation` adds a spelling only to the HOL expression space. Prefix, infix,
postfix, immediate cases, and grouped cases follow Rhombus `operator` syntax;
operands must be identifiers. Every use lowers to a call of the final target
function with operands in source order. The target may itself be overloaded.

Notation adds no constant or theorem and creates no ordinary Rhombus operator.
If executable code needs the same spelling outside a logical declaration, it
must declare an ordinary Rhombus `operator` separately. Notation is visible to
the declarations that follow it and is exported explicitly with
`only_space hol_expr`.

The available named precedence levels, strongest first, are:

```text
hol_application
hol_power
hol_prefix_arithmetic
hol_multiplication
hol_addition
hol_append
hol_set_intersection
hol_set_union
hol_relation
hol_equality
hol_negation
hol_conjunction
hol_disjunction
hol_implication
hol_equivalence
```

The usual Rhombus precedence and associativity options (`~order`,
`~stronger_than`, `~weaker_than`, `~same_as`, `~same_on_left_as`,
`~same_on_right_as`, and `~associativity`) apply.

### 4.7 `overload`

```rhombus
overload public_name(ArgumentType, ...) = implementation
overload public_name(ArgumentType, ...) :: ResultType = implementation
overload public_name(arg :: ArgumentType, ...) = implementation(arg, ...)
```

An overload declaration adds a typed clause for one callable name. A direct
call and notation targeting that name share exactly one resolver.

The resolver uses first-order unification of the complete argument tuple and,
when known, the expected result type. It selects one implementation constant
at elaboration time. All clauses for a public name have the same arity and must
not overlap; an ambiguous or inapplicable call is a compile-time error listing
available candidates. A zero-argument call may use its expected result type.

A template is needed when implementation argument order differs from public
argument order. It must use every public argument exactly once. There is no
runtime dispatch, implicit numeric coercion, or overload term in HOL.

The language-reserved notation-facing names are `add`, `subtract`, `negate`,
`multiply`, `power`, `less`, `less_equal`, `greater`, `greater_equal`,
`append`, `member`, `union`, and `intersection`. Their implementations are
library or module declarations, not language primitives.

### 4.8 `quickcheck`

```rhombus
quickcheck name:
  forall (arg :: ConcreteType, ...): proposition

quickcheck name(~samples: n, ~size: n, ~seed: n):
  forall (arg :: ConcreteType, ...): proposition
```

`quickcheck` runs the executable reading of a universally quantified property
over generated concrete values. It adds no theorem and no theory content. A
passing check is testing evidence, not proof; a failing check aborts module
initialization with a shrunk counterexample, its effective seed, and shrink
count.

Input types must have registered runtime generators and shrinkers. The property
must have an executable reading: executable calls, conditionals, Boolean
connectives, equality, literals, and statically resolved overloads are allowed;
implication, existential quantification, `exists1`, `select`, `wf`, and other
logic-only terms are rejected. `~samples` sets the number of input tuples,
`~size` bounds generated depth, and `~seed` makes the run reproducible.

## 5. Function bodies and expressions

A top-level `function` body is a sequence whose final expression is its value:

```text
body ::= expression
       | let Id = expression; body
       | let pattern = expression; body
       | function Id(args) :: Type: body; body
       | match expression | pattern: body | ...
```

`let` and `match` are body forms, not arbitrary expression operands. A pattern
`let` must be irrefutable. Logical lowering substitutes a `let` initializer at
its uses; executable lowering preserves ordinary evaluation. Termination
analysis considers both readings, so a discarded runtime initializer may not
hide a non-descending recursive call.

Named and anonymous `function` forms inside a `function`, theorem expression,
or `definition` body are lambdas, not top-level recursive declarations:

```rhombus
function make_succ() :: Nat -> Nat:
  function (x :: Nat) :: Nat: succ(x)
```

A named local function is sequential `let` sugar. It may capture earlier local
bindings and enclosing parameters, but may not refer to itself, a later local
function, or the enclosing top-level recursive function through a nested binder.
Local and anonymous parameter or result types may be inferred from context.

Supported expressions are identifiers; named application; literals; calls via
notation; type ascription `expression :: Type`; parenthesized expressions;
anonymous/case-clause lambdas; `block: body`; `match`; `if`; `cond`; Boolean
operators; arithmetic, relation, append, and set operators. Runtime-only or
effectful Rhombus expressions are not admitted in a logical/executable function
body.

```rhombus
cond
| guard: result
| ...
| ~else: result
```

`cond` tests guards top-to-bottom, requires a final last `~else`, and lowers to
right-nested `if` in both readings.

## 6. Patterns and matching

Patterns occur in match clauses, top-level function rows, local irrefutable
bindings, and binders where the grammar permits them:

```text
pattern ::= _ | Id | Constructor(pattern, ...)
          | NonnegativeInteger
          | [] | [pattern, ...] | [pattern, ..., & rest]
          | Pair(pattern, pattern)
          | #true | #false
          | "string literal"
          | (pattern :: Type)
```

Patterns may nest arbitrarily. `_` matches and binds nothing. Constructor,
Boolean, pair, list, and numeral patterns refine a pattern matrix. Rows are
ordered, but totality is mandatory: every constructor shape must be covered and
every written row must be reachable.

List expression and pattern syntax desugars through constructors supplied by a
list datatype:

```rhombus
[]
[x, y, & rest]
```

`Pair(x, y)` is the product form. Boolean patterns are complete only when both
`#true` and `#false` are covered or a catch-all covers the remainder.

String literal patterns are constructor patterns as specified in section 7.5;
they are not a separate matching mechanism.

A nested `match` may refine an already-bound subposition, but may not re-match a
position already refined by an enclosing pattern. This preserves one pattern
matrix with unambiguous variable scopes and decision-tree compilation.

## 7. Propositions, sets, operators, and literals

### 7.1 Propositions

A theorem statement uses the same HOL expression space with a proposition
admissibility policy:

```text
prop ::= expression
       | not prop | prop and prop | prop or prop
       | prop ==> prop | prop <=> prop | prop === prop
       | forall (Id :: Type, ...): prop
       | exists (Id :: Type, ...): prop
       | exists1 (Id :: Type): prop
       | select (Id :: Type): prop
       | Set{} | Set{expression, ...} | Set{Id :: Type | prop}
       | if prop | prop | prop | cond ...
```

`forall` and `exists` accept one or more binders. `exists1` and `select` accept
exactly one. Binder types may be inferred where their use determines a unique
type. A quantifier extends as far right as possible.

Logical spellings are `not`, `and`, `or`, `===`, `==>`, and `<=>`. Equality and
equivalence denote the same polymorphic equality constant but have different
precedence. Named logical constants include `true`, `false`, `eq`, `imp`,
`conj`, `disj`, `neg`, `exists1`, `select`, and `wf`.

`true`, `false`, equality, conjunction, disjunction, and negation have both
readings. `imp`, `exists1`, `select`, and `wf` are logic-only. Existential and
choice constructs consequently cannot occur in executable `function` bodies or
`quickcheck` properties.

### 7.2 Sets

A set is a predicate of type `?a -> Boolean`, not a separate kernel type:

- `Set{}` is the always-false predicate.
- `Set{a, ...}` is membership by a disjunction of equalities.
- `Set{x :: T | p}` is `function (x :: T) :: Boolean: p`.

Set membership is ordinary application. Set equality is function equality and
is proved with theorem option `~extensionality:`.

### 7.3 Operator behavior and precedence

In an executable body, Rhombus spellings have their ordinary counterparts:
`#true`/`#false`, `!`, `&&`, `||`, and `==`. In propositions, use logical
spellings described above. `&&` and `||` short-circuit at runtime, while `and`
and `or` are strict logically; totality makes this difference unobservable in
valid function bodies.

`+`, `-`, unary `-`, `*`, `**`, comparisons, `++`, `in`, `union`, and
`intersect` lower to the named overloadable calls from section 4.7. `**`, `++`,
and `==>` are right-associative. Multiplication, addition, set intersection,
set union, conjunction, and disjunction are left-associative. Relations and
equality are non-associative: `a < b < c` and `a === b === c` are errors.

### 7.4 Native numerals

A nonnegative numeral is accepted only when its type is determined by context.
A lexical negative numeral is `negate(nonnegative-numeral)` and therefore
requires a selected `negate` overload. There are no implicit numeric coercions.

The standard language-supported natural type is the kernel-reserved `Nat` with
`zero` and `succ`. The accelerated numeric backend is part of the language
contract: a `Nat` literal is a compact canonical value, and construction,
closed equality, ordering, and arithmetic are performed by checked native
numeric conversions rather than a number-of-successors term walk. Native code
may select a conversion step, but the result must be a kernel theorem; it cannot
assert arithmetic on the host runtime's authority.

The same compact representation is required in patterns. A `Nat` literal
pattern is an atomic numeric discrimination, justified by the native numeric
equality conversion; it must not expand to `succ(...succ(zero())...)`. User
functions still observe the ordinary `zero`/`succ` equations when they match
those constructors. The frontend may expose a compact value to such a function
only by applying the kernel-checked conversion appropriate to that equation.

#### Kernel literal representation

The compact value is a kernel-internal canonical term form `NatLit(n)`, where
`n` is a host nonnegative integer payload. It is not a new HOL constant, an
axiom, or user-written syntax. It is a compact representation of the existing
Peano value:

```text
NatLit(0)     = zero()
NatLit(n + 1) = succ(NatLit(n))
```

The Isabelle model, term checker, type checker, substitution operations, term
ordering, code generator, and Rhombus kernel ABI must all recognize `NatLit`.
It is well-typed only as the reserved object-language `Nat` type, and its
denotation is exactly the corresponding HOLZF natural. The public kernel facade
may construct it only through `mk_nat_lit(theory, n)` and inspect it through
`dest_nat_lit`; raw ABI construction remains unavailable to clients.

`NAT_LIT_CONV` and `NAT_CASE_CONV` are theorem-producing kernel conversions.
The former exposes the equations above without materializing the predecessor
chain; the latter produces the checked zero/successor case theorem used by a
literal pattern or ordinary `match` on a compact value. Closed native
arithmetic, equality, and order conversions likewise return a `Thm`. This
preserves the existing Peano equations for user definitions while making a
literal and a literal-pattern constant size.

### 7.5 String data

`String` is an immutable finite sequence of natural-number codepoints:

```rhombus
datatype String
| text(codepoints :: List.of(Nat))
```

This is intentionally the complete logical representation. There is no `Char`
datatype, no 21-Boolean-field record, and no second numeric encoding. A string
literal maps every source Unicode scalar value to its corresponding native
`Nat` value. Equality, matching, and recursion operate on the resulting
codepoint sequence. They are not byte equality, UTF-8 equality, host-language
string identity, Unicode-normalized equality, or grapheme-cluster equality.
Consequently, canonically distinct source scalar sequences remain distinct:
`"e\u0301"` and `"\u00e9"` are not equal unless a user-defined normalization
function proves them equal.

`String` is nominal because it is wrapped by `text`; it cannot be accidentally
interchanged with `List.of(Nat)`. The wrapper does not hide the data from HOL:
its ordinary selector exposes the codepoint list for library definitions.
Values manually constructed with `text` may contain any `Nat`; literal syntax
itself produces only source Unicode scalar values. Unicode validity checks,
normalization, encoding, and character classification are ordinary library
functions, not a refinement type or frontend policy.

#### Literal elaboration

String literals are context-directed values of type `String`. The lexer accepts
source Unicode scalar values; elaboration rejects no non-ASCII scalar merely for
its magnitude. A literal expands through ordinary declared constructors and the
native `Nat` literal path:

```text
""       => text(nil())
"ab"     => text(cons(97, cons(98, nil())))
```

The same Core tree drives logical elaboration and runtime emission. Runtime
emission may use an efficient host representation, but it must produce the same
`text`/`cons`/native-`Nat` value that the logical reading denotes.

Literal size is proportional to the number of source scalars: one `text` node,
one list cell, and one compact `Nat` literal per scalar. Native numeric
conversion removes the old dependence on codepoint magnitude. Thus `"日本語"`
has the same asymptotic literal size and native-computation path as any other
three-scalar string.

#### Literal patterns

A string literal is valid in every pattern position where the scrutinee has type
`String`. It is the ordinary constructor pattern corresponding to the literal:

```rhombus
function first_is_a(s :: String) :: Boolean:
  match s
  | "a": #true
  | _: #false
```

The `"a"` row is `text(cons(97, nil()))`, with `97` handled by the native
`Nat` literal-pattern rule. Normal ordered-pattern, reachability, and
exhaustiveness rules apply. `""`, non-empty ASCII strings, and non-ASCII strings
are equally supported. A source string pattern never expands a codepoint to a
successor chain, never lowers to a host string comparison, and never introduces
a string-specific decision-tree case.

#### Kernel boundary

`String` is **not** a kernel primitive. The language prelude derives
`List.of` and `String` through the ordinary datatype mechanism, then exposes
their constructors to literal elaboration. To the kernel, `String` is an
ordinary theory type, constants, and theorems created by conservative
extensions.

The accelerated `Nat` representation and conversions are the only kernel-level
numeric facility string processing relies on. The kernel must not gain a
reserved `String` type name, a string term node, native host-string equality, a
string-specific inference rule, or a string-specific axiom. String operations
reuse the checked native numeral conversions plus ordinary list/datatype
theorems; no second trusted string evaluator exists.

#### API boundary and cutover

String construction, matching, equality, and literal syntax are language
features. Higher operations—append, map, size, reverse, normalization,
encoding/decoding, indexing, and character classification—are ordinary
library-defined functions over `String` and `Nat`; they are not kernel or
frontend primitives.

The `Char` datatype, its `char` constructor, `List.of(Char)`, and all bit-field
literal lowering are removed. There is no compatibility alias, implicit
conversion, or legacy literal path. All declarations that formerly exposed
characters now expose `Nat` codepoints.

## 8. Termination and recursion

A recursive `function` is admitted only when its equations are a conservative
extension. Nontermination would make clausal equations inconsistent, so this is
a soundness requirement, not an optimization or style preference.

The checker tries two methods in order.

1. **Lexicographic structural descent.** It greedily finds argument positions
   such that every recursive call preserves an earlier prefix and decreases the
   next selected position to a proper recursive constructor subterm. This is a
   complete greedy choice: a currently admissible column remains admissible, and
   choosing it only discharges call sites. It supports lexicographic recursion,
   such as descent on `[m, n]` for Ackermann-style definitions.
2. **Measure descent.** If structural descent fails, an adjacent
   `proof: ~measure: expression` supplies a measure. Each recursive call creates
   a guarded obligation that the recursive-call measure is below the enclosing
   pattern measure. The ordinary theorem prover must close every obligation. A
   branch condition that calls the function being defined is not among an
   obligation's assumptions: the function has no equations yet, so the call has
   to descend whichever way that branch went.

Every recursive datatype derives `T_lt`, its well-founded proper-subterm
relation. A measure must produce such a declared datatype; a Boolean or another
type without a derived subterm relation is rejected. `T_lt` is derived as the
transitive closure of a non-recursive direct-child predicate and proved
well-founded using the datatype's induction principle.

A `function.together:` family is checked the same way, on the combined
function its members are read as (section 4.2): one order spans the family,
either from every member's `~measure:` or from an argument column per member
at a common recursive datatype. A datatype family's union type is such a
datatype, which is what lets a recursion cross between mutually recursive
datatypes.

Nested recursion and recursive calls through a nested lambda are not
supported. They are rejected, not treated as unchecked definitions.

## 9. The automatic prover

The prover is a deterministic ACL2-style waterfall. It performs no search and
no backtracking. A stage either makes progress and returns its subgoals to the
top, or passes the goal down. A goal that reaches the bottom is a failed proof;
its scoped trace is shown as the compile-time residue.

The pipeline is:

1. **Simplification:** rewrite the conclusion and assumptions to fixed point
   with enabled function/definition equations, datatype equations, projections,
   theorem-local `~use` facts, and assumptions; beta-normalize between rewrite
   passes.
2. **Destructor elimination:** when a constructor discriminator assumption is
   present, replace a selector-observed value by its constructor-and-selector
   reconstruction.
3. **Fertilization:** use a non-cyclic variable equality assumption to replace
   that variable in the conclusion, then drop the used equality to avoid loops.
4. **Generalization:** replace repeated non-variable saturated subterms with
   fresh variables to strengthen an induction goal.
5. **Irrelevance elimination:** discard assumptions that share no variables,
   transitively, with the conclusion.
6. **Specialization:** normalize universally quantified intermediate goals for
   the following induction phase. This is an internal stage and not a normal
   `~skip:` target.
7. **Induction:** choose a datatype variable using recursion-descent metadata or
   the user `~induct:` override; split over constructors and add induction
   hypotheses for recursive fields. Nested induction is bounded at depth six.

A goal is immutable data: a list of assumptions plus a conclusion. A stage does
not create a theorem. It returns subgoals, trace events, and a justification
function that can combine proved subgoals using kernel rules only. Therefore a
prover bug may leave a valid theorem unproved, but cannot turn a false statement
into a kernel theorem.

## 10. Trust model

The LCF kernel is the sole authority able to construct opaque `Thm` values. Its
public primitive inference rules are:

```text
REFL  TRANS  MK_COMB  ABS  BETA
ASSUME  EQ_MP  DEDUCT_ANTISYM_RULE  INST  INST_TYPE
```

The current kernel also exposes conservative theory-extension principles:

```text
new_type
new_constant
new_axiom
new_basic_definition
new_basic_type_definition
```

The language layer may use the conservative definition and type-definition
principles, but must not use `new_axiom` for a datatype, function, definition,
or theorem. Each derived declaration checks that its output theory has the same
axiom set as its input theory. A failure of that invariant rejects the
source declaration.

The trusted base has the standard ETA, choice (`SELECT`), Boolean-cases, and
infinity assumptions. Recursive datatypes are derived using the one shared
infinity assumption, rather than introducing an axiom schema per datatype.
Logical connectives, datatype laws, subterm relations, non-recursive definitions,
well-founded recursion equations, conversions, rewriting, and all tactic
justifications are derived.

The kernel's limits must be documented honestly:

- importing the raw kernel module exposes `new_axiom`; the language claim
  “compiled means proved” applies only to code that does not exercise that
  escape hatch;
- the Isabelle development, code generator, Rhombus compiler, and runtime are
  part of the trusted computing base; and
- parameterized datatype soundness depends on correct positivity checking before
  type-variable specialization.

## 11. Required non-goals

The language does not add effects, mutation, exceptions, dynamic dispatch,
runtime identity, implicit numeric coercions, or a runtime overload mechanism
to the logical fragment. It does not preserve obsolete compatibility syntax.

A feature whose direct HOL elaboration is unavailable is rejected rather than
silently becoming ordinary Rhombus or an unchecked logical assumption. The
language must remain explainable as a small surface layer over ordinary HOL
terms, conservative definitions, derived datatypes, and well-founded recursion.
