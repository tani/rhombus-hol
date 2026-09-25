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
and the required trust and execution boundaries. It does **not** otherwise
specify the standard library of proved datatypes and functions. Library types
such as `List.of` and `Integer` appear primarily as examples of syntax the
language must support. Section 1.1 fixes the standard automata library's
executable representation, and section 7.5 fixes `String` because string
literal syntax depends on its representation.

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
  datatype normally emits classes; the exact reserved `Nat` declaration is the
  runtime-representation exception described in sections 4.1 and 7.4. A
  `function` emits a Rhombus function. Types and proof-only constructs are
  erased.

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

### 1.1 Standard-library executable automata

The standard automata library has one representation for each kind of
automaton, and every automaton operation is declared with `function` so that
it has both a logical meaning and ordinary runtime code.

`DFA.of(?q, ?a)`, constructed by `dfa`, stores one initial state, a transition
function, and a final-state predicate. `dfa_run` follows the transition
function over a `List.of(?a)`, and `dfa_accepts` tests the resulting state.

The nondeterministic representations make their finite search space explicit:

- `NFA.of(?q, ?a)`, constructed by `nfa`, stores an equality decider of type
  `?q -> ?q -> Boolean`, a `FiniteSet.of(?q)` state universe, an initial
  `FiniteSet.of(?q)`, a transition predicate of type
  `?q -> ?a -> ?q -> Boolean`, and a final-state predicate.
- `EpsilonNFA.of(?q, ?a)`, constructed by `epsilon_nfa`, stores the same data
  plus an epsilon-transition predicate of type `?q -> ?q -> Boolean`.

The NFA operations are `nfa_run`, `nfa_accepts`, and `nfa_determinize`. The
epsilon-NFA operations are `epsilon_nfa_closure`, `epsilon_nfa_run`,
`epsilon_nfa_accepts`, `epsilon_nfa_eliminate`, and
`epsilon_nfa_determinize`. Run and epsilon-closure operations return
`FiniteSet.of(?q)`. Epsilon elimination returns `NFA.of(?q, ?a)`.
Determinization returns `DFA.of(FiniteSet.of(?q), ?a)`, whose states are finite
sets of source states.

Every destination search enumerates only the stored universe and uses the
stored equality decider for finite-set operations. Epsilon closure is bounded
structurally by consuming the universe list as fuel, so it terminates even
when epsilon transitions contain cycles. The universe is therefore part of
the automaton representation rather than optional metadata.

`nfa_determinize_accepts_iff` states that `nfa_accepts` agrees with acceptance
by the DFA returned from `nfa_determinize` for every word, and
`nfa_determinize_language` gives the corresponding extensional language
equality. These theorems are unconditional: NFA acceptance and the subset
construction use the same finite-set runner.

Likewise, `epsilon_nfa_determinize_accepts_iff` and
`epsilon_nfa_determinize_language` are unconditional preservation theorems for
`epsilon_nfa_accepts` and the DFA returned by `epsilon_nfa_determinize`. The
epsilon-NFA source and the produced DFA share the same bounded closure and
subset-construction computation.

Finite-universe epsilon elimination additionally has a representation
obligation. `epsilon_nfa_well_formed(m)` requires the stored equality decider
to agree with logical equality, the initial states to belong to the explicit
universe, and the universe to be closed under epsilon and symbol transitions.
Under that explicit hypothesis, `epsilon_nfa_eliminate_accepts_iff` proves
word-acceptance preservation and `epsilon_nfa_eliminate_language` proves
language preservation. No well-formedness premise is required by either
determinization theorem, because those theorems compare the executable
runners directly.

#### Generic regular expressions

Importing `rhombus/hol/stdlib open` exposes the generic regular-expression
library. `Regexp.of(?a)` is an AST over an arbitrary symbol type `?a` with
exactly six constructors:

- `regexp_none()` accepts no words and `regexp_epsilon()` accepts only the
  empty word.
- `regexp_atom(predicate)` accepts a one-symbol word when the
  `?a -> Boolean` predicate accepts that symbol. The predicate is executable,
  so compiled matching remains ordinary runtime code.
- `regexp_alternate(left, right)`, `regexp_sequence(left, right)`, and
  `regexp_star(body)` denote union, concatenation, and Kleene closure.

`regexp_literal(decide_equal, value)` is a convenience function that constructs
an atom from an executable equality decider; it is not a seventh AST
constructor. The inductively defined relation
`regexp_accepts(r, word)` gives the language semantics independently of every
automaton representation and runner. Its rules give epsilon the empty word,
atoms their accepted singleton words, alternation either branch, sequencing
the concatenation of two accepted words, and star zero or more accepted body
words.

`regexp_compile(pattern :: String) :: Option.of(Regexp.of(Codepoint))` parses
the standard-library `String` codepoint list into an executable
regular-expression AST. Its grammar is:

```text
pattern       ::= ε | alternation
alternation   ::= concatenation ("|" concatenation)*
concatenation ::= repetition+
repetition    ::= atom ("*")?
atom          ::= literal | "." | "\" codepoint | "(" alternation ")"
literal       ::= any Unicode codepoint other than |, *, (, ), ., or \
```

Here `ε` denotes empty input in the start rule, not a pattern codepoint. The
compiler unwraps each `Codepoint` with `codepoint_to_nat` to recognize the
operators by their ASCII values: `|` is 124, `*` is 42, `(` is 40, `)` is 41,
`.` is 46, and backslash is 92. Alternation has the lowest precedence,
implicit concatenation the next, and postfix `*` the highest; parentheses
group an alternation. Each unescaped literal denotes an atom using executable
`codepoint_equal`; `.` denotes an atom whose predicate accepts every
codepoint. A backslash makes exactly the next codepoint a literal, including
any operator codepoint.

The empty entire pattern compiles to `some(regexp_epsilon())`. Every other
successful parse consumes the complete input and returns `some(result)`, where
`result` is the resulting `Regexp.of(Codepoint)`. Dangling escapes, unmatched
parentheses, leading or trailing `|`, empty alternatives or groups, leading or
repeated `*`, and any leftover malformed input are rejected with `none()`.

Compilation follows the conventional Thompson pipeline:

```text
Regexp -> EpsilonNFA -> NFA -> DFA
```

`regexp_to_epsilon_nfa` performs Thompson construction,
`regexp_to_nfa` eliminates epsilon transitions, and `regexp_to_dfa`
determinizes the resulting NFA. `regexp_matches(r, word)` executes the DFA and
tests the whole word; it is not a substring search.

The principal compiler theorems are
`regexp_to_epsilon_nfa_well_formed` and
`regexp_to_epsilon_nfa_accepts_iff` for the Thompson result;
`regexp_to_nfa_accepts_iff` and `regexp_to_nfa_language` for epsilon
elimination; and `regexp_to_dfa_accepts_iff` and
`regexp_to_dfa_language` for determinization. The direct semantic
correspondences are `regexp_to_nfa_semantics_iff` and
`regexp_to_dfa_semantics_iff`. The executable matcher is related to each stage
by `regexp_matches_epsilon_nfa_iff`, `regexp_matches_nfa_iff`, and
`regexp_matches_dfa_iff`, while `regexp_matches_iff` is the end-to-end
correctness theorem
`regexp_matches(r, word) <=> regexp_accepts(r, word)`.

`regexp_find(r, input)` returns an `Option.of(RegexpMatch)`.
`regexp_match(start, end)` constructs a result, and
`regexp_match_start` and `regexp_match_end` select its `Nat` offsets. Search is
leftmost-longest: it chooses the earliest start having a match, then the
greatest accepted end at that start. Ranges are half-open `[start, end)`,
measured in input-list elements; `start === end` is a valid zero-width match.

`regexp_replace_first(r, replacement, input)` replaces only that
leftmost-longest range. `regexp_replace_all(r, replacement, input)` repeats the
same search over the unconsumed original input; replacement symbols are never
searched. A nonempty match consumes its range. After a zero-width match before
EOF, replace-all emits the replacement, copies exactly one original symbol at
the match position unchanged, and resumes after that symbol. At a zero-width
match at EOF, it emits the replacement once and stops.

The four String adapters are `string_regexp_matches`,
`string_regexp_find`, `string_regexp_replace_first`, and
`string_regexp_replace_all`. They accept `Regexp.of(Codepoint)` and convert
strings to and from codepoint lists. Consequently String search offsets count
codepoints, not encoded bytes, and replacement follows exactly the generic
list behavior above.

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

Except for the exact reserved declaration
`datatype Nat | zero() | succ(pred :: Nat)`, the executable reading emits one
ordinary Rhombus class per constructor, with a shared interface for matching,
structural equality, readable printing, fields, and constructor calls. The
reserved `Nat` is the intentional runtime-representation exception: its
executable values are host nonnegative integers as specified in section 7.4.
This exception does not change its logical datatype, constructor constants, or
derived theorems, and no other datatype is mapped to integers.

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
constructors build. A single `datatype` declaration has the same member-level
semantics as a one-member family.

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
  ~induct: [variable, ...]
  ~split: [proposition, ...]
  ~choose: [expression, ...]
  ~use: [theorem, ...]
  ~skip: [stage, ...]
  ~disable: [rule, ...]
  ~limit: nonnegative_integer
  ~extensionality: [variable, ...]
```

A theorem is elaborated as a Boolean HOL term and proved during compilation.
Its successful theorem object is retained under `name`, but it is **not** added
to the global rewrite database merely because it exists. A later proof enables
it explicitly with `~use`; adding an unrelated theorem must not silently change
automation.

The `proof:` block is optional. Its options only control proof search; none can
admit a false proposition. Each option keyword may occur at most once.
Every bracketed list shown above must be nonempty, and its elements retain
their written order; repeated keywords never concatenate lists.

- `~induct:` gives strict, ordered induction-variable hints. The first hint is
  consumed at the first induction on each unresolved branch, and the remaining
  hints propagate in order to every generated subgoal. If the next named
  variable cannot be inducted on in any unresolved branch, the proof fails
  explicitly. The induction heuristic resumes only after all listed hints are
  exhausted.
- `~extensionality:` gives fresh names for sequential function-extensionality
  steps. Every listed name is consumed in order before `~choose:` or `~split:`
  is applied; each step requires the current goal to be an equality at function
  type (including predicate-encoded sets).
- `~split:` performs its Boolean case splits in list order.
- `~choose:` supplies existential witnesses in list order, before case splits.
- `~use:` enables the listed theorems for this proof only.
- `~disable:` disables the listed rewrite rules for this proof only.
- `~skip:` skips the listed named waterfall stages for this proof only.
- `~limit:` sets the nonnegative proof-step limit.

### 4.6 `notation`

```rhombus
notation <&> :: Boolean:
  ~order: hol_conjunction
  ~associativity: ~none
| (#false <&> _):
    #false
| (#true <&> right):
    right
```

`notation` adds a spelling only to the HOL expression space. Its canonical
parenthesized prefix, infix, and postfix case heads, legacy unparenthesized
heads, immediate cases, and named groups follow Rhombus `operator` layout.
Prefix may be combined with infix or postfix; infix and postfix may not be
combined.

Operands use the closed HOL pattern grammar from section 6, including
variables, `_`, static type annotations, literals, lists, products, and
declared datatype constructors. As with Rhombus `operator`, an operand pattern
that occupies more than one shrubbery term must be parenthesized inside the
operator head, for example `((some(value)) <op> right)`.

Cases of each fixity are tried in source order, but must be exhaustive and every
row must be reachable. Each operand position has one HOL type, so patterns
cannot dispatch between unrelated runtime types.
At a use, arbitrary operand expressions are evaluated once from left to right
before value-pattern dispatch.

A shared or case-local `:: HOLType` is a static result constraint. It is not a
Rhombus predicate check or converter. `:~`, `~unsafe`, `~name`, `~who`,
repetition lifting, partial no-match failure, effects, and multiple values are
not part of HOL notation. Precedence options precede the HOL body; the body may
use the complete admitted body grammar, and calls in it—including overloaded
calls—see types inferred from both the operand expressions and patterns.

Notation normalizes to an immediately applied anonymous Core function with one
shared pattern matrix. The existing checker and decision-tree compiler therefore
define both its logical and executable readings. Notation adds no constant or
theorem, creates no ordinary Rhombus or repetition operator, and remains visible
only to following HOL declarations. Export it explicitly with
`only_space hol_expr`; importing that binding carries the same HOL notation
table across the module boundary.

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
Without a shared named block, only the first case of each fixity may declare
options. Shared and case-local options may not repeat the same kind.
`~associativity` applies only to an infix fixity.

### 4.7 `overload`

```rhombus
overload public_name(ArgumentType, ...) = implementation
overload public_name(ArgumentType, ...) :: ResultType = implementation
overload public_name(arg :: ArgumentType, ...) = implementation(arg, ...)
```

An overload declaration adds a typed clause for one callable name. Direct calls
and calls in notation implementation expressions share exactly one resolver.

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

In the logical reading, a bare nonnegative numeral pattern uses the kernel's
atomic compact `Nat` numeral discriminator described in section 7.4 and
therefore requires a `Nat` scrutinee. Its executable reading uses that
section's host-integer discrimination. Signed `Integer` literals are not
patterns, and `Rational` has no literal form.

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

A bare nonnegative decimal `n` is self-typed as `Nat`. The explicitly positive
form `+n` and lexically negative form `-n` are self-typed as `Integer`; `+0`
and `-0` both normalize to integer zero. Prefix `+` is available only on a bare
decimal literal. Unary `-` on any nonliteral expression remains the ordinary
overloadable `negate` operator.

An expected type checks a literal's fixed type; it never selects or converts
that type. In particular, `10 :: Integer`, `+10 :: Nat`, and passing `10` to
an `Integer` parameter are errors. There are no implicit numeric coercions.
`Rational` has no literal form, including no fraction syntax: construct a
whole value explicitly with `rational_from_integer(+n)` or use the appropriate
constructor/API.

The normalized frontend retains only
`CoreNatLit(value :: NonnegInt, at)` as a numeric literal node. Surface
normalization directly encodes `+n` as
`CoreCall(CoreGlobalRef(int_nonnegative), [CoreNatLit(n)])`; `-n` uses the same
ordinary call shape with `int_negative` and magnitude `n - 1`. Thus
`CoreNatLit(n)` becomes the Nat-only checked form
`CheckedNumeral(n :: NonnegInt, at)`, while an integer literal follows the
same checked constant-resolution and type-checking path as other
object-language applications. Its resulting `Integer` type is unified with
the expected type. Both `+0` and `-0` normalize through `int_nonnegative(0)`.

At the exact reserved object-language declaration
`datatype Nat | zero() | succ(pred :: Nat)`, a `CheckedNumeral` has two compact
readings: logical elaboration produces `mk_nat_lit(theory, n)`, whose kernel
term is `NatLit(n)`, while executable emission produces the host
`Nat`/`NonnegInt` integer `n`. The backends therefore handle only Nat
numerals. Integer literals reach them as ordinary checked `int_nonnegative` or
`int_negative` constructor applications around that Nat literal, so neither backend
branches on a signed numeral. `Integer` does not acquire a new host-integer
representation.

For this reserved declaration only, executable `zero()` returns `0` and
executable `succ(n)` returns `n + 1`. A `zero()` runtime pattern tests that the
value is zero. A `succ(p)` runtime pattern accepts only a positive integer and
binds `p` to its predecessor. Thus generic generators, shrinkers, and functions
written with `zero` and `succ` continue to use the same expression and pattern
interface without allocating Peano constructor chains. Every other datatype
retains the class-per-constructor executable representation.

This host arithmetic is only the executable reading; it does not prove a HOL
equation or authorize a kernel result. Logically, `Nat`, `zero`, and `succ`
remain the ordinary reserved datatype with its constructor equations,
distinctness, injectivity, cases, and induction theorems. Kernel arithmetic,
equality, ordering, and zero/successor case conversions remain checked,
theorem-producing conversions.

A bare surface `Nat` literal pattern is likewise split: its logical reading is
an atomic numeric discrimination over `NatLit(n)`, and its executable reading
tests the host nonnegative integer against `n`. Neither reading expands the
literal to `succ(...succ(zero())...)`. Explicitly signed integer patterns are
rejected.

#### Kernel literal representation

In the logical reading, the compact value is a kernel-internal canonical term
form `NatLit(n)`, where `n` is a host nonnegative integer payload. It is not a
new HOL constant, an axiom, user-written syntax, or the executable value. It is
a compact representation of the existing Peano value:

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

`Codepoint` is a nominal wrapper around `Nat`, and `String` is an immutable
finite sequence of those wrappers:

```rhombus
datatype Codepoint
| codepoint(codepoint_value :: Nat)

datatype String
| text(codepoints :: List.of(Codepoint))
```

The public API exports `Codepoint`, `codepoint`, `codepoint_to_nat`, and the
curried executable decider `codepoint_equal`; the generated
`codepoint_value` field selector is not exported. The wrapper is nominal only:
`codepoint` accepts every `Nat`, including values that are not Unicode scalar
values. There is deliberately no scalar-value invariant or validation hidden
in the datatype.

This is the complete logical string representation. A string literal maps
every source Unicode scalar value to a `codepoint` containing the corresponding
native `Nat`. Equality, matching, and recursion operate on the resulting
codepoint sequence. They are not byte equality, UTF-8 equality,
host-language string identity, Unicode-normalized equality, or
grapheme-cluster equality. Consequently, canonically distinct source scalar
sequences remain distinct: `"e\u0301"` and `"\u00e9"` are not equal unless a
user-defined normalization function proves them equal.

The two nominal layers prevent accidental interchange: `Codepoint` is not
`Nat`, and `String` is not `List.of(Codepoint)`. The ordinary `text`
constructor still exposes the list to HOL library definitions. Values manually
constructed with `codepoint` may contain any `Nat`; literal syntax itself
produces only source Unicode scalar values. Unicode validity checks,
normalization, encoding, and character classification are ordinary library
functions, not a refinement type or frontend policy.

#### Literal elaboration

String literals are context-directed values of type `String`. The lexer
accepts source Unicode scalar values; elaboration rejects no non-ASCII scalar
merely for its magnitude. A literal expands through ordinary declared
constructors, with each scalar written as the corresponding surface `Nat`
numeral:

```text
""       => text(nil())
"ab"     => text(cons(codepoint(97), cons(codepoint(98), nil())))
```

The same Core tree drives logical elaboration and runtime emission, but the
representations remain distinct. After elaboration, the logical `codepoint`
contains the corresponding compact logical `Nat` term; the executable
`codepoint` contains the host nonnegative integer emitted for the same surface
`Nat` numeral. In both readings, `text`, list, and `codepoint` remain ordinary
datatype values; there is no String- or Codepoint-specific compact
representation.

Logical literal size is proportional to the number of source scalars: one
`text` node, one list cell, one `codepoint` node, and one compact logical `Nat`
term per scalar. The executable reading likewise uses one host integer per
scalar.
Neither size depends on codepoint magnitude. Thus `"日本語"` has the same
asymptotic literal size and native-computation path as any other three-scalar
string.

#### Literal patterns

A string literal is valid in every pattern position where the scrutinee has
type `String`. It is the ordinary constructor pattern corresponding to the
literal:

```rhombus
function first_is_a(s :: String) :: Boolean:
  match s
  | "a": #true
  | _: #false
```

The `"a"` row is `text(cons(codepoint(97), nil()))`. The surface numeral `97`
uses the logical/executable `Nat` literal-pattern split from section 7.4 inside
the ordinary `codepoint` constructor. Normal
ordered-pattern, reachability, and exhaustiveness rules apply. `""`, non-empty
ASCII strings, and non-ASCII strings are equally supported. A source string
pattern never expands a codepoint to a successor chain, never lowers to a host
string comparison, and never introduces a string-specific decision-tree case.

#### Kernel boundary

Neither `Codepoint` nor `String` is a kernel primitive. The language prelude
derives `List.of`, `Codepoint`, and `String` through the ordinary datatype
mechanism, then exposes their constructors to literal elaboration. To the
kernel, both wrappers are ordinary theory types, constants, and theorems
created by conservative extensions.

The compact logical `Nat` numeral representation and theorem-producing
conversions are the only kernel-level numeric facility string processing
relies on. The kernel must not gain a reserved `String` type name, a string term
node, native
host-string equality, a string-specific inference rule, or a string-specific
axiom. Executably, the `Nat` field of an ordinary `codepoint` value uses the
host-integer representation from section 7.4; this is not a special
representation for `Codepoint` or `String`. Logical string operations reuse
the checked numeral conversions plus ordinary list/datatype theorems; no
second trusted string evaluator exists.

#### API boundary and cutover

String construction, matching, equality, and literal syntax are language
features. Higher operations—append, map, size, reverse, normalization,
encoding/decoding, indexing, and character classification—are ordinary
library-defined functions over `String`, `Codepoint`, and `Nat`; they are not
kernel or frontend primitives.

The standard-library conversion boundary is `string_to_codepoints` and
`string_from_codepoints`, both using `List.of(Codepoint)`. String singleton,
map, prefix, regexp, search, and replacement APIs likewise expose `Codepoint`,
never bare `Nat` symbols. There is no compatibility alias, implicit
conversion, or legacy direct-`Nat` string path.

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
6. **Induction:** choose a datatype variable using recursion-descent metadata or
   the user `~induct:` override; split over constructors, open the companion
   quantifiers introduced by the induction predicate, and add induction
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
