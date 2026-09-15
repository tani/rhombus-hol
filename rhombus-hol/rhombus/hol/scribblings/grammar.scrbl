#lang rhombus/scribble/manual

@title(~tag: "grammar"){Types, Expressions and Propositions}

@section(~tag: "types"){Types}

@verbatim{
Type = Id                 a declared datatype with no parameters
     | Id.of(Type, ...)   a declared type constructor, applied
     | ?a                 a type variable
     | Type -> Type       a function type (right associative)
     | (Type)             explicit grouping
     | Boolean            the type of propositions
}

Type variables are written @rhombus(?a), @rhombus(?b) and so on. A function is
implicitly polymorphic in every type variable it mentions; there is no
@tt{forall} at the type level to write.

Parameterized datatype declarations bind a constructor namespace: for
example, @tt{datatype List.of(?a)} binds @tt{List.of}, and an instance is
written @tt{List.of(Nat)}. The bare name @tt{List} is not a type, because its
argument is missing. Function arrows associate to the right, so
@tt{A -> B -> C} means @tt{A -> (B -> C)}; write
@tt{(A -> B) -> C} when the domain is itself a function.

@rhombus(Boolean) is spelled as Rhombus spells it. A function's annotations are
erased on the way to the executable half, but the conditions of its
@rhombus(if) forms are not, so the two halves have to agree on what a Boolean
is.

@section(~tag: "expressions"){Expressions}

This is the grammar of a @rhombus(function, ~datum) body. HOL expressions use
a dedicated, extensible enforestation space; function bodies admit only the
pure, total forms below.

@verbatim{
body = expr                        the value of the body
     | let Id = expr               a local definition, then the rest
       body
     | let pattern = expr          an irrefutable-pattern local definition
       body
     | function Id(arg :: Type, ...) :: Type:   a named local function,
         body                                   then the rest
       body
     | match Id | clause | ...     on a parameter or a pattern variable

expr = Id                          a parameter, pattern variable or local
     | Id(expr, ...)               a constructor, function or named primitive
     | NonnegativeInteger          an expected Nat, Integer, or Rational
     | #true | #false | true | false
     | !expr
     | expr && expr
     | expr || expr
     | expr == expr
     | -expr
     | expr ** expr
     | expr * expr
     | expr + expr | expr - expr
     | expr ++ expr
     | expr in expr
     | expr union expr
     | expr intersect expr
     | expr < expr | expr <= expr | expr > expr | expr >= expr
     | if expr | expr | expr
     | cond-expr
     | expr notation-op expr
     | expr :: Type                an expected-type ascription
     | function (arg :: Type, ...) :: Type: body    an anonymous function
     | function | (pattern, ...): body | ...        a case-clause function
     | block: body                 an ordinary expression built from a body
     | (expr)

cond-expr = cond
            | expr: expr
            | ...
            | ~else: expr

clause = CtorId(Id, ...): body
       | CtorId: body

row = (pattern, ...): body      on the declaration, one per argument
    | pattern: body             at one argument, parentheses optional
}

@rhombus(let) and @rhombus(match) are forms of a @emph{body}, not of an
expression: a @rhombus(let) is a statement followed by the rest of the body,
and there is no @rhombus(let) inside the operand of a @rhombus(&&). That is
not a notational choice --- it is what the elaborator accepts.

@rhombus(cond) tests its guards from top to bottom and returns the body of the
first true guard. A final @rhombus(~else) clause is mandatory and must be last:

@rhombusblock(
  function pick(b :: Boolean, x :: Nat, y :: Nat) :: Nat:
    cond
    | b: x
    | ~else: y
)

Both the executable and logical readings lower this form to right-nested
@rhombus(if) expressions. Guards and clause results are expressions, not full
bodies, so a clause cannot contain a local @rhombus(let) or
@rhombus(match).

The built-in operators mean in the logic what they mean in Rhombus:
@rhombus(#true) and @rhombus(#false) are the truth values, @rhombus(!) is
negation, @rhombus(&&) and @rhombus(||) are conjunction and disjunction, and
@rhombus(==) is equality at any type. Arithmetic, append, membership, and set
operators lower to ordinary named calls: @tt{add}, @tt{subtract},
@tt{negate}, @tt{multiply}, @tt{power}, @tt{less}, @tt{less_equal},
@tt{greater}, @tt{greater_equal}, @tt{append}, @tt{member}, @tt{union}, and
@tt{intersection}. The elaborator resolves each named call directly or through
the overload clauses imported with the current theory. There is no runtime
type switch and no implicit numeric coercion: the complete argument tuple and,
when available, the expected result type must select one non-overlapping
clause.

@rhombus(notation, ~datum) adds a spelling to the HOL expression space. Each
use lowers to a normal call of the declaration's final function name. It can
therefore occur in a logical @rhombus(function) when that function has an
executable reading, even though the notation itself is not bound in ordinary
Rhombus code.

@rhombus(&&) and @rhombus(||) short-circuit when the module runs, while the
logical @tt{and} and @tt{or} are strict. Nothing can tell the difference,
because every function in this grammar is total.

Anything outside the grammar is a compile error that names the offending
expression. Ordinary runtime-only operators are outside it. A string
literal is admitted as an expression (it desugars to @tt{text} applied to
a @tt{List.of(Nat)} of character codes, over whatever datatypes provide
@tt{Nat}, @tt{List.of(?a)}, and @tt{text}), but not yet as a pattern in a
@rhombus(match) clause or row (see "Matching" below). A bare numeral
is also rejected when its numeric type cannot be determined from an
overload argument, function domain, or checked result. The lexical form
@tt{-1} is the @tt{negate} call applied to the nonnegative numeral
@tt{1}; it therefore requires an expected type with an applicable
@tt{negate} overload clause.

@subsection{Local definitions}

A @rhombus(let) is @emph{substituted} in the logical reading: the equation is
about the value, and it mentions the initializer only where the body reads the
variable.

@rhombusblock(
  function unread(n :: Nat) :: Nat:
    match n
    | zero(): zero()
    | succ(k):
        let ignored = unread(k)
        succ(zero())
)

states @tt{unread(succ(k)) === succ(zero)}, with no @rhombus(unread) on the
right. The compiled program still evaluates the initializer, though, so
termination is checked against @emph{both} readings: the call above has to
descend even though the equation does not mention it, and one that does not
is refused. See @secref("trust") for why the two readings are kept apart.

@subsection{Matching}

A body may be a @rhombus(match) on one of the parameters, and each clause body
may itself be a @rhombus(match) on a @emph{different} parameter. The nesting is
flattened into a pattern matrix, which is what lets a definition descend on
more than one argument.

@rhombusblock(
  function ack(m :: Nat, n :: Nat) :: Nat:
    match m
    | zero(): succ(n)
    | succ(p):
        match n
        | zero(): ack(p, succ(zero()))
        | succ(q): ack(p, ack(succ(p), q))
)

The matrix must cover the product of the matched columns. It may overlap:
clauses are @emph{ordered}, and where several match the earliest wins ---
the same reading the @rhombus(match) this compiles to gives the same text.
What is refused is a clause no argument shape can reach, since that is a
mistake however the clauses are arranged.

@tt{_} stands for a position the clause does not name. It may appear inside
a pattern (@tt{Cons(x, _)}) or as a whole clause head (@tt{| _: ...}), which
is how a catch-all after a specific case is written.

A pattern position may also be a bracket list pattern (@tt{[]},
@tt{[x]}, @tt{[x, y, & rest]}), which desugars to nested @tt{cons}/@tt{nil}
constructor patterns over whatever datatype provides them --- the pattern
counterpart of a bracket list literal expression --- and a nonnegative
numeral, which desugars to the matched constructor chain of whatever
datatype the scrutinee's type declares (so @tt{| 0: ... | succ(k): ...}
pattern (@tt{Pair(x, y)}) matches the language's one product type.

A @tt{#true} or @tt{#false} pattern matches @tt{Boolean}. The kernel's
@tt{bool} is a primitive type rather than a declaration, so the facts the
pattern compiler needs --- two nullary constructors, their distinctness,
cases and induction --- are derived from @tt{BOOL_CASES_AX} and installed
with the base theory; no axiom is added. Totality is then checked as for
any other datatype, so @tt{| #true: ...} alone is a missing case, not a
fallthrough.

A @tt{String} literal pattern is accepted and means what it says, but it
is only practical for @tt{""}. A string is @tt{text} applied to the list of
its codepoints and a codepoint is a unary numeral, so a one-character
literal is a constructor chain as deep as its codepoint (97 for
@tt{"a"}), and compiling the match exhausts the proof-search step limit.
Match on @tt{text(codes)} and compare the codepoint list instead.

@subsection{Clauses on the declaration}

The same matrix may be written on the declaration itself, one row of patterns
per clause covering every argument, which is how Rhombus's own multi-case
@rhombus(fun) is written:

@rhombusblock(
  function app(xs :: List.of(?a), ys :: List.of(?a)) :: List.of(?a)
  | (Nil(), ys): ys
  | (Cons(x, rest), ys): Cons(x, app(rest, ys))
)

A row must have one pattern per argument; at one argument the parentheses may
be dropped, exactly as a one-argument @rhombus(match) clause drops them. The
patterns are the same patterns, so nesting, @tt{_} and the ordering above all
read the same way here, and a row may constrain every column at once ---
which a nested @rhombus(match) cannot say in a single clause:

@rhombusblock(
  function eq2(m :: Nat, n :: Nat) :: Nat
  | (zero(), zero()): zero()
  | (succ(a), succ(b)): succ(eq2(a, b))
  | (_, _): zero()
)

This is sugar in the strict sense: a row refines the same pattern vector the
nested form refines, so nothing downstream --- the decision tree, coverage,
termination, the @tt{WFREC} derivation --- can tell which form was written.
The executable half becomes a multi-case @rhombus(fun) over the same
patterns, so the first matching clause wins on both sides.

A definition's equations are stated at the shapes each clause actually
@emph{wins} at, not at its pattern as written --- @tt{| zero(): a | _: b}
gives @tt{f(zero) === a} and @tt{f(succ(k)) === b}, never the inconsistent
pair @tt{f(zero) === a} and @tt{forall n: f(n) === b}.

A pattern may nest to any depth: @tt{Cons(x, Cons(y, rest))} is a pattern,
written directly in a clause head, or built the same way one level at a time
via a nested @rhombus(match) on an already-bound variable --- @tt{match xs |
Cons(x, rest): match rest | Nil(): ...} refines the tail @tt{Cons(x, rest)}
already bound. A nested @rhombus(match) may not re-match a position that has
already been refined --- which matters because a pattern variable can shadow
a parameter of the same name.

@section(~tag: "propositions"){Propositions}

This is the grammar of a @rhombus(theorem, ~datum) statement. It is enforested
in the same dedicated HOL expression space as function expressions, with a
different admissibility policy.

@verbatim{
prop = expr
     | not prop
     | prop and prop
     | prop or prop
     | prop ==> prop
     | prop <=> prop
     | prop === prop
     | forall (Id :: Type, ...): prop
     | exists (Id :: Type, ...): prop
     | exists1 (Id :: Type): prop      exactly one binder
     | select (Id :: Type): prop       exactly one binder
     | Set{}                          the canonical empty set
     | Set{expr, ...}                 an extensional set literal
     | Set{Id :: Type | prop}         a set comprehension
     | if prop | prop | prop
     | cond-prop
     | prop notation-op prop
     | (prop)

cond-prop = cond
            | prop: prop
            | ...
            | ~else: prop
}

A proposition is never emitted as Rhombus, so it uses the logical spellings:
@tt{and}, @tt{or}, @tt{not}, @tt{===} for equality, @tt{==>} for implication
and @tt{<=>} for equivalence. (Equality and equivalence are the same relation;
the two spellings differ only in precedence, so that an equivalence between
equations reads without parentheses.)

The same @rhombus(cond) form is available in a proposition, with proposition
guards and results and the same mandatory final @rhombus(~else). Since
@rhombus(quickcheck) uses this proposition grammar, it accepts
@rhombus(cond) when every branch has an executable reading.

@subsection{Named logical constants}

The initial theory exposes the canonical names of its logical constants to HOL
name resolution. The named and operator forms below denote the same constants:

@verbatim{
true, false                       Boolean values (#true, #false)
eq(x, y)                          equality (==, ===, <=>)
imp(p, q)                         implication (==>)
conj(p, q), disj(p, q)            conjunction and disjunction (&&/and, ||/or)
neg(p)                            negation (!, not)
exists1(predicate)                unique existence
select(predicate)                 choice
wf(relation)                      well-foundedness
}

Their types are @tt{eq :: ?a -> ?a -> Boolean},
@tt{imp, conj, disj :: Boolean -> Boolean -> Boolean},
@tt{neg :: Boolean -> Boolean},
@tt{exists1 :: (?a -> Boolean) -> Boolean},
@tt{select :: (?a -> Boolean) -> ?a}, and
@tt{wf :: (?a -> ?a -> Boolean) -> Boolean}.

@tt{true}, @tt{false}, @tt{eq}, @tt{conj}, @tt{disj}, and @tt{neg} have both
logical and executable readings, so they may appear in a
@rhombus(function) body or executable @rhombus(quickcheck) property.
@tt{imp}, @tt{exists1}, @tt{select}, and @tt{wf} are logic-only named
applications. Use them in theorem statements and proof terms, not in a
@rhombus(function) or @rhombus(quickcheck). Universal quantification,
existential quantification, and conditionals use the dedicated
@rhombus(forall), @rhombus(exists), @rhombus(if), and @rhombus(cond) forms
instead of calls to their kernel constants.

@subsection{Quantifier and choice binders, and @tt{Set} values}

@rhombus(exists1) and @rhombus(select) also have dedicated binder forms,
parallel to @rhombus(forall) and @rhombus(exists), taking exactly one
binder (unlike @rhombus(forall)/@rhombus(exists), which take one or
more):

@rhombusblock(
  theorem unique_zero:
    exists1 (x :: Nat): x === zero()

  theorem pick_zero:
    (select (x :: Nat): x === zero()) === zero()
)

Each desugars to the named kernel constant applied to an anonymous
function: @tt{exists1 (x :: T): p} is
@tt{exists1(function (x :: T): p)}, and likewise for @rhombus(select).
Supplying more than one binder is a compile-time error, since
@tt{exists1}/@tt{select} generalize no further than a single witness.
A binder's type may be omitted and inferred from how the bound variable
is used in the body, exactly like a @rhombus(forall)/@rhombus(exists)
binder.

A @tt{Set} value is an ordinary predicate (@tt{?a -> Boolean}), not a
distinct builtin set type: @tt{Set{}} is the predicate that rejects every
element, @tt{Set{e, ...}} is the extensional disjunction-of-equalities
predicate over its listed elements, and @tt{Set{x :: T | prop}} (binder
type optional, same inference rule) is the predicate @tt{function
(x :: T) :: Boolean: prop}. All three are applied directly as a function
to test membership. Two sets built from different literal descriptions
are proved equal the same way two functions are: see @tt{~extensionality}
in @secref("declarations").

Because they assert existence or uniqueness without computing a witness,
@rhombus(exists), @rhombus(exists1), and @rhombus(select) have no
executable reading: they may appear in a @rhombus(theorem) statement but
not in a @rhombus(function) body or an executable @rhombus(quickcheck)
property. A @tt{Set} comprehension's own body, and @rhombus(forall), are
ordinary predicates and follow the same executability rule as any other
expression they are built from.

@subsection{Precedence}

Strongest first. @tt{**}, @tt{++}, and @tt{==>} are right-associative.
Arithmetic multiplication, addition, set intersection, set union, conjunction,
and disjunction associate to the left. Relations and equality are
non-associative, so chains such as @tt{a < b < c} and @tt{a === b === c} are
syntax errors.

@tabular(
  ~sep: @hspace(2),
  ~column_properties: [#'left, #'left, #'left],
  ~row_properties: [#'bottom_border],
  [[@bold{order}, @bold{proposition}, @bold{expression}],
   [@tt{hol_application}, "named application", "named application"],
   [@tt{hol_power}, @tt{**}, @tt{**}],
   [@tt{hol_prefix_arithmetic}, @tt{-x}, @tt{-x}],
   [@tt{hol_multiplication}, @tt{*}, @tt{*}],
   [@tt{hol_addition}, @tt{+ -}, @tt{+ -}],
   [@tt{hol_append}, @tt{++}, @tt{++}],
   [@tt{hol_set_intersection}, @tt{intersect}, @tt{intersect}],
   [@tt{hol_set_union}, @tt{union}, @tt{union}],
   [@tt{hol_relation}, @tt{< <= > >= in}, @tt{< <= > >= in}],
   [@tt{hol_equality}, @tt{===}, @tt{==}],
   [@tt{hol_negation}, @tt{not}, @tt{!}],
   [@tt{hol_conjunction}, @tt{and}, @tt{&&}],
   [@tt{hol_disjunction}, @tt{or}, @tt{||}],
   [@tt{hol_implication}, @elem{@tt{==>} (right)}, ""],
   [@tt{hol_equivalence}, @tt{<=>}, ""]])

A quantifier extends as far to the right as it can, so

@rhombusblock(
  forall (xs :: List.of(?a)): app(xs, Nil()) === xs and rev(xs) === rev(xs)
)

quantifies over the whole conjunction.

These levels govern frontend notation-aware rendering. The kernel printer is
canonical and prints selected implementation constants as applications such
as @tt{nat_add(x, y)}; the frontend surface printer reconstructs notation only
when it is given explicit overload and notation tables.
