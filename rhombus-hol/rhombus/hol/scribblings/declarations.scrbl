#lang rhombus/scribble/manual

@title(~tag: "declarations"){Declarations}

These are the forms that @rhombuslangname(rhombus/hol) gives a logical reading.
Anything else in a module body is ordinary Rhombus.

The declarations that change the current theory, including
@rhombus(overload, ~datum), are bound macros. A user-written declaration macro
can expand to them; generated declarations contribute executable bindings and
logical state in the same expansion order as directly written declarations.
They must ultimately expand in a module body, not inside a @rhombus(block) or
a @rhombus(fun) body.

@rhombus(notation, ~datum) is also a bound macro. Each notation definition is
visible while the following logical declaration is enforested.

@section{@rhombus(datatype, ~datum)}

@verbatim{
datatype Id
| ctor
| ...

datatype Id.of(?tyvar, ...)
| ctor
| ...

ctor = CtorId
     | CtorId()
     | CtorId(field :: Type, ...)
}

Declares an @deftech{algebraic datatype}. A type variable is written
@rhombus(?a). A parameterized declaration binds @tt{Id.of}; the bare
@tt{Id} remains a constructor namespace and cannot be used as a type without
its arguments. Nullary datatypes continue to use their bare identifier.
The declaration head may end in @tt{:}; this is the block form of the same
declaration. A nullary constructor declaration may likewise omit its empty
parentheses. Thus @tt{datatype Nat: | zero} and
@tt{datatype Nat | zero()} declare the same datatype shape. The omission
applies to the constructor declaration; expressions and patterns in this
manual use the explicit call form @tt{zero()}.

@rhombusblock(
  datatype List.of(?a)
  | Nil()
  | Cons(head :: ?a, tail :: List.of(?a))
)

Logically this @emph{derives} the usual characterisation of the type ---
constructors are injective, distinct constructors build distinct values, every
value is built by some constructor, and the induction principle holds --- as
theorems with no hypotheses. A non-recursive type is built as a sum of
products over its field types; a recursive one is carved out of the labelled
trees over @tt{num} with the kernel's type-definition principle. Neither adds
an axiom. Field selectors and constructor discriminators are declared too, so
@rhombus(List) above brings
@rhombus(Cons_head), @rhombus(Cons_tail), @rhombus(is_Nil) and
@rhombus(is_Cons) into the theory. All of their equations enter the rewriter,
which is what makes @rhombus(match)-defined functions compute during a proof.

A recursive datatype also gets its @tech{subterm relation}; see
@secref("termination").

Except for the exact reserved declaration
@tt{datatype Nat | zero() | succ(pred :: Nat)}, executable datatypes emit one
Rhombus class per constructor, related by an interface so that a value can be
matched against any of them. The classes are ordinary: they compare
structurally with @rhombus(==) and print readably.

The reserved @tt{Nat} is the intentional runtime-representation exception.
Its executable values are host nonnegative integers: @tt{zero()} produces
@tt{0}, @tt{succ(n)} produces @tt{n + 1}, @tt{zero()} patterns test for zero,
and @tt{succ(p)} patterns accept positive integers and bind the predecessor.
Its logical datatype, constructor equations, and derived theorems are
unchanged, and no other datatype is represented this way.

A declaration is rejected unless every recursive occurrence of the type is
@deftech{strictly positive} --- informally, the type being declared may not
appear to the left of an arrow in a field. An ill-founded declaration has no
set of labelled trees to be carved out of, so it now fails to be constructed
rather than being assumed into existence.

@subsection{Mutually recursive datatypes}

@verbatim{
datatype.together:
  datatype Id
  | ctor
  | ...
  datatype Id
  | ctor
  | ...
}

A @tt{datatype.together:} block declares a family of datatypes at once, so a
constructor field may be at any member of the family. Every member declares
the same type parameters, constructor names are distinct across the family,
and every member must be inhabited by values the family's own constructors
build.

@rhombusblock(
  datatype.together:
    datatype Expr
    | lit(value :: Nat)
    | app(args :: Args)
    datatype Args
    | anil()
    | acons(head :: Expr, tail :: Args)
)

The family is read as one ordinary recursive datatype --- the union of every
member's constructors --- with each member carved out of it as the least set
its own constructors build, which is @rhombus(inductive, ~datum)'s
construction. So a family adds no representation and no new principle, and
each member derives exactly what a lone declaration derives, stated about its
own constructors. The family's joint induction, whose hypotheses may be about
any member, is kept by name as @tt{Member1_..._union_induct} for a proof's
@tt{~use:}.

A single @rhombus(datatype, ~datum) declaration is the one-member case of the
same form.

@section{@rhombus(function, ~datum)}

@verbatim{
function Id(arg :: Type, ...) :: Type:
  body
proof:
  ~measure: expr
}

Declares a total, terminating function. The body must be in the grammar of
@secref("expressions"); anything else is an error naming the offending
expression.

@rhombusblock(
  function app(xs :: List.of(?a), ys :: List.of(?a)) :: List.of(?a):
    match xs
    | Nil(): ys
    | Cons(x, rest): Cons(x, app(rest, ys))
)

Logically each winning clause becomes one equation, universally closed over the
clause's variables, and each equation enters the rewriter. Before any of that
the definition must pass three checks: the clauses must cover every case, every
clause must win for at least one argument shape after earlier clauses take
priority, and the recursion must be shown to terminate
(@secref("termination")). Clauses may overlap; matching is ordered and the
earliest matching clause wins in both the logical and executable readings.
The compiler prepares that checked clause matrix once. A
@rhombus(function, ~datum) defines a non-recursive matrix directly or derives
its recursive equations from the selected well-founded order. If this version
cannot construct that proof, it refuses the declaration.

Executably it emits a Rhombus @rhombus(fun) with the type annotations erased.
The erasure is why the annotations may mention type variables that have no
run-time meaning.

An optional adjacent @rhombus(proof, ~datum) block supplies a termination
argument through @tt{~measure: expression} for a definition that does not
descend structurally. It is checked only when no structural descent can be
found, so a measure on a definition that already descends is not examined.

@subsection{Mutually recursive functions}

@verbatim{
function.together:
  function Id(arg :: Type, ...) :: Type
  | (pattern, ...): body
  | ...
  function Id(arg :: Type, ...) :: Type
  | (pattern, ...): body
  | ...
}

A @tt{function.together:} block declares a family of functions at once, so a
member's body may call any member of the family. Each member declares every
parameter type and its result type --- the members are elaborated against each
other, not inferred from their bodies --- and all members use the same type
variables. A member is always called with all of its arguments. A member may
still carry its own adjacent @rhombus(proof, ~datum) block.

@rhombusblock(
  function.together:
    function a_size(a :: Args) :: Nat
    | (anil()): zero()
    | (acons(e, r)): plus(e_size(e), a_size(r))
    function e_size(e :: Expr) :: Nat
    | (lit(n)): succ(zero())
    | (app(a)): succ(a_size(a))
)

The family is read as one ordinary function over a tagged argument: a domain
datatype with one constructor per member, and a result datatype when the
members' result types differ. That function is derived by the same
well-founded machinery a lone recursive @rhombus(function, ~datum) uses, and
each member is then the plain definition that tags its arguments and reads the
result back. Each member's own clausal equations are derived from it and enter
the rewriter, so proofs see the members and never the encoding. Executably the
members are ordinary Rhombus functions calling each other.

Because a call leaves the member that made it, the descent order spans the
family: either every member supplies @tt{~measure:} into one datatype, or the
family descends structurally on one argument column per member, read through a
datatype family's union type when the recursion crosses between mutually
recursive datatypes (@secref("termination")).

A member's @rhombus(proof, ~datum) block is the ordinary one: it sits next to
that member inside the block and carries exactly one @tt{~measure:}. Since
the members' measures are read as one measure over the tag, they land in the
same type, and a measure may not call a member of its own family --- it
justifies the family's definition, so it cannot use it.

@section{@rhombus(definition, ~datum)}

@verbatim{
definition Id :: Type:
  expr
}

Declares one non-recursive constant with an explicit type. The right-hand side
is checked as a HOL term of that type and installed through HOL's basic
definition principle. Its resulting equation enters the rewriter, so later
theorems unfold uses of the definition normally.

@rhombusblock(
  definition choose_zero :: Nat:
    select (n :: Nat): n === zero()
)

Definitions are logical only: they emit no Rhombus binding and may use
noncomputable HOL terms such as @rhombus(select, ~datum). Use
@rhombus(function, ~datum) for a definition that must run: it has an
executable reading, supports pattern clauses and recursion, and therefore
accepts only the executable expression subset.

@subsection(~tag: "local-function"){Local and anonymous @rhombus(function, ~datum)}

@verbatim{
function (arg :: Type, ...) :: Type:
  body

function Id(arg :: Type, ...) :: Type:
  body
tail
}

Anywhere inside a @rhombus(function) or @rhombus(theorem) body, @tt{function}
means a HOL lambda abstraction rather than a recursive constant definition.
Parenthesized parameters with no name (@tt{function (x :: Nat) :: Nat: ...})
produce an anonymous first-class function value, usable as an ordinary
argument, result, or applied directly:

@rhombusblock(
  function make_succ() :: Nat -> Nat:
    function (x :: Nat) :: Nat: succ(x)
)

A named local @tt{function Id(...): body} desugars to @tt{let} binding
@tt{Id} to that lambda value, then the rest of the enclosing body:
@tt{function f(x): e; tail} means @tt{let f = (function (x): e) in tail}.
No new semantic mechanism is introduced --- named local functions are
ordinary non-recursive @rhombus(let) sugar, so they follow @rhombus(let)'s
own sequential scoping (@secref("expressions")):
a local function sees every earlier binding in the same body, including
earlier local functions, but not itself and not any local function
declared after it. Nesting to any depth, and lexical capture of an
enclosing parameter or @rhombus(let), both follow from this: a local
function's free variables are resolved the same way any other nested
lambda's would be.

Because a local function is a plain lambda, it has no recursive binding of
its own name and no @rhombus(proof, ~datum) block. Three shapes are
therefore rejected rather than silently accepted:

@itemlist(
  @item{A local function's body referring to its own name (local
        self-recursion).}
  @item{A local function's body referring to a local function declared
        later in the same enclosing body (a forward reference).}
  @item{A local or anonymous function's body calling the enclosing
        @rhombus(function, ~datum) that is currently being defined ---
        the top-level recursive-definition machinery is not extended to
        reach through a nested lambda.}
)

A parameter or result type may be omitted from a local or anonymous
function; it is then inferred from how the value is used, exactly like
any other omitted binder type (@secref("propositions")). A local
function may also use the case-clause form
@tt{function | (pattern, ...): body | ...} in place of an explicit
parameter list, with each case's own patterns supplying the parameters ---
the same form available for a top-level @rhombus(function, ~datum)'s
declaration-level clauses.

@section{@rhombus(inductive, ~datum)}

@verbatim{
inductive Id(Type, ...)
| Id: proposition
| ...

inductive.together:
  inductive Id(Type, ...)
  | Id: proposition
  | ...
  inductive Id(Type, ...)
  | Id: proposition
  | ...
}

Declares the least predicates closed under the given rules. Each head lists
one predicate's argument types; each rule is a closed proposition about the
predicates being declared, so it quantifies over its own variables.

@rhombusblock(
  inductive spine(Tree)
  | spine_leaf: spine(leaf())
  | spine_node: forall (r :: Tree): spine(r) ==> spine(node(leaf(), r))
)

The declaration makes one basic definition per predicate --- each is a
component of the intersection of every predicate family the rules are closed
under, which ordinary higher-order quantification already expresses --- and
then @emph{derives} three families of theorems from them: one introduction
theorem per rule, under the rule's own name; @tt{Id_induct} per predicate,
saying that any family closed under the rules contains it; and @tt{Id_cases}
per predicate, the inversion theorem, saying that membership came from some
rule concluding with that predicate. Nothing is postulated.

Predicates declared in one @tt{inductive.together:} block are mutually
recursive: they share every rule, so a rule may conclude with any of them and
reach the others through its premises.

@rhombusblock(
  inductive.together:
    inductive even_depth(Tree)
    | even_leaf: even_depth(leaf())
    | even_step: forall (t :: Tree): odd_depth(t) ==> even_depth(node(t, t))
    inductive odd_depth(Tree)
    | odd_step: forall (t :: Tree): even_depth(t) ==> odd_depth(node(t, t))
)

Those theorems are retained by name like a @rhombus(theorem, ~datum) and are
requested with @tt{~use:}; they do not enter the rewriter, so the automation
never unfolds the fixed point by itself.

A rule is rejected unless it concludes with one of the declared predicates
applied to its arguments, and unless every recursive occurrence in a premise
is an application of a declared predicate in a position the rules are monotone
in. An occurrence under @rhombus(not, ~datum), one to the left of a nested
@tt{==>}, one passed to another function, and one inside a rule's own
arguments are each refused: without monotonicity there need be no least
predicates closed under the rules, and the introduction theorems would not be
derivable.

Like @rhombus(definition, ~datum), an inductive predicate is logical only and
emits no Rhombus binding.

@section(~tag: "notation"){HOL notation}

@verbatim{
notation operator-name :: ResultType:
  operator-option
  ...
| (left-pattern operator-name right-pattern) :: ResultType:
    HOLBody
| ...
}

@rhombus(notation, ~datum) adds an operator spelling to the HOL expression
space. Its canonical parenthesized prefix, infix, and postfix heads follow
Rhombus @rhombus(operator, ~datum) case layout; legacy unparenthesized heads,
immediate @tt{|} cases, and named groups of cases are also accepted. Prefix
may be combined with infix or postfix, but infix and postfix cannot be
combined.

Each operand is one pattern from the closed HOL pattern grammar: variables,
@rhombus(_), static type annotations, supported literals and collection forms,
and declared datatype constructors. A compound operand pattern that occupies
more than one shrubbery term must be parenthesized inside the operator head,
just as for @rhombus(operator, ~datum).

Cases of each fixity are tried in source order. Unlike a general Rhombus
operator, however, the matrix must be exhaustive, every row must be reachable,
and each operand column has one HOL type. Thus notation cannot use dynamic
patterns to dispatch between unrelated runtime types.

At each use, arbitrary operand expressions are evaluated once, from left to
right, before the selected fixity's cases match their values. A shared or
case-local @rhombus(::, ~bind) annotation is a static HOL result type, not a
Rhombus predicate check or converter:

@rhombusblock(
  notation <&> :: Boolean:
    ~order: hol_conjunction
    ~associativity: ~none
  | (#false <&> _):
      #false
  | (#true <&> right):
      right

  theorem conjunction_example:
    false <&> true
)

The implementation of every case is a HOL body, including sequential
@rhombus(let), @rhombus(match), and local @rhombus(function) forms. Notation
normalizes to an immediately applied anonymous Core function and the same
ordered pattern matrix feeds logical elaboration and executable lowering.
Actual operand types and pattern constraints are available while overloaded
calls in a body are resolved.

The notation itself has no ordinary Rhombus binding or repetition binding and
adds no logical constant. @rhombus(:~, ~bind), @rhombus(~unsafe),
@rhombus(~name), @rhombus(~who), partial no-match behavior, effects, and
multiple values are deliberately unsupported. Outside a logical declaration,
use the body's ordinary Rhombus operations directly or declare a separate
ordinary @rhombus(operator, ~datum); the two expression spaces remain explicit.

The precedence options are the ones accepted by Rhombus
@rhombus(operator, ~datum), including @rhombus(~order),
@rhombus(~stronger_than), @rhombus(~weaker_than),
@rhombus(~same_as), @rhombus(~same_on_left_as),
@rhombus(~same_on_right_as), and @rhombus(~associativity).
A named order supplies its associativity; an explicit associativity is checked
against that order. Without a shared named block, only the first case of each
fixity may declare options. Shared and case-local options cannot repeat the
same kind, and @rhombus(~associativity) applies only to an infix fixity.
The available HOL orders, strongest to weakest, are
@rhombus(hol_application), @rhombus(hol_power),
@rhombus(hol_prefix_arithmetic), @rhombus(hol_multiplication),
@rhombus(hol_addition), @rhombus(hol_append),
@rhombus(hol_set_intersection), @rhombus(hol_set_union),
@rhombus(hol_relation), @rhombus(hol_equality),
@rhombus(hol_negation), @rhombus(hol_conjunction),
@rhombus(hol_disjunction), @rhombus(hol_implication), and
@rhombus(hol_equivalence). See @secref("propositions") for the built-in
operators at each order.

Multiple fixities of one operator can share options:

@rhombusblock(
  notation <~>:
    ~order: hol_conjunction
  | (<~> value):
      neg(value)
  | (left <~> right):
      conj(left, right)
)

Different spellings use separate, symmetric declarations:

@rhombusblock(
  notation (left <+> right):
    ~order: hol_addition
    custom_add(left, right)

  notation (a <++> b):
    ~order: hol_addition
    custom_add(a, b)
)

Notation definitions take effect before the following declaration is
enforested. Export the HOL-space binding explicitly:

@rhombusblock(
  export:
    only_space hol_expr:
      <&>
)

Importing that module with @rhombus(open) makes the notation available to
following @rhombus(function) and @rhombus(theorem) declarations.

@section{Function overloading}

@rhombus(overload, ~datum) adds an overload clause to a callable function
name. No separate registration form or operator-specific overload form is
needed. Direct calls and calls in notation implementation expressions use the
same resolver.

@verbatim{
overload add(Nat, Nat) = nat_add
overload add(Integer, Integer) = int_add

notation (left <+> right):
  ~order: hol_addition
  add(left, right)
}

Here @tt{x <+> y} binds @tt{left} and @tt{right} before checking
@tt{add(left, right)}. The ordinary elaborator sees the call, checks whether
@tt{add} has overload clauses, and selects a clause from the argument types and,
when available, the expected result type. A successful call becomes a direct
call to the selected implementation constant. Kernel terms contain no overload
node, and generated executable code performs no runtime type test.

The notation-facing overloaded names are @tt{add}, @tt{subtract},
@tt{negate}, @tt{multiply}, @tt{power}, @tt{less}, @tt{less_equal},
@tt{greater}, @tt{greater_equal}, @tt{append}, @tt{member}, @tt{union}, and
@tt{intersection}. The standard library also makes common operations available
through @tt{map}, @tt{empty}, @tt{size}, @tt{reverse}, @tt{flatten},
@tt{height}, @tt{contains}, @tt{delete}, @tt{to_list}, @tt{compare},
@tt{minimum}, and @tt{maximum}. Importing a theory imports its overload
registry together with its constants and theorems.

The standard method set is:

@itemlist(
  @item{@tt{Nat}: arithmetic, power, four order comparisons, three-way
        comparison, minimum, and maximum.}
  @item{@tt{Integer} and @tt{Rational}: arithmetic, unary negation, four order
        comparisons, three-way comparison, minimum, and maximum.}
  @item{@tt{Option.of(?a)}: map and empty.}
  @item{@tt{List.of(?a)}: append, map, empty, size, reverse, flatten, and
        contains.}
  @item{@tt{NonemptyList.of(?a)}: append, map, and conversion to a list.}
  @item{@tt{BinaryTree.of(?a)} and @tt{RoseTree.of(?a)}: map, size, flatten,
        height, and contains.}
  @item{@tt{FiniteSet.of(?a)}: empty, size, contains, delete, and conversion to
        a list.}
  @item{@tt{FiniteMap.of(?k, ?v)}: value map, empty, size, key containment,
        deletion, and conversion to a list.}
  @item{@tt{String}: append, map, empty, size, and reverse.}
  @item{@tt{?a -> Boolean} sets: membership, union, intersection, and
        subtraction.}
  @item{@tt{?a -> ?a -> Boolean} relations: union, intersection, and
        subtraction.}
)

Each clause declares the complete argument tuple. Every argument and the
expected result type participate in first-order unification. Clauses for one
function name must have one arity and must not overlap; an overlap is rejected
when the clause is registered instead of creating an order-dependent winner.
No applicable clause is a compile error listing the available candidates.

The accepted forms are:

@verbatim{
overload function_name(ArgumentType, ...) = constant
overload function_name(ArgumentType, ...) :: ResultType = constant

overload function_name(name :: ArgumentType, ...) = constant(name, ...)
}

The result annotation is optional when the implementation constant determines
it. The first @rhombus(overload, ~datum) clause establishes a callable
function name; no separate declaration is required:

@verbatim{
overload map(?a -> ?b, List.of(?a)) = list_map
overload empty() = nil

function mapped_empty(f :: Nat -> Nat) :: List.of(Nat):
  map(f, empty())
}

The outer expected @tt{List.of(Nat)} result selects @tt{map}'s clause; its
selected argument signature then supplies the expected type that selects
@tt{empty}.

A bare implementation constant receives arguments in signature order. When
its parameter order differs, name the signature arguments and write a call
template:

@verbatim{
notation (element in collection):
  ~order: hol_relation
  member(element, collection)

overload member(
  element :: ?a,
  collection :: ?a -> Boolean
) = set_member(collection, element)

overload greater(
  left :: Integer,
  right :: Integer
) = int_lt(right, left)
}

Thus @tt{x in s} lowers to @tt{set_member(s, x)}, while @tt{x > y} lowers to
@tt{int_lt(y, x)}. A template must use every overload argument exactly once.
Zero-argument overloaded functions may use the expected result type for
contextual selection, so nested calls such as @tt{map(f, empty())} resolve
statically.

@section(~tag: "automata"){Executable automata}

The standard automata library has one representation for each kind of
automaton, and every automaton operation is declared with
@rhombus(function, ~datum) so that it has both a logical meaning and ordinary
run-time code.

@tt{DFA.of(?q, ?a)}, constructed by @tt{dfa}, stores one initial state, a
transition function, and a final-state predicate. @tt{dfa_run} follows the
transition function over a @tt{List.of(?a)}, and @tt{dfa_accepts} tests the
resulting state.

The nondeterministic representations make their finite search space explicit:

@itemlist(
 @item{@tt{NFA.of(?q, ?a)}, constructed by @tt{nfa}, stores an equality
  decider (@tt{?q -> ?q -> Boolean}), a @tt{FiniteSet.of(?q)} state universe,
  an initial @tt{FiniteSet.of(?q)}, a transition predicate
  (@tt{?q -> ?a -> ?q -> Boolean}), and a final-state predicate.}
 @item{@tt{EpsilonNFA.of(?q, ?a)}, constructed by @tt{epsilon_nfa}, stores the
  same data and an epsilon-transition predicate
  (@tt{?q -> ?q -> Boolean}).}
)

The NFA operations are @tt{nfa_run}, @tt{nfa_accepts}, and
@tt{nfa_determinize}. The epsilon-NFA operations are
@tt{epsilon_nfa_closure}, @tt{epsilon_nfa_run},
@tt{epsilon_nfa_accepts}, @tt{epsilon_nfa_eliminate}, and
@tt{epsilon_nfa_determinize}. Run and epsilon-closure operations return
@tt{FiniteSet.of(?q)}. Epsilon elimination returns @tt{NFA.of(?q, ?a)}.
Determinization returns @tt{DFA.of(FiniteSet.of(?q), ?a)}, whose states are
finite sets of source states.

Every destination search enumerates only the stored universe and uses the
stored equality decider for finite-set operations. Epsilon closure is bounded
structurally by consuming the universe list as fuel, so it terminates even
when epsilon transitions contain cycles. The universe is therefore part of
the automaton representation rather than optional metadata.

@tt{nfa_determinize_accepts_iff} states that @tt{nfa_accepts} agrees with
acceptance by the DFA returned from @tt{nfa_determinize} for every word, and
@tt{nfa_determinize_language} gives the corresponding extensional language
equality. These theorems are unconditional: NFA acceptance and the subset
construction use the same finite-set runner.

Likewise, @tt{epsilon_nfa_determinize_accepts_iff} and
@tt{epsilon_nfa_determinize_language} are unconditional preservation theorems
for @tt{epsilon_nfa_accepts} and the DFA returned by
@tt{epsilon_nfa_determinize}. The epsilon-NFA source and the produced DFA
share the same bounded closure and subset-construction computation.

Finite-universe epsilon elimination additionally has a representation
obligation. @tt{epsilon_nfa_well_formed(m)} requires the stored equality
decider to agree with logical equality, the initial states to belong to the
explicit universe, and the universe to be closed under epsilon and symbol
transitions. Under that explicit hypothesis,
@tt{epsilon_nfa_eliminate_accepts_iff} proves word-acceptance preservation and
@tt{epsilon_nfa_eliminate_language} proves language preservation. No
well-formedness premise is required by either determinization theorem, because
those theorems compare the executable runners directly.

@subsection{Generic regular expressions}

Importing @tt{rhombus/hol/stdlib} with @rhombus(open) exposes the generic
regular-expression library. @tt{Regexp.of(?a)} is an AST over an arbitrary
symbol type @tt{?a} with exactly six constructors:

@itemlist(
 @item{@tt{regexp_none()} accepts no words and @tt{regexp_epsilon()} accepts
  only the empty word.}
 @item{@tt{regexp_atom(predicate)} accepts a one-symbol word when its
  executable @tt{?a -> Boolean} predicate accepts that symbol, so compiled
  matching remains ordinary run-time code.}
 @item{@tt{regexp_alternate(left, right)},
  @tt{regexp_sequence(left, right)}, and @tt{regexp_star(body)} denote union,
  concatenation, and Kleene closure.}
)

@tt{regexp_literal(decide_equal, value)} is a convenience function that
constructs an atom from an executable equality decider; it is not a seventh
AST constructor. The inductively defined relation
@tt{regexp_accepts(r, word)} gives the language semantics independently of
every automaton representation and runner. Its rules give epsilon the empty
word, atoms their accepted singleton words, alternation either branch,
sequencing the concatenation of two accepted words, and star zero or more
accepted body words.

The standard library defines @tt{Codepoint} as a nominal wrapper
@tt{codepoint(Nat)} and @tt{String} as @tt{text(List.of(Codepoint))}. The public
@tt{codepoint_to_nat} operation unwraps it, and curried @tt{codepoint_equal}
provides executable equality. The wrapper deliberately accepts every
@tt{Nat}; it carries no Unicode scalar-value invariant. Thus @tt{Codepoint} is
not interchangeable with @tt{Nat}, and @tt{String} is not interchangeable
with @tt{List.of(Codepoint)}, without treating either nominal boundary as
validation.

@tt{regexp_compile(pattern :: String) :: Option.of(Regexp.of(Codepoint))}
parses the standard-library @tt{String} codepoint list into an executable
regular-expression AST. Its grammar is:

@verbatim{
pattern       ::= ε | alternation
alternation   ::= concatenation ("|" concatenation)*
concatenation ::= repetition+
repetition    ::= atom ("*")?
atom          ::= literal | "." | "\" codepoint | "(" alternation ")"
literal       ::= any Unicode codepoint other than |, *, (, ), ., or \
}

Here @tt{ε} denotes empty input in the start rule, not a pattern codepoint. The
compiler unwraps each @tt{Codepoint} with @tt{codepoint_to_nat} to recognize
the operators by their ASCII values: @tt{|} is 124, @tt{*} is 42, @tt{(} is
40, @tt{)} is 41, @tt{.} is 46, and backslash is 92. Alternation has the
lowest precedence, implicit concatenation the next, and postfix @tt{*} the
highest; parentheses group an alternation. Each unescaped literal denotes an
atom using executable @tt{codepoint_equal}. @tt{.} denotes an atom whose
predicate accepts every codepoint. A backslash makes exactly the next
codepoint a literal, including any operator codepoint.

The empty entire pattern compiles to @tt{some(regexp_epsilon())}. Every other
successful parse consumes the complete input and returns @tt{some(result)},
where @tt{result} is the resulting @tt{Regexp.of(Codepoint)}. Dangling
escapes, unmatched parentheses, leading or trailing @tt{|}, empty alternatives
or groups, leading or repeated @tt{*}, and any leftover malformed input are
rejected with @tt{none()}.

Compilation follows the conventional Thompson pipeline
@tt{Regexp -> EpsilonNFA -> NFA -> DFA}. @tt{regexp_to_epsilon_nfa} performs
Thompson construction, @tt{regexp_to_nfa} eliminates epsilon transitions, and
@tt{regexp_to_dfa} determinizes the resulting NFA.
@tt{regexp_matches(r, word)} executes the DFA and tests the whole word; it is
not a substring search.

The principal compiler theorems are
@tt{regexp_to_epsilon_nfa_well_formed} and
@tt{regexp_to_epsilon_nfa_accepts_iff} for the Thompson result;
@tt{regexp_to_nfa_accepts_iff} and @tt{regexp_to_nfa_language} for epsilon
elimination; and @tt{regexp_to_dfa_accepts_iff} and
@tt{regexp_to_dfa_language} for determinization. The direct semantic
correspondences are @tt{regexp_to_nfa_semantics_iff} and
@tt{regexp_to_dfa_semantics_iff}. The executable matcher is related to each
stage by @tt{regexp_matches_epsilon_nfa_iff},
@tt{regexp_matches_nfa_iff}, and @tt{regexp_matches_dfa_iff}, while
@tt{regexp_matches_iff} is the end-to-end correctness theorem
@tt{regexp_matches(r, word) <=> regexp_accepts(r, word)}.

@tt{regexp_find(r, input)} returns an @tt{Option.of(RegexpMatch)}.
@tt{regexp_match(start, end)} constructs a result, and
@tt{regexp_match_start} and @tt{regexp_match_end} select its @tt{Nat} offsets.
Search is leftmost-longest: it chooses the earliest start having a match, then
the greatest accepted end at that start. Ranges are half-open
@tt{[start, end)}, measured in input-list elements; @tt{start === end} is a
valid zero-width match.

@tt{regexp_replace_first(r, replacement, input)} replaces only that
leftmost-longest range. @tt{regexp_replace_all(r, replacement, input)} repeats
the same search over the unconsumed original input; replacement symbols are
never searched. A nonempty match consumes its range. After a zero-width match
before EOF, replace-all emits the replacement, copies exactly one original
symbol at the match position unchanged, and resumes after that symbol. At a
zero-width match at EOF, it emits the replacement once and stops.

The four String adapters are @tt{string_regexp_matches},
@tt{string_regexp_find}, @tt{string_regexp_replace_first}, and
@tt{string_regexp_replace_all}. They accept @tt{Regexp.of(Codepoint)} and
convert strings with @tt{string_to_codepoints} and
@tt{string_from_codepoints}. Consequently String search offsets count
codepoints, not encoded bytes, and replacement follows exactly the generic
list behavior above.

@section{@rhombus(theorem, ~datum) and @rhombus(proof, ~datum)}

@verbatim{
theorem Id:
  proposition

proof:
  proof_option
  ...

proof_option = ~induct: [Id, ...]
             | ~split: [proposition, ...]
             | ~choose: [term, ...]
             | ~use: [Id, ...]
             | ~skip: [Id, ...]
             | ~disable: [Id, ...]
             | ~limit: nonnegative_integer
             | ~extensionality: [Id, ...]
}

States a proposition and proves it while the module compiles. The proposition
grammar is in @secref("propositions").

The @rhombus(proof, ~datum) clause is optional and defaults to the same
waterfall automation as an empty option configuration. When present, it
must follow its theorem immediately and contain one or more option groups.

@rhombusblock(
  theorem app_nil_r:
    forall (xs :: List.of(?a)): app(xs, Nil()) === xs

  theorem app_assoc:
    forall (xs :: List.of(?a), ys :: List.of(?a), zs :: List.of(?a)):
      app(app(xs, ys), zs) === app(xs, app(ys, zs))
  proof:
    ~induct: [xs]
)

Every theorem is retained by name but is not added to the global rule database.
Use a theorem explicitly in a proof with the @rhombus(~use) option.
Adding an unrelated theorem therefore cannot change later automation.

Every proof-option keyword may appear at most once. Every bracketed option list
must be nonempty, retains its written order, and cannot be continued by
repeating the keyword.

The @rhombus(~induct) list gives strict nested induction hints. The first name
is consumed when an unresolved branch reaches induction; the remaining names
are propagated in order to every generated subgoal. A branch where its next
named variable cannot be inducted on is an explicit proof failure. Once all
listed names are consumed, the ordinary induction heuristic resumes.
@rhombus(~split) performs its Boolean case splits in list order.
@rhombus(~choose) supplies existential candidates in list order, before the
case splits. @rhombus(~use) names theorems to enable for this proof only, which
is useful when a lemma is too aggressive to leave in the rewriter permanently.
@rhombus(~disable) names rules to disable for this proof only.
@rhombus(~skip) names waterfall stages --- @tt{simplify}, @tt{eliminate},
@tt{fertilize}, @tt{generalize}, @tt{irrelevance}, @tt{induct} --- to skip
for this proof only; see @secref("prover"). @rhombus(~limit) sets this
proof's nonnegative search-step ceiling. None of the options change what the
prover is allowed to conclude, only what it tries.

The @rhombus(~extensionality) list names fresh variables for sequential
function-extensionality steps. All names are consumed in order before
@rhombus(~choose), @rhombus(~split), or the ordinary waterfall runs. Each step
reduces an equality of functions (including @tt{Set} values, which are
functions to @rhombus(Boolean)) to pointwise equality using the kernel's
derived @tt{EXT} rule, with no new axiom. A non-function equality at any
requested step is a compile-time error, not a silent no-op:

@rhombusblock(
  theorem funs_equal:
    double === add_self
  proof:
    ~extensionality: [x]
)

@section(~tag: "importing"){Importing a theory}

There is no separate form for importing a theory. An ordinary Rhombus
@rhombus(import) of a @rhombuslangname(rhombus/hol) module brings both halves:
its functions, because that is what an import does, and its theory, so its
datatypes, definitions and theorems are available to the prover.

@rhombusblock(
  import: "list_proofs.rhm" open
)

A module is recognised as a theory by having one --- every
@rhombuslangname(rhombus/hol) module publishes its theory in a
@rhombus(hol_theory, ~datum) submodule --- so this is checked, not guessed from
the shape of the path. An import of anything else passes through untouched, and
one @rhombus(import) form may name both:

@rhombusblock(
  import:
    "plain_helper.rhm" open
    "list_proofs.rhm" open
)

Adoption is transitive: the imported theory already contains whatever it
imported in turn, so a dependency does not have to be named again.

@subsection{Ordering}

Two rules follow from keeping the chain of theories linear. An import of a
theory must come before the module's own logical declarations, and when there
is more than one they must be given in dependency order. Adopting a theory that
is not an extension of the one already in scope is an error, because a module
holding two unrelated theories could not use their theorems together.

@subsection{Forms that cannot be read}

To find the module path in an import clause, the longest prefix of the clause
that parses as one is taken. That covers @rhombus("path.rhm"),
@rhombus(lib("collection/path.rhm")) and @rhombus(collection/path), with any
modifiers after them.

It does not cover a clause whose path is inside a block, as in
@rhombus(import: meta: "path.rhm"). Rather than drop such a theory silently,
an import that names a theory in a form this version cannot read is an error,
and says so.

@section{@rhombus(quickcheck, ~datum)}

@verbatim{
quickcheck Id:
  forall (arg :: ConcreteType, ...): proposition

quickcheck Id(~samples: n, ~size: n, ~seed: n):
  forall (arg :: ConcreteType, ...): proposition
}

Tests the executable reading of a HOL proposition on generated values at run
time. The body uses exactly the same proposition syntax as
@rhombus(theorem, ~datum), including @rhombus(===, ~datum),
@rhombus(and, ~datum), @rhombus(or, ~datum), and @rhombus(not, ~datum).
Passing a quickcheck is evidence against simple mistakes, not a proof.

The intended workflow requires no duplicated property:

@rhombusblock(
  quickcheck rev_involutive(~samples: 500):
    forall (xs :: List.of(Nat)): rev(rev(xs)) === xs
)

After it passes, change the declaration head and add a proof:

@rhombusblock(
  theorem rev_involutive:
    forall (xs :: List.of(Nat)): rev(rev(xs)) === xs
  proof:
    ~induct: [xs]
)

Input types must be concrete because every input needs a run-time generator.
A generator and shrinker are registered alongside each datatype declaration
under the type's own name. The registry works through transitive imports; the
datatype need not be declared in the quickcheck's own module.

The proposition must have an executable reading. Function calls, conditionals,
Boolean connectives, equality, numerals, and statically overloaded calls are
lowered through the same runtime path used by a declared
@rhombus(function, ~datum). Logic-only constants and existential
quantification are rejected.

@rhombus(~samples) selects the number of generated input tuples.
@rhombus(~size) bounds generated-value depth. @rhombus(~seed) makes a run
reproducible; its default is deterministic, and every counterexample report
includes the effective seed and number of shrinking steps.

A successful declaration produces no binding and adds nothing to the theory.
A falsified property fails module initialization immediately with its shrunk
inputs. Consequently, @rhombus(quickcheck, ~datum) must appear directly in a
@rhombuslangname(rhombus/hol) module body, like
@rhombus(theorem, ~datum); run the module or use @tt{raco test} to execute it.
