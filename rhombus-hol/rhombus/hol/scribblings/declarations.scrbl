#lang rhombus/scribble/manual

@title(~tag: "declarations"){Declarations}

These are the forms that @rhombuslangname(rhombus/hol) gives a logical reading.
Anything else in a module body is ordinary Rhombus.

The declarations that change the current theory are recognised by the
language's module-block expander and must appear directly in the module body.
They cannot appear inside a @rhombus(block), inside a @rhombus(fun) body, or
in the expansion of a user-written macro.

@rhombus(notation, ~datum) and @rhombus(check_property, ~datum) are genuine
bound macros. Notation definitions are expanded one declaration at a time, so
a binding established by one is visible while the following logical
declaration is enforested.

@section{@rhombus(type, ~datum)}

@verbatim{
type Id
| ctor
| ...

type Id(~tyvar, ...)
| ctor
| ...

ctor = CtorId()
     | CtorId(field :: Type, ...)
}

Declares an @deftech{algebraic datatype}. A type variable is written
@rhombus(~a) rather than @tt{'a}, because @tt{'} opens a syntax literal and
could not be lexed here.

@rhombusblock(
  type List(~a)
  | Nil()
  | Cons(head :: ~a, tail :: List(~a))
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

Executably it emits one Rhombus class per constructor, related by an interface
so that a value can be matched against any of them. The classes are ordinary:
they compare structurally with @rhombus(==) and print readably.

A declaration is rejected unless every recursive occurrence of the type is
@deftech{strictly positive} --- informally, the type being declared may not
appear to the left of an arrow in a field. An ill-founded declaration has no
set of labelled trees to be carved out of, so it now fails to be constructed
rather than being assumed into existence.

@section{@rhombus(function, ~datum)}

@verbatim{
function Id(arg :: Type, ...) :: Type:
  body

function Id(arg :: Type, ...) :: Type ~measure(expr):
  body
}

Declares a total, terminating function. The body must be in the grammar of
@secref("expressions"); anything else is an error naming the offending
expression.

@rhombusblock(
  function app(xs :: List(~a), ys :: List(~a)) :: List(~a):
    match xs
    | Nil(): ys
    | Cons(x, rest): Cons(x, app(rest, ys))
)

Logically each clause becomes one equation, universally closed over the
clause's variables, and each equation enters the rewriter. Before any of that
the definition must pass three checks: the clauses must cover every case, no
two may overlap, and the recursion must be shown to terminate
(@secref("termination")).

Executably it emits a Rhombus @rhombus(fun) with the type annotations erased.
The erasure is why the annotations may mention type variables that have no
run-time meaning.

@rhombus(~measure) supplies a termination argument for a definition that does
not descend structurally. It is checked only when no structural descent can be
found, so a measure on a definition that already descends is not examined.

@section(~tag: "surface-operators"){HOL expression notation}

@verbatim{
notation (left op right):
  [~runtime: expression]
  [~logic: Constant(left, right)]
  ~order: order
}

@rhombus(notation, ~datum) assigns runtime meaning, logical meaning, or both
to an infix spelling. At least one of @rhombus(~runtime) and
@rhombus(~logic) is required. The declaration creates only the bindings
requested by its clauses:

@itemlist(
  @item{With only @rhombus(~runtime), the notation is an ordinary Rhombus
        operator. It is not accepted in theorem statements or logical
        @rhombus(function) bodies.}
  @item{With only @rhombus(~logic), the notation is available in theorem
        statements and proof @rhombus(~cases) propositions. It has no
        ordinary Rhombus binding and is rejected in a logical
        @rhombus(function) body.}
  @item{With both clauses, the notation is reflected: it is available as an
        ordinary Rhombus operator, in logical @rhombus(function) bodies, and
        in theorem statements.}
)

A logic-only notation can describe proof syntax that has no useful runtime
reading:

@rhombusblock(
  notation (x <&> y):
    ~logic: conj(x, y)
    ~order: hol_conjunction

  theorem conjunction_example:
    true <&> true
)

A reflected notation gives the same spelling separate runtime and HOL
interpretations:

@rhombusblock(
  notation (x <+> y):
    ~runtime: x && y
    ~logic: conj(x, y)
    ~order: hol_conjunction
)

The notation author is responsible for making the two clauses denote the same
operation. The definition and proof machinery use the corresponding side.
The @rhombus(~logic) clause must have the form
@rhombus(Constant(left, right), ~datum), using the two declared operand names
in order.

The available named orders, strongest to weakest, are
@rhombus(hol_application), @rhombus(hol_equality),
@rhombus(hol_negation), @rhombus(hol_conjunction),
@rhombus(hol_disjunction), @rhombus(hol_implication), and
@rhombus(hol_equivalence). See @secref("propositions") for the built-in
operators at each order.

Notation declarations take effect before the following declaration is
enforested. Exporting and importing a reflected notation brings both its
ordinary and HOL-space bindings:

@rhombusblock(
  export: both <+>
)

@subsection{Migrating operator extensions}

An ordinary @rhombus(operator) remains runtime-only. Code that previously
expected the proposition parser to recognize an operator by spelling should
instead declare @rhombus(notation, ~datum) with the meanings it needs. There
is no numeric precedence hook and no parser table to modify.

Choose a named @tt{hol_*} order. Omit @rhombus(~runtime) for proof-only
notation; omit @rhombus(~logic) for runtime-only notation. Existing ordinary
operators intentionally remain rejected by logical declarations instead of
being assigned a default logical meaning.

@section{@rhombus(theorem, ~datum) and @rhombus(proof, ~datum)}

@verbatim{
theorem Id:
  proposition

theorem ~attribute ... Id:
  proposition
proof:
  tactic

attribute = ~rewrite_rule | ~simp

tactic = auto
       | auto ~induct: Id
       | auto(~induct: Id, ~using: [Id, ...], ~do_not: [Id, ...],
              ~in_theory: [Id, ...], ~cases: [proposition, ...])
}

States a proposition and proves it while the module compiles. The proposition
grammar is in @secref("propositions").

The @rhombus(proof, ~datum) clause is optional and defaults to
@rhombus(auto, ~datum); write one only when the prover needs a hint. It must
follow its theorem immediately.

@rhombusblock(
  theorem app_nil_r:
    forall (xs :: List(~a)): app(xs, Nil()) === xs

  theorem ~rewrite_rule app_assoc:
    forall (xs :: List(~a), ys :: List(~a), zs :: List(~a)):
      app(app(xs, ys), zs) === app(xs, app(ys, zs))
  proof:
    auto ~induct: xs
)

@rhombus(~rewrite_rule) (equivalently @rhombus(~simp)) adds the proved theorem
to the rewriter, so later proofs can use it. Without an attribute a theorem is
recorded but not used for rewriting.

The options of @rhombus(auto, ~datum) must be parenthesised when there is more
than one: two keyword-and-block forms written in sequence nest the second
inside the first.

@rhombus(~induct) names a variable to induct on. @rhombus(~using) names
theorems to enable for this proof only, which is useful when a lemma is too
aggressive to leave in the rewriter permanently. @rhombus(~in_theory) names
rules to disable for this proof only, on top of whatever a module-level
@rhombus(disable_rules, ~datum) already disabled --- useful when an enabled
rule is firing somewhere it should not, without turning it off for the whole
module. @rhombus(~cases) splits the goal on one or more Boolean terms up
front, one true/false branch per term, before the waterfall runs; the terms
may refer to the theorem's own quantified variables. @rhombus(~do_not) names
waterfall stages --- @tt{simplify}, @tt{eliminate}, @tt{fertilize},
@tt{generalize}, @tt{irrelevance}, @tt{induct} --- to skip for this proof
only; see @secref("prover"). None of these change what the prover is
allowed to conclude, only what it tries.

@section{@rhombus(disable_rules, ~datum) and @rhombus(enable_rules, ~datum)}

@verbatim{
disable_rules [Id, ...]
enable_rules [Id, ...]
}

Switch rewrite rules off and on for the declarations that follow. The names are
those of theorems, of functions (which names all of that function's equations
at once), of datatypes, of a datatype's subterm relation, and of the two
built-in groups @rhombus(propositional, ~datum) and
@rhombus(conditional, ~datum).

@rhombusblock(
  disable_rules [app]

  theorem about_app_without_unfolding_it:
    forall (xs :: List(~a)): app(xs, Nil()) === app(xs, Nil())

  enable_rules [app]
)

The usual reason is to keep a proof from unfolding something --- to reason
about a function through its proved properties rather than its equations --- or
to park a lemma that is useful in one place and too aggressive everywhere else.
For the latter, @rhombus(~using) on a single proof is usually better than
disabling the rule around it.

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

@section{@rhombus(check_property, ~datum)}

@verbatim{
check_property Id:
  forall (arg :: Type, ...): expression

check_property Id(~samples: n, ~size: n):
  forall (arg :: Type, ...): expression
}

Tests an executable Boolean expression on generated values at run time. The
body is ordinary Rhombus expression syntax, not the logical proposition syntax
used by @rhombus(theorem, ~datum), so equality is written @rhombus(==). This is
not a proof; it is the cheap check you run while you are still working out what
is true.

@rhombusblock(
  check_property rev_involutive(~samples: 500):
    forall (xs :: List(Nat)): rev(rev(xs)) == xs
)

The binder types must be concrete --- a generator cannot be built for a type
variable. A generator and a shrinker are registered alongside each datatype
declaration, under the type's own name, in a run-time registry that
@rhombus(check_property, ~datum) draws from; any declared datatype can be
sampled, and a counterexample is shrunk before it is reported.

The body is not restricted to an equation. It may use any Rhombus expression
that produces a Boolean, including function calls, conditionals, local
definitions, and Boolean operators.

Because the registry is keyed by name rather than by an identifier this
module would have to import, a type need not be declared in the same module
as the @rhombus(check_property, ~datum) that samples it, or even be imported
directly --- being pulled in transitively, through some other import, is
enough. @rhombus(check_property, ~datum) can equally be written in an
ordinary @rhombuslangname(rhombus) module that never declares
@rhombuslangname(rhombus/hol) as its language at all, as long as it imports
@rhombus(check_property) and the types it needs.

@rhombus(~samples) is how many values to try, @rhombus(~size) bounds how deep a
generated value can get. The declaration's value is the outcome, so a test can
assert on it.

Unlike the other forms on this page, @rhombus(check_property, ~datum) is a
genuine, independently bound macro: it never touches the theory a module
builds up, since checking a property means running the emitted code rather
than proving anything, so there is no state for it to thread through. That
also means it can be written by a macro of the user's own, and Rhombus's
ordinary expansion will still find it.

@section{@rhombus(declare, ~datum) and @rhombus(expect, ~datum)}

@verbatim{
declare Id
expect [Id, ...]
}

@rhombus(expect, ~datum) asserts, at compile time, that the module has declared
exactly the named things in exactly that order, and is an error otherwise.
@rhombus(declare, ~datum) adds a name to that record without declaring anything
logical.

These exist for testing the language itself. They are documented because they
are visible, not because a proof development needs them.

@section{@rhombus(axiomatic_function, ~datum)}

The same grammar as @rhombus(function, ~datum), and a different contract: it
@emph{postulates} its clausal equations rather than deriving them. Always ---
not only when the derivation would have failed. A form whose meaning depended
on which recursion schemes this version happens to handle is the thing having
two forms is for.

Termination, exhaustiveness and non-overlap are still checked, because those
are what make postulating the equations a conservative extension; see
@secref("termination"). What is skipped is the proof.

@rhombus(function, ~datum) refuses a definition whose recursion it cannot
build a well-founded order for, so an ordinary declaration never extends the
theory by assumption. This is the form to write when you want one anyway; see
@secref("trust") for what it costs.
