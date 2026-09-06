#lang rhombus/scribble/manual

@title(~tag: "declarations"){Declarations}

These are the forms that @rhombuslangname(rhombus/hol) gives a logical reading.
Anything else in a module body is ordinary Rhombus.

Most of these are recognised by scanning the module body, not by binding their
first word, so such a declaration must appear directly in the module body. It
cannot appear inside a @rhombus(block), inside a @rhombus(fun) body, or in the
expansion of a user-written macro. This is a limitation of this version.

@rhombus(check_property, ~datum) is the exception: it touches none of the
state the others thread through the module (see its own section below), and
that is what let it become a genuine, independently bound macro. It can
appear as the expansion of a user's own macro, the same as @rhombus(fun) or
@rhombus(class) could.

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

Logically this postulates the usual characterisation of the type: constructors
are injective, distinct constructors build distinct values, every value is
built by some constructor, and the induction principle holds. Field selectors
and constructor discriminators are declared too, so @rhombus(List) above brings
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
appear to the left of an arrow in a field. Without that check the axioms would
be inconsistent, so this is the load-bearing soundness condition of the whole
datatype mechanism.

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
       | auto(~induct: Id, ~using: [Id, ...], ~do_not: [Id, ...])
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
aggressive to leave in the rewriter permanently. @rhombus(~do_not) names
waterfall stages --- @tt{simplify}, @tt{eliminate}, @tt{fertilize},
@tt{generalize}, @tt{irrelevance}, @tt{induct} --- to skip for this proof
only; see @secref("prover"). It changes what the prover tries, never what it
is allowed to conclude.

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
