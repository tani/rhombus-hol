#lang rhombus/scribble/manual

@title(~tag: "declarations"){Declarations}

These are the forms that @rhombuslangname(rhombus/hol) gives a logical reading.
Anything else in a module body is ordinary Rhombus.

The declarations that change the current theory, including
@rhombus(dispatch, ~datum), are recognised by the language's module-block
expander and must appear directly in the module body. They cannot appear
inside a @rhombus(block), inside a @rhombus(fun) body, or in the expansion of
a user-written macro.

@rhombus(notation, ~datum) is a genuine bound macro. Notation definitions are
expanded one declaration at a time, so a binding established by one is visible
while the following logical declaration is enforested.

@section{@rhombus(type, ~datum)}

@verbatim{
type Id
| ctor
| ...

type Id(?tyvar, ...)
| ctor
| ...

ctor = CtorId()
     | CtorId(field :: Type, ...)
}

Declares an @deftech{algebraic datatype}. A type variable is written
@rhombus(?a).

@rhombusblock(
  type List(?a)
  | Nil()
  | Cons(head :: ?a, tail :: List(?a))
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
  function app(xs :: List(?a), ys :: List(?a)) :: List(?a):
    match xs
    | Nil(): ys
    | Cons(x, rest): Cons(x, app(rest, ys))
)

Logically each clause becomes one equation, universally closed over the
clause's variables, and each equation enters the rewriter. Before any of that
the definition must pass three checks: the clauses must cover every case, no
two may overlap, and the recursion must be shown to terminate
(@secref("termination")).
The compiler prepares that checked clause matrix once. An ordinary
@rhombus(function, ~datum) defines a non-recursive matrix directly or derives
its recursive equations from the selected well-founded order; the explicit
@rhombus(axiomatic_function, ~datum) form reuses the same preparation and
postulates those equations instead.


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

The anonymous @rhombus(notation, ~datum) form assigns runtime meaning, logical
meaning, or both to an infix spelling. At least one of @rhombus(~runtime) and
@rhombus(~logic) is required. The declaration creates only the bindings
requested by its clauses:

@itemlist(
  @item{With only @rhombus(~runtime), the notation is an ordinary Rhombus
        operator. It is not accepted in theorem statements or logical
        @rhombus(function) bodies.}
  @item{With only @rhombus(~logic), the notation is available in theorem
        statements and proof @rhombus(split) propositions. It has no
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
@rhombus(hol_application), @rhombus(hol_power),
@rhombus(hol_prefix_arithmetic), @rhombus(hol_multiplication),
@rhombus(hol_addition), @rhombus(hol_append),
@rhombus(hol_set_intersection), @rhombus(hol_set_union),
@rhombus(hol_relation), @rhombus(hol_equality),
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

@subsection{Fixed and overloaded notation}

The @rhombus(notation, ~datum) declaration has two expression forms. An
anonymous pattern has one fixed interpretation:

@verbatim{
notation (x <&> y):
  ~logic: conj(x, y)
  ~order: hol_conjunction
}

A named pattern introduces notation for a static dispatch family:

@verbatim{
notation Add (left + right):
  ~order: hol_addition
  ~associativity: ~left
}

The fixed form uses @rhombus(~logic) and @rhombus(~runtime) as described above.
The named form only binds syntax. A separate @rhombus(dispatch, ~datum)
declaration supplies type-directed meanings. Rhombus's ordinary
@rhombus(operator) declaration remains runtime-only and is not assigned a
logical meaning.

Both notation forms use a named @tt{hol_*} order; there is no numeric
precedence hook or parser table to modify.

@section{Static dispatch}

The standard notation families are @tt{Add}, @tt{Subtract}, @tt{Negate},
@tt{Multiply}, @tt{Power}, @tt{Less}, @tt{LessEqual}, @tt{Greater},
@tt{GreaterEqual}, @tt{Append}, @tt{Membership}, @tt{Union}, and
@tt{Intersection}. Importing a theory imports its dispatch registry together
with its constants and theorems. Dispatch is also available for ordinary
function names such as @tt{map}; it is not restricted to operator notation.

The standard method set is:

@itemlist(
  @item{@tt{Nat}: addition, subtraction, multiplication, power, and all four
        order comparisons.}
  @item{@tt{Integer} and @tt{Rational}: addition, subtraction,
        multiplication, unary negation, and all four order comparisons.}
  @item{@tt{List(?a)} and @tt{String}: append.}
  @item{@tt{Function(?a, Boolean)} sets: membership, union, and intersection.}
  @item{@tt{Function(?a, Function(?a, Boolean))} relations: union and
        intersection.}
)

A notation declaration and its methods use distinct declaration heads:

@verbatim{
notation CustomAdd (left <+> right):
  syntax (left <++> right)
  ~order: hol_addition
  ~associativity: ~left

dispatch CustomAdd(Nat, Nat) = nat_add
}

The notation pattern binds the first spelling in the HOL expression space.
Additional @rhombus(syntax, ~datum) clauses bind aliases. Pattern shape
determines arity and whether the spelling is infix or prefix. All aliases must
use the same operand names and fixity. Infix declarations require
@rhombus(~associativity); prefix declarations omit it:

@verbatim{
notation Negate (- value):
  ~order: hol_prefix_arithmetic

dispatch Negate(Integer) = int_negate
}

A method declares the complete argument tuple, not a distinguished carrier.
Every argument and the expected result type participate in first-order
unification. Method signatures for one family must not overlap; an overlap is
rejected when the method is registered instead of creating an
order-dependent winner. No applicable method is a compile error listing the
available candidates. Generated executable functions and logical terms
contain a direct call to the selected constant, not a runtime type test.

The accepted method forms are:

@verbatim{
dispatch Family(ArgumentType, ...) = constant
dispatch Family(ArgumentType, ...) :: ResultType = constant

dispatch Family(name :: ArgumentType, ...):
  constant(name, ...)
}

The result annotation is optional when the implementation constant determines
it. Dispatch declarations create ordinary named families as needed, so no
notation declaration is required:

@verbatim{
dispatch map(Function(?a, ?b), List(?a)) = list_map
dispatch empty() = list_empty

function mapped_empty(f :: Function(Nat, Nat)) :: List(Nat):
  map(f, empty())
}

The outer expected @tt{List(Nat)} result selects @tt{map}'s method; its selected
argument signature then supplies the expected type that selects @tt{empty}.

A bare implementation constant receives arguments in signature order. When
its parameter order differs, name the signature arguments and write a call
template:

@verbatim{
notation Membership (element in collection):
  ~order: hol_relation
  ~associativity: ~none

dispatch Membership(
  element :: ?a,
  collection :: Function(?a, Boolean)
):
  set_member(collection, element)

dispatch Greater(
  left :: Integer,
  right :: Integer
):
  int_lt(right, left)
}

Thus @tt{x in s} lowers to @tt{set_member(s, x)}, while @tt{x > y} lowers to
@tt{int_lt(y, x)}. A template must use every dispatch argument exactly once.
Zero-argument families may use the expected result type for contextual
selection, so nested calls such as @tt{map(f, empty())} resolve statically.

@section{@rhombus(theorem, ~datum) and @rhombus(proof, ~datum)}

@verbatim{
theorem Id:
  proposition

proof:
  tactic
  ...

tactic = induct(Id)
       | split(proposition)
       | choose(term)
       | use([Id, ...])
       | skip([Id, ...])
       | disable([Id, ...])
       | limit(nonnegative_integer)
}

States a proposition and proves it while the module compiles. The proposition
grammar is in @secref("propositions").

The @rhombus(proof, ~datum) clause is optional and defaults to the same
waterfall automation as an empty directive configuration. When present, it
must follow its theorem immediately and contain one or more tactic forms.

@rhombusblock(
  theorem app_nil_r:
    forall (xs :: List(?a)): app(xs, Nil()) === xs

  theorem app_assoc:
    forall (xs :: List(?a), ys :: List(?a), zs :: List(?a)):
      app(app(xs, ys), zs) === app(xs, app(ys, zs))
  proof:
    induct(xs)
)

Every theorem is retained by name but is not added to the global rule database.
Use a theorem explicitly in a proof with @rhombus(use([theorem]), ~datum).
Adding an unrelated theorem therefore cannot change later automation.

@rhombus(induct(variable), ~datum) names a variable to induct on; it may
appear once. @rhombus(split(proposition), ~datum) adds a Boolean case split;
repeat it for each proposition. @rhombus(choose(term), ~datum) supplies one
existential candidate; it may repeat. @rhombus(use([theorem]), ~datum) names
theorems to enable for this proof only, which is useful when a lemma is too
aggressive to leave in the rewriter permanently. @rhombus(disable([rule]), ~datum)
names rules to disable for this proof only, on top of whatever a
module-level @rhombus(disable_rules, ~datum) already disabled.
@rhombus(skip([stage]), ~datum) names waterfall stages ---
@tt{simplify}, @tt{eliminate}, @tt{fertilize}, @tt{generalize},
@tt{irrelevance}, @tt{induct} --- to skip for this proof only; see
@secref("prover"). @rhombus(limit(steps), ~datum) sets this proof's
nonnegative search-step ceiling and may appear once. The list directives may
repeat and append their values in source order. None of the directives change what the
prover is allowed to conclude, only what it tries.

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
    forall (xs :: List(?a)): app(xs, Nil()) === app(xs, Nil())

  enable_rules [app]
)

The usual reason is to keep a proof from unfolding something --- to reason
about a function through its proved properties rather than its equations --- or
to park a lemma that is useful in one place and too aggressive everywhere else.
For the latter, @rhombus(use, ~datum) on a single proof is usually better than
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
    forall (xs :: List(Nat)): rev(rev(xs)) === xs
)

After it passes, change the declaration head and add a proof:

@rhombusblock(
  theorem rev_involutive:
    forall (xs :: List(Nat)): rev(rev(xs)) === xs
  proof:
    induct(xs)
)

Input types must be concrete because every input needs a run-time generator.
A generator and shrinker are registered alongside each datatype declaration
under the type's own name. The registry works through transitive imports; the
datatype need not be declared in the quickcheck's own module.

The proposition must have an executable reading. Function calls, conditionals,
Boolean connectives, equality, numerals, and statically dispatched calls are
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
