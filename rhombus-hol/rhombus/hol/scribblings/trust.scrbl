#lang rhombus/scribble/manual

@title(~tag: "trust"){What Is Assumed}

A proof assistant is only worth what its trusted base is worth. This section
says what that base is, and where it leaks.

@section{The kernel}

Theorems are values of an opaque type. There is no public constructor, no
reflection into one, and no serialised form, so the only way to obtain a
theorem is to have the kernel make it. Everything above the kernel --- derived
rules, conversions, the rewriter, the whole waterfall --- can only assemble
calls to it. A bug up there costs a proof, not soundness.

The kernel provides ten primitive inference rules, following HOL Light:
@tt{REFL}, @tt{TRANS}, @tt{MK_COMB}, @tt{ABS}, @tt{BETA}, @tt{ASSUME},
@tt{EQ_MP}, @tt{DEDUCT_ANTISYM_RULE}, @tt{INST} and @tt{INST_TYPE}. Terms are
locally nameless, so alpha-equivalence is structural equality and there is no
alpha-conversion to get wrong.

@section{The axioms}

Three, following HOL4:

@itemlist(
 @item{@bold{ETA} --- @tt{(fun x: f(x)) === f}}
 @item{@bold{SELECT} --- the choice operator returns a witness when one exists}
 @item{@bold{BOOL_CASES} --- @tt{(t <=> true) or (t <=> false)}}
)

There is deliberately no axiom of infinity: datatypes arrive axiomatically, so
no infinite type ever has to be bootstrapped.

BOOL_CASES is derivable from choice and eta, but taking it directly saves a
long stretch of derived-rule scripting and costs nothing in confidence --- it
is a standard consistent basis.

Every logical connective is @emph{defined} on top of the kernel's equality, not
postulated. So are the conditional rules @tt{if true | a | b === a} and its
dual, the thirteen propositional simplification rules, and the subterm relation
of every datatype.

@section{What is postulated beyond that}

Two constructions add axioms, each behind a checked condition that is the whole
soundness argument for it.

@bold{Datatypes.} A @rhombus(type, ~datum) declaration postulates injectivity,
distinctness, exhaustiveness and induction. These are consistent exactly when
the declaration is @tech{strictly positive}, and the positivity checker is what
enforces it. This is the single most load-bearing check in the system.

@bold{Function definitions.} A @rhombus(function, ~datum) declaration
postulates one equation per clause. These are a conservative extension exactly
when the definition is exhaustive, non-overlapping and terminating, which is
what @secref("termination") is about.

Both sit behind a narrow seam. Replacing either with a derivation --- a real
initial-algebra construction, a well-founded recursion theorem --- would change
nothing above it.

@section{Theories}

A theorem carries a stamp identifying the theory it was proved in, and a theory
records its ancestors. A rule that combines theorems checks that one theory
extends the other.

This is not bookkeeping. Without it, two modules could extend a shared theory
in incompatible ways --- one declaring @tt{zero} at one type, the other at
another --- and a theorem from each could be combined into a proof of anything.
Theorems from sibling theories are refused.

Across modules, a @rhombuslangname(rhombus/hol) module publishes its finished
theory as a compile-time value, and @rhombus(use_theory, ~datum) adopts it:
the same theory, the same theorem objects. Nothing is re-parsed and nothing is
re-asserted, so there is no trust boundary at a module edge. An earlier design
published a @emph{description} of the theory and re-admitted each theorem on
the word of the exporting module's compile; that was a trust boundary, and it
could be forged by hand-writing the description.

@section{Where this leaks}

Three honest caveats.

@bold{The kernel is reachable.} Its module lives under @tt{private/}, which is
a convention and not a barrier. A module that imports it directly can call
@tt{new_axiom} and manufacture any theorem it likes. "It compiled, so it was
proved" therefore holds for modules that do not do that, which is not the same
as holding unconditionally. Sealing this properly needs the private modules to
be protected at the module-system level; that is not done.

@bold{The implementation is not verified.} The kernel is a few hundred lines of
ordinary Rhombus. It is small enough to read, and it is structured so that
reading it is the intended way to gain confidence, but nothing has been proved
about it.

@bold{Type variables in postulated axioms.} Datatype and definition axioms are
polymorphic, and their instantiation goes through the same @tt{INST_TYPE} as
everything else. That is standard, but it means the positivity checker has to
be right about parameterised types, not merely about ground ones.

@section{Limitations of this version}

Beyond the termination restrictions in @secref("termination"):

@itemlist(

 @item{Declarations must appear directly in a module body --- not inside
  @rhombus(block), not inside a macro expansion.}

 @item{Patterns are one constructor deep, clauses are unordered, and there are
  no wildcards.}

 @item{@rhombus(use_theory, ~datum) must precede the module's own declarations,
  and several must be given in dependency order. Two theories neither of which
  extends the other cannot be used together.}

 @item{Adopting a theory re-runs the exporting module's proofs, once per
  importing compilation.}

 @item{@rhombus(check_property, ~datum) checks a universally quantified
  equation over concrete types only.}

 @item{The function body grammar has no arithmetic, no literals other than the
  Booleans, no @rhombus(let) and no lambda.}

)
