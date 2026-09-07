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

@section{Alignment with HOL Light's @tt{fusion.ml}}

The kernel's public surface is deliberately close to HOL Light's, close enough
that reading @tt{fusion.ml} is a reasonable way to predict what this kernel
does before reading it. Three differences, and why each one is there:

@itemlist(
 @item{@bold{@tt{BETA} takes an arbitrary redex}, not only the trivial
  @tt{(fun x: t(x))(x) === t(x)}. HOL Light's primitive @tt{BETA} is
  deliberately the trivial case only; general beta conversion is a derived
  rule built on top of it. Terms here are locally nameless, so substitution
  cannot capture, and admitting the general case as primitive costs nothing
  in soundness --- it is exactly as easy to state and check as the trivial
  case. Taking the general case as primitive removes one derived-rule layer
  (@tt{BETA_CONV} composed with a substitution argument) that would otherwise
  exist purely to work around named bound variables, which this
  representation does not have.}
 @item{@bold{@tt{Thm} carries a @tt{Stamp}}, not a bare theory reference.
  HOL Light's kernel has a single global, mutably-extended theory, so a
  theorem needs no lineage tag to know what it can be combined with. This
  kernel's theories are immutable values (see the section on theories below,
  needed because @tt{raco make} compiles many modules in one process and a
  single mutable global would make one module's declarations leak into
  another's), so a rule combining two theorems has to check they come from
  one line of extension. The ten rules' @emph{content} is unchanged; the
  stamp check is bookkeeping the mutable-theory design does not need.}
 @item{@bold{Two extra polymorphic definitional principles} beyond the eight
  HOL Light exposes as primitive-adjacent (@tt{new_constant},
  @tt{new_axiom}, @tt{new_basic_definition}): @tt{new_type} and
  @tt{new_basic_type_definition} are named the same as HOL Light's and do the
  same thing (the latter is the one genuinely conservative type-formation
  principle, carving a new type out of a nonempty predicate on an existing
  one). Nothing here is additional trust; it is the same principle under the
  same name.}
)

Everything else --- the argument order, the error conditions each rule
checks, and the set of ten primitive rules itself
(@tt{REFL}/@tt{TRANS}/@tt{MK_COMB}/@tt{ABS}/@tt{BETA}/@tt{ASSUME}/@tt{EQ_MP}/
@tt{DEDUCT_ANTISYM_RULE}/@tt{INST}/@tt{INST_TYPE}) --- matches
@tt{fusion.ml} rule for rule. Type unification (used only by the elaborator,
never by a proof step), pretty printing, and the compile-time trace log used
by the independent Idris differential checker are not part of this
comparison: none of the three exists in @tt{fusion.ml} either, and none of
the three is one of the ten rules or a definitional principle --- printing
lives beside the kernel only because @tt{check_term}'s error messages need
it (see @tt{PLAN.md} section 1 for why that one dependency cannot be cut
without a circular import), and type unification was already moved out to
the elaborator (@tt{rhombus-hol-lib/.../elab.rhm}) before this section was
written.

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
theory in a @rhombus(hol_theory, ~datum) submodule, and an @rhombus(import) of
that module adopts it: the same theory, the same theorem objects. Nothing is re-parsed and nothing is
re-asserted, so there is no trust boundary at a module edge. A design that
instead published a @emph{description} of the theory and re-admitted each
theorem on the word of the exporting module's compile would introduce exactly
such a boundary, forgeable by hand-writing the description.

@section{Where this leaks}

Three honest caveats.

@bold{The kernel is reachable.} Its module lives at @tt{rhombus/hol/kernel.rhm},
an ordinary file with no module-system enforcement behind it. A module that
imports it directly can call @tt{new_axiom} and manufacture any theorem it
likes. "It compiled, so it was proved" therefore holds for modules that do not
do that, which is not the same as holding unconditionally. Sealing this
properly needs the kernel module to be protected at the module-system level;
that is not done.

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

 @item{Most declarations must appear directly in a module body --- not inside
  @rhombus(block), not inside a macro expansion. @rhombus(check_property, ~datum)
  is the one exception; see @secref("declarations").}

 @item{Patterns may nest to any depth (a constructor pattern's own
  arguments may themselves be further constructor patterns, and a
  @rhombus(match) may refine a variable an enclosing pattern already bound),
  but clauses are unordered and there are no wildcards: a variable pattern
  may sit beside constructor patterns at the same position, but more than
  one clause reaching the same fully-refined case is an overlap error, not a
  fallback.}

 @item{An import of a theory must precede the module's own declarations, and
  several must be given in dependency order. Two theories neither of which
  extends the other cannot be used together. An import whose module path this
  version cannot read is refused rather than quietly treated as ordinary.}

 @item{Adopting a theory re-runs the exporting module's proofs, once per
  importing compilation.}

 @item{@rhombus(check_property, ~datum) checks a universally quantified
  equation over concrete types only, and only over a type that some declared
  datatype has registered a generator and a shrinker for; if none was, the
  error surfaces at run time, when the property is actually checked, rather
  than at compile time.}

 @item{The function body grammar has @rhombus(if), @rhombus(cond), local
  @rhombus(let), no arithmetic, and no literals other than the Booleans.}

 @item{There is no fuel or timeout on rewriting, deliberately --- see
  @secref("prover"). A rewrite rule that is not permutative and does not
  terminate is not rejected: @rhombus(mk_rule)'s admission conditions catch a
  variable left-hand side, an unconstrained variable or type variable on the
  right, and a trivial equation, but nothing checks that the rule actually
  makes progress. Such a rule sends simplification into an infinite loop, and
  since simplification happens while a module compiles, that hangs
  @tt{raco make} rather than failing it.}

)
