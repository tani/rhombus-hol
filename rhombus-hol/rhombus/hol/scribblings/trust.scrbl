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

Four:

@itemlist(
 @item{@bold{ETA} --- @tt{(fun x: f(x)) === f}}
 @item{@bold{SELECT} --- the choice operator returns a witness when one exists}
 @item{@bold{BOOL_CASES} --- @tt{(t <=> true) or (t <=> false)}}
 @item{@deftech{axiom of infinity} --- there is an injection from the type
  @tt{ind} into itself that is not onto}
)

The first three follow HOL4. BOOL_CASES is derivable from choice and eta, but
taking it directly saves a long stretch of derived-rule scripting and costs
nothing in confidence --- it is a standard consistent basis.

Infinity is there because @emph{recursive} datatypes are derived rather than
postulated, and the construction needs an infinite type to index the trees it
carves them out of. It is stated once, in the base theory, and shared: a
module declaring ten recursive datatypes assumes it exactly as often as a
module declaring none. Non-recursive datatypes do not touch it --- they are
built from @tt{unit}, @tt{prod} and @tt{sum} over their field types --- but
they are in the same theory, so it is present either way.

That trade is the point. The alternative, and what this system did before,
was to assume no infinity and instead postulate every recursive datatype's
characterisation: injectivity, distinctness, exhaustiveness and induction,
per declaration. One shared axiom replaced an unbounded number of
per-declaration ones.

Every logical connective is @emph{defined} on top of the kernel's equality, not
postulated. So are the conditional rules @tt{if true | a | b === a} and its
dual, and the thirteen propositional simplification rules.

A datatype's subterm relation @tt{T_lt} is derived twice over, and both
halves matter because so much rests on them. That @tt{T_lt} is @emph{well
founded} is proved from the datatype's own induction principle
(@tt{prove_wf_t_lt}); it is what every derived recursive function recurses
in. That @tt{T_lt} @emph{is} the subterm relation --- its two equations per
datatype --- is proved as well: the relation is defined as @tt{TC T_child},
the transitive closure of a direct-child predicate spelled with the
datatype's own discriminators and selectors, so neither the closure nor the
child predicate is a recursive definition and neither needs a recursion
theorem. The equations then follow from the closure's induction principle
(@tt{rhombus/hol/tclosure}).

@section{What is postulated beyond that}

One construction can still add axioms, and only in one corner of its range:
a @rhombus(function, ~datum) whose recursion this version cannot build a
well-founded relation for. Everything else --- both kinds of datatype, the
subterm relation each brings, and every function that either does not
recurse or recurses in a way the deriver handles --- is proved. Which one
you get is decided by a check, not by a flag, and counting the axioms a
module's theory ends up with is the way to tell (@tt{axioms_of}).

You do not have to count, though, because the compiler does. Every
declaration that takes a derived path checks that the theory it produced has
the same number of axioms as the theory it started from, and refuses the
declaration otherwise. So "derived" is an invariant rather than a claim: a
path that quietly began postulating --- which is a way this has actually
broken before --- fails at the declaration that did it, naming it.

@bold{Datatypes.} A @rhombus(type, ~datum) is @emph{derived}, recursive or
not. A non-recursive one --- any number of constructors, fields and type
parameters --- is built as a sum of products of @tt{unit} over its field
types. A @emph{self-recursive} one is carved out of the labelled trees over
@tt{num} (@tt{rhombus/hol/treerep}, @tt{rhombus/hol/datatype_rec}): its
representation is the least set of trees closed under its constructors, cut
out by @tt{new_basic_type_definition}, and its injectivity, distinctness,
exhaustiveness, induction, discriminators, selectors and destructor
elimination all come out as theorems with no hypotheses. Run the axiom
schema on the same declaration and every statement agrees --- the same
theory, reached by proof.

What a self-recursive declaration still costs is one thing: the @tech{axiom
of infinity}, which the base theory carries once however many datatypes a
module declares, because the trees are indexed by paths over @tt{num}. So a
module declaring two recursive datatypes assumes four things --- the base
logic's three and infinity --- and declaring a third would not move that
number.

There is no third case and no fallback: a field either is the type itself or
it is not, so the axiom schema is no longer on the declaration path at all.
It survives only as the baseline the derivations are differentially tested
against.

The @tech{strict positivity} check still guards the declaration, but it no
longer guards a consistency claim about axioms nobody proved --- an
ill-founded declaration now fails to be carved rather than being assumed.

@bold{Function definitions.} A @rhombus(function, ~datum) that does not call
itself is @emph{defined}, whatever its patterns look like: its decision tree
is written as a closed term with the datatype's discriminators for the tests
and its selectors for the variables, @rhombus(new_basic_definition) takes
that, and the clausal equations --- one per leaf, so that ordered clauses
resolve the way they were written --- are proved by unfolding it.

A @rhombus(function, ~datum) that does recurse is @emph{derived} whenever the
recursion has a well-founded relation this version can build: its clausal
equations are proved from a well-founded recursion theorem (itself derived,
not postulated) applied to a step function compiled from the same decision
tree. That covers structural descent in any one argument column, several
arguments (derived over their tuple, with the relation pulled back along the
projection onto the descending column), patterns nested to any depth, and an
explicit @rhombus(~measure) --- whose order is the measure's own result
type's subterm relation pulled back along the measure, and whose descent
facts are the obligations the termination check discharged, used under the
branch conditions they were discharged under.

What still postulates one equation per shape: a definition whose descent is
genuinely lexicographic, where no single column shrinks at every call
(Ackermann's function), since that needs a lexicographic product rather than
a pullback along one projection; and one whose relevant type --- the
descending argument's, or the measure's result --- is not a datatype this
module declared. Those are a conservative extension exactly when the
definition is exhaustive and terminating, which is what
@secref("termination") is about.

That last seam is the only one left in the system, and it sits behind a
narrow gate. The derivations that have replaced the others changed nothing
above them: the theorems have the same statements, so the rule database, the
waterfall and @rhombus(match) compilation cannot tell which side a given
datatype or function came from.

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

 @item{Patterns may nest to any depth, clauses are ordered (earliest match
  wins, as in the @rhombus(match) they compile to), and @tt{_} names a
  position a clause does not use --- inside a pattern or as a whole clause
  head. A clause that no argument shape can reach is still refused, and so
  is a matrix that leaves a constructor uncovered: ordering is a way to
  write a fallback, not a way to skip totality.

  A definition's equations are stated at the shapes each clause wins at,
  which is what makes an overlapping matrix consistent at all --- postulating
  a catch-all as written, beside the specific clause that precedes it, would
  equate their two right-hand sides. Both installers agree on this, so a
  definition means the same thing whether its equations were derived or
  postulated.}

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

 @item{Proof search is bounded, but a rule that does not make progress is
  still admitted. @rhombus(mk_rule)'s conditions catch a variable left-hand
  side, an unconstrained variable or type variable on the right, and a
  trivial equation; nothing checks that a rule shrinks anything. Such a rule
  no longer hangs @tt{raco make}, because rewriting runs against a shared
  step budget and detects a position that rewrites back to a term it has
  already been --- but it fails the compile with a resource error rather than
  telling you which rule was at fault. See @secref("prover").}

)
