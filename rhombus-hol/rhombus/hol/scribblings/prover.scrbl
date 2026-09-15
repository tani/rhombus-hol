#lang rhombus/scribble/manual

@title(~tag: "prover"){The Prover}

Proofs are found by a @deftech{waterfall}, in the ACL2 sense: a fixed pipeline
of stages, each of which either makes progress on a goal or passes it down. A
stage that makes progress sends its subgoals back to the top. A goal that falls
off the bottom is left open, and the record of what was tried becomes the
error message.

@nested(~style: #'inset){
 @verbatim{simplification -> destructor elimination -> fertilization ->
generalization -> elimination of irrelevance -> induction}
}

There is no search and no backtracking. The prover is a function of the goal
and the rule database, which is what makes a failure reproducible and a
successful proof stable when an unrelated theorem is added elsewhere.

@section{Simplification}

The goal is rewritten to a normal form with every enabled rule: the equations
of every declared function, the injectivity, distinctness, discriminator and
selector equations of every datatype, the product projections
(@tt{fst(Pair(x, y)) === x} and its dual), proof-local theorems selected by
@rhombus(~use: [theorem]), and the goal's own assumptions.

A rule is indexed by its left-hand side, so an equation's two orientations are
two different rules. A datatype derives each distinctness fact in one
orientation --- @tt{not (zero === succ(x))} --- and that says nothing about
the phrase @tt{succ(zero) === zero}, so the database is given the symmetric
form of each as well. Neither can loop: both rewrite an equation to
@tt{false}.

The rewritten goal is then beta-normalized. A rewrite rule is indexed by the
head constant of its left-hand side, and a beta redex --- a @rhombus(function)
expression applied to an argument --- has no head constant, so no rule can ever
match one. Anonymous and local functions, an expression-position
@rhombus(let), @rhombus(exists1), @rhombus(select) and a @rhombus(Set)
comprehension all elaborate to exactly that shape, and unfolding an ordinary
function whose argument is one creates further redexes, so the two passes
alternate until neither applies. Beta conversion is applied to the goal the
waterfall holds, not inside the rewriter, which is what keeps it away from the
equations of a recursive definition: there a redex is the folded recursive
call, and reducing it would expose the @tt{WFREC} encoding instead.

The assumptions are simplified too, not merely used as rules. An assumption is
only a rule for the conclusion, which says nothing when the assumption is
@tt{not nul(zero)}: as a rule it rewrites a phrase that does not occur. Reduced
it is @tt{false}, and the goal is closed whatever its conclusion. Guarded
recursion produces exactly that shape, so measure obligations depend on it.

A rule whose two sides are permutations of each other --- commutativity, say
--- is applied in one direction only, ordered by a term ordering, so it cannot
oscillate.

@section{Destructor elimination}

A goal that talks about a value through its selectors is rewritten to talk
about its constructor instead: knowing @tt{is_Cons(xs)}, the goal is restated
with @tt{xs} replaced by @tt{Cons(Cons_head(xs), Cons_tail(xs))}. This is what
lets simplification proceed on a variable whose shape is known but not written.

@section{Fertilization}

An assumption of the shape @tt{x === t} or @tt{t === x}, with @tt{x} a
variable that does not occur in @tt{t}, lets every occurrence of @tt{x} in the
conclusion be rewritten to @tt{t}. Its usual source is an induction
hypothesis freshly exposed by the previous case split, of exactly that shape.

The hypothesis a fertilization step used is dropped from the resulting
subgoal's own assumption list, so a given equation is used at most once along
one branch. Two equations can otherwise be cyclic --- @tt{x === f(y)} and
@tt{y === g(x)} each pass the occurs check alone, but eliminating @tt{x} can
reintroduce @tt{y}, whose own equation reintroduces @tt{x} --- and without
this, the two would toggle the goal back and forth forever instead of ever
reaching the bottom of the pipeline.

@section{Generalization}

A subterm that appears on both sides of the goal and is not a constructor
application is replaced by a fresh variable. This throws information away, and
it is what makes induction hypotheses strong enough to be useful.

Only saturated application spines are candidates, and function-typed terms
never are: generalizing a partial application produces a goal that is not just
weaker but false.

@section{Elimination of irrelevance}

A hypothesis that shares no variable, even transitively through other kept
hypotheses, with anything the conclusion needs is dropped before induction is
attempted. Such a hypothesis cannot help prove the conclusion, and keeping it
around can only confuse the heuristics that come after --- most often the
choice of induction variable.

Dropping it needs no proof step: a theorem proved from fewer assumptions is
already usable wherever more are available, so the subgoal's proof, unchanged,
is the parent goal's proof too.

@section{Induction}

A variable of a declared datatype is chosen and the goal is split into one case
per constructor, with an induction hypothesis for each recursive field.

The variable is chosen by the argument positions the functions in the goal
actually recurse on --- the same information the termination checker produced,
so the prover inducts the way the definitions recurse. The
@rhombus(~induct: variable) option overrides the choice.

Nested induction is bounded at depth six. That constant is not a tuning budget;
it is what makes the driver a function rather than a search. Induction
introduces fresh variables of the same type, so without a bound the prover
would induct forever.

@section{When a proof fails}

The residue is the goals left open, each with the trail of stages that produced
it:

@nested(~style: #'inset){
 @verbatim{
theorem: rev_is_identity: could not prove.
Remaining goal,
  after
    induction on xs (case Cons)
    simplification
    induction on y (case Cons)
    simplification
    assuming rev(y) === y
    assuming app(z, Cons(x, Nil)) === Cons(x, z)
    y === x and x === y
}
}

The trail is usually enough to say what happened. Here it says the conjecture
is false rather than unproved: the prover got down to @tt{y === x and x === y}
for arbitrary distinct @tt{x} and @tt{y}, which no lemma will close.

When a goal is instead a true statement the prover could not reach --- an
instance of associativity, say --- the fix is to prove that statement as its
own theorem and select it explicitly with @rhombus(~use: [associativity]).

The things to reach for, in order: prove the missing theorem and select it with
@rhombus(~use); give @rhombus(~induct: variable) when the prover picked the
wrong variable; give @rhombus(~use: [lemma]) when an existing theorem is
needed here; give
@rhombus(~disable: [rule]) --- ACL2's @tt{:in-theory (disable ...)} ---
to turn off a named rewrite rule for this proof when an enabled rule is firing
where it should not; give
@rhombus(~split: proposition) --- ACL2's @tt{:cases} --- when the goal
turns on a Boolean term (typically an application of an uninterpreted or
externally-supplied predicate) that no other stage can resolve, to split on it
up front and let each branch reach its own conclusion with that term's truth
value as a hypothesis; give @rhombus(~skip: [stage]) --- ACL2's
@tt{:do-not} --- to turn off one of @tt{simplify}, @tt{eliminate},
@tt{fertilize}, @tt{generalize}, @tt{irrelevance} or @tt{induct} for this
proof only, on the rare occasion a stage's heuristic is actively getting in
the way. None of these can turn a false conjecture true or a wrong proof into a
right one: a bad choice of any of them just changes what the residue looks like.

@section{Justification}

No stage can produce a theorem. Each hands back its subgoals together with a
function that builds a theorem for the goal out of theorems for the subgoals,
and those functions are composed only when every leaf is closed. The only
theorems that exist are the ones the kernel made, so a bug in a stage can make
the prover fail to find a proof, or find an unnecessary one, but cannot make it
report a proof that does not exist.

Logical @tt{Goal} values contain only assumptions and a conclusion. Stages
attach a typed trace event to each generated subgoal; the orchestration layer
scopes those events while constructing the proof tree, and only a failed
@tt{Residue} retains them. Terms and symbols are converted to display strings
only when the residue message is rendered. Proof-tree execution is likewise a
scoped executor capability, with deterministic sequential execution as the
default policy.
