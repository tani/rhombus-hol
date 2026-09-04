#lang rhombus/scribble/manual

@title(~tag: "prover"){The Prover}

Proofs are found by a @deftech{waterfall}, in the ACL2 sense: a fixed pipeline
of stages, each of which either makes progress on a goal or passes it down. A
stage that makes progress sends its subgoals back to the top. A goal that falls
off the bottom is left open, and the record of what was tried becomes the
error message.

@nested(~style: #'inset){
 @verbatim{simplification -> destructor elimination -> generalization -> induction}
}

There is no search and no backtracking. The prover is a function of the goal
and the rule database, which is what makes a failure reproducible and a
successful proof stable when an unrelated theorem is added elsewhere.

@section{Simplification}

The goal is rewritten to a normal form with every enabled rule: the equations
of every declared function, the injectivity, distinctness, discriminator and
selector equations of every datatype, every theorem marked
@rhombus(~rewrite_rule), and the goal's own assumptions.

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

@section{Generalization}

A subterm that appears on both sides of the goal and is not a constructor
application is replaced by a fresh variable. This throws information away, and
it is what makes induction hypotheses strong enough to be useful.

Only saturated application spines are candidates, and function-typed terms
never are: generalizing a partial application produces a goal that is not just
weaker but false.

@section{Induction}

A variable of a declared datatype is chosen and the goal is split into one case
per constructor, with an induction hypothesis for each recursive field.

The variable is chosen by the argument positions the functions in the goal
actually recurse on --- the same information the termination checker produced,
so the prover inducts the way the definitions recurse. @rhombus(~induct)
overrides the choice.

Nested induction is bounded at depth two. That constant is not a tuning budget;
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
own theorem and mark it @rhombus(~rewrite_rule).

The three things to reach for, in order: prove the missing lemma and mark it a
rewrite rule; give @rhombus(~induct) when the prover picked the wrong variable;
give @rhombus(~using) when a lemma is needed here but is too aggressive to
leave enabled everywhere.

@section{Justification}

No stage can produce a theorem. Each hands back its subgoals together with a
function that builds a theorem for the goal out of theorems for the subgoals,
and those functions are composed only when every leaf is closed. The only
theorems that exist are the ones the kernel made, so a bug in a stage can make
the prover fail to find a proof, or find an unnecessary one, but cannot make it
report a proof that does not exist.
