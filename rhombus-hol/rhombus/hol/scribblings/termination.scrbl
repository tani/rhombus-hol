#lang rhombus/scribble/manual

@title(~tag: "termination"){Termination}

A recursive definition is admitted only once it has been shown to terminate.
This is not a style rule. The clausal equations of a non-terminating definition
are inconsistent --- @tt{f(x) = f(x) + 1} proves @tt{0 = 1} --- so the check is
what makes a definition a conservative extension rather than an axiom.

Two methods are tried, in this order.

@section{Lexicographic structural descent}

The first method is syntactic and generates nothing to prove. It looks for an
order of argument positions such that every recursive call leaves some prefix
of them unchanged and shrinks the next one to a proper constructor subterm of
its pattern.

Descending on a single argument is the one-element case:

@rhombusblock(
  function app(xs :: List(~a), ys :: List(~a)) :: List(~a):
    match xs
    | Nil(): ys
    | Cons(x, rest): Cons(x, app(rest, ys))
)

@rhombus(rest) is a field of the pattern @rhombus(Cons(x, rest)), so column
@rhombus(xs) descends at the only recursive call, and the order is just
@rhombus(xs).

Ackermann's function needs two:

@rhombusblock(
  function ack(m :: Nat, n :: Nat) :: Nat:
    match m
    | zero(): succ(n)
    | succ(p):
        match n
        | zero(): ack(p, succ(zero()))
        | succ(q): ack(p, ack(succ(p), q))
)

No single argument decreases at every call --- the inner call holds @rhombus(m)
and shrinks @rhombus(n) --- but the order @rhombus(m), @rhombus(n) settles all
three calls.

The search is greedy, and that is not an approximation: a column that is
admissible at one step stays admissible, and taking it can only discharge call
sites, so if any order works the greedy one does.

"Proper constructor subterm" is meant shallowly: the argument must be a field
of the pattern at that position, at the same type. A deeper notion would admit
definitions whose recursion the one-constructor-deep induction schemes could
not follow, so the checker would be accepting functions the prover could not
reason about.

@section{Measures}

When no order exists, the author may supply one with @rhombus(~measure).

@rhombusblock(
  function down(n :: Nat) :: Nat ~measure(n):
    if nul(n) | zero() | succ(down(pred_of(n)))
)

The recursion here is on a computed argument, not on a field of a pattern, so
the syntactic check cannot see it. The measure says that @rhombus(n) gets
smaller anyway.

Each recursive call raises one obligation: the measure of the arguments is
below the measure of the patterns, under the branch conditions that reach the
call. The obligation above is

@nested(~style: #'inset){
 @verbatim{forall (x :: Nat): not nul(x) ==> Nat_lt(pred_of(x), x)}
}

and it goes through the same prover as a theorem, with everything declared so
far available. Note the guard: a call inside the false branch of an
@rhombus(if) only has to decrease when that branch is taken, which is most of
what a measure is for.

If an obligation cannot be discharged, the definition is a compile error
carrying the obligation and the goals that were left over.

A measure is examined only when no structural order was found. Putting
@rhombus(~measure) on a definition that already descends structurally is
therefore harmless but also unchecked --- the structural argument is complete
on its own.

@section{The subterm relation}

A measure has to decrease in @emph{something}, and that something has to be
well-founded. Every recursive datatype declaration generates its
@deftech{subterm relation}, named by appending @tt{_lt} to the type's name:

@rhombusblock(
  type Nat
  | zero()
  | succ(pred :: Nat)
)

brings @rhombus(Nat_lt) into the theory, defined by

@nested(~style: #'inset){
 @verbatim{
Nat_lt(x, zero) <=> false
Nat_lt(x, succ(y)) <=> x === y or Nat_lt(x, y)
}
}

which is exactly @tt{<}. For a branching type both children count:

@nested(~style: #'inset){
 @verbatim{
Tree_lt(x, Node(l, v, r))
  <=> x === l or (Tree_lt(x, l) or (x === r or Tree_lt(x, r)))
}
}

Two things make this the right order to measure into. It is @emph{derived, not
postulated}, and in a stronger sense than "installed through a definitional
seam": the relation is @tt{TC(Nat_child)}, the transitive closure of a
direct-child predicate written with the datatype's own discriminators and
selectors. Neither the closure nor the child predicate recurses, so neither
needs a recursion theorem, and the equations above are @emph{proved} from the
closure's induction principle rather than asserted. And it is
@emph{well-founded by the datatype's own induction principle}: a descending
chain would be an infinitely deep term, and induction says there are none.

That is why a measure must land in a declared datatype. A measure into
@rhombus(Boolean), or into any type with no subterm relation, is rejected.

The relation's equations are in the rewriter under its own name, so
@rhombus(disable_rules [Nat_lt]) reaches them without touching the datatype's
other rules.

@section{What is not supported}

@itemlist(

 @item{@bold{Nested recursion.} A recursive call among the arguments of
  another recursive call has no obligation this version can state, because the
  obligation would mention the function being defined.}

 @item{@bold{Mutual recursion.} Two functions that call each other cannot be
  declared; neither is complete when the other is checked.}

 @item{@bold{Recursion under a binder.} There are no lambdas in the body
  grammar, so this cannot arise, and it is reported if it somehow does.}

)
