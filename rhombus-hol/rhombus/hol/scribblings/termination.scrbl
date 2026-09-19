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
  function app(xs :: List.of(?a), ys :: List.of(?a)) :: List.of(?a):
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
sites, so if any order works the greedy one does. The recorded order contains
only the columns needed to settle the calls. Separately, the prover records
every position that descends at every call as an induction hint; those extra
positions improve induction without widening the well-founded order.

"Proper constructor subterm" may be reached through any number of recursive
fields of the same datatype. A nested pattern variable is therefore a proper
subterm exactly when the datatype's generated @tt{T_lt} relation connects it
to the original pattern. Fields of other types do not count.

@section{Measures}

When no structural order exists, an adjacent @rhombus(proof, ~datum) block may
supply one with @tt{~measure: expression}.

@rhombusblock(
  function down(n :: Nat) :: Nat:
    if nul(n) | zero() | succ(down(pred_of(n)))
  proof:
    ~measure: n
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

A measure is examined only when no structural order was found. Adding a
@tt{~measure:} option to a definition that already descends structurally is
therefore harmless but also unchecked --- the structural argument is complete
on its own.

@section{The subterm relation}

A measure has to decrease in @emph{something}, and that something has to be
well-founded. Every recursive datatype declaration generates its
@deftech{subterm relation}, named by appending @tt{_lt} to the type's name:

@rhombusblock(
  datatype Nat
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

The relation's equations are in the rewriter under its own name, so a proof can
suppress them with @rhombus(~disable: [Nat_lt]) without touching the
datatype's other rules.

@section{A family of functions}

A @tt{function.together:} family is checked as the one tagged function its
members are read as, so it uses this same machinery: one order spans the
family, because a recursive call leaves the member that made it. Either every
member supplies a @tt{~measure:} landing in one declared datatype, or the
family descends structurally --- one argument column per member, at a common
recursive datatype. A @tt{datatype.together:} family's union type is such a
datatype, and it is what relates values of different members, so a recursion
that crosses between mutually recursive datatypes descends in it.

A branch condition that calls the function being defined is not among an
obligation's assumptions: the function has no equations yet, so the call has
to descend whichever way that branch went.

@section{What is not supported}

@itemlist(

 @item{@bold{Nested recursion.} A recursive call among the arguments of
  another recursive call has no obligation this version can state, because the
  obligation would mention the function being defined.}

 @item{@bold{Recursion under a binder.} A local or anonymous
  @rhombus(function) inside a recursive definition's body is an ordinary
  non-recursive lambda (@secref("local-function")): it has no binding of
  its own name, and a call from inside it back to the enclosing definition
  currently being checked is a recursive call reached through that
  lambda's binder. The checker walks into every @tt{Abs} node of the
  elaborated term, so this is caught and reported the same way any other
  unstated recursive call is, not silently accepted.}

)
