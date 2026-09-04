#lang rhombus/scribble/manual

@title(~tag: "overview"){Two Readings of One Declaration}

Every logical declaration in a @rhombuslangname(rhombus/hol) module is read
twice, from the same source text.

@itemlist(

 @item{@bold{Logically}, as a declaration in a @deftech{theory}: a datatype
  contributes injectivity, distinctness, exhaustiveness and induction axioms; a
  function contributes one equation per clause; a theorem contributes a proved
  statement.}

 @item{@bold{Executably}, as ordinary Rhombus: a datatype becomes a class per
  constructor, and a function becomes a Rhombus function with its type
  annotations erased.}

)

The two readings go through the same parser on the same syntax, so they cannot
disagree about what a definition says. This is the reason the surface syntax
uses Rhombus's own spellings wherever a construct exists on both sides ---
@rhombus(#true), @rhombus(!), @rhombus(&&), @rhombus(||), @rhombus(==) and
@rhombus(if) --- while constructs that exist only in the logic get their own
spellings, such as @rhombus(===, ~datum), @rhombus(and, ~datum) and
@rhombus(forall, ~datum).

@section{When things happen}

Proofs run @emph{while the module is compiled}, not when it is run. A theorem
that cannot be proved is a compile error, and so is a definition that cannot be
shown to terminate. Nothing about the logic happens at run time; by then the
module is just Rhombus code.

One consequence is worth stating plainly: a failed proof is reported the way a
syntax error is, at the line of the declaration, with the goals that were left
over.

@rhombusblock(
  theorem rev_is_identity:
    forall (xs :: List(~a)): rev(xs) === xs
)

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

@section{A complete module}

@rhombusblock(
  #,(@hash_lang()) #,(@rhombuslangname(rhombus/hol))

  export:
    List
    Nil
    Cons
    app
    rev

  type List(~a)
  | Nil()
  | Cons(head :: ~a, tail :: List(~a))

  function app(xs :: List(~a), ys :: List(~a)) :: List(~a):
    match xs
    | Nil(): ys
    | Cons(x, rest): Cons(x, app(rest, ys))

  function rev(xs :: List(~a)) :: List(~a):
    match xs
    | Nil(): Nil()
    | Cons(x, rest): app(rev(rest), Cons(x, Nil()))

  theorem ~rewrite_rule app_nil_r:
    forall (xs :: List(~a)): app(xs, Nil()) === xs

  theorem ~rewrite_rule app_assoc:
    forall (xs :: List(~a), ys :: List(~a), zs :: List(~a)):
      app(app(xs, ys), zs) === app(xs, app(ys, zs))

  theorem rev_app_distr:
    forall (xs :: List(~a), ys :: List(~a)):
      rev(app(xs, ys)) === app(rev(ys), rev(xs))
)

An ordinary Rhombus module can import that one and use it:

@rhombusblock(
  #,(@hash_lang()) #,(@rhombuslangname(rhombus))
  import: "list_proofs.rhm" open

  rev(Cons(1, Cons(2, Cons(3, Nil()))))
)

@section{What is not intercepted}

@rhombuslangname(rhombus/hol) is still a general-purpose language. Only the
declaration forms in @secref("declarations") are given a logical reading;
everything else --- including ordinary @rhombus(fun), @rhombus(def),
@rhombus(class) and @rhombus(import) --- means exactly what it means in
@rhombuslangname(rhombus).

In particular @rhombus(fun) is never intercepted. A logical definition is
written with @rhombus(function, ~datum), and the separate keyword is what makes
it possible to report a body outside the definable grammar as an error instead
of silently treating the definition as an ordinary one.

@rhombusblock(
  // a logical definition: equations, axioms, a termination check
  function double(n :: Nat) :: Nat:
    match n
    | zero(): zero()
    | succ(k): succ(succ(double(k)))

  // an ordinary Rhombus function: no logical meaning, no restrictions
  fun describe(n :: Int) :: String:
    "the number " +& n
)
