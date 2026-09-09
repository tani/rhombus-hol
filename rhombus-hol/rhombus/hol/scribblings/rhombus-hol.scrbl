#lang rhombus/scribble/manual

@title(~style: #'toc){Rhombus/HOL}

@docmodule(~lang, rhombus/hol)

Rhombus/HOL is a theorem prover embedded in Rhombus: an LCF-style
higher-order-logic kernel with an ACL2-style automatic prover on top. A module
written in @rhombuslangname(rhombus/hol) is an ordinary Rhombus module that may
also contain logical declarations, and those declarations have two readings at
once. A datatype is a set of axioms @emph{and} a set of Rhombus classes; a
function definition is a set of equations @emph{and} a Rhombus function; a
theorem is a claim that is proved while the module compiles.

@rhombusblock(
  #,(@hash_lang()) #,(@rhombuslangname(rhombus/hol))

  type List(~a)
  | Nil()
  | Cons(head :: ~a, tail :: List(~a))

  function app(xs :: List(~a), ys :: List(~a)) :: List(~a):
    match xs
    | Nil(): ys
    | Cons(x, rest): Cons(x, app(rest, ys))

  theorem ~rewrite_rule app_nil_r:
    forall (xs :: List(~a)): app(xs, Nil()) === xs
)

That module exports a working @rhombus(app) function, and it does not compile
unless @rhombus(app_nil_r) is proved.

@table_of_contents()

@include_section("overview.scrbl")
@include_section("declarations.scrbl")
@include_section("grammar.scrbl")
@include_section("termination.scrbl")
@include_section("prover.scrbl")
@include_section("trust.scrbl")

@section{License and Third-Party Notices}

Original Rhombus/HOL material is distributed under 0BSD. Because the
implementation closely follows established theorem provers, potentially
derivative portions are conservatively distributed with the retained HOL
Light, HOL4, ACL2, and QuickCheck notices. Generated versions of this manual
also carry the applicable Scribble/Racket and embedded-font notices. The
source distribution includes the complete terms in @tt{LICENSE},
@tt{THIRD_PARTY_NOTICES}, and @tt{LICENSES/}; the public site links the same
files from its front page.
