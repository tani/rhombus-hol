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

  type List.of(?a)
  | Nil()
  | Cons(head :: ?a, tail :: List.of(?a))

  function app(xs :: List.of(?a), ys :: List.of(?a)) :: List.of(?a):
    match xs
    | Nil(): ys
    | Cons(x, rest): Cons(x, app(rest, ys))

  theorem app_nil_r:
    forall (xs :: List.of(?a)): app(xs, Nil()) === xs
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

@tt{LICENSE} contains the 0BSD terms for original Rhombus/HOL material.
@tt{REUSE.toml} is the authoritative per-file copyright and SPDX license map.
@tt{THIRD_PARTY_NOTICES} records exact source-derived scopes separately from
design references and generated assets. @tt{LICENSES/} contains canonical SPDX
terms; @tt{THIRD_PARTY_LICENSES/} retains audited upstream notices and exact
revisions. Package-local copies keep independently distributable archives
self-contained. The public site links the repository-level documents from its
front page.
