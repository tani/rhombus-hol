#lang rhombus/scribble/manual

@title(~tag: "grammar"){Types, Expressions and Propositions}

@section(~tag: "types"){Types}

@verbatim{
Type = Id                 a declared datatype with no parameters
     | Id(Type, ...)      a declared datatype, applied
     | ~a                 a type variable
     | Boolean            the type of propositions
}

Type variables are written @rhombus(~a), @rhombus(~b) and so on. A function is
implicitly polymorphic in every type variable it mentions; there is no
@tt{forall} at the type level to write.

@rhombus(Boolean) is spelled as Rhombus spells it. A function's annotations are
erased on the way to the executable half, but the conditions of its
@rhombus(if) forms are not, so the two halves have to agree on what a Boolean
is.

@section(~tag: "expressions"){Expressions}

This is the grammar of a @rhombus(function, ~datum) body. It is small on
purpose: everything in it is total and pure, which is what lets a definition be
read as a set of equations.

@verbatim{
expr = Id                          a parameter or pattern variable
     | Id(expr, ...)               a constructor, or a declared function
     | #true | #false
     | !expr
     | expr && expr
     | expr || expr
     | expr == expr
     | if expr | expr | expr
     | (expr)
     | match Id | clause | ...     at the top of a body, or under a clause

clause = CtorId(Id, ...): body
       | CtorId: body
}

The operators are Rhombus's own, and they mean in the logic what they mean in
Rhombus: @rhombus(#true) and @rhombus(#false) are the truth values,
@rhombus(!) is negation, @rhombus(&&) and @rhombus(||) are conjunction and
disjunction, @rhombus(==) is equality at any type. They have to be Rhombus's
spellings because the body is emitted verbatim as the executable half; a
different spelling would give the two readings different meanings.

@rhombus(&&) and @rhombus(||) short-circuit when the module runs, while the
logical @tt{and} and @tt{or} are strict. Nothing can tell the difference,
because every function in this grammar is total.

Anything outside the grammar is a compile error that names the offending
expression. Arithmetic, string literals, @rhombus(let) and @rhombus(block) are
all outside it in this version.

@subsection{Matching}

A body may be a @rhombus(match) on one of the parameters, and each clause body
may itself be a @rhombus(match) on a @emph{different} parameter. The nesting is
flattened into a pattern matrix, which is what lets a definition descend on
more than one argument.

@rhombusblock(
  function ack(m :: Nat, n :: Nat) :: Nat:
    match m
    | zero(): succ(n)
    | succ(p):
        match n
        | zero(): ack(p, succ(zero()))
        | succ(q): ack(p, ack(succ(p), q))
)

The matrix must cover the product of the matched columns and must not overlap.
There are no wildcard clauses and no clause ordering: every clause in a matched
column names a constructor, and each constructor of that type appears exactly
once.

A pattern is one constructor deep. @tt{succ(succ(k))} is not a pattern in this
version, because the induction schemes it derives follow one constructor at a
time and could not reason about a definition that matched deeper. A nested
@rhombus(match) may not re-match a column that has already been refined ---
which matters because a pattern variable can shadow a parameter of the same
name.

@section(~tag: "propositions"){Propositions}

This is the grammar of a @rhombus(theorem, ~datum) statement. It is read by the
same precedence parser as an expression, in a different mode, so the two agree
about how a term groups.

@verbatim{
prop = expr
     | not prop
     | prop and prop
     | prop or prop
     | prop ==> prop
     | prop <=> prop
     | prop === prop
     | forall (Id :: Type, ...): prop
     | exists (Id :: Type, ...): prop
     | if prop | prop | prop
     | (prop)
}

A proposition is never emitted as Rhombus, so it uses the logical spellings:
@tt{and}, @tt{or}, @tt{not}, @tt{===} for equality, @tt{==>} for implication
and @tt{<=>} for equivalence. (Equality and equivalence are the same relation;
the two spellings differ only in precedence, so that an equivalence between
equations reads without parentheses.)

@subsection{Precedence}

Tightest first. Only @tt{==>} is right-associative.

@tabular(
  ~sep: @hspace(2),
  ~column_properties: [#'left, #'left, #'left],
  ~row_properties: [#'bottom_border],
  [[@bold{level}, @bold{proposition}, @bold{expression}],
   ["70", @tt{===}, @tt{==}],
   ["60", @tt{not}, @tt{!}],
   ["50", @tt{and}, @tt{&&}],
   ["40", @tt{or}, @tt{||}],
   ["30", @elem{@tt{==>} (right)}, ""],
   ["20", @tt{<=>}, ""],
   ["10", @elem{@tt{forall}, @tt{exists}}, ""]])

A quantifier extends as far to the right as it can, so

@rhombusblock(
  forall (xs :: List(~a)): app(xs, Nil()) === xs and rev(xs) === rev(xs)
)

quantifies over the whole conjunction.

These levels are also the printer's. A goal the prover could not close is
printed with them, so a residue reads back as the proposition it came from.
