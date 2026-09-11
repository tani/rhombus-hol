#lang rhombus/scribble/manual

@title(~tag: "grammar"){Types, Expressions and Propositions}

@section(~tag: "types"){Types}

@verbatim{
Type = Id                 a declared datatype with no parameters
     | Id(Type, ...)      a declared datatype, applied
     | ?a                 a type variable
     | Boolean            the type of propositions
}

Type variables are written @rhombus(?a), @rhombus(?b) and so on. A function is
implicitly polymorphic in every type variable it mentions; there is no
@tt{forall} at the type level to write.

@rhombus(Boolean) is spelled as Rhombus spells it. A function's annotations are
erased on the way to the executable half, but the conditions of its
@rhombus(if) forms are not, so the two halves have to agree on what a Boolean
is.

@section(~tag: "expressions"){Expressions}

This is the grammar of a @rhombus(function, ~datum) body. HOL expressions use
a dedicated, extensible enforestation space; function bodies admit only the
pure, total forms below.

@verbatim{
body = expr                        the value of the body
     | let Id = expr               a local definition, then the rest
       body
     | match Id | clause | ...     on a parameter or a pattern variable

expr = Id                          a parameter, pattern variable or local
     | Id(expr, ...)               a constructor, or a declared function
     | #true | #false
     | !expr
     | expr && expr
     | expr || expr
     | expr == expr
     | if expr | expr | expr
     | expr reflected-op expr
     | (expr)

clause = CtorId(Id, ...): body
       | CtorId: body

row = (pattern, ...): body      on the declaration, one per argument
    | pattern: body             at one argument, parentheses optional
}

@rhombus(let) and @rhombus(match) are forms of a @emph{body}, not of an
expression: a @rhombus(let) is a statement followed by the rest of the body,
and there is no @rhombus(let) inside the operand of a @rhombus(&&). That is
not a notational choice --- it is what the elaborator accepts.

The built-in operators mean in the logic what they mean in Rhombus:
@rhombus(#true) and @rhombus(#false) are the truth values, @rhombus(!) is
negation, @rhombus(&&) and @rhombus(||) are conjunction and disjunction, and
@rhombus(==) is equality at any type. A @rhombus(notation, ~datum)
declaration with both @rhombus(~runtime) and @rhombus(~logic) adds another
operator with both meanings. An ordinary Rhombus operator and runtime-only
notation have no logical meaning and are rejected in a
@rhombus(function); logic-only notation is rejected because no executable
operator exists.

@rhombus(&&) and @rhombus(||) short-circuit when the module runs, while the
logical @tt{and} and @tt{or} are strict. Nothing can tell the difference,
because every function in this grammar is total.

Anything outside the grammar is a compile error that names the offending
expression. Arithmetic, string literals, @rhombus(block), ordinary
runtime-only operators, runtime-only notation, and logic-only notation are all
outside it in this version.

@subsection{Local definitions}

A @rhombus(let) is @emph{substituted} in the logical reading: the equation is
about the value, and it mentions the initializer only where the body reads the
variable.

@rhombusblock(
  function unread(n :: Nat) :: Nat:
    match n
    | zero(): zero()
    | succ(k):
        let ignored = unread(k)
        succ(zero())
)

states @tt{unread(succ(k)) === succ(zero)}, with no @rhombus(unread) on the
right. The compiled program still evaluates the initializer, though, so
termination is checked against @emph{both} readings: the call above has to
descend even though the equation does not mention it, and one that does not
is refused. See @secref("trust") for why the two readings are kept apart.

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

The matrix must cover the product of the matched columns. It may overlap:
clauses are @emph{ordered}, and where several match the earliest wins ---
the same reading the @rhombus(match) this compiles to gives the same text.
What is refused is a clause no argument shape can reach, since that is a
mistake however the clauses are arranged.

@tt{_} stands for a position the clause does not name. It may appear inside
a pattern (@tt{Cons(x, _)}) or as a whole clause head (@tt{| _: ...}), which
is how a catch-all after a specific case is written.

@subsection{Clauses on the declaration}

The same matrix may be written on the declaration itself, one row of patterns
per clause covering every argument, which is how Rhombus's own multi-case
@rhombus(fun) is written:

@rhombusblock(
  function app(xs :: List(?a), ys :: List(?a)) :: List(?a)
  | (Nil(), ys): ys
  | (Cons(x, rest), ys): Cons(x, app(rest, ys))
)

A row must have one pattern per argument; at one argument the parentheses may
be dropped, exactly as a one-argument @rhombus(match) clause drops them. The
patterns are the same patterns, so nesting, @tt{_} and the ordering above all
read the same way here, and a row may constrain every column at once ---
which a nested @rhombus(match) cannot say in a single clause:

@rhombusblock(
  function eq2(m :: Nat, n :: Nat) :: Nat
  | (zero(), zero()): zero()
  | (succ(a), succ(b)): succ(eq2(a, b))
  | (_, _): zero()
)

This is sugar in the strict sense: a row refines the same pattern vector the
nested form refines, so nothing downstream --- the decision tree, coverage,
termination, the @tt{WFREC} derivation --- can tell which form was written.
The executable half becomes a multi-case @rhombus(fun) over the same
patterns, so the first matching clause wins on both sides.

A definition's equations are stated at the shapes each clause actually
@emph{wins} at, not at its pattern as written --- @tt{| zero(): a | _: b}
gives @tt{f(zero) === a} and @tt{f(succ(k)) === b}, never the inconsistent
pair @tt{f(zero) === a} and @tt{forall n: f(n) === b}.

A pattern may nest to any depth: @tt{Cons(x, Cons(y, rest))} is a pattern,
written directly in a clause head, or built the same way one level at a time
via a nested @rhombus(match) on an already-bound variable --- @tt{match xs |
Cons(x, rest): match rest | Nil(): ...} refines the tail @tt{Cons(x, rest)}
already bound. A nested @rhombus(match) may not re-match a position that has
already been refined --- which matters because a pattern variable can shadow
a parameter of the same name.

@section(~tag: "propositions"){Propositions}

This is the grammar of a @rhombus(theorem, ~datum) statement. It is enforested
in the same dedicated HOL expression space as function expressions, with a
different admissibility policy.

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
     | prop logical-op prop
     | prop reflected-op prop
     | (prop)
}

A proposition is never emitted as Rhombus, so it uses the logical spellings:
@tt{and}, @tt{or}, @tt{not}, @tt{===} for equality, @tt{==>} for implication
and @tt{<=>} for equivalence. (Equality and equivalence are the same relation;
the two spellings differ only in precedence, so that an equivalence between
equations reads without parentheses.)

@subsection{Precedence}

Strongest first. Only @tt{==>} is right-associative. User-defined operators
select one of these named orders with @rhombus(~order).

@tabular(
  ~sep: @hspace(2),
  ~column_properties: [#'left, #'left, #'left],
  ~row_properties: [#'bottom_border],
  [[@bold{order}, @bold{proposition}, @bold{expression}],
   [@tt{hol_application}, "named application", "named application"],
   [@tt{hol_equality}, @tt{===}, @tt{==}],
   [@tt{hol_negation}, @tt{not}, @tt{!}],
   [@tt{hol_conjunction}, @tt{and}, @tt{&&}],
   [@tt{hol_disjunction}, @tt{or}, @tt{||}],
   [@tt{hol_implication}, @elem{@tt{==>} (right)}, ""],
   [@tt{hol_equivalence}, @tt{<=>}, ""]])

A quantifier extends as far to the right as it can, so

@rhombusblock(
  forall (xs :: List(?a)): app(xs, Nil()) === xs and rev(xs) === rev(xs)
)

quantifies over the whole conjunction.

These levels are also the printer's. A goal the prover could not close is
printed with them, so a residue reads back as the proposition it came from.
