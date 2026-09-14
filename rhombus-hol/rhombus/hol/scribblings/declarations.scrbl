#lang rhombus/scribble/manual

@title(~tag: "declarations"){Declarations}

These are the forms that @rhombuslangname(rhombus/hol) gives a logical reading.
Anything else in a module body is ordinary Rhombus.

The declarations that change the current theory, including
@rhombus(overload, ~datum), are recognised by the language's module-block
expander and must appear directly in the module body. They cannot appear
inside a @rhombus(block), inside a @rhombus(fun) body, or in the expansion of
a user-written macro.

@rhombus(notation, ~datum) is a bound macro. Each notation definition is
visible while the following logical declaration is enforested.

@section{@rhombus(datatype, ~datum)}

@verbatim{
datatype Id
| ctor
| ...

datatype Id.of(?tyvar, ...)
| ctor
| ...

ctor = CtorId
     | CtorId()
     | CtorId(field :: Type, ...)
}

Declares an @deftech{algebraic datatype}. A type variable is written
@rhombus(?a). A parameterized declaration binds @tt{Id.of}; the bare
@tt{Id} remains a constructor namespace and cannot be used as a type without
its arguments. Nullary datatypes continue to use their bare identifier.
The declaration head may end in @tt{:}; this is the block form of the same
declaration. A nullary constructor declaration may likewise omit its empty
parentheses. Thus @tt{datatype Nat: | zero} and
@tt{datatype Nat | zero()} declare the same datatype shape. The omission
applies to the constructor declaration; expressions and patterns in this
manual use the explicit call form @tt{zero()}.

@rhombusblock(
  datatype List.of(?a)
  | Nil()
  | Cons(head :: ?a, tail :: List.of(?a))
)

Logically this @emph{derives} the usual characterisation of the type ---
constructors are injective, distinct constructors build distinct values, every
value is built by some constructor, and the induction principle holds --- as
theorems with no hypotheses. A non-recursive type is built as a sum of
products over its field types; a recursive one is carved out of the labelled
trees over @tt{num} with the kernel's type-definition principle. Neither adds
an axiom. Field selectors and constructor discriminators are declared too, so
@rhombus(List) above brings
@rhombus(Cons_head), @rhombus(Cons_tail), @rhombus(is_Nil) and
@rhombus(is_Cons) into the theory. All of their equations enter the rewriter,
which is what makes @rhombus(match)-defined functions compute during a proof.

A recursive datatype also gets its @tech{subterm relation}; see
@secref("termination").

Executably it emits one Rhombus class per constructor, related by an interface
so that a value can be matched against any of them. The classes are ordinary:
they compare structurally with @rhombus(==) and print readably.

A declaration is rejected unless every recursive occurrence of the type is
@deftech{strictly positive} --- informally, the type being declared may not
appear to the left of an arrow in a field. An ill-founded declaration has no
set of labelled trees to be carved out of, so it now fails to be constructed
rather than being assumed into existence.

@section{@rhombus(function, ~datum)}

@verbatim{
function Id(arg :: Type, ...) :: Type:
  body
proof:
  ~measure: expr
}

Declares a total, terminating function. The body must be in the grammar of
@secref("expressions"); anything else is an error naming the offending
expression.

@rhombusblock(
  function app(xs :: List.of(?a), ys :: List.of(?a)) :: List.of(?a):
    match xs
    | Nil(): ys
    | Cons(x, rest): Cons(x, app(rest, ys))
)

Logically each winning clause becomes one equation, universally closed over the
clause's variables, and each equation enters the rewriter. Before any of that
the definition must pass three checks: the clauses must cover every case, every
clause must win for at least one argument shape after earlier clauses take
priority, and the recursion must be shown to terminate
(@secref("termination")). Clauses may overlap; matching is ordered and the
earliest matching clause wins in both the logical and executable readings.
The compiler prepares that checked clause matrix once. An ordinary
@rhombus(function, ~datum) defines a non-recursive matrix directly or derives
its recursive equations from the selected well-founded order; the explicit
@rhombus(axiomatic_function, ~datum) form reuses the same preparation and
postulates those equations instead.


Executably it emits a Rhombus @rhombus(fun) with the type annotations erased.
The erasure is why the annotations may mention type variables that have no
run-time meaning.

An optional adjacent @rhombus(proof, ~datum) block supplies a termination
argument through @tt{~measure: expression} for a definition that does not
descend structurally. It is checked only when no structural descent can be
found, so a measure on a definition that already descends is not examined.

@section(~tag: "notation"){HOL notation}

@verbatim{
notation left op right:
  operator-option
  ...
  FunctionName
}

@rhombus(notation, ~datum) adds an operator spelling to the HOL expression
space. It follows Rhombus @rhombus(operator, ~datum) case syntax: operands and
the operator appear directly in the declaration head, and prefix, infix,
postfix, immediate @tt{|} cases, and named groups of cases are accepted.
Operands must be identifiers. Precedence options precede exactly one final
function name.

Each notation use lowers to a normal call of that function, with operands in
source order:

@rhombusblock(
  notation left <&> right:
    ~order: hol_conjunction
    conj

  theorem conjunction_example:
    true <&> true
)

The notation itself has no ordinary Rhombus binding. It can nevertheless
appear in a @rhombus(function) body when its target function has an executable
reading: the logical and executable halves lower the same Core call. Outside a
logical declaration, use the target function directly. If ordinary Rhombus
code also needs the operator spelling, declare a separate ordinary
@rhombus(operator, ~datum); the two expression spaces remain explicit.

The precedence options are the ones accepted by Rhombus
@rhombus(operator, ~datum), including @rhombus(~order),
@rhombus(~stronger_than), @rhombus(~weaker_than),
@rhombus(~same_as), @rhombus(~same_on_left_as),
@rhombus(~same_on_right_as), and @rhombus(~associativity).
A named order supplies its associativity; an explicit associativity is checked
against that order. The available HOL orders, strongest to weakest, are
@rhombus(hol_application), @rhombus(hol_power),
@rhombus(hol_prefix_arithmetic), @rhombus(hol_multiplication),
@rhombus(hol_addition), @rhombus(hol_append),
@rhombus(hol_set_intersection), @rhombus(hol_set_union),
@rhombus(hol_relation), @rhombus(hol_equality),
@rhombus(hol_negation), @rhombus(hol_conjunction),
@rhombus(hol_disjunction), @rhombus(hol_implication), and
@rhombus(hol_equivalence). See @secref("propositions") for the built-in
operators at each order.

Multiple fixities of one operator can share options:

@rhombusblock(
  notation <~>:
    ~order: hol_conjunction
  | <~> value:
      neg
  | left <~> right:
      conj
)

Different spellings use separate, symmetric declarations:

@rhombusblock(
  notation left <+> right:
    ~order: hol_addition
    custom_add

  notation a <++> b:
    ~order: hol_addition
    custom_add
)

Notation definitions take effect before the following declaration is
enforested. Export the HOL-space binding explicitly:

@rhombusblock(
  export:
    only_space hol_expr:
      <&>
)

Importing that module with @rhombus(open) makes the notation available to
following @rhombus(function) and @rhombus(theorem) declarations.

@section{Function overloading}

@rhombus(overload, ~datum) adds an overload clause to a callable function
name. No separate registration form or operator-specific overload form is
needed. A direct call and notation targeting the same name are resolved
identically.

@verbatim{
overload add(Nat, Nat) = nat_add
overload add(Integer, Integer) = int_add

notation left <+> right:
  ~order: hol_addition
  add
}

Here @tt{x + y} lowers to the same named call as @tt{add(x, y)}. The ordinary
elaborator sees the call, checks whether @tt{add} has overload clauses, and
selects a clause from the argument types and, when available, the expected
result type. A successful call becomes a direct call to the selected
implementation constant. Kernel terms contain no overload node, and generated
executable code performs no runtime type test.

The standard overloaded function names are @tt{add}, @tt{subtract},
@tt{negate}, @tt{multiply}, @tt{power}, @tt{less}, @tt{less_equal},
@tt{greater}, @tt{greater_equal}, @tt{append}, @tt{member}, @tt{union}, and
@tt{intersection}. Importing a theory imports its overload registry together
with its constants and theorems. User-defined names such as @tt{map} use the
same mechanism.

The standard method set is:

@itemlist(
  @item{@tt{Nat}: addition, subtraction, multiplication, power, and all four
        order comparisons.}
  @item{@tt{Integer} and @tt{Rational}: addition, subtraction,
        multiplication, unary negation, and all four order comparisons.}
  @item{@tt{List.of(?a)} and @tt{String}: append.}
  @item{@tt{?a -> Boolean} sets: membership, union, and intersection.}
  @item{@tt{?a -> ?a -> Boolean} relations: union and intersection.}
)

Each clause declares the complete argument tuple. Every argument and the
expected result type participate in first-order unification. Clauses for one
function name must have one arity and must not overlap; an overlap is rejected
when the clause is registered instead of creating an order-dependent winner.
No applicable clause is a compile error listing the available candidates.

The accepted forms are:

@verbatim{
overload function_name(ArgumentType, ...) = constant
overload function_name(ArgumentType, ...) :: ResultType = constant

overload function_name(name :: ArgumentType, ...) = constant(name, ...)
}

The result annotation is optional when the implementation constant determines
it. The first @rhombus(overload, ~datum) clause establishes a callable
function name; no separate declaration is required:

@verbatim{
overload map(?a -> ?b, List.of(?a)) = list_map
overload empty() = list_empty

function mapped_empty(f :: Nat -> Nat) :: List.of(Nat):
  map(f, empty())
}

The outer expected @tt{List.of(Nat)} result selects @tt{map}'s clause; its
selected argument signature then supplies the expected type that selects
@tt{empty}.

A bare implementation constant receives arguments in signature order. When
its parameter order differs, name the signature arguments and write a call
template:

@verbatim{
notation element in collection:
  ~order: hol_relation
  member

overload member(
  element :: ?a,
  collection :: ?a -> Boolean
) = set_member(collection, element)

overload greater(
  left :: Integer,
  right :: Integer
) = int_lt(right, left)
}

Thus @tt{x in s} lowers to @tt{set_member(s, x)}, while @tt{x > y} lowers to
@tt{int_lt(y, x)}. A template must use every overload argument exactly once.
Zero-argument overloaded functions may use the expected result type for
contextual selection, so nested calls such as @tt{map(f, empty())} resolve
statically.

@section{@rhombus(theorem, ~datum) and @rhombus(proof, ~datum)}

@verbatim{
theorem Id:
  proposition

proof:
  proof_option
  ...

proof_option = ~induct: Id
             | ~split: proposition
             | ~choose: term
             | ~use: [Id, ...]
             | ~skip: [Id, ...]
             | ~disable: [Id, ...]
             | ~limit: nonnegative_integer
}

States a proposition and proves it while the module compiles. The proposition
grammar is in @secref("propositions").

The @rhombus(proof, ~datum) clause is optional and defaults to the same
waterfall automation as an empty option configuration. When present, it
must follow its theorem immediately and contain one or more option groups.

@rhombusblock(
  theorem app_nil_r:
    forall (xs :: List.of(?a)): app(xs, Nil()) === xs

  theorem app_assoc:
    forall (xs :: List.of(?a), ys :: List.of(?a), zs :: List.of(?a)):
      app(app(xs, ys), zs) === app(xs, app(ys, zs))
  proof:
    ~induct: xs
)

Every theorem is retained by name but is not added to the global rule database.
Use a theorem explicitly in a proof with the @rhombus(~use) option.
Adding an unrelated theorem therefore cannot change later automation.

The @rhombus(~induct) option names a variable to induct on; it may appear
once. @rhombus(~split) adds a Boolean case split; repeat it for each
proposition. @rhombus(~choose) supplies one existential candidate and may
repeat. @rhombus(~use) names theorems to enable for this proof only, which is
useful when a lemma is too aggressive to leave in the rewriter permanently.
@rhombus(~disable) names rules to disable for this proof only.
@rhombus(~skip) names waterfall stages --- @tt{simplify}, @tt{eliminate},
@tt{fertilize}, @tt{generalize}, @tt{irrelevance}, @tt{induct} --- to skip
for this proof only; see @secref("prover"). @rhombus(~limit) sets this
proof's nonnegative search-step ceiling and may appear once. The list options
may repeat and append their values in source order. None of the options
change what the prover is allowed to conclude, only what it tries.

@section(~tag: "importing"){Importing a theory}

There is no separate form for importing a theory. An ordinary Rhombus
@rhombus(import) of a @rhombuslangname(rhombus/hol) module brings both halves:
its functions, because that is what an import does, and its theory, so its
datatypes, definitions and theorems are available to the prover.

@rhombusblock(
  import: "list_proofs.rhm" open
)

A module is recognised as a theory by having one --- every
@rhombuslangname(rhombus/hol) module publishes its theory in a
@rhombus(hol_theory, ~datum) submodule --- so this is checked, not guessed from
the shape of the path. An import of anything else passes through untouched, and
one @rhombus(import) form may name both:

@rhombusblock(
  import:
    "plain_helper.rhm" open
    "list_proofs.rhm" open
)

Adoption is transitive: the imported theory already contains whatever it
imported in turn, so a dependency does not have to be named again.

@subsection{Ordering}

Two rules follow from keeping the chain of theories linear. An import of a
theory must come before the module's own logical declarations, and when there
is more than one they must be given in dependency order. Adopting a theory that
is not an extension of the one already in scope is an error, because a module
holding two unrelated theories could not use their theorems together.

@subsection{Forms that cannot be read}

To find the module path in an import clause, the longest prefix of the clause
that parses as one is taken. That covers @rhombus("path.rhm"),
@rhombus(lib("collection/path.rhm")) and @rhombus(collection/path), with any
modifiers after them.

It does not cover a clause whose path is inside a block, as in
@rhombus(import: meta: "path.rhm"). Rather than drop such a theory silently,
an import that names a theory in a form this version cannot read is an error,
and says so.

@section{@rhombus(quickcheck, ~datum)}

@verbatim{
quickcheck Id:
  forall (arg :: ConcreteType, ...): proposition

quickcheck Id(~samples: n, ~size: n, ~seed: n):
  forall (arg :: ConcreteType, ...): proposition
}

Tests the executable reading of a HOL proposition on generated values at run
time. The body uses exactly the same proposition syntax as
@rhombus(theorem, ~datum), including @rhombus(===, ~datum),
@rhombus(and, ~datum), @rhombus(or, ~datum), and @rhombus(not, ~datum).
Passing a quickcheck is evidence against simple mistakes, not a proof.

The intended workflow requires no duplicated property:

@rhombusblock(
  quickcheck rev_involutive(~samples: 500):
    forall (xs :: List.of(Nat)): rev(rev(xs)) === xs
)

After it passes, change the declaration head and add a proof:

@rhombusblock(
  theorem rev_involutive:
    forall (xs :: List.of(Nat)): rev(rev(xs)) === xs
  proof:
    ~induct: xs
)

Input types must be concrete because every input needs a run-time generator.
A generator and shrinker are registered alongside each datatype declaration
under the type's own name. The registry works through transitive imports; the
datatype need not be declared in the quickcheck's own module.

The proposition must have an executable reading. Function calls, conditionals,
Boolean connectives, equality, numerals, and statically overloaded calls are
lowered through the same runtime path used by a declared
@rhombus(function, ~datum). Logic-only constants and existential
quantification are rejected.

@rhombus(~samples) selects the number of generated input tuples.
@rhombus(~size) bounds generated-value depth. @rhombus(~seed) makes a run
reproducible; its default is deterministic, and every counterexample report
includes the effective seed and number of shrinking steps.

A successful declaration produces no binding and adds nothing to the theory.
A falsified property fails module initialization immediately with its shrunk
inputs. Consequently, @rhombus(quickcheck, ~datum) must appear directly in a
@rhombuslangname(rhombus/hol) module body, like
@rhombus(theorem, ~datum); run the module or use @tt{raco test} to execute it.

@section{@rhombus(axiomatic_function, ~datum)}

The same grammar as @rhombus(function, ~datum), and a different contract: it
@emph{postulates} its clausal equations rather than deriving them. Always ---
not only when the derivation would have failed. A form whose meaning depended
on which recursion schemes this version happens to handle is the thing having
two forms is for.

Termination, exhaustiveness, and reachability under ordered matching are still
checked, because those are what make postulating the resulting winning
equations a conservative extension; see @secref("termination"). What is
skipped is the proof.

@rhombus(function, ~datum) refuses a definition whose recursion it cannot
build a well-founded order for, so an ordinary declaration never extends the
theory by assumption. This is the form to write when you want one anyway; see
@secref("trust") for what it costs.
