#lang rhombus

// The `#lang rhombus/hol` language module.
//
// `#lang X` resolves to `X.rkt`'s `reader` submodule, while `import: X`
// resolves `X.rhm` -- hence this `.rkt`/`.rhm` pair.  The file extension is
// the only thing Racket-ish about this file; its contents are Rhombus.

import:
  rhombus/meta open
  "hol/frontend/module_block.rhm" as mb
  "hol/frontend/surface_space.rhm" open
  "hol/frontend/surface_notation.rhm" as sn

module reader ~lang rhombus/reader:
  ~lang: "hol.rkt"

export:
  all_from(rhombus):
    except:
      #%module_block
      import
  rename:
    mb.module_block as #%module_block
    mb.datatype as datatype
    mb.inductive as inductive
    mb.definition as definition
    mb.function as function
    mb.theorem as theorem
    mb.proof as proof
    mb.overload as overload
    mb.quickcheck as quickcheck
    mb.hol_import as import
    sn.notation as notation
  hol_expr
  hol_equivalence
  hol_implication
  hol_disjunction
  hol_conjunction
  hol_negation
  hol_relation
  hol_equality
  hol_set_union
  hol_set_intersection
  hol_append
  hol_addition
  hol_multiplication
  hol_prefix_arithmetic
  hol_power
  hol_application
  hol_ascription
  only_space hol_expr:
    names:
      #%literal
      #%parens
      #%call
      #%brackets
      #%braces
    === <=> ==> and or not == && || ! + - * ** < <= > >= ++ in union intersect if cond forall exists exists1 select function block match Pair Set ::
