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
  rename:
    mb.module_block as #%module_block
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
  only_space hol_expr:
    names:
      #%literal
      #%parens
      #%call
    === <=> ==> and or not == && || ! + - * ** < <= > >= ++ in union intersect if cond forall exists
