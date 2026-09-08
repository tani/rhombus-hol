#lang rhombus

// The `#lang rhombus/hol` language module.
//
// `#lang X` resolves to `X.rkt`'s `reader` submodule, while `import: X`
// resolves `X.rhm` -- hence this `.rkt`/`.rhm` pair.  The file extension is
// the only thing Racket-ish about this file; its contents are Rhombus.

import:
  rhombus/meta open
  "hol/module_block.rhm" as mb
  "hol/surface_space.rhm" open
  "hol/surface_notation.rhm" open

module reader ~lang rhombus/reader:
  ~lang: "hol.rkt"

export:
  all_from(rhombus):
    except:
      #%module_block
  rename:
    mb.module_block as #%module_block
  hol_expr
  hol_equivalence
  hol_implication
  hol_disjunction
  hol_conjunction
  hol_negation
  hol_equality
  hol_application
  notation
  only_space hol_expr:
    names:
      #%literal
      #%parens
      #%call
    === <=> ==> and or not == && || ! if cond forall exists
  mb.check_property
