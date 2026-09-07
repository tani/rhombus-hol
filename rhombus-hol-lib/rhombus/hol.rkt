#lang rhombus

// The `#lang rhombus/hol` language module.
//
// `#lang X` resolves to `X.rkt`'s `reader` submodule, while `import: X`
// resolves `X.rhm` -- hence this `.rkt`/`.rhm` pair.  The file extension is
// the only thing Racket-ish about this file; its contents are Rhombus.

import:
  rhombus/meta open
  "hol/module_block.rhm" as mb

module reader ~lang rhombus/reader:
  ~lang: "hol.rhm"

export:
  all_from(rhombus):
    except:
      #%module_block
  rename:
    mb.module_block as #%module_block
  mb.check_property
