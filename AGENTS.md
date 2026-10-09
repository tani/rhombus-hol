# Project policy

Rhombus/HOL is a direct Rhombus port of the HOL Light proof engine.

## Engine boundary

The source-to-source port covers:

`fusion -> basics -> nets -> preterm -> parser -> equal -> bool -> drule -> tactics -> itab -> simp`,
extended by the requested direct translation of the standard theory sequence
from `theorems.ml` through `define.ml`. Track implementation and validation
separately; generated files alone do not establish a completed port.

Theory quotations are HOL Light text written as `@hol|{...}|`. They are read
by the direct translation of HOL Light's `parser.ml` (`rhombus/hol/parser.rhm`)
and `preterm.ml` type inference (`private/type_inference.rhm`), at run time and
against the theory tables of that moment, exactly as HOL Light's quotation
expander calls `parse_term` / `parse_type`. Copy quotation text from the pinned
HOL Light sources unchanged. Do not port HOL Light's printer. Replay every
proof in the Rhombus kernel; never import recorded theorems as axioms.
String patterns (`define_type`, `INTRO_TAC` and the like) go through the same
`parser.rhm` lexer and combinators as upstream; keep no second parser.

## Translation policy

The primary reference is upstream HOL Light. Preserve module order, logical
boundaries, derived-rule structure, and operational behavior unless Rhombus
requires a local mechanical adaptation.

Keep the HOL Light-corresponding modules directly under `rhombus/hol/`.
Mechanical OCaml-compatibility helpers belong under `rhombus/hol/private/`
and must not become an alternative proof architecture.

Do not reintroduce the deleted Isabelle/HOL kernel, waterfall prover, previous
Rhombus/HOL frontend, executable-language layer, or multi-package layout.

Prefer direct translations over redesigns inside the engine. Every semantic
departure from HOL Light should be local and documented.

## Binding style

Use `let` for sequential local value bindings, including destructuring and
local mutable state. Use `def` for module-level values; exports and forward
references depend on its definition-wide scope. Keep recursive function
definitions as `fun`. A local `def` requires an actual recursive or forward
reference and a short explanation.
