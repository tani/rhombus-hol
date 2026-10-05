# Project policy

Rhombus/HOL is a direct Rhombus port of the HOL Light proof engine.

## Engine boundary

The source-to-source port covers:

`fusion -> basics -> nets -> equal -> bool -> drule -> tactics -> itab -> simp`.

Do not port HOL Light's parser, preterm, or printer. The frontend above the
engine is Rhombus-native and should use Rhombus macros and syntax facilities.

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
