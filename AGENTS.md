# Project policy

This repository is a from-scratch Rhombus port of HOL Light.

The primary reference is upstream HOL Light.  Preserve its module order,
logical boundary, derived-rule structure, and operational behaviour unless
Rhombus requires a mechanical adaptation.

Do not reintroduce the deleted Isabelle/HOL kernel, waterfall prover, previous
Rhombus/HOL frontend, executable-language layer, or compatibility wrappers.

Keep one package and one implementation.  Prefer direct translations over new
architectures.  Every departure from HOL Light should be local and documented.
