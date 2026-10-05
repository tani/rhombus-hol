# Project policy

Rhombus/HOL is a direct Rhombus port of the HOL Light proof engine.

## Engine boundary

The source-to-source port covers:

`fusion -> basics -> nets -> equal -> bool -> drule -> tactics -> itab -> simp`,
extended by the requested direct translation of the standard theory sequence
from `theorems.ml` through `define.ml`. Track implementation and validation
separately; generated files alone do not establish a completed port.

Do not port HOL Light's text parser or printer as the frontend. The frontend
above the engine is Rhombus-native and should use Rhombus macros and syntax
facilities. Private type-inference data and algorithms required by the
requested standard theories may be translated directly; they must not expose
a HOL text frontend.
Literal HOL quotations in the theory sources may be expanded offline into
public term/type constructors. Replay every proof in the Rhombus kernel;
never import recorded theorems as axioms. A native inductive-type specification
frontend may supply the small type-description API needed by `ind_types`.

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
