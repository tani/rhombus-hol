# Changelog

## Unreleased

- Replaced the fixed, numeric-precedence HOL proposition parser with the dedicated `rhombus/hol/expr` enforestation space.
- Added `logical_operator` for theorem-only notation and `reflected_operator` for paired runtime and logical operators.
- Made HOL expression expansion declaration-ordered, so same-module and imported operator bindings are visible to later functions, theorem statements, and proof cases.
- Added source-located `CoreExpr`, `CoreFunctionSpec`, pattern, function-body, and tactic nodes; theory lookup and type resolution now happen only during elaboration.
- Removed the legacy precedence-climbing proposition parser and raw-syntax function elaborator. Compatibility elaboration entry points now accept Core values.
- Preserved evaluation obligations for local `let` initializers in Core function bodies.
