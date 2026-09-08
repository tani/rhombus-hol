# Changelog

## Unreleased

- Replaced the fixed, numeric-precedence HOL proposition parser with the dedicated `rhombus/hol/expr` enforestation space.
- Added the unified `notation` definer; optional `~runtime` and `~logic` clauses create runtime-only, logic-only, or reflected notation, with at least one meaning required.
- Made HOL expression expansion declaration-ordered, so same-module and imported operator bindings are visible to later functions, theorem statements, and proof cases.
- Added source-located `CoreExpr`, `CoreFunctionSpec`, pattern, function-body, and tactic nodes; theory lookup and type resolution now happen only during elaboration.
- Removed the legacy precedence-climbing proposition parser and raw-syntax function elaborator. Compatibility elaboration entry points now accept Core values.
- Preserved evaluation obligations for local `let` initializers in Core function bodies.
