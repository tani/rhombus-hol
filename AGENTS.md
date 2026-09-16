# AGENTS.md

## Project Policy

This repository values semantic clarity, structural simplicity, and a small trusted implementation over compatibility, abstraction for its own sake, or premature performance work.

The guiding principle is:

> Implement the largest clean intersection of Rhombus and HOL, and admit additional Rhombus syntax when it is a natural, semantics-preserving surface form for ordinary HOL terms.

When choosing between two correct implementations, prefer the one with fewer concepts, fewer moving parts, less duplicated logic, and a smaller long-term maintenance burden.


---

## 1. Language Design Policy

### 1.1 Required intersection

Any construct that is natural in both Rhombus and HOL SHOULD be supported unless there is a concrete soundness or implementation reason not to.

Examples include:

* higher-order functions
* anonymous functions
* lexical binding
* function application
* ordinary pure expressions
* type ascription
* tuples/products
* list construction and matching
* pattern matching
* pure conditionals
* polymorphic typing where supported by HOL

Do not preserve an artificial restriction merely because the current frontend happens not to support the construct.

### 1.2 Rhombus syntax as HOL sugar

A Rhombus construct MAY be admitted even if HOL does not have the same surface syntax, provided that it has a direct, simple, semantics-preserving elaboration into ordinary HOL terms.

Preferred elaborations are small and unsurprising, such as:

* local named function → `let` + lambda
* anonymous `function` → lambda abstraction
* list literal → nested list constructors
* pair syntax → product constructor
* local pure binding → `let`
* expression pattern matching → datatype case analysis

Do not introduce a new logical primitive when ordinary HOL already expresses the construct.

### 1.3 Do not overextend the object language

Rhombus features that fundamentally rely on effects, mutation, exceptions, dynamic dispatch, runtime identity, or other non-HOL semantics MUST NOT be added merely for syntactic completeness.

The language should feel like Rhombus, but remain recognizably HOL.

---

## 2. Simplicity Is a Primary Objective

Simplicity outranks performance unless performance is required for correctness or practical usability.

A slower implementation is preferable when it is materially simpler, easier to audit, easier to prove correct, or removes architectural duplication.

Do not optimize speculative hot paths.

Do not preserve complexity because it is already implemented.

### 2.1 Reward structural reduction

Reducing code size is a positive outcome when it reflects a real reduction in structural complexity.

Reward changes that:

* remove obsolete abstractions
* merge duplicated passes
* delete redundant state plumbing
* remove dead compatibility layers
* replace special cases with one general mechanism
* collapse parallel logical/runtime/frontend mechanisms into shared representations where appropriate
* eliminate wrappers that no longer enforce an invariant
* delete functions whose only purpose disappeared after a redesign

A decrease in line count is desirable when caused by better structure.

### 2.2 Do not reward compression

Do not reduce code by making it harder to read.

Avoid:

* dense one-liners
* obscure metaprogramming used only to save lines
* deeply nested expressions
* clever encodings that hide control flow
* overloaded helpers with unrelated responsibilities
* premature generic frameworks

The target is fewer concepts, not merely fewer characters.

---

## 3. Deletion Policy

Backward compatibility is not a project goal.

If a cleaner specification makes old syntax, old APIs, old helpers, old state, or old tests unnecessary, delete them.

Do not keep compatibility shims unless they reduce the total implementation complexity.

Whenever a specification change removes a feature or special case, actively search for implementation logic that existed only to support it.

Typical deletion targets include:

* obsolete parser branches
* outdated AST variants
* dead elaboration paths
* stale runtime lowering
* compatibility wrappers
* redundant validation
* duplicated diagnostics
* state fields that no longer carry semantic information
* tests for behavior that is intentionally removed

A specification simplification is incomplete if the implementation still carries the old machinery.

---

## 4. Architecture Policy

Prefer one small semantic core over multiple overlapping subsystems.

The intended direction is:

```text
Rhombus-like HOL surface syntax
            ↓
small theory-independent core
            ↓
HOL elaboration + executable lowering
```

Avoid adding layers unless they enforce a real invariant.

### 4.1 One representation when possible

When logical and executable interpretations describe the same source construct, they SHOULD consume the same normalized core representation.

Do not independently parse or reconstruct the same semantics in multiple subsystems.

### 4.2 Desugar early when it simplifies the core

Surface sugar SHOULD be lowered before the semantic core when doing so removes concepts from later phases.

For example:

```text
local named function
    ↓
let-bound anonymous function
```

is preferable to introducing a second full local-function definition subsystem if recursion is not required.

### 4.3 Keep the kernel boundary small

Do not add kernel primitives for constructs that can be derived using existing HOL primitives.

Prefer:

* lambda
* application
* equality
* type definition
* basic definition
* existing datatype theorems
* existing well-founded recursion machinery

over new trusted operations.

---

## 5. Effects and Capability Separation

Use effects to separate authority, mutable state, ambient context, tracing, search control, and similar operational capabilities.

Do not pass large monolithic context objects through the system when a component only needs one capability.

Prefer explicit effect capabilities such as:

```text
Reader / environment access
state updates
search budget
trace emission
proof execution
failure
```

over manually threading unrelated fields through every function.

### 5.1 Principle of least authority

A function SHOULD receive only the capabilities it needs.

For example, a pure type parser should not receive proof execution authority.

A term elaborator should not gain mutation authority merely because another phase needs mutable state.

A simplifier should not implicitly gain tracing or search-budget state unless it actually uses them.

### 5.2 Separate semantic state from operational state

Logical meaning, lexical environment, theory state, proof search state, tracing, and runtime bookkeeping SHOULD remain distinct.

Do not merge them into one convenience structure without a strong reason.

### 5.3 Effects are not mandatory ceremony

Do not introduce an effect abstraction where a plain pure function is simpler.

Use effects where they remove parameter plumbing, clarify authority boundaries, or isolate stateful behavior.

The goal is decomposition, not effect maximalism.

---

## 6. Performance Policy

Correctness and simplicity come first.

Performance work is justified when:

* profiling identifies a real bottleneck
* an algorithm is asymptotically inappropriate
* the current implementation is impractical for intended workloads
* simplification and performance improvement align

Performance work is not justified merely because a lower-level implementation might be faster.

Prefer a simple algorithm with obvious semantics over a complicated optimized one when the practical difference is small.

After architecture stabilizes, optimize measured hot paths.

---

## 7. Testing Policy

Tests exist to protect the intended specification, not historical behavior.

Tests MAY be deleted, merged, or rewritten when the specification changes.

Do not preserve a feature solely because tests exist for it.

Prefer a smaller test suite with high semantic coverage over a large suite that duplicates implementation details.

### 7.1 Keep tests that protect invariants

High-value tests include:

* logical soundness
* no-new-axioms guarantees
* elaboration/runtime agreement
* type safety
* termination checking
* exhaustiveness
* parser/elaborator integration
* representative end-to-end examples
* regressions for previously subtle bugs

### 7.2 Remove low-value duplication

Delete tests that:

* assert intentionally removed compatibility behavior
* duplicate another test without protecting a distinct invariant
* lock in internal implementation structure
* exist only because an obsolete subsystem used to require them

### 7.3 New abstractions require integration tests

Whenever a frontend construct is added, verify the complete path:

```text
surface syntax
→ core representation
→ logical elaboration
→ runtime lowering where executable
→ proof / evaluation behavior
```

Parser-only support is not completion.

---

## 8. Backward Compatibility

Backward compatibility may be ignored.

Breaking changes are acceptable when they produce a better language or a smaller architecture.

Do not add:

* deprecated aliases
* compatibility modes
* migration layers
* dual implementations
* legacy syntax fallbacks

unless doing so makes the code simpler overall.

The repository should optimize for the best current design, not preservation of historical interfaces.

---

## 9. Refactoring Policy

Refactoring is not secondary work. It is part of feature implementation.

When adding a feature exposes a poor abstraction, fix the abstraction rather than routing around it.

When two mechanisms become equivalent after a feature is added, unify them.

When a generalized implementation subsumes an old special case, delete the special case.

Every substantial feature change SHOULD ask:

1. What logic becomes redundant?
2. What representation can now be unified?
3. Which helpers no longer encode a meaningful invariant?
4. Which state can be removed?
5. Which tests now duplicate the same semantic property?
6. Can the final codebase be smaller than before?

---

## 10. Code Review Criteria

A change should be reviewed in this order:

1. Is the semantics sound?
2. Does it preserve the HOL trust model?
3. Is the specification natural for both Rhombus and HOL?
4. Can the same behavior be expressed with fewer concepts?
5. Is state/capability ownership clear?
6. Is there duplicated parsing, elaboration, or lowering?
7. Did the change leave obsolete logic behind?
8. Are tests protecting semantics rather than historical implementation?
9. Is complexity justified by measured need?
10. Did total structural complexity decrease where possible?

A feature that works but substantially increases architectural complexity without necessity is not considered a good implementation.

---

## 11. Preferred Change Pattern

When implementing a new language feature, prefer this sequence:

1. State the semantic meaning in ordinary HOL.
2. Identify the corresponding natural Rhombus syntax.
3. Normalize/desugar the syntax into the smallest existing core form possible.
4. Add a new core node only when desugaring would lose required information or create more complexity.
5. Implement logical elaboration.
6. Implement executable lowering when the construct has a sound executable interpretation.
7. Update termination/evaluation-obligation traversal where necessary.
8. Delete superseded special cases.
9. Consolidate tests.
10. Measure whether the architecture became simpler.

---

## 12. Non-Goals

Do not optimize for:

* backward compatibility
* preservation of every historical test
* minimal diffs
* performance before profiling
* maximal abstraction
* maximal feature parity with full Rhombus
* retaining code merely because it already exists

Do optimize for:

* soundness
* minimal trusted surface
* semantic regularity
* simple code
* small code
* explicit capability boundaries
* easy auditability
* easy refactoring
* direct correspondence between syntax and HOL meaning

---

## 13. HOL extensions

Any standard construct, inference principle, or definition principle that properly belongs to HOL SHOULD be exposed in Rhombus/HOL when doing so preserves the HOL trust model. The absence of a direct counterpart in ordinary Rhombus is not, by itself, a reason to omit an essential HOL capability. Prefer a minimal Rhombus-style surface extension that elaborates to existing HOL terms, theorems, or derived rules, and avoid new kernel primitives whenever the capability can be derived from the existing HOL foundation.


---

## 14. Final Rule

When uncertain between two designs, choose the one that makes the repository easier to explain from first principles.

The preferred implementation is the one for which the answer to

> “Why does this machinery exist?”

is shortest.

If a specification improvement allows code, state, abstractions, tests, or special cases to disappear, remove them.

