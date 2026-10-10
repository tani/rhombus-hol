# Rhombus/HOL frontend: design

Status: proposal. Nothing here is implemented. It needs an AGENTS.md amendment
(section 9) before code lands.

## 1. Goal

A `#lang rhombus/hol` in which proofs and definitions are written as Rhombus
code, with the ported HOL Light engine (`fusion` through `define`) as the only
backend. Every theorem is replayed in the Rhombus kernel.

The frontend is a thin layer over the engine. It is not a second prover.

## 2. What the previous frontend did, and what to keep out

The pre-restart tree (`315f348^`) had:

- a `frontend/parser` -> `frontend/checker` pipeline producing a Core IR, with
  name resolution and typing done at compile time;
- two backends consuming that IR: `backend/code` (executable Rhombus) and
  `backend/proof` (kernel terms, a waterfall prover, its own definition
  principles for datatypes and recursive functions);
- an Isabelle/HOL kernel formalisation, four packages, and a normative
  `LANGUAGE_SPEC.md`.

My reading of the history is that the cost came from owning a second
elaborator, a second type checker, and a second proof architecture next to the
kernel. This design avoids all three:

| Old | New |
| --- | --- |
| Own checker and Core IR | Reuse `preterm.rhm` type inference; the IR is HOL Light's `preterm` |
| Compile-time name and type checking | Run-time, against the theory tables of that moment (same as `@hol`) |
| Waterfall prover, own `define` | `prove` + tactics, `define`, `define_type`, `new_inductive_definition` from the port |
| Logic and code both derived from the source | Code derived from the *theorems* after the logic is done |
| Four packages, Isabelle kernel | One package, one directory |

## 3. Layering

```text
rhombus/hol/lang/          frontend (no HOL Light counterpart)
rhombus/hol/*.rhm          engine and theories (unchanged)
rhombus/hol/private/       OCaml-compat support (unchanged)
```

`lang/` is a new, fourth layer next to logic, library and adapter. Rules:

1. It calls only the public engine API. It never builds a `thm` or touches
   kernel representation; macros expand to calls such as `prove`,
   `new_definition`, `define`.
2. It has no parser or type checker of its own for HOL terms. Text goes through
   `parser.rhm`; Rhombus-syntax terms (phase 3) become `preterm` values and go
   through `preterm.rhm`.
3. It adds no logical primitive and no axiom. No `sorry`/`mk_thm`.
4. Engine modules never import from `lang/`.

Planned files:

```text
lang/reader.rkt      `#lang rhombus/hol` reader; module language = prelude
lang/prelude.rhm     re-exports engine API, theories, printer, frontend forms
lang/decl.rhm        theorem / definition / datatype / inductive / ...
lang/proof.rhm       `by:` tactic blocks
lang/diagnostics.rhm source locations, failure reports
lang/term.rhm        phase 3: Rhombus syntax -> preterm
lang/codegen.rhm     phase 4: executable reading from theorems
```

## 4. Execution model: run time, in order

HOL Light state (constants, types, parse tables, theorem lists) is global and
mutable, and `@hol` already reads against it at run time. The frontend follows:

- Macros are purely syntactic. They expand to ordinary run-time calls. No
  engine instantiation at phase 1, so there is exactly one engine state.
- A module is a script executed in order, like loading a `.ml` file.
  `require` order is load order.
- Redefining a constant or type is an error, as in HOL Light.
- Errors (type error, unknown constant, failed tactic) are run-time exceptions
  and carry the source location of the declaration (section 7).

Consequence: no editor-time errors before running. Accepted.

Open cost: importing a module re-runs its proofs. Milestone 0 measures this for
the full theory stack; if it is too slow, the answer is a replay cache that
re-checks (never one that trusts recorded theorems).

## 5. Surface syntax

Terms stay HOL Light text in `@hol|{...}|` in phases 1-2. Declarations and
proofs are Rhombus forms.

### 5.1 Theorems and tactic blocks

```rhombus
theorem ADD_COMM: @hol|{!m n. m + n = n + m}|
  by:
    INDUCT_TAC
    | REWRITE_TAC [ADD_CLAUSES]
    | ASM_REWRITE_TAC [ADD_CLAUSES]
```

Expansion: `def ADD_COMM = prove(@hol|{...}|, INDUCT_TAC then_tac ... )`.

- Lines of a `by:` block are joined with `then_tac` (THEN).
- A tactic followed by `|` branches is `then_list` (THENL) over those branches.
- `or_tac` (ORELSE) stays an explicit infix. `then_tac`, `then_list`, `or_tac`
  are the existing `private/proof_syntax.rhm` operators, so precedence and
  associativity are upstream's.
- Tactic expressions inside are ordinary Rhombus expressions over the engine's
  tactics. No tactic language of our own.
- `have`/`suffices` style steps are sugar for `SUBGOAL_THEN` and
  `ASM_CASES_TAC`, added only after the basic block is validated.

The binding is a normal Rhombus `def`, exported with the module. Also
registered in HOL Light's theorem-name database if the port has one for it.

### 5.2 Definitions

```rhombus
definition EVEN2: @hol|{EVEN2 n <=> EVEN n}|        // new_definition
datatype: "tree = Leaf | Node tree num tree"          // define_type
function: @hol|{(size Leaf = 0) /\ (size (Node l n r) = size l + 1 + size r)}|  // define
inductive: @hol|{...}|                                 // new_inductive_definition
```

- Each form binds the same names HOL Light does (`EVEN2_DEF`,
  `tree_INDUCT`, `tree_RECURSION`, ...). The bound names are derived from the
  theorem names the engine returns, not recomputed.
- String patterns go through `parser.rhm`, as AGENTS.md requires.
- `function` expands to `define` and fails if `define` fails. It does not
  generate its own termination argument.

### 5.3 Output

Module-level theorem values print through `printer.rhm` (`|- ...`), and a
failed `by:` block prints the remaining goals with the goal printer, so
`raco`/REPL output looks like HOL Light's. The `g/e/b/p` goalstack remains
available for interactive work.

## 6. Rhombus-syntax terms (phase 3)

Optional and gated on phases 1-2 being validated. Goal: write
`fun`-looking definitions and `match`/`if` terms in Rhombus syntax.

- A macro translates the syntax object into constructor calls for
  `preterm` (`Varp`, `Constp`, `Combp`, `Absp`, `Typing`) and then calls the
  same `retypecheck` path `parse_term` uses. Type inference is upstream's.
- Name resolution: identifiers bound by an enclosing HOL binder become
  variables; all others are emitted as `Varp` and resolved by the engine
  against the constant table, exactly as the text parser does.
- `match` elaborates to the datatype's case/recursor theorems; `if` to `COND`;
  `let` to `LET`. Only constructs with a direct, total HOL meaning are
  accepted; effects, mutation and exceptions are rejected (the old AGENTS.md
  principle, kept).
- Antiquotation of Rhombus values into terms is an extension HOL Light does
  not have; if added it is marked `// departure:` and substitutes placeholders
  after parsing.

## 7. Diagnostics

`lang/diagnostics.rhm` wraps engine failures with:

- source location of the declaration (and the tactic line where known);
- the goal state at failure, via the goal printer;
- for `define`/`define_type` failures, the engine's message unchanged.

OCaml `Failure` and `Fail` exceptions stay what they are; the wrapper adds
context and re-raises. It never swallows a failure.

## 8. Executable reading (phase 4)

The old frontend generated runnable code from the same Core as the logic. Here
it is the reverse: code is generated from the theorems.

- `function`/`define` yields equations `f (C x1 .. xn) = rhs`. `codegen.rhm`
  compiles equations whose left sides are constructor patterns into a Rhombus
  function; anything else is a compile error naming the equation.
- `datatype` yields a class per constructor from the engine's recorded
  inductive-type tables.
- `num` maps to nonnegative Rhombus integers; `real` and other non-executable
  types are rejected.
- It reads only kernel theorems and terms, so there is no second elaborator
  and no consistency problem between logic and code.

Correctness of the generated code is not a kernel matter. It is tested by
evaluating the equations through the kernel's own `compute`/rewriting and
comparing with the generated function on samples.

## 9. Policy changes needed

AGENTS.md currently says "Do not reintroduce the deleted ... previous
Rhombus/HOL frontend, executable-language layer, or multi-package layout".
This design adds a *new* frontend, so that sentence needs to change to
something like:

> A frontend may exist under `rhombus/hol/lang/` as a layer above the engine.
> It follows the rules in `docs/FRONTEND_DESIGN.md`. Do not reintroduce the
> deleted Isabelle/HOL kernel, waterfall prover, previous frontend code, or
> multi-package layout.

Also check that `tools/literalness/measure.py` ignores `lang/`, so the
logic-layer score is unaffected.

## 10. Validation

Tracked separately from implementation, per AGENTS.md.

- Differential: re-state a set of theorems from `theorems.rhm`, `bool.rhm`,
  `arith.rhm` in frontend syntax; check the result is `==` (same concl and
  hyps) to the engine's theorem.
- Definitions: for each form, compare constants, types and returned theorems
  with the direct `define`/`define_type` calls.
- Negative tests: unknown constant, ill-typed term, failing tactic, duplicate
  definition each give a located error.
- Trust test: a grep-style check that `lang/` imports no kernel internals.
- Phase 3: same terms written as text and as Rhombus syntax elaborate to
  `aconv`-equal terms.
- Phase 4: generated functions agree with kernel evaluation of the equations.

## 11. Milestones

- **M0 (spike).** `#lang rhombus/hol` resolves through `lang/reader.rkt` and
  runs a module that loads the stack. Measure load time of the full theory
  stack and of a module re-running its proofs. Decide on the cache question.
- **M1.** `prelude`, `theorem`, `by:`, diagnostics. Acceptance: ~20 theorems
  from `theorems.rhm` re-proved in frontend syntax, identical to upstream.
- **M2.** `definition`, `datatype`, `function`, `inductive`, `type`.
- **M3.** Rhombus-syntax terms.
- **M4.** Code extraction.
- **M5.** Scribble manual and examples.

## 12. Open decisions

1. **Scope of the first release.** M1-M2 (HOL text terms, Rhombus
   declarations) or M3 (Rhombus-syntax terms) as the minimum? I recommend
   M1-M2 first.
2. **Executable reading.** Keep it (M4, from theorems) or drop it? The old
   frontend had it; it is the largest single piece.
3. **Import cost.** If replay on import is too slow, accept a re-checking
   cache?
4. **Language name.** Keep `#lang rhombus/hol`?
