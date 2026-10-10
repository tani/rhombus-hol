# Rhombus/HOL frontend: design

Status: proposal. Nothing here is implemented. It needs an AGENTS.md amendment
(section 10) before code lands. Build order: the waterfall prover (section 9)
first, then the frontend.

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
rhombus/hol/waterfall/     automatic prover: tactics over the engine
rhombus/hol/*.rhm          engine and theories (unchanged)
rhombus/hol/private/       OCaml-compat support (unchanged)
```

`waterfall/` and `lang/` are new layers above the engine: `lang/` depends on
`waterfall/`, `waterfall/` on the engine, never the reverse. Rules for both:

1. It calls only the public engine API. It never builds a `thm` or touches
   kernel representation; macros expand to calls such as `prove`,
   `new_definition`, `define`.
2. It has no parser or type checker of its own for HOL terms. Text goes through
   `parser.rhm`; Rhombus-syntax terms (phase 3) become `preterm` values and go
   through `preterm.rhm`.
3. It adds no logical primitive and no axiom. No `sorry`/`mk_thm`, and no
   `new_axiom` (the old prover's `~sorry` used one; it is not carried over).
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

## 9. Waterfall prover (built first)

Reference: Papapanagiotou and Fleuriot, *The Boyer-Moore Waterfall Model
Revisited* (arXiv:1808.03810), a HOL Light reconstruction of Boulton's HOL90
Boyer-Moore tactic with extensions. We follow its final configuration (BMF).
The old Isabelle-era prover (an ACL2-style waterfall with its own goal and
justification machinery) is not the reference any more.

Why first: it is testable with no new syntax (plain Rhombus calls with `@hol`
quotations), it fixes what a bare `theorem NAME: stmt` means in the frontend,
and the frontend's definition forms must feed it rules.

### 9.1 Model

Clauses (disjunctions of literals) are poured from the top of a waterfall.
Each heuristic either proves the clause (it evaporates), replaces it with
simpler clauses that are poured again from the top, disproves it (immediate
failure), or fails and passes it down. Clauses that reach the bottom form a
*pool*. Induction is applied to a pool clause; the resulting base and step
clauses go through a *new* waterfall. The overall proof is a tactic: each
heuristic returns subgoals plus a justification built from engine rules, so a
bug can leave a true goal unproved but cannot yield a false theorem.

### 9.2 Shell registry

Per datatype, the data the heuristics need, read from what the engine returns
for the type (`ind_types`, `define_type` results), not recomputed:

name, bottom objects, constructors, accessors, type axiom, induction theorem,
cases theorem, distinctness and one-one theorems.

Seeded for `num` and `list`; extended by the frontend's `datatype`.
Function registry: recursive functions with their definitional equations and
recursive argument position (one recursive argument per function, as in the
paper; a stated limitation).

### 9.3 Heuristics, top to bottom (BMF)

| # | Heuristic | Built from | Notes |
| --- | --- | --- | --- |
| 1 | tautology | `ITAUT` (ported `itab.rhm`) | at the top; proves or fails, never rewrites |
| 2 | clausal form | HOL Light normalisation of the clause | splits conjunctions; needs quantifiers already gone |
| 3 | substitution | `SUBST` on `~(x = t)`, `x` not in `t` | |
| 4 | simplify | `simp.ml` (the paper's `REWRITE_CONV` variant, "BMR") | enabled rules: user rewrites and function definitions |
| 5 | setify | drop duplicate disjuncts | needed once the HOL simplifier replaces the Boyer-Moore one |
| 6 | equality (cross-fertilisation) | negated equalities whose side is not an explicit value template | |
| 7 | generalisation | Boyer-Moore minimal common subterms, **plus** Aderhold's *variables apart* | not Aderhold's common-subterm algorithm (paper: it was worse here) |
| 8 | irrelevance | partition by shared variables; drop falsifiable partitions | unsafe; may be replaced by "inverse weakening" later |
| pool | induction | the type's induction theorem, variable chosen from recursive argument positions | not applied twice to the same clause on one branch |

MESON is not in the pipeline. `ARITH_RULE` is not either; the paper's BMF does
not use it. `NUM_REDUCE_CONV` is used only by the counterexample checker.

### 9.4 Loop control and over-generalisation

The paper found that unguarded runs looped on more than a third of its
theorems. These are part of v1, not later work:

- **Warehouse filter**: per waterfall, remember clauses already processed and
  the heuristic applied; on a repeat, skip that heuristic. Not shared across
  waterfalls (inductions). Also refuse induction on a clause already inducted
  on in the same branch.
- **Maximum depth**: bound on the syntax-tree depth at which a variable occurs
  (default 12). It prevented about four times as many loops as the warehouse.
- **Counterexample checker** (essential for variables-apart generalisation):
  ground each free variable with a random constructor term from the shell
  (depth-limited, increasing chance of a bottom object), evaluate with
  function definitions, constructor/accessor equations and `NUM_REDUCE_CONV`.
  Reduces to False: reject. Reduces to True: allow. Does not decide: reject
  (the safe option). Default 5 checks per generalisation.
  Determinism departure: the random source is a fixed-seed PRNG owned by the
  waterfall, so runs and traces are reproducible.

### 9.5 API and feedback

```rhombus
WATERFALL_TAC :: Tactic                  // default options; all-or-nothing
waterfall(opts) :: Tactic                // rules, gen lemmas, heuristics, depth, checks
waterfall_trace :: () -> TraceEvent list
```

Options (user control, as in the paper section 3.4): enabled rewrite rules,
generalisation lemmas, which heuristics run and in what order, max depth,
number of counterexample checks, trace on/off. Per-call options layer over a
session registry without mutating it; `enable_rules`/`disable_rules` mutate it.
The paper's registry could not remove rules; ours can.

Trace format follows the paper's Fig. 3: clause, heuristic name on success,
resulting clauses, `Proven: |- ...`, and the induction target. A failing run
reports the pool and the reason. The frontend prints this (section 7).
A residue-returning variant exposes the pool as goals for `g`/`e`.

### 9.6 Frontend interaction

`theorem NAME: stmt` with no `by:` runs `WATERFALL_TAC`. The frontend's
`datatype`/`function`/`definition` forms add shells, function equations and
rewrite rules to the registry. Proving a helper lemma and adding it as a
rewrite rule is the intended workflow (the paper's EVEN/ODD example: the
looping goals prove once `~ODD n <=> EVEN n` is a rule).

### 9.7 Validation

The paper gives a benchmark and baselines, so there is a number to hit.

- Benchmark: the 120 Peano-arithmetic theorems of HOL Light's base plus the
  Rippling list/arith set (paper: 145 theorems, appendices A and B give the
  definitions and rewrite rules). Expected for BMF: about 47% of the first
  set and 37% of the second, with successful proofs averaging under 0.5 s in
  OCaml. Our target is parity on which theorems prove, not on time.
- Per-heuristic tests on hand-built clauses, each checked by kernel replay.
- Regression theorems from the paper's Table 3 (`m + n = n + m`,
  `m * n = n * m`, `REVERSE (REVERSE x) = x`, ...).
- Looping cases from Table 4 terminate by failure (depth or warehouse), and
  prove after the `~ODD n <=> EVEN n` rule is added.
- Disprover: over-generalisations from the paper (`n <= n0`, `m + n = n0 + m`)
  are rejected.
- Determinism: two runs give identical traces.
- No `new_axiom`; the axiom list is unchanged after a run.

### 9.8 Cost note

The paper's tool is a reconstruction of Boulton's HOL90 code, and it had to
rebuild `SUBS_OCCS` and `INDUCT_TAC` for HOL Light. Here `tactics.rhm`,
`itab.rhm`, `simp.rhm` and `define.rhm` are already ported, so the size is
mostly the heuristics, registry, disprover and trace. I have not measured
this; W1 is the spike.

## 10. Policy changes needed

AGENTS.md currently says "Do not reintroduce the deleted Isabelle/HOL kernel,
waterfall prover, previous Rhombus/HOL frontend, executable-language layer, or
multi-package layout". This design adds a new waterfall prover and a new
frontend, so that sentence needs to change to something like:

> An automatic prover may exist under `rhombus/hol/waterfall/` and a frontend
> under `rhombus/hol/lang/`, as layers above the engine, following
> `docs/FRONTEND_DESIGN.md`. They compose engine tactics and rules only. Do not
> reintroduce the deleted Isabelle/HOL kernel, its waterfall or frontend code,
> or the multi-package layout.

Also check that `tools/literalness/measure.py` ignores `lang/` and `waterfall/`, so the
logic-layer score is unaffected.

## 11. Validation

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

## 12. Milestones

Waterfall first (W), then frontend (M).

- **W0.** Shell and function registries; `waterfall(opts)` driver with
  heuristics 1, 2, 4 and the trace; prove a trivial lemma.
- **W1.** Heuristics 3, 5, 6, 8 and induction; warehouse filter and max depth.
  Spike to check the size estimate in 9.8.
- **W2.** Generalisation (Boyer-Moore and variables apart) and the
  counterexample checker; port the paper's Table 3 and Table 4 cases.
- **W3.** Full benchmark run against the paper's baselines; options, rule
  removal, residue-returning variant.
- **M0 (spike).** `#lang rhombus/hol` resolves through `lang/reader.rkt` and
  runs a module that loads the stack. Measure replay-on-import cost.
- **M1.** `prelude`, `theorem`, `by:`, diagnostics, waterfall as default.
- **M2.** `definition`, `datatype`, `function`, `inductive`, `type`, feeding
  the registry.
- **M3.** Rhombus-syntax terms.
- **M4.** Code extraction.
- **M5.** Scribble manual and examples.

## 13. Open decisions

0. **Waterfall baseline.** Follow the paper's BMF (section 9.3) exactly for
   v1, with ACL2-style destructor elimination and `~induct:` hints left for
   later? I recommend yes: it has published baselines to check against.
1. **Scope of the first release.** M1-M2 (HOL text terms, Rhombus
   declarations) or M3 (Rhombus-syntax terms) as the minimum? I recommend
   M1-M2 first.
2. **Executable reading.** Keep it (M4, from theorems) or drop it? The old
   frontend had it; it is the largest single piece.
3. **Import cost.** If replay on import is too slow, accept a re-checking
   cache?
4. **Language name.** Keep `#lang rhombus/hol`?
