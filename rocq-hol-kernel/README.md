# rocq-hol-kernel

A Rocq (Coq 9.1.1) formalization of `rhombus-hol-kernel`'s term algebra and
LCF kernel (`rhombus-hol-kernel/rhombus/hol/{names,htype,term,kernel}.rhm`),
plus a set-theoretic denotational semantics and semantic soundness/
conservativity proofs `idris-hol-kernel/` deliberately does not attempt. It
is an independent verification artifact, not a runtime dependency:
`rhombus-hol-kernel`'s own `kernel.rhm` is 100% native Rhombus and remains
the trust boundary Rhombus/HOL actually runs on. This directory is not
referenced by `raco make`/`raco test` and adds no runtime dependency to any
Rhombus package.

## What is proved

**Syntactic**, matching `idris-hol-kernel`'s own scope: every one of the
kernel's ten primitive rules preserves `WellFormedThm`, and theory extension
never un-declares a prior name (`newTypeMonotone`/`newConstantMonotone`/…).
`Kernel.v` (2181 lines) is otherwise a line-for-line transliteration of
`names.rhm`/`htype.rhm`/`term.rhm`/`kernel.rhm`.

**Semantic** — the part `idris-hol-kernel` explicitly leaves open — is where
this development goes further:

- A set-theoretic model (`Frame`/`interpType`/`denote`, `Semantics.v`, 802
  lines): every `check_term`-valid closed term gets a genuine value,
  parametric in a type-variable valuation (`tv`) and an interpretation of
  every type operator/constant a theory can ever declare (`frTyOp`/
  `frConst`).
- **All ten primitive rules preserve `Valid`** (semantic validity: every
  model of the theory that satisfies the hypotheses also satisfies the
  conclusion) — `assumeValid`, `transValid`, `mkCombValid`, `absValid`,
  `betaValid`, `eqMpValid`, `deductAntisymValid`, `instValid`,
  `instTypeValid` (`REFL`'s trivial companion, `reflValid`, inline). This is
  the semantic half `idris-hol-kernel`'s README names as out of scope for
  that port.
- **Two of the four non-`new_axiom` extension principles are proved
  conservative**: `new_type_conservative` in full generality (unconditional
  — any model of the source theory is already a model of the extension) and
  `new_constant_conservative` conditionally (on the caller supplying a
  semantically coherent family for the new constant, which is the correct
  shape — an entirely free constant has no canonical denotation to derive
  one from; whether such a family always exists for an arbitrary reachable
  model is a separate fact, established below only for the restricted
  master corollary's specific induction, not in general).
- **A master corollary**, `type_and_constant_theories_have_models`
  (`Soundness.v`): every theory reachable from `initial_theory` via only
  `new_type`/`new_constant` (the restricted relation `ReachedFromTypeConst`)
  has a model, built by induction using a single canonical constant family
  (`fc_n0`, `interpType_witness_gen` specialised to the initial, `unit`-
  valued type-operator interpretation, together with its own naturality
  proof `interpType_witness_frTyOp0_natural`).

## What is not proved, and exactly why

Two of the four extension principles' conservativity are **not** proved —
each has an explanatory comment at its (absent) proof site in `Soundness.v`
rather than a stub, an `Admitted`, or a fabricated hypothesis:

- **`new_basic_definition_conservative`** (comment above where it would sit,
  `Soundness.v`): not an architectural obstruction, just unfinished, large
  proof engineering. Extending a model to a fresh, *defined* constant
  requires the constant's family to equal the definiens' own denotation at
  every type instance a later `type_match` can reach it at — including
  instances that arise from composing two independent substitutions, not
  merely one already-checked one. Closing that needs a structural naturality
  theorem this development does not yet have (a generalisation of
  `denote_inst_type`'s proof to two substitutions rather than one). Nothing
  about the `Frame` design blocks it — it is exactly the kind of gap that
  gets closed by more of the same kind of proof already in this file.
- **`new_basic_type_definition_conservative`**: every attempted construction
  ran into the same verified obstruction, not (yet) a proof that the
  `Frame` record admits no construction at all. `frTyOp`'s type-operator
  arguments are passed as bare `seq Type` (no attached inhabitant), while
  `frTyOp_inhab` requires every instance — including ones built from
  argument lists with no witness anywhere, e.g. containing `False` — to be
  inhabited unconditionally. The subset type `new_basic_type_definition`
  introduces is genuinely new content (built from a witnessed predicate);
  every construction tried needed an inhabitant the bare `seq Type`
  argument could not supply, and none of the narrower workarounds
  attempted (see `PLAN.md` §11.2) got past that. One possible fix changes
  `frTyOp`'s argument type to `seq {T : Type & T}`, which would ripple
  through most of `Semantics.v`+`Soundness.v`; whether that specific
  change is *necessary*, versus some other repair (a weaker/theory-relative
  naturality law, or building the model for the whole final theory at
  once instead of incrementally), was not established — this is recorded
  as an open problem, not routed around with an extra axiom or a
  narrowed, silently weaker theorem.

The master corollary follows the same principle by construction, not by
omission: it is named `type_and_constant_theories_have_models`, not
`definitional_theories_have_models`, and its relation is
`ReachedFromTypeConst`, not a general `ReachedFrom` — both names make the
restricted scope (`new_type`/`new_constant` only) visible at every call
site, so nothing downstream can mistake it for covering `new_axiom`,
`new_basic_definition`, or `new_basic_type_definition`.

`new_axiom` itself was never in scope for a conservativity proof — it is
the kernel's deliberate, documented escape hatch, and asserting its
conservativity would be false in general.

### A design bug found and fixed along the way

The first version of `Frame` required `frConst`'s type-substitution
naturality (`frConst F n tv (type_subst tyin ty) = …`) *unconditionally*,
for every name and every type — including a bare type variable. That is
incompatible with `ModelsTheory`'s own requirement that `frConst F NEq` be
genuine equality at every instance: instantiating the unconditional law at
`ty := HTyVar x` and a substitution mapping `x` to an equality-shaped type
forces `frConst F NEq` at the *bare variable* `x` to already equal
transported equality for every possible instantiation simultaneously,
which no `tv`-total, opaque-`Type`-respecting `frConst` can satisfy. The
fix, `ModelsTheoryNat` (`Semantics.v`), makes this law theory-relative:
required only at types that are genuine instances (via `type_match`) of a
*declared* constant's own generic type, which structurally excludes the
bare-variable counterexample. See the comment on `ModelsTheoryNat` for the
full argument.

## Axioms

`src/PrintAssumptions.v` runs `Print Assumptions` over every theorem listed
above (both `Valid` preservation and the two proved conservativity
principles plus the master corollary) and is compiled as part of `make`.
The closure is exactly four, all standard Rocq/Coq standard-library axioms,
none of them a choice principle:

- `ProofIrrelevance.proof_irrelevance`
- `FunctionalExtensionality.functional_extensionality_dep`
- `PropExtensionality.propositional_extensionality`
- `Eqdep.Eq_rect_eq.eq_rect_eq` (pulled in transitively by
  `Eqdep_dec.UIP_dec`, used for `HType_UIP`)

Nothing from `Classical_Prop`/`ClassicalEpsilon` appears, because nothing
proved here needs excluded middle: that axiom was needed by the attempted
construction of `new_basic_type_definition_conservative`, which is not
proved and is not included in this build.

## Reproducing

```sh
cd rocq-hol-kernel
nix develop .. --command bash -c 'coq_makefile -f _CoqProject -o Makefile && make'
```

This compiles every file in dependency order (`Names.v`, `HType.v`,
`Term.v`, `Kernel.v`, `Semantics.v`, `Soundness.v`, `PrintAssumptions.v`)
with zero errors and zero `Admitted`. `grep -rn "^Admitted\\." src/*.v`
comes back empty (the word "admitted" does appear once, in
`Semantics.v`'s own prose comment about an earlier design, not as a
proof-closing tactic).

## Layout

- `src/Names.v` — canonical names of the logical constants and type
  constructors, as an inductive `Name` (mirrors `idris-hol-kernel`'s own
  `Name.idr`: an interned identity, never text, needs no axiom for its own
  equality).
- `src/HType.v` — HOL types: `TyVar`/`TyApp`, substitution, matching,
  ordering (`htype.rhm`).
- `src/Term.v` — locally-nameless terms (`term.rhm`).
- `src/Kernel.v` — the ten primitive inference rules, theory extension
  (`new_type`/`new_constant`/`new_axiom`/`new_basic_definition`/
  `new_basic_type_definition`), and every `WellFormedThm`-preservation
  proof (`kernel.rhm`).
- `src/Semantics.v` — `Frame`/`interpType`/`denote`, `ModelsTheory`/
  `ModelsTheoryNat`, and the `Frame`-independent lemmas about `type_match`/
  `denote` that both `Soundness.v`'s per-rule proofs and its
  conservativity proofs need.
- `src/Soundness.v` — every per-rule `Valid`-preservation proof, the two
  proved conservativity principles (`new_type_conservative`,
  `new_constant_conservative`), the two documented-but-unproved gaps
  (with their explanatory comments), `Frame0`/`initial_theory`'s own model,
  and the restricted master corollary
  (`ReachedFromTypeConst`/`type_and_constant_theories_have_models`).
- `src/PrintAssumptions.v` — `Print Assumptions` over every theorem this
  development claims, to keep the axiom list (above) honest and checked on
  every build rather than asserted in prose alone.
