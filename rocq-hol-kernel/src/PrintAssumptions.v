(** Prints the full axiom closure of every top-level theorem this
    development claims: the ten primitive rules' [Valid] preservation,
    the two fully-proved conservativity principles ([new_type]/
    [new_constant]), and the master corollary built from them. Compiled
    as part of a plain `make`, or run standalone:
    [coqc -R src RocqHolKernel src/PrintAssumptions.v].

    Expected axiom closure: [proof_irrelevance], [functional_extensionality_dep]
    (from which [functional_extensionality] is derived),
    [propositional_extensionality], and [Eq_rect_eq.eq_rect_eq] (pulled
    in transitively by [Eqdep_dec.UIP_dec], used for [HType_UIP]) --
    four classical-but-not-choice axioms, all from Coq's own standard
    library. Nothing from [ClassicalEpsilon]/[Classical_Prop] should
    appear: this file does not import them, and no theorem printed
    below transitively depends on [new_basic_type_definition_conservative]
    (which is not proved here -- see the comment above it in
    [Soundness.v] -- and would need such an axiom, per that comment). *)
From RocqHolKernel Require Import Names HType Term Kernel Semantics Soundness.

(* Kernel-level: the ten primitive rules preserve well-formedness. *)
Print Assumptions reflWellFormed.
Print Assumptions assumeWellFormed.
Print Assumptions transWellFormed.
Print Assumptions mkCombWellFormed.
Print Assumptions absWellFormed.
Print Assumptions betaWellFormed.
Print Assumptions deductAntisymWellFormed.
Print Assumptions eqMpWellFormed.
Print Assumptions instWellFormed.
Print Assumptions instTypeWellFormed.

(* Semantic soundness: the ten primitive rules preserve Valid. *)
Print Assumptions reflValid.
Print Assumptions assumeValid.
Print Assumptions transValid.
Print Assumptions mkCombValid.
Print Assumptions absValid.
Print Assumptions betaValid.
Print Assumptions eqMpValid.
Print Assumptions deductAntisymValid.
Print Assumptions instValid.
Print Assumptions instTypeValid.

(* Conservativity: the two proved principles (one unconditional, one
   conditional on a caller-supplied family). *)
Print Assumptions new_type_conservative.
Print Assumptions new_constant_conservative.

(* The master corollary built from them. *)
Print Assumptions type_and_constant_theories_have_models.
Print Assumptions type_and_constant_theories_have_models_from_initial.
