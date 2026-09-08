From mathcomp Require Import all_boot finmap.
From Stdlib Require Import Eqdep_dec ProofIrrelevance FunctionalExtensionality.
From RocqHolKernel Require Import Names HType Term Kernel.
Open Scope fmap_scope.
Open Scope fset_scope.

(** * Set-theoretic denotational semantics.

    [interpType]/[Frame]/[denote] give every [check_term]-valid, closed
    term a genuine set-theoretic meaning, parametric in an interpretation
    of type variables ([tv]) and of the two type operators every theory
    starts with plus whatever [new_type] adds ([frTyOp]), and of every
    constant at every type instance it can appear at ([frConst]). *)

(** [tv] is universally quantified (by [ModelsTheory]/[Valid]) over
    *every* [Name -> {T : Type & T}] -- [frConst]'s signature is
    [forall tv, ...], with no way to restrict which [tv] a [Frame] must
    answer for. Interpreting a type variable as [projT1 (tv n)], the
    *type* component of the dependent pair [tv n : {T : Type & T}],
    rather than requiring a separate, independently-supplied [Name ->
    Type] valuation is what keeps every instance of [interpType]
    inhabited regardless of [tv]: [tv n]'s own second projection,
    [projT2 (tv n)], already carries a genuine witness of
    [projT1 (tv n)] by construction (a [{T : Type & T}] value cannot
    exist without one), so there is no degenerate "[tv] assigns an
    uninhabited type" case to guard against separately. This is what
    makes [Frame] itself a constructible type -- see
    [interpType_witness_gen] immediately below. Every other case
    ([HTyApp]) is inhabited by construction given a [Frame]'s own
    [frTyOp] is chosen (by whoever builds a concrete [Frame]) to be
    pointwise inhabited too. *)
Fixpoint interpType (tyi : (Name -> {T : Type & T}) -> Name -> seq HType -> seq Type -> Type) (tv : Name -> {T : Type & T}) (ty : HType) : Type :=
  match ty with
  | HTyVar n => projT1 (tv n)
  | HTyApp n args =>
      match n, args with
      | NBool, _ => Prop
      | NFun, [:: A; B] => interpType tyi tv A -> interpType tyi tv B
      | NFun, _ => unit
      | _, _ => tyi tv n args (map (interpType tyi tv) args)
      end
  end.

(** Every interpreted type is inhabited, given only [tyi]'s own
    per-instance witness ([Hinhab], generalising a [Frame]'s
    [frTyOp_inhab]) -- [tv] itself is *always* pointwise inhabited now,
    since [tv n]'s second projection carries the witness by
    construction; this is exactly what makes [Frame] itself
    constructible (see [frConst]'s field below), unlike an earlier
    version of this file where [tv : Name -> Type] admitted no such
    witness and [frConst] -- being asked for a value at *every* [tv],
    including [fun _ => False] -- had no possible definition. *)
Fixpoint interpType_witness_gen (tyi : (Name -> {T : Type & T}) -> Name -> seq HType -> seq Type -> Type)
    (Hinhab : forall tv n htyargs args, tyi tv n htyargs args)
    (tv : Name -> {T : Type & T}) (ty : HType) : interpType tyi tv ty.
Proof.
case: ty => [n | n args] /=.
- exact: (projT2 (tv n)).
- case: n args => [args | args | args | args | args | id args].
  + case: args => [| A [| B [| C rest]]] /=.
    * exact: tt.
    * exact: tt.
    * exact: (fun _ => interpType_witness_gen tyi Hinhab tv B).
    * exact: tt.
  + exact: True.
  + exact: (Hinhab tv NEq args (map (interpType tyi tv) args)).
  + exact: (Hinhab tv NAlpha args (map (interpType tyi tv) args)).
  + exact: (Hinhab tv NRepVar args (map (interpType tyi tv) args)).
  + exact: (Hinhab tv (NUser id) args (map (interpType tyi tv) args)).
Defined.

(** A [tv] transported through a type substitution [tyin]: the type
    variable valuation that makes denoting [ty] under it agree with
    denoting [type_subst tyin ty] under the original [tv] --
    [interpType_subst] below states and [INST_TYPE]'s soundness proof
    uses exactly this agreement. Packages a witness alongside the
    transported type (via [interpType_witness_gen]) so the result is
    itself a valid [Name -> {T : Type & T}], not just [Name -> Type]. *)
Definition tv_subst (tyi : (Name -> {T : Type & T}) -> Name -> seq HType -> seq Type -> Type)
    (Hinhab : forall tv n htyargs args, tyi tv n htyargs args)
    (tv : Name -> {T : Type & T}) (tyin : {fmap Name -> HType}) : Name -> {T : Type & T} :=
  fun m => existT _ (interpType tyi tv (odflt (HTyVar m) tyin.[? m]))
             (interpType_witness_gen tyi Hinhab tv (odflt (HTyVar m) tyin.[? m])).

(** The substitution law a [Frame]'s own [frTyOp] must satisfy, stated
    abstractly over a raw [tyi] first so it can be referenced from
    inside the [Frame] record below (a field's type may depend on an
    earlier field, not on the record itself, which does not exist yet).
    Proved once here from exactly the "opaque type-operator commutes
    with substitution" fact at the [HTyApp] leaves -- the [HTyVar] and
    [NBool]/[NFun] cases commute for free, by [interpType]'s own
    definition. *)
Lemma interpType_subst_gen (tyi : (Name -> {T : Type & T}) -> Name -> seq HType -> seq Type -> Type)
    (Hinhab : forall tv n htyargs args, tyi tv n htyargs args)
    (Hsubst : forall tv (tyin : {fmap Name -> HType}) n args,
      tyi tv n (map (type_subst tyin) args)
        (map (interpType tyi tv) (map (type_subst tyin) args)) =
      tyi (tv_subst tyi Hinhab tv tyin) n args
        (map (interpType tyi (tv_subst tyi Hinhab tv tyin)) args))
    tv tyin ty :
  interpType tyi tv (type_subst tyin ty) = interpType tyi (tv_subst tyi Hinhab tv tyin) ty.
Proof.
elim/HType_rect: ty => [n | n args IH].
- rewrite /= /tv_subst.
  by case E: (tyin.[? n]) => [t|] //=.
- move: n args IH => [| | | | | id] args IH.
  + case: args IH => [| A [| B [| C rest]]] //= IH.
    move: IH => [-> [-> _]].
    by [].
  + by [].
  + by rewrite /= (Hsubst tv tyin NEq args).
  + by rewrite /= (Hsubst tv tyin NAlpha args).
  + by rewrite /= (Hsubst tv tyin NRepVar args).
  + by rewrite /= (Hsubst tv tyin (NUser id) args).
Qed.

(** [frConst] is total over every [(n, tv, ty)] triple, including
    undeclared names or off-genuine-instance types -- deliberate: matches
    [check_term]'s own job of restricting which [(n, ty)] pairs actually
    occur in a well-formed term; [Frame] is never asked about the rest.
    Constructible for every [tv] precisely because [tv]'s codomain
    [{T : Type & T}] carries its own witness -- see [interpType_witness_gen]
    and [Frame0]/[initial_theory]'s model below.

    [frTyOp_subst] is the type-substitution naturality every genuine
    HOL "general model" satisfies by construction (a model assigns
    each type operator a value depending only on the *interpreted*
    types its arguments denote, never on how those types were spelled)
    -- [INST_TYPE]'s soundness needs exactly this, stated here as an
    explicit closure condition on [Frame] rather than re-deriving
    [Frame] from more primitive genuinely-parametric data, matching
    how [frTyOp_inhab] already states inhabitedness as a closure
    condition rather than a derived fact. The analogous naturality law
    for [frConst] is *not* a [Frame] field -- it is theory-relative
    (see [ModelsTheoryNat] below), because an unconditional version
    for [frConst] is incompatible with [ModelsTheory]'s [NEq] clause
    (see the comment there). *)
Record Frame := mkFrame {
  frTyOp : (Name -> {T : Type & T}) -> Name -> seq HType -> seq Type -> Type;
  frTyOp_inhab : forall tv n htyargs args, frTyOp tv n htyargs args;
  frTyOp_subst : forall tv (tyin : {fmap Name -> HType}) n args,
    frTyOp tv n (map (type_subst tyin) args)
      (map (interpType frTyOp tv) (map (type_subst tyin) args)) =
    frTyOp (tv_subst frTyOp frTyOp_inhab tv tyin) n args
      (map (interpType frTyOp (tv_subst frTyOp frTyOp_inhab tv tyin)) args);
  frConst : forall (n : Name) (tv : Name -> {T : Type & T}) (ty : HType), interpType frTyOp tv ty
}.

(** The substitution law specialised to a concrete [Frame]'s own
    [frTyOp], via its [frTyOp_subst] field. *)
Lemma interpType_subst (F : Frame) tv tyin ty :
  interpType (frTyOp F) tv (type_subst tyin ty) =
  interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) ty.
Proof. exact: (interpType_subst_gen (frTyOp F) (frTyOp_inhab F) (frTyOp_subst F) tv tyin ty). Defined.

(** [interpType_witness_gen] specialised to a concrete [Frame]. *)
Definition interpType_witness (F : Frame) (tv : Name -> {T : Type & T}) (ty : HType) :
    interpType (frTyOp F) tv ty :=
  interpType_witness_gen (frTyOp F) (frTyOp_inhab F) tv ty.

(** [t] is well-typed everywhere it applies one term to another and every
    [TmBVar] matches its binder -- purely structural, independent of any
    [Theory] (the arity/declaration checks [check_open_term] performs are
    theory bookkeeping irrelevant to what [denote] needs to type-check). *)
Fixpoint WellTypedShape (t : Term) (env : seq HType) : Prop :=
  match t with
  | TmBVar i ty => i < size env /\ nth ty env i = ty
  | TmComb f x =>
      WellTypedShape f env /\ WellTypedShape x env /\
      is_fun (type_of f) /\ (dest_fun (type_of f)).1 = type_of x
  | TmAbs aty b => WellTypedShape b (aty :: env)
  | _ => True
  end.

Lemma check_open_term_WellTypedShape thy t env :
  check_open_term thy t env -> WellTypedShape t env.
Proof.
elim: t env => [v | i ty | n ty | f IHf x IHx | aty b IHb] env //=.
- by move=> /andP[/andP[Hlt Heq] _]; split=> //; exact/eqP.
- move=> /andP[/andP[Hf Hx] Hdom].
  split; first exact: IHf.
  split; first exact: IHx.
  move: Hdom => /andP[Hisfun Heq].
  split; first exact: Hisfun.
  exact/eqP.
- by move=> /andP[_ Hb]; exact: IHb.
Qed.

(** Applying an interpreted function value to an interpreted argument
    value, given the argument's type matches the function's domain -- the
    one place [denote]'s [TmComb] case needs a type-cast, justified by
    [WellTypedShape]'s own equation. *)
Definition applyFun (F : Frame) (tv : Name -> {T : Type & T}) (fty xty : HType)
    (Hisfun : is_fun fty) (Heq : (dest_fun fty).1 = xty)
    (fv : interpType (frTyOp F) tv fty) (xv : interpType (frTyOp F) tv xty) :
    interpType (frTyOp F) tv (dest_fun fty).2.
Proof.
move: fv xv Heq.
case: fty Hisfun => [n | n [|d [|r [|]]]] //= Hisfun.
case: n Hisfun => [Hisfun|Hisfun|Hisfun|Hisfun|Hisfun|id Hisfun] //= fv xv Heq.
- move: xv; rewrite -Heq => xv.
  exact: (fv xv).
- by move/eqP: Hisfun.
Defined.

(** The one fact every rule that builds or consumes [mk_comb]/[mk_eq]
    needs about [applyFun]: at a genuine function type [mk_fun d r], it
    is exactly "cast the argument across [Heq], then apply". Proved once
    here, by re-deriving [applyFun]'s own case split rather than
    unfolding its compiled proof term (the two are *not* interchangeable
    under Coq's own reduction -- the compiled term gets stuck on the
    opaque [eqP] instance for [Name], even though the boolean it decides
    fully computes; substituting [xty] for [d] via [Heq] first, before
    anything else touches it, is what lets the final [case: xty / Heq]
    close both sides by computation.) *)
Lemma applyFun_mk_fun (F : Frame) tv d r xty (Hisfun : is_fun (mk_fun d r))
    (Heq : (dest_fun (mk_fun d r)).1 = xty)
    (fv : interpType (frTyOp F) tv (mk_fun d r)) (xv : interpType (frTyOp F) tv xty) :
  applyFun F tv (mk_fun d r) xty Hisfun Heq fv xv =
  fv (eq_rect xty (interpType (frTyOp F) tv) xv d (esym Heq)).
Proof.
rewrite /applyFun /mk_fun /mk_tyapp /=.
move: xv.
case: xty / Heq.
by [].
Qed.

(** A stack of interpreted values, one per entry of a [seq HType] --
    interprets [check_open_term]'s own [env : seq HType] of enclosing
    binder types, but carrying values rather than just types. *)
Inductive DEnv (F : Frame) (tv : Name -> {T : Type & T}) : seq HType -> Type :=
  | DEnvNil : DEnv F tv [::]
  | DEnvCons ty env0 :
      interpType (frTyOp F) tv ty -> DEnv F tv env0 -> DEnv F tv (ty :: env0).

Fixpoint dnth (F : Frame) (tv : Name -> {T : Type & T}) (env : seq HType) (d : DEnv F tv env) (i : nat)
    {struct d} : i < size env -> interpType (frTyOp F) tv (nth (HTyVar NAlpha) env i).
Proof.
case: d i => [| ty env0 v d0] [| i0] Hi //=.
exact: (dnth F tv env0 d0 i0 Hi).
Defined.

(** [denote] is total (built to type-check unconditionally given only
    [WellTypedShape], the same total-modulo-well-formedness pattern
    [type_of] itself follows); its value is only claimed meaningful for
    terms that additionally pass [check_term]. [venv] interprets every
    free variable (HOL's free variables are implicitly universally
    quantified at the meta level; nothing in this kernel's ten primitive
    rules ever binds one, so [Valid] below universally quantifies over
    [venv] the same way it does over [tv]). *)
Fixpoint denote (F : Frame) (tv : Name -> {T : Type & T})
    (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v))
    (env : seq HType) (d : DEnv F tv env) (t : Term) {struct t} :
    WellTypedShape t env -> interpType (frTyOp F) tv (type_of t).
Proof.
case: t d => [v | i ty | n ty | f x | aty b] d Hwt /=.
- exact: (venv v).
- move: Hwt => [Hlt Hnth].
  move: (dnth F tv env d i Hlt).
  by rewrite -(set_nth_default (HTyVar NAlpha) ty Hlt) Hnth.
- exact: (frConst F n tv ty).
- move: Hwt => [Hf [Hx [Hisfun Heq]]].
  move: (applyFun F tv (type_of f) (type_of x) Hisfun Heq
    (denote F tv venv env d f Hf) (denote F tv venv env d x Hx)).
  case: (is_fun (type_of f)) Hisfun => [Hisfun|Hisfun] //=.
- move=> a.
  exact: (denote F tv venv (aty :: env) (DEnvCons F tv aty env a d) b Hwt).
Defined.

(** Denoting a closed ([env = [::]]), [check_term]-valid term, bundling
    the [WellTypedShape] derivation so callers never see it. *)
Definition SafeDenote (F : Frame) (thy : Theory) (tv : Name -> {T : Type & T})
    (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v)) (t : Term)
    (Hct : check_term thy t) : interpType (frTyOp F) tv (type_of t) :=
  denote F tv venv [::] (DEnvNil F tv) t
    (check_open_term_WellTypedShape thy t [::] Hct).

(** [SafeDenote] does not actually look at [thy] except through [Hct] --
    an easy but important fact: it lets every soundness/conservativity
    proof transport a denotation across a theory extension for free, as
    long as the *term* being denoted is unaffected. *)
Lemma SafeDenote_irrel_thy (F : Frame) (thy thy' : Theory) (tv : Name -> {T : Type & T})
    (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v)) (t : Term)
    (Hct : check_term thy t) (Hct' : check_term thy' t) :
  SafeDenote F thy tv venv t Hct = SafeDenote F thy' tv venv t Hct'.
Proof. by rewrite /SafeDenote (proof_irrelevance _ (check_open_term_WellTypedShape thy t [::] Hct) (check_open_term_WellTypedShape thy' t [::] Hct')). Qed.

(** [interpType _ _ bool_ty] is [Prop] by definition, regardless of [tv]
    -- casting a denotation of a term known [is_bool] into that [Prop]. *)
Definition denoteProp (F : Frame) (thy : Theory) (tv : Name -> {T : Type & T})
    (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v)) (t : Term)
    (Hct : check_term thy t) (Hbt : is_bool t) : Prop :=
  eq_rect (type_of t) (interpType (frTyOp F) tv)
    (SafeDenote F thy tv venv t Hct) bool_ty (elimT eqP Hbt).

Lemma denoteProp_irrel (F : Frame) (thy : Theory) (tv : Name -> {T : Type & T})
    (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v)) (t : Term)
    (Hct1 Hct2 : check_term thy t) (Hbt1 Hbt2 : is_bool t) :
  denoteProp F thy tv venv t Hct1 Hbt1 = denoteProp F thy tv venv t Hct2 Hbt2.
Proof.
rewrite /denoteProp (eq_irrelevance Hct1 Hct2) (eq_irrelevance Hbt1 Hbt2) //.
Qed.

(** * Models

    A model must interpret [NEq] as genuine equality at every type
    instance -- the one logical constant the ten primitive rules
    themselves ever construct (every other connective, in this kernel,
    is [new_basic_definition]d in the derived layer, out of scope here,
    so nothing else needs a fixed interpretation) -- must validate every
    axiom the theory has accumulated, and must interpret every constant
    [th_defs] has ever recorded an equation for exactly as that equation
    prescribes, at *every* type instance the equation's own type
    variables can be substituted to -- this is what makes a defined
    constant no more polymorphic, semantically, than its own defining
    term. *)
(** [frConst]'s substitution naturality, but theory-relative: required
    only at [ty] that are genuine instances (via [type_match]) of a
    *declared* constant's own generic type -- never at an arbitrary
    [ty] (in particular never at a bare [HTyVar], reachable only by
    first substituting a declared name's *own* generic type, which is
    never a bare variable). The counterexample below only establishes
    that the unconditional version of this law (naturality at every
    [ty], regardless of any theory) is incompatible with
    [ModelsTheory]'s [NEq] clause below, which pins [frConst F NEq] to
    *genuine* equality -- it does not by itself show the unconditional
    law has no [Frame] satisfying it in isolation (a [Frame] whose
    [frConst] never needs to equal genuine equality anywhere is a
    separate question this file does not settle). Concretely:
    instantiating the unconditional law at [ty := HTyVar x] and
    [tyin := [x |-> mk_fun dom (mk_fun dom bool_ty)]] would force
    [frConst F NEq] at the bare type variable [x] to equal transported
    genuine equality for *every* choice of [dom] and [tv] simultaneously
    -- something no [Frame] satisfying the [NEq] clause and this
    unconditional law together can do, since [frConst] cannot inspect
    an opaque [Type] to detect "is this secretly an equality-relation
    type". Gating by [const_type]/[type_match] avoids the counterexample
    entirely: [type_match] against a pattern built from [HTyApp] can
    never succeed against a bare [HTyVar] target, so the only [ty] this
    clause ever applies to are exactly the shapes a constant's own
    generic type allows.
    Factored out of [ModelsTheory] as its own definition so the
    [inst_type]-commutation lemmas in [Soundness.v] (which only ever
    need this one clause, never the other three) can be stated against
    it directly, instead of the full [ModelsTheory]. *)
Definition ModelsTheoryNat (F : Frame) (thy : Theory) : Prop :=
  forall n gty, const_type thy n = Some gty ->
     forall ty (m : {fmap Name -> HType}), type_match gty ty [fmap] = Some m ->
     forall tv (tyin : {fmap Name -> HType}),
     frConst F n tv (type_subst tyin ty) =
       eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) ty) (fun T => T)
         (frConst F n (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) ty)
         (interpType (frTyOp F) tv (type_subst tyin ty))
         (esym (interpType_subst_gen (frTyOp F) (frTyOp_inhab F) (frTyOp_subst F) tv tyin ty)).

Definition ModelsTheory (F : Frame) (thy : Theory) : Prop :=
  (forall (dom : HType) (tv : Name -> {T : Type & T}),
     frConst F NEq tv (mk_fun dom (mk_fun dom bool_ty)) =
       @eq (interpType (frTyOp F) tv dom))
  /\
  (forall ax, List.In ax (th_axioms thy) ->
     forall tv (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v))
       (Hct : check_term thy (thm_concl ax)) (Hbt : is_bool (thm_concl ax)),
     denoteProp F thy tv venv (thm_concl ax) Hct Hbt)
  /\
  (forall n df, (th_defs thy).[? n] = Some df ->
     forall r, dest_eq (thm_concl df) = Some (mk_const n (type_of r), r) ->
     forall (Hr : check_term thy r) tv
       (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v))
       (sigma : {fmap Name -> HType})
       (Htyin : forall n0 ty0, sigma.[? n0] = Some ty0 -> check_type thy ty0),
     frConst F n tv (type_subst sigma (type_of r)) =
       eq_rect (type_of (inst_type sigma r)) (interpType (frTyOp F) tv)
         (SafeDenote F thy tv venv (inst_type sigma r)
            (proj1 (check_open_term_inst_type thy sigma r [::] Htyin Hr)))
         (type_subst sigma (type_of r))
         (proj2 (check_open_term_inst_type thy sigma r [::] Htyin Hr)))
  /\
  ModelsTheoryNat F thy.

(** A model whose defined-constant clause additionally holds at every
    type instance reachable through [type_match] against an
    already-declared definition's own right-hand side, stated free of
    any [check_term]/[check_type] theory gate -- purely in terms of
    [WellTypedShape]/[denote] instead of [check_term]/[SafeDenote]. This
    is what the four non-[new_axiom] conservativity proofs need: the
    invariant must survive a theory extension (e.g. [new_type] adding a
    fresh type name that a later [type_match] can bind), so it cannot be
    gated behind [check_term thy], which only ever grows more permissive
    as [thy] grows, never shrinks -- a theory-independent clause is the
    one that a model of [thy] can hand forward unchanged as a model of
    any [thy'] extending it. *)
Definition ModelsTheoryUniform (F : Frame) (thy : Theory) : Prop :=
  ModelsTheory F thy /\
  (forall n df, (th_defs thy).[? n] = Some df ->
     forall r, dest_eq (thm_concl df) = Some (mk_const n (type_of r), r) ->
     WellTypedShape r [::] ->
     forall tv (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v)) ty m,
       type_match (type_of r) ty [fmap] = Some m ->
       forall (Hshape : WellTypedShape (inst_type m r) [::])
         (Ety : type_of (inst_type m r) = ty),
       frConst F n tv ty =
         eq_rect (type_of (inst_type m r)) (interpType (frTyOp F) tv)
           (denote F tv venv [::] (DEnvNil F tv) (inst_type m r) Hshape) ty Ety).

(** * Semantic validity

    A theorem is [Valid] in a frame when it is [WellFormedThm] and, in
    every model of its theory, every free-variable instance that makes
    every hypothesis true also makes the conclusion true. *)
Definition Valid (F : Frame) (thy : Theory) (th : Thm) : Prop :=
  WellFormedThm thy th /\
  (ModelsTheory F thy ->
   forall tv (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v)),
   (forall h (Hch : check_term thy h) (Hbh : is_bool h), h \in thm_hyps th ->
      denoteProp F thy tv venv h Hch Hbh) ->
   forall (Hcc : check_term thy (thm_concl th)) (Hbc : is_bool (thm_concl th)),
   denoteProp F thy tv venv (thm_concl th) Hcc Hbc).

(** * Type-substitution semantics

    [type_match]'s accumulator, once it has matched every type variable
    of a pattern against a concrete type, denotes exactly that concrete
    type back out under [type_subst] -- the fact [INST_TYPE]'s semantic
    soundness rests on, since instantiating a theorem's conclusion at a
    type substitution and instantiating the *type* of an already-checked
    constant occurrence via [type_match] are the same computation. *)

Lemma type_subst_eq_on (f g : {fmap Name -> HType}) pat :
  (forall n, type_occurs n pat -> f.[? n] = g.[? n]) ->
  type_subst f pat = type_subst g pat.
Proof.
elim/HType_rect: pat => [n | n args IH] Heq //=.
- by rewrite (Heq n (eqxx n)).
- congr HTyApp.
  elim: args IH Heq => [| a args' IHa] //= [Ha Hargs] Heq.
  congr cons.
  + apply: Ha => n0 Hn.
    apply: Heq.
    by rewrite Hn.
  + apply: IHa => // n0 Hn.
    move: Hn => /= Hn.
    apply: Heq.
    by rewrite Hn orbT.
Qed.

Lemma type_match_mono pat :
  forall t (acc m : {fmap Name -> HType}),
  type_match pat t acc = Some m ->
  forall n v, acc.[? n] = Some v -> m.[? n] = Some v.
Proof.
elim/HType_rect: pat => [n | n pargs IH] t acc m.
- rewrite /=.
  case E: (acc.[? n]) => [prev|].
  + case: (@eqP _ prev t) => [Hpt [<-] | _ //] n0 v0 Hv0.
    exact: Hv0.
  + move=> [<-] n0 v0 Hv0.
    case: (@eqP _ n0 n) => [Heq | Hne].
      by move: Hv0; rewrite Heq E.
    by rewrite fnd_set (negbTE (introN eqP Hne)).
- rewrite /=.
  case: t => [n2 | n2 targs] //=.
  case: ifP => [Hcond | _ //].
  move: Hcond => /andP[Heqn Heqsz] Hm n0 v0 Hv0.
  move: acc m Hv0 Hm.
  elim: pargs targs IH Heqsz => [| p ps IHps].
  + move=> [| t2 ts] // _ _ acc m Hv0 [<-].
    exact: Hv0.
  + move=> [| t2 ts] // [Hp Hps] Heqsz acc m Hv0.
    case E: (type_match p t2 acc) => [a2|] // Hm.
    have Hv1 : a2.[? n0] = Some v0 := Hp t2 acc a2 E n0 v0 Hv0.
    exact: (IHps ts Hps Heqsz a2 m Hv1 Hm).
Qed.

Lemma type_match_covers pat :
  forall t (acc m : {fmap Name -> HType}),
  type_match pat t acc = Some m ->
  forall n, type_occurs n pat -> n \in domf m.
Proof.
elim/HType_rect: pat => [n | n pargs IH] t acc m.
- rewrite /=.
  case E: (acc.[? n]) => [prev|].
  + case: (@eqP _ prev t) => [Hpt [<-] | _ //] n0 /eqP ->.
    by rewrite -fndSome E.
  + move=> [<-] n0 /eqP ->.
    by rewrite -fndSome fnd_set eqxx.
- rewrite /=.
  case: t => [n2 | n2 targs] //=.
  case: ifP => [Hcond | _ //].
  move: Hcond => /andP[Heqn Heqsz] Hm n0 Hn0.
  move: acc m Hm Hn0.
  elim: pargs targs IH Heqsz => [| p ps IHps] //=.
  move=> [| t2 ts] // [Hp Hps] Heqsz acc m Hm.
  move=> /orP[Hn0a | Hn0ps].
  + case E: (type_match p t2 acc) Hm => [a2|] //= Hm2.
    have Hin_a2 : n0 \in domf a2 := Hp t2 acc a2 E n0 Hn0a.
    case Ekf: (a2.[? n0]) => [v0|]; last first.
      by move: Hin_a2; rewrite -fndSome Ekf.
    have Hmwhole : type_match (HTyApp n2 ps) (HTyApp n2 ts) a2 = Some m.
      by rewrite /= eqxx -eqSS Heqsz.
    have Hmono := type_match_mono (HTyApp n2 ps) (HTyApp n2 ts) a2 m Hmwhole n0 v0 Ekf.
    by rewrite -fndSome Hmono.
  + case E: (type_match p t2 acc) Hm => [a2|] //= Hm2.
    exact: (IHps ts Hps Heqsz a2 m Hm2 Hn0ps).
Qed.

Lemma type_match_sound pat :
  forall t (acc m : {fmap Name -> HType}),
  (forall n v, acc.[? n] = Some v -> v = type_subst m (HTyVar n)) ->
  type_match pat t acc = Some m -> type_subst m pat = t.
Proof.
elim/HType_rect: pat => [n | n pargs IH] t acc m Hinv.
- rewrite /=.
  case E: (acc.[? n]) => [prev|].
  + case: (@eqP _ prev t) => [Hpt [<-] | _ //].
    by rewrite E /= Hpt.
  + move=> [<-].
    by rewrite /= fnd_set eqxx.
- rewrite /=.
  case: t => [n2 | n2 targs] //=.
  case: ifP => [Hcond | _ //].
  move: Hcond => /andP[Heqn Heqsz] Hm.
  have -> : n = n2 by exact/eqP.
  congr HTyApp.
  move: acc Hinv Hm.
  elim: pargs targs IH Heqsz => [| p ps IHps].
  + by move=> [| t2 ts] // _ _ acc _ [<-].
  + move=> [| t2 ts] // [Hp Hps] Heqsz acc Hinv.
    case E: (type_match p t2 acc) => [a2|] // Hm.
    have Hinv_a2 : forall n0 v0, acc.[? n0] = Some v0 -> v0 = type_subst a2 (HTyVar n0).
      move=> n0 v0 Hv0.
      have Hmono := type_match_mono p t2 acc a2 E n0 v0 Hv0.
      by rewrite /= Hmono.
    have Hp2 : type_subst a2 p = t2 := Hp t2 acc a2 Hinv_a2 E.
    have Hmwhole : type_match (HTyApp n2 ps) (HTyApp n2 ts) a2 = Some m.
      by rewrite /= eqxx -eqSS Heqsz.
    have Hinv2 : forall n0 v0, a2.[? n0] = Some v0 -> v0 = type_subst m (HTyVar n0).
      move=> n0 v0 Hv0.
      have Hmono := type_match_mono (HTyApp n2 ps) (HTyApp n2 ts) a2 m Hmwhole n0 v0 Hv0.
      by rewrite /= Hmono.
    have Heqsz' : size ps == size ts by rewrite -eqSS.
    have Hrest := IHps ts Hps Heqsz' a2 Hinv2 Hm.
    have Hp2' : type_subst m p = t2.
      rewrite -Hp2.
      apply: type_subst_eq_on => n0 Hn0.
      have Hin_a2 : n0 \in domf a2 := type_match_covers p t2 acc a2 E n0 Hn0.
      case Ev0: (a2.[? n0]) => [v0|]; last first.
        by move: Hin_a2; rewrite -fndSome Ev0.
      have Hmono := type_match_mono (HTyApp n2 ps) (HTyApp n2 ts) a2 m Hmwhole n0 v0 Ev0.
      exact: Hmono.
    by rewrite /= Hp2' Hrest.
Qed.

(** * Reasoning about [denote] from the outside

    [denote]/[applyFun] are total, tactic-compiled functions; unfolding
    an *applied* instance of either one, for an abstract argument, gets
    stuck on Coq's own opaque [Equality.axiom] witness for [Name] --
    even though the boolean it decides always computes. The lemmas
    below are the reusable escape hatches every per-rule soundness proof
    in [Soundness.v] needs: [denote] does not care which [WellTypedShape]
    witness it is handed ([denote_irrel]), [HType] being a decidable
    [eqType] gives proof irrelevance for its own equality proofs
    ([HType_UIP]), and [SafeDenote_comb]/[SafeDenote_mk_eq] compute
    [SafeDenote] of a [mk_comb]/[mk_eq] application in terms of
    [SafeDenote] of its immediate subterms, with every stuck cast
    discharged once, here. *)

Lemma denote_irrel F tv venv env d t (Hwt1 Hwt2 : WellTypedShape t env) :
  denote F tv venv env d t Hwt1 = denote F tv venv env d t Hwt2.
Proof. by rewrite (proof_irrelevance _ Hwt1 Hwt2). Qed.

Lemma HType_eq_dec (x y : HType) : {x = y} + {x <> y}.
Proof. case: (@eqP _ x y) => [->|Hne]; [by left | by right]. Defined.

Lemma HType_UIP (x y : HType) (p q : x = y) : p = q.
Proof. exact: (Eqdep_dec.UIP_dec HType_eq_dec p q). Qed.

Lemma type_of_mk_comb_isfun f x :
  is_fun (type_of f) -> type_of (mk_comb f x) = (dest_fun (type_of f)).2.
Proof. rewrite /mk_comb /= => ->. by []. Qed.

(** [eq_rect]/[eq_rect_r], composed back to back across a boolean
    reflected as [b = true]/[b : bool] itself, cancel -- regardless of
    which two (necessarily equal, by proof irrelevance) proofs justify
    the two casts. *)
Lemma eq_rect_cancel2 (Ty : Type) (Q : Ty -> Type) (b : bool) (A B : Ty)
    (p : Q A) (e : b = true) (e' : (if b then A else B) = A) :
  eq_rect (if b then A else B) Q
    (@eq_rect_r bool true (fun b0 => Q (if b0 then A else B)) p b e) A e' = p.
Proof.
move: e' e p.
case: b => //= e' e p.
by rewrite (proof_irrelevance _ e' (erefl A)) (proof_irrelevance _ e (erefl true)).
Qed.

(** [eq_rect_r] with a motive independent of the boolean it reflects is
    the identity. *)
Lemma eq_rect_r_const (A Q : Type) (x y : A) (p : Q) (e : y = x) :
  eq_rect_r (fun _ : A => Q) p e = p.
Proof. move: e. by case: x /. Qed.

(** Transporting a function [Q x -> R] across [x = y] and applying it
    to a [Q y] value is the same as applying the original function to
    the argument transported back. *)
Lemma eq_rect_arrow_apply (Ty R : Type) (Q : Ty -> Type) (x y : Ty)
    (f : Q x -> R) (e : x = y) (z : Q y) :
  eq_rect x (fun ty => Q ty -> R) f y e z = f (eq_rect y Q z x (esym e)).
Proof. move: z. by case: y / e. Qed.

(** [denote] on each constructor, in a form usable without unfolding
    the compiled [Fixpoint] by hand -- the [TmFVar]/[TmConst] cases are
    already computationally transparent (no cast at all); [TmBVar]
    needs [dnth]'s generic-default value transported across the
    [nth]-default-irrelevance/[WellTypedShape] equations, [TmAbs] is
    again cast-free (the codomain [mk_fun aty (type_of b)] unfolds to
    the function space directly), and [TmComb] needs [applyFun]'s own
    cast, exactly as [SafeDenote_comb] below specialises it to a closed
    term. *)
Lemma denote_bvar F tv venv env d i ty (Hlt : i < size env) (Hnth : nth ty env i = ty) :
  denote F tv venv env d (TmBVar i ty) (conj Hlt Hnth) =
  eq_rect (nth ty env i) (interpType (frTyOp F) tv)
    (eq_rect (nth (HTyVar NAlpha) env i) (interpType (frTyOp F) tv)
       (dnth F tv env d i Hlt) (nth ty env i)
       (esym (set_nth_default (HTyVar NAlpha) ty Hlt)))
    ty Hnth.
Proof.
rewrite /denote /=.
rewrite (eq_rect_arrow_apply HType (interpType (frTyOp F) tv ty)
  (interpType (frTyOp F) tv) (nth ty env i) (nth (HTyVar NAlpha) env i)).
unfold eq_rect_r.
rewrite (eq_rect_arrow_apply HType (interpType (frTyOp F) tv ty)
  (interpType (frTyOp F) tv) ty (nth ty env i) id (esym Hnth)).
by rewrite (HType_UIP _ _ (esym (esym Hnth)) Hnth).
Qed.

Lemma denote_abs F tv venv env d aty b (Hwt : WellTypedShape (TmAbs aty b) env) :
  denote F tv venv env d (TmAbs aty b) Hwt =
  fun a => denote F tv venv (aty :: env) (DEnvCons F tv aty env a d) b Hwt.
Proof. by []. Qed.

Lemma denote_comb F tv venv env d f x
    (Hisfun : is_fun (type_of f)) (Hdom : (dest_fun (type_of f)).1 = type_of x)
    (Hf : WellTypedShape f env) (Hx : WellTypedShape x env)
    (Hfx : WellTypedShape (TmComb f x) env) :
  eq_rect (type_of (mk_comb f x)) (interpType (frTyOp F) tv)
    (denote F tv venv env d (mk_comb f x) Hfx)
    (dest_fun (type_of f)).2 (type_of_mk_comb_isfun f x Hisfun)
  = applyFun F tv (type_of f) (type_of x) Hisfun Hdom
      (denote F tv venv env d f Hf) (denote F tv venv env d x Hx).
Proof.
rewrite /mk_comb /=.
move: Hfx => [a [a0 [a1 b1]]].
rewrite (proof_irrelevance _ a1 Hisfun) (HType_UIP _ _ b1 Hdom).
rewrite (denote_irrel F tv venv env d f a Hf).
rewrite (denote_irrel F tv venv env d x a0 Hx).
have Ety : (if is_fun (type_of f) then (dest_fun (type_of f)).2 else bool_ty)
    = (dest_fun (type_of f)).2.
  rewrite ifT //.
rewrite (HType_UIP _ _ (type_of_mk_comb_isfun f x Hisfun) Ety).
move: (applyFun F tv (type_of f) (type_of x) Hisfun Hdom
  (denote F tv venv env d f Hf) (denote F tv venv env d x Hx)) Ety.
move: Hisfun.
case: (is_fun (type_of f)) => [Hisfun|Hisfun] //= Happ Ety.
by rewrite (HType_UIP _ _ Ety (erefl (dest_fun (type_of f)).2)).
Qed.


(** [SafeDenote] of [mk_comb f x], expressed via [applyFun] on the
    [SafeDenote] of [f] and of [x] directly -- the reusable replacement
    for unfolding [denote]'s own [TmComb] case by hand. *)
Lemma SafeDenote_comb F thy tv venv f x
    (Hisfun : is_fun (type_of f)) (Hdom : (dest_fun (type_of f)).1 = type_of x)
    (Hf : check_term thy f) (Hx : check_term thy x)
    (Hfx : check_term thy (mk_comb f x)) :
  eq_rect (type_of (mk_comb f x)) (interpType (frTyOp F) tv)
    (SafeDenote F thy tv venv (mk_comb f x) Hfx)
    (dest_fun (type_of f)).2 (type_of_mk_comb_isfun f x Hisfun)
  = applyFun F tv (type_of f) (type_of x) Hisfun Hdom
      (SafeDenote F thy tv venv f Hf) (SafeDenote F thy tv venv x Hx).
Proof.
rewrite /SafeDenote.
exact: (denote_comb F tv venv [::] (DEnvNil F tv) f x Hisfun Hdom
  (check_open_term_WellTypedShape thy f [::] Hf)
  (check_open_term_WellTypedShape thy x [::] Hx)
  (check_open_term_WellTypedShape thy (mk_comb f x) [::] Hfx)).
Qed.

(** [denoteProp] of [mk_eq l r] is, exactly, [SafeDenote l = SafeDenote r]
    (transported across [type_of l = type_of r], since the two sides
    need not share a literal [HType]) -- given a model interprets [NEq]
    as genuine equality ([HM], [ModelsTheory]'s own first clause). Every
    rule that builds or consumes a [mk_eq] proof obligation goes through
    this lemma rather than unfolding [denote] on [mk_eq]'s own three-deep
    [TmComb]/[TmConst] structure by hand. *)
Lemma SafeDenote_mk_eq F thy tv venv l r
    (Hl : check_term thy l) (Hr : check_term thy r) (Hlr : type_of l = type_of r)
    (Hbeq : is_bool (mk_eq l r))
    (HM : forall dom tv, frConst F NEq tv (mk_fun dom (mk_fun dom bool_ty)) =
            @eq (interpType (frTyOp F) tv dom))
    (Heq : check_term thy (mk_eq l r)) :
  denoteProp F thy tv venv (mk_eq l r) Heq Hbeq <->
  SafeDenote F thy tv venv l Hl =
    eq_rect (type_of r) (interpType (frTyOp F) tv) (SafeDenote F thy tv venv r Hr)
      (type_of l) (esym Hlr).
Proof.
rewrite /denoteProp /SafeDenote /mk_eq /mk_comb /= HM.
move: (check_open_term_WellTypedShape thy
  (TmComb (TmComb (mk_const NEq (mk_fun (type_of l) (mk_fun (type_of l) bool_ty))) l) r)
  [::] Heq) => [[_ [a3 [a4 b4]]] [a0 [a1 b1]]].
rewrite (HType_UIP _ _ b4 (erefl (type_of l))) (HType_UIP _ _ b1 Hlr).
rewrite (denote_irrel F tv venv [::] (DEnvNil F tv) l a3 (check_open_term_WellTypedShape thy l [::] Hl)).
rewrite (denote_irrel F tv venv [::] (DEnvNil F tv) r a0 (check_open_term_WellTypedShape thy r [::] Hr)).
rewrite (HType_UIP _ _ (eqP Hbeq) (erefl bool_ty)) /=.
rewrite (eq_rect_arrow_apply HType Prop (interpType (frTyOp F) tv) (type_of l) (type_of r)
  (@eq (interpType (frTyOp F) tv (type_of l))
     (denote F tv venv [::] (DEnvNil F tv) l (check_open_term_WellTypedShape thy l [::] Hl)))
  Hlr (denote F tv venv [::] (DEnvNil F tv) r (check_open_term_WellTypedShape thy r [::] Hr))).
by [].
Qed.

(** * Frame-swap invariance

    A theory extension that adds a brand-new constant [n] (via
    [new_constant]) needs a model [F'] that agrees with [F] everywhere
    except at [n] -- [denote]/[SafeDenote]/[denoteProp] on a [thy]-checked
    term never actually invoke [frConst] at a name the term does not
    itself mention, so they cannot tell [F] and [F'] apart as long as
    [n] does not occur in [thy] (which [new_constant]'s freshness check,
    [const_type thy n = None], guarantees for every already-checked
    term). Proved once, structurally, here; every conservativity proof
    that builds an [exists F', ...] extension reuses it rather than
    re-deriving it. *)
Section FrameAgree.
Variables (F : Frame)
  (frConst'' : forall (n : Name) (tv : Name -> {T : Type & T}) (ty : HType), interpType (frTyOp F) tv ty).

Definition frame_override := mkFrame (frTyOp F) (frTyOp_inhab F) (frTyOp_subst F) frConst''.

Fixpoint DEnv_cast tv env (d : DEnv F tv env) : DEnv frame_override tv env :=
  match d with
  | DEnvNil => DEnvNil frame_override tv
  | DEnvCons ty env0 v d0 => DEnvCons frame_override tv ty env0 v (DEnv_cast tv env0 d0)
  end.

Lemma dnth_cast tv env (d : DEnv F tv env) i (Hi : i < size env) :
  dnth frame_override tv env (DEnv_cast tv env d) i Hi = dnth F tv env d i Hi.
Proof.
by elim: d i Hi => [| ty0 env0 v0 d0 IHd] [|i0] Hi //=.
Qed.

Lemma denote_frame_agree (n : Name) thy
    (Hagree : forall n0 tv ty0, n0 <> n -> frConst'' n0 tv ty0 = frConst F n0 tv ty0) t :
  const_type thy n = None ->
  forall tv venv env (d : DEnv F tv env) (Hcheck : check_open_term thy t env) (Hwt : WellTypedShape t env),
  denote frame_override tv venv env (DEnv_cast tv env d) t Hwt = denote F tv venv env d t Hwt.
Proof.
move=> Hfresh.
elim: t => [v | i ty | n0 ty | f IHf x IHx | aty b IHb] tv venv env d Hcheck Hwt //=.
- move: Hwt => [Hlt Hnth].
  move: (dnth_cast tv env d i Hlt) => Hd.
  move: (dnth frame_override tv env (DEnv_cast tv env d) i Hlt) (dnth F tv env d i Hlt) Hd Hnth
    => v1 v2 -> Hnth.
  by [].
- move: Hcheck => /andP[_ Hc].
  case Egty: (const_type thy n0) Hc => [gty|] // Hc.
  have Hne : n0 <> n.
    by move=> Heq; move: Egty; rewrite Heq Hfresh.
  exact: (Hagree n0 tv ty Hne).
- move: Hcheck => /andP[/andP[Hcf Hcx] _].
  move: Hwt => [Hf [Hx [Hisfun Heq]]] /=.
  have IHf' := IHf tv venv env d Hcf Hf.
  have IHx' := IHx tv venv env d Hcx Hx.
  move: IHf' IHx'.
  move: (denote frame_override tv venv env (DEnv_cast tv env d) f Hf) (denote F tv venv env d f Hf)
    (denote frame_override tv venv env (DEnv_cast tv env d) x Hx) (denote F tv venv env d x Hx)
    => fv1 fv2 xv1 xv2 -> ->.
  by [].
- move: Hcheck => /andP[_ Hcb].
  apply: functional_extensionality => a.
  exact: (IHb tv venv (aty :: env) (DEnvCons F tv aty env a d) Hcb Hwt).
Qed.

Lemma SafeDenote_frame_agree (n : Name) thy
    (Hagree : forall n0 tv ty0, n0 <> n -> frConst'' n0 tv ty0 = frConst F n0 tv ty0)
    (Hfresh : const_type thy n = None) t tv venv (Hct : check_term thy t) :
  SafeDenote frame_override thy tv venv t Hct = SafeDenote F thy tv venv t Hct.
Proof.
rewrite /SafeDenote.
exact: (denote_frame_agree n thy Hagree t Hfresh tv venv [::] (DEnvNil F tv) Hct
  (check_open_term_WellTypedShape thy t [::] Hct)).
Qed.

Lemma denoteProp_frame_agree (n : Name) thy
    (Hagree : forall n0 tv ty0, n0 <> n -> frConst'' n0 tv ty0 = frConst F n0 tv ty0)
    (Hfresh : const_type thy n = None) t tv venv (Hct : check_term thy t) (Hbt : is_bool t) :
  denoteProp frame_override thy tv venv t Hct Hbt = denoteProp F thy tv venv t Hct Hbt.
Proof.
rewrite /denoteProp (SafeDenote_frame_agree n thy Hagree Hfresh t tv venv Hct) //.
Qed.

End FrameAgree.
