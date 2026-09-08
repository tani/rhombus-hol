(** The LCF kernel: the whole trust boundary of Rhombus/HOL.

    Transliteration of [rhombus-hol-kernel/rhombus/hol/kernel.rhm].  No
    attempt is made to reproduce Rhombus's [constructor ~none]/[authentic]
    module-privacy trick with a sealed Coq module: every lemma below is of
    the shape [WellFormed thy th -> ... -> WellFormed thy' th'] (or, in
    [Soundness.v], [Valid Frame thy th -> ...]); a hand-constructed [Thm]
    value that never went through a kernel function simply fails to
    satisfy the premise and cannot be fed into any proved lemma to derive
    a false conclusion. Rhombus's opacity defends against a *runtime*
    adversary calling into a compiled library; there is no analogous
    adversary inside a Coq proof script, so the defense has nothing to buy
    here -- this mirrors what [idris-hol-kernel/README.md] itself already
    concedes about its own [export]/private-constructor trick ("This
    guarantee is Idris-level only and does not survive compilation to
    Racket"). *)

From mathcomp Require Import all_boot finmap.
From HB Require Import structures.
From Stdlib Require Import ZArith.
From RocqHolKernel Require Import Names HType Term.

Open Scope fmap_scope.
Open Scope fset_scope.

Definition fset_all {T : choiceType} (p : T -> bool) (A : {fset T}) : bool :=
  all p (enum_fset A).

Lemma fset_allP {T : choiceType} (p : T -> bool) (A : {fset T}) :
  reflect (forall x, x \in A -> p x) (fset_all p A).
Proof.
apply: (iffP allP) => H x; move: (H x); by rewrite -/(x \in enum_fset A).
Qed.

(** * Lineage

    Every theory node has a unique identity, and carries the set of
    identities of all its ancestors (itself included).  A theorem is
    stamped with the node it was proved in.  A linear (root, generation)
    counter is NOT enough (see [kernel.rhm]'s own comment): immutable
    theories fork, and ancestor *sets* are what makes forked branches
    incomparable, which is what they are. *)
Record Stamp := mkStamp {
  st_id : Name;
  st_gen : nat;
  st_ancestors : {fset Name}
}.

(** True when a theorem stamped [a] is usable in a theory stamped [b]:
    [b]'s theory is [a]'s, or an extension of it. *)
Definition descends (a b : Stamp) : bool := st_id a \in st_ancestors b.

(** [kernel.rhm] mints a fresh identity via [Symbol.uninterned_from_string],
    an effect a pure total language has no built-in analogue for.  Rather
    than a bespoke "fuel"/state-threading scheme invented for this port
    alone, every stamp-minting function below takes the fresh identity as
    an explicit parameter, and the lemmas that need it fresh (so that
    forked branches come out incomparable) say so as an explicit
    hypothesis -- the proof obligation a real [gensym] discharges for
    free at runtime becomes a hypothesis the caller of the lemma
    discharges instead.  Stated here, once, rather than left implicit at
    every call site below. *)
Definition next_stamp (fresh : Name) (prev : Stamp) : Stamp :=
  mkStamp fresh (st_gen prev).+1 (fresh |` st_ancestors prev).

(** Two theorems may be combined only when their theories lie on one line
    of extension.  The result belongs to the later of the two. *)
Definition combine_stamps (a b : Stamp) : option Stamp :=
  if descends a b then Some b
  else if descends b a then Some a
  else None.

(** * Theorems

    The hypothesis field is readable; what is gated (in [kernel.rhm], by
    [constructor ~none]) is *construction* -- see the note above on why
    this port does not reproduce that gate. Terms are locally nameless,
    so structural equality is already equality up to alpha; storing
    [thm_hyps] as [{fset Term}] (rather than [kernel.rhm]'s duplicate-free
    insertion-order list) makes [Thm] equality literal Coq equality on
    the record, and makes the historical soundness bug this project
    actually hit -- comparing hypotheses by a non-injective-on-names
    ordering instead of by [==] -- structurally impossible to even state
    here (see [Names.v]). [Kernel.hyp_insert]/[hyp_union]/[hyp_remove]/
    [rehash_hyps] below reimplement [kernel.rhm]'s own list algorithm
    verbatim and prove it denotes correctly to this set semantics. *)
Record Thm := mkThm {
  thm_hyps : {fset Term};
  thm_concl : Term;
  thm_stamp : Stamp
}.

Definition hyps_of (th : Thm) : {fset Term} := thm_hyps th.
Definition concl_of (th : Thm) : Term := thm_concl th.
Definition stamp_of (th : Thm) : Stamp := thm_stamp th.

(** * Theories

    Closed off the same way as [Stamp] and [Thm] in [kernel.rhm], and for
    a soundness reason there, not just hygiene -- see [kernel.rhm]'s own
    comment on the attack a forgeable [Theory] would open.  That comment's
    premise (a runtime adversary holding a value that skipped the
    kernel's own construction) does not arise in a Coq proof script,
    for the same reason given above for [Thm]. *)
Record Theory := mkTheory {
  th_tyops : {fmap Name -> nat};
  th_consts : {fmap Name -> HType};
  th_axioms : seq Thm;
  th_defs : {fmap Name -> Thm};
  th_stamp : Stamp
}.

Definition type_arity (thy : Theory) (n : Name) : option nat := (th_tyops thy).[? n].
Definition const_type (thy : Theory) (n : Name) : option HType := (th_consts thy).[? n].
Definition axioms_of (thy : Theory) : seq Thm := th_axioms thy.
Definition definition_of (thy : Theory) (n : Name) : option Thm := (th_defs thy).[? n].

(** A rule that takes a theory must check that the theorem belongs to it. *)
Definition in_theory (thy : Theory) (th : Thm) : bool :=
  descends (thm_stamp th) (th_stamp thy).

Definition extend (thy : Theory) (fresh : Name)
    (tyops : {fmap Name -> nat}) (consts : {fmap Name -> HType})
    (axioms : seq Thm) (defs : {fmap Name -> Thm}) : Theory :=
  mkTheory tyops consts axioms defs (next_stamp fresh (th_stamp thy)).

(** * Well-formedness *)

Fixpoint check_type (thy : Theory) (t : HType) : bool :=
  match t with
  | HTyVar _ => true
  | HTyApp n args =>
      match type_arity thy n with
      | Some ar => (ar == size args) && all (check_type thy) args
      | None => false
      end
  end.

(** [env] holds the argument types of the enclosing binders, innermost
    first.  The [TmBVar] case's binder-type check is the actual
    soundness content of this function: without it,
    [TmAbs num (TmComb p (TmBVar 0 bool_ty))] would be accepted (it is
    locally closed, and both types are declared), its [type_of] would be
    [num -> bool] so it applies to a number, and beta-reducing it yields
    an ill-typed term inside a theorem.  [check_term_liar_rejected] below
    reproduces this exact attack from [tests/kernel.rhm]'s soundness
    regressions. *)
Fixpoint check_open_term (thy : Theory) (t : Term) (env : seq HType) : bool :=
  match t with
  | TmFVar v => check_type thy (fv_ty v)
  | TmBVar i ty => (i < size env) && (nth ty env i == ty) && check_type thy ty
  | TmConst n ty =>
      check_type thy ty &&
      match const_type thy n with
      | Some gty => match type_match gty ty [fmap] with Some _ => true | None => false end
      | None => false
      end
  | TmComb f x =>
      check_open_term thy f env && check_open_term thy x env &&
      let fty := type_of f in
      is_fun fty && ((dest_fun fty).1 == type_of x)
  | TmAbs aty b => check_type thy aty && check_open_term thy b (aty :: env)
  end.

Definition check_term (thy : Theory) (t : Term) : bool := check_open_term thy t [::].

Definition is_bool (t : Term) : bool := type_of t == bool_ty.

Definition check_prop (thy : Theory) (t : Term) : bool := check_term thy t && is_bool t.

(** * Equality *)

Definition mk_eq (l r : Term) : Term :=
  let ty := type_of l in
  mk_comb (mk_comb (mk_const NEq (mk_fun ty (mk_fun ty bool_ty))) l) r.

Definition dest_eq (t : Term) : option (Term * Term) :=
  match t with
  | TmComb (TmComb (TmConst n _) l) r => if n == NEq then Some (l, r) else None
  | _ => None
  end.

Definition is_eq (t : Term) : bool := dest_eq t != None.

Lemma dest_eq_mk_eq l r : dest_eq (mk_eq l r) = Some (l, r).
Proof. rewrite /dest_eq /mk_eq /mk_comb /=. by case: (@eqP _ NEq NEq) => // []. Qed.

(** * Well-formed theories

    Pins down the one theory-shaped fact every rule below implicitly
    leans on when it builds an equation: [NEq]'s generic type is exactly
    the one [initial_theory] declares, and [bool]/[fun] are declared with
    the arities [check_type] needs to accept [bool_ty]/[mk_fun].  Matches
    [idris-hol-kernel]'s own [WellFormedTheory]/[mkEqCheckSound] naming
    and role. *)
Definition WellFormedTheory (thy : Theory) : Prop :=
  type_arity thy NBool = Some 0 /\
  type_arity thy NFun = Some 2 /\
  const_type thy NEq = Some (mk_fun (HTyVar NAlpha) (mk_fun (HTyVar NAlpha) bool_ty)) /\
  st_id (th_stamp thy) \in st_ancestors (th_stamp thy).

Lemma check_typeE thy n args :
  check_type thy (HTyApp n args) =
    match type_arity thy n with
    | Some ar => (ar == size args) && all (check_type thy) args
    | None => false
    end.
Proof. by []. Qed.

Lemma check_type_bool_ty thy : WellFormedTheory thy -> check_type thy bool_ty.
Proof. move=> [Hb _]; by rewrite /bool_ty /mk_tyapp check_typeE Hb. Qed.

Lemma check_type_mk_fun thy a b :
  WellFormedTheory thy -> check_type thy a -> check_type thy b ->
  check_type thy (mk_fun a b).
Proof.
move=> [_ [Hf _]] Ha Hb.
by rewrite /mk_fun /mk_tyapp check_typeE Hf /= Ha Hb.
Qed.

Lemma is_fun_HTyApp fty : is_fun fty -> exists d r, fty = HTyApp NFun [:: d; r].
Proof.
case: fty => [n | n args] //=.
case: args => [|d [|r [|]]] //= /eqP ->.
by exists d, r.
Qed.

Lemma is_fun_check_type thy fty :
  WellFormedTheory thy -> check_type thy fty -> is_fun fty ->
  check_type thy (dest_fun fty).1 && check_type thy (dest_fun fty).2.
Proof.
move=> WFT Hct Hfun.
have [d [r Efty]] := is_fun_HTyApp fty Hfun.
move: Hct; rewrite Efty check_typeE => Hct.
case: WFT => [_ [Hfn _]]; rewrite Hfn in Hct.
move: Hct => /andP[_ /andP[Hd /andP[Hr _]]].
rewrite /dest_fun /=.
case: (@eqP _ NFun NFun) => [_ | Hne]; last by case: Hne.
by apply/andP; split.
Qed.

Lemma check_open_term_type_of thy t env :
  WellFormedTheory thy -> check_open_term thy t env -> check_type thy (type_of t).
Proof.
move=> WFT; elim: t env => [v | i ty | n ty | f IHf x IHx | aty b IHb] env //=.
- by move=> /andP[/andP[_ _] H].
- by move=> /andP[H _].
- move=> /andP[/andP[Hf Hx] /andP[Hisfun Hdom]].
  have Hfty := IHf env Hf.
  rewrite /= Hisfun /=.
  by have /andP[_ ->] := is_fun_check_type thy (type_of f) WFT Hfty Hisfun.
- move=> /andP[Haty Hb].
  have Hbty := IHb (aty :: env) Hb.
  case: WFT => [_ [Hfn _]].
  by rewrite /= Hfn /= Haty Hbty.
Qed.

Lemma check_term_type_of thy t :
  WellFormedTheory thy -> check_term thy t -> check_type thy (type_of t).
Proof. exact: check_open_term_type_of. Qed.

(** The whole match-generation instantiation [mk_eq]'s constant use needs:
    matching the generic type [NEq] is declared at ([HTyVar NAlpha ->
    HTyVar NAlpha -> bool]) against the concrete instance [mk_eq] builds
    it at always succeeds, binding [NAlpha] to the equated type. *)
Lemma type_match_alpha_gen ty :
  type_match (mk_fun (HTyVar NAlpha) (mk_fun (HTyVar NAlpha) bool_ty))
             (mk_fun ty (mk_fun ty bool_ty)) [fmap]
    = Some ([fmap].[NAlpha <- ty]).
Proof.
rewrite /mk_fun /mk_tyapp /type_match -/type_match /=.
rewrite fnd_fmap0 /=.
rewrite fnd_set.
case: (@eqP _ NAlpha NAlpha) => [_ | []] //=.
by case: (@eqP _ ty ty) => [_ | []] //=.
Qed.

Lemma mkEqCheckSound thy l r :
  WellFormedTheory thy -> check_term thy l -> check_term thy r ->
  type_of l = type_of r -> check_term thy (mk_eq l r).
Proof.
move=> WFT Hl Hr Heq.
have Hty := check_term_type_of thy l WFT Hl.
rewrite /check_term in Hl Hr.
rewrite /check_term /mk_eq /mk_comb.
case: WFT => [Hbool [Hfun [Hconst _]]].
rewrite /= Hl Hr Hfun Hbool Hty Hconst type_match_alpha_gen /= Heq.
by case: (@eqP _ (type_of r) (type_of r)) => [_ | []] //=.
Qed.

Lemma is_bool_mk_eq l r : is_bool (mk_eq l r).
Proof.
rewrite /is_bool /mk_eq /mk_comb /=.
by case: (@eqP _ bool_ty bool_ty) => [_ | []] //=.
Qed.

(** * Well-formed theorems

    Every rule below is of the shape [WellFormedThm thy th -> ... ->
    WellFormedThm thy th']; see the top of this file for why the rules
    themselves need no sealing to make this trust boundary hold. *)
Definition WellFormedThm (thy : Theory) (th : Thm) : Prop :=
  check_term thy (thm_concl th) /\
  (forall h, h \in thm_hyps th -> check_term thy h) /\
  is_bool (thm_concl th) /\
  (forall h, h \in thm_hyps th -> is_bool h) /\
  descends (thm_stamp th) (th_stamp thy).

(** * The ten primitive rules

    HOL Light's set, unchanged in content.  The locally nameless
    representation only simplifies the side conditions: no alpha
    comparisons, and [BETA] is not restricted to the trivial redex.  Each
    is total, [option]-returning where [kernel.rhm] errors (matching the
    plan's general pattern), and each comes with the well-formedness
    preservation theorem named to match [idris-hol-kernel]'s own
    (`reflWellFormed`, `transWellFormed`, ...). *)

(** [|- t = t] *)
Definition REFL (thy : Theory) (t : Term) : option Thm :=
  if check_term thy t then Some (mkThm fset0 (mk_eq t t) (th_stamp thy)) else None.

Lemma reflWellFormed thy t th' :
  WellFormedTheory thy -> REFL thy t = Some th' -> WellFormedThm thy th'.
Proof.
rewrite /REFL => WFT.
case Hct: (check_term thy t) => //; move=> [<-].
have Hcc := mkEqCheckSound thy t t WFT Hct Hct erefl.
split; first exact: Hcc.
split; first by move=> h; rewrite in_fset0.
split; first exact: is_bool_mk_eq.
split; first by move=> h; rewrite in_fset0.
by case: WFT => [_ [_ [_ Hself]]].
Qed.

Lemma type_match_alpha_gen_inv ty m :
  type_match (mk_fun (HTyVar NAlpha) (mk_fun (HTyVar NAlpha) bool_ty)) ty [fmap] = Some m ->
  exists dom, ty = mk_fun dom (mk_fun dom bool_ty).
Proof.
rewrite /mk_fun /mk_tyapp /type_match -/type_match /=.
case: ty => [n | n args] //=.
case: (@eqP _ NFun n) => [<- | _] //=.
case: args => [|d [|r2 [|]]] //=.
rewrite fnd_fmap0 /=.
case: r2 => [n2 | n2 args2] //=.
case: (@eqP _ NFun n2) => [<- | _] //=.
case: args2 => [|d2 [|r3 [|]]] //=.
rewrite fnd_set.
case: (@eqP _ NAlpha NAlpha) => [_ | []] //=.
case: (@eqP _ d d2) => [<- | _] //=.
case: r3 => [n3 | n3 args3] //=.
case: (@eqP _ NBool n3) => [<- | _] //=.
case: args3 => [|] //= _.
by exists d.
Qed.

Lemma dest_eq_inv t l r :
  dest_eq t = Some (l, r) -> exists ty, t = TmComb (TmComb (TmConst NEq ty) l) r.
Proof.
rewrite /dest_eq.
case: t => [v | i ty | n ty | f x | aty b] //.
case: f => [v | i ty2 | n2 ty2 | f2 x2 | aty2 b2] //.
case: f2 => [v | i ty3 | n3 ty3 | f3 x3 | aty3 b3] //.
case: (@eqP _ n3 NEq) => [-> | _] //= [<- <-].
by exists ty3.
Qed.

Lemma check_term_eq_inv thy ty l r :
  WellFormedTheory thy -> check_term thy (TmComb (TmComb (TmConst NEq ty) l) r) ->
  check_term thy l /\ check_term thy r /\ type_of l = type_of r.
Proof.
move=> WFT.
rewrite /check_term /=.
move=> /andP[/andP[/andP[/andP[HA Hl] HC] Hr] /andP[_ Hdom]].
split; first exact: Hl.
split; first exact: Hr.
move: HA => /andP[_ Hmatch].
case: WFT => [_ [_ [Hconst _]]].
move: Hmatch; rewrite Hconst.
case Hm: (type_match _ ty [fmap]) => [m|] //= _.
have [dom Ety] := type_match_alpha_gen_inv ty m Hm.
move: HC Hdom; rewrite Ety /dest_fun /=.
by move=> /eqP <- /eqP.
Qed.

Lemma check_term_dest_eq_inv thy t l r :
  WellFormedTheory thy -> check_term thy t -> dest_eq t = Some (l, r) ->
  check_term thy l /\ check_term thy r /\ type_of l = type_of r.
Proof.
move=> WFT Hct Hde.
have [ty Et] := dest_eq_inv t l r Hde.
rewrite Et in Hct.
exact: check_term_eq_inv thy ty l r WFT Hct.
Qed.

Lemma fset_all_union (T : choiceType) (p : T -> bool) (A B : {fset T}) :
  (forall x, x \in A -> p x) -> (forall x, x \in B -> p x) ->
  forall x, x \in (A `|` B) -> p x.
Proof. move=> HA HB x; rewrite in_fsetU => /orP[]; [exact: HA | exact: HB]. Qed.

Lemma fset_all_diff (T : choiceType) (p : T -> bool) (A B : {fset T}) :
  (forall x, x \in A -> p x) -> forall x, x \in (A `\` B) -> p x.
Proof. move=> HA x; rewrite in_fsetD => /andP[_ Hx]; exact: HA. Qed.

Lemma fset_all_image (T1 T2 : choiceType) (f : T1 -> T2) (p : T2 -> bool)
    (A : {fset T1}) :
  (forall x, x \in A -> p (f x)) -> forall y, y \in (f @` A) -> p y.
Proof. move=> HA y /imfsetP [x xA ->]; exact: HA. Qed.

Lemma combine_stamps_desc thy sa sb st :
  descends sa (th_stamp thy) -> descends sb (th_stamp thy) ->
  combine_stamps sa sb = Some st -> descends st (th_stamp thy).
Proof.
move=> Hda Hdb; rewrite /combine_stamps.
case: ifP => [_ [<-] | _] //.
case: ifP => [_ [<-] | _] //.
Qed.

(** [|- l = m]   [|- m = r]
    -------------------
         [|- l = r] *)
Definition TRANS (a b : Thm) : option Thm :=
  match dest_eq (thm_concl a), dest_eq (thm_concl b) with
  | Some (l, m1), Some (m2, r) =>
      if m1 == m2 then
        match combine_stamps (thm_stamp a) (thm_stamp b) with
        | Some st => Some (mkThm (thm_hyps a `|` thm_hyps b) (mk_eq l r) st)
        | None => None
        end
      else None
  | _, _ => None
  end.

Lemma transWellFormed thy a b th' :
  WellFormedTheory thy -> WellFormedThm thy a -> WellFormedThm thy b ->
  TRANS a b = Some th' -> WellFormedThm thy th'.
Proof.
move=> WFT [Hca [Hha [_ [Hbha Hda]]]] [Hcb [Hhb [_ [Hbhb Hdb]]]].
rewrite /TRANS.
case Ea: (dest_eq (thm_concl a)) => [[l m1]|] //.
case Eb: (dest_eq (thm_concl b)) => [[m2 r]|] //.
case: (@eqP _ m1 m2) => [Em | _] //=.
case Ecs: (combine_stamps (thm_stamp a) (thm_stamp b)) => [st | ] //.
move=> [<-].
have [Hl _] := check_term_dest_eq_inv thy (thm_concl a) l m1 WFT Hca Ea.
have [_ [Hr _]] := check_term_dest_eq_inv thy (thm_concl b) m2 r WFT Hcb Eb.
have [_ [_ Etm1]] := check_term_dest_eq_inv thy (thm_concl a) l m1 WFT Hca Ea.
have [_ [_ Etm2]] := check_term_dest_eq_inv thy (thm_concl b) m2 r WFT Hcb Eb.
have Etlr : type_of l = type_of r by rewrite Etm1 Em Etm2.
split; first exact: mkEqCheckSound thy l r WFT Hl Hr Etlr.
split.
  by apply: fset_all_union Hha Hhb.
split; first exact: is_bool_mk_eq.
split.
  by apply: fset_all_union Hbha Hbhb.
exact: combine_stamps_desc thy (thm_stamp a) (thm_stamp b) st Hda Hdb Ecs.
Qed.

(** [|- f = g]   [|- x = y]
    -------------------
       [|- f x = g y] *)
Definition MK_COMB (fth xth : Thm) : option Thm :=
  match dest_eq (thm_concl fth), dest_eq (thm_concl xth) with
  | Some (f, g), Some (x, y) =>
      let fty := type_of f in
      if is_fun fty && ((dest_fun fty).1 == type_of x) then
        match combine_stamps (thm_stamp fth) (thm_stamp xth) with
        | Some st =>
            Some (mkThm (thm_hyps fth `|` thm_hyps xth)
                        (mk_eq (mk_comb f x) (mk_comb g y)) st)
        | None => None
        end
      else None
  | _, _ => None
  end.

Lemma mkCombWellFormed thy fth xth th' :
  WellFormedTheory thy -> WellFormedThm thy fth -> WellFormedThm thy xth ->
  MK_COMB fth xth = Some th' -> WellFormedThm thy th'.
Proof.
move=> WFT [Hcf [Hhf [_ [Hbhf Hdf]]]] [Hcx [Hhx [_ [Hbhx Hdx]]]].
rewrite /MK_COMB.
case Ef: (dest_eq (thm_concl fth)) => [[f g]|] //.
case Ex: (dest_eq (thm_concl xth)) => [[x y]|] //.
have [Hf [Hg Efg]] := check_term_dest_eq_inv thy (thm_concl fth) f g WFT Hcf Ef.
have [Hx [Hy Exy]] := check_term_dest_eq_inv thy (thm_concl xth) x y WFT Hcx Ex.
case: ifP => [/andP[Hisfun Hdom] | //].
case Ecs: (combine_stamps (thm_stamp fth) (thm_stamp xth)) => [st | ] //.
move=> [<-].
rewrite /check_term in Hf Hg Hx Hy.
have Hcfx : check_term thy (mk_comb f x).
  by rewrite /check_term /mk_comb /= Hf Hx Hisfun Hdom.
have Hcgy : check_term thy (mk_comb g y).
  by rewrite /check_term /mk_comb /= Hg Hy -Efg -Exy Hisfun Hdom.
have Etxy : type_of (mk_comb f x) = type_of (mk_comb g y).
  by rewrite /mk_comb /= Hisfun -Efg Hisfun.
split; first exact: mkEqCheckSound thy (mk_comb f x) (mk_comb g y) WFT Hcfx Hcgy Etxy.
split.
  by apply: fset_all_union Hhf Hhx.
split; first exact: is_bool_mk_eq.
split.
  by apply: fset_all_union Hbhf Hbhx.
exact: combine_stamps_desc thy (thm_stamp fth) (thm_stamp xth) st Hdf Hdx Ecs.
Qed.

Lemma type_of_abstract_at j v t : type_of (abstract_at j v t) = type_of t.
Proof.
elim: t j => [w | i ty | n ty | f IHf x IHx | aty b IHb] j //=.
- by case: (@eqP _ w v) => [-> | _].
- by rewrite IHf.
- by rewrite IHb.
Qed.

(** Abstracting a free variable [v] of a well-checked type over a term
    already checked in [env] gives a term checked in [env] extended with
    [v]'s type as the new innermost binder -- the structural fact
    [mk_abs]'s own well-formedness rests on. *)
Lemma abstract_at_check thy v env t :
  check_type thy (fv_ty v) ->
  check_open_term thy t env ->
  check_open_term thy (abstract_at (size env) v t) (rcons env (fv_ty v)).
Proof.
move=> Hv.
elim: t env => [w | i ty | n ty | f IHf x IHx | aty b IHb] env /=.
- case: (@eqP _ w v) => [-> | _] /=.
  + move=> _.
    rewrite size_rcons ltnSn nth_rcons ltnn if_same.
    case: (@eqP _ (fv_ty v) (fv_ty v)) => [_ | []] //=.
  + by [].
- move=> /andP[/andP[Hlt Heq] Hct].
  rewrite size_rcons.
  have Hlt2 : i < (size env).+1 by exact: leq_trans Hlt (leqnSn _).
  rewrite Hlt2 nth_rcons Hlt Heq Hct //.
- by [].
- move=> /andP[/andP[Hf Hx] Hdom].
  rewrite (IHf env Hf) (IHx env Hx) !type_of_abstract_at Hdom //.
- move=> /andP[Haty Hb].
  rewrite Haty /=.
  have := IHb (aty :: env) Hb.
  by rewrite rcons_cons.
Qed.

Lemma check_term_mk_abs thy v body :
  check_type thy (fv_ty v) -> check_term thy body ->
  check_term thy (mk_abs v body).
Proof.
move=> Hv Hb.
by rewrite /check_term /mk_abs /= Hv (abstract_at_check thy v [::] body Hv Hb).
Qed.

(**        [|- l = r]          ([v] not free in the hypotheses)
    -------------------------
     [|- (\v. l) = (\v. r)]

    Takes the theory so that the abstracted variable's type is checked:
    without that, an undeclared type constructor could enter through the
    binder. *)
Definition ABS (thy : Theory) (v : FVar) (th : Thm) : option Thm :=
  if descends (thm_stamp th) (th_stamp thy) && check_type thy (fv_ty v) &&
     fset_all (fun h => ~~ vfree_in v h) (thm_hyps th)
  then
    match dest_eq (thm_concl th) with
    | Some (l, r) =>
        Some (mkThm (thm_hyps th) (mk_eq (mk_abs v l) (mk_abs v r)) (th_stamp thy))
    | None => None
    end
  else None.

Lemma absWellFormed thy v th th' :
  WellFormedTheory thy -> WellFormedThm thy th ->
  ABS thy v th = Some th' -> WellFormedThm thy th'.
Proof.
move=> WFT [Hct [Hh [_ [Hbh _]]]].
rewrite /ABS.
case: ifP => [/andP[/andP[_ Hv] _] | //].
case Ee: (dest_eq (thm_concl th)) => [[l r]|] //.
move=> [<-].
have [Hl [Hr Elr]] := check_term_dest_eq_inv thy (thm_concl th) l r WFT Hct Ee.
have Hcl := check_term_mk_abs thy v l Hv Hl.
have Hcr := check_term_mk_abs thy v r Hv Hr.
have Etlr : type_of (mk_abs v l) = type_of (mk_abs v r).
  by rewrite /mk_abs /= !type_of_abstract_at Elr.
split; first exact: mkEqCheckSound thy (mk_abs v l) (mk_abs v r) WFT Hcl Hcr Etlr.
split; first exact: Hh.
split; first exact: is_bool_mk_eq.
split; first exact: Hbh.
by case: WFT => [_ [_ [_ Hself]]].
Qed.

(** * Subject reduction for substitution

    The full story [BETA] rests on: a closed term stays well-typed at
    any binder depth ([check_open_term_weaken]/[check_open_term_closed_any]),
    shifting a term already closed at [cutoff] is the identity
    ([shift_check_id]), [type_of] is invariant under [shift], and
    substituting a closed, correctly-typed [arg] for the outermost bound
    variable of a term checked one binder deeper preserves both its type
    and its well-formedness ([subst_at_type_check]), specialising to
    [subst_bvar] -- the whole of what [BETA] performs. *)
Lemma check_open_term_weaken thy t env extra :
  check_open_term thy t env -> check_open_term thy t (env ++ extra).
Proof.
elim: t env => [w | i ty | n ty | f IHf x IHx | aty b IHb] env //=.
- move=> /andP[/andP[Hlt Heq] Hct].
  rewrite nth_cat Hlt size_cat.
  by rewrite (leq_trans Hlt (leq_addr _ _)) Heq Hct.
- move=> /andP[/andP[Hf Hx] Hdom].
  by rewrite (IHf env Hf) (IHx env Hx) Hdom.
- move=> /andP[Haty Hb].
  by rewrite Haty (IHb (aty :: env) Hb).
Qed.

Lemma check_open_term_closed_any thy t env :
  check_open_term thy t [::] -> check_open_term thy t env.
Proof. by move=> H; have := check_open_term_weaken thy t [::] env H. Qed.

Lemma shift_check_id thy d cutoff t env :
  size env <= cutoff -> check_open_term thy t env -> shift d cutoff t = t.
Proof.
elim: t cutoff env => [w | i ty | n ty | f IHf x IHx | aty b IHb] cutoff env //=.
- move=> Hle /andP[/andP[Hlt _] _].
  have Hic : i < cutoff by exact: leq_trans Hlt Hle.
  by rewrite Hic.
- move=> Hle /andP[/andP[Hf Hx] _].
  by rewrite (IHf cutoff env Hle Hf) (IHx cutoff env Hle Hx).
- move=> Hle /andP[_ Hb].
  have Hle2 : (size env).+1 <= cutoff.+1 by rewrite ltnS.
  by rewrite (IHb cutoff.+1 (aty :: env) Hle2 Hb).
Qed.

Lemma type_of_shift d cutoff t : type_of (shift d cutoff t) = type_of t.
Proof.
elim: t cutoff => [w | i ty | n ty | f IHf x IHx | aty b IHb] cutoff //=.
- by case: (i < cutoff).
- by rewrite IHf.
- by rewrite IHb.
Qed.

Lemma subst_at_type_check thy arg extra body :
  check_open_term thy arg [::] ->
  check_open_term thy body (extra ++ [:: type_of arg]) ->
  type_of (subst_at (size extra) arg body) = type_of body /\
  check_open_term thy (subst_at (size extra) arg body) extra.
Proof.
move=> Harg.
elim: body extra => [w | i ty | n ty | f IHf x IHx | aty b IHb] extra /=.
- by [].
- case: (@eqP _ i (size extra)) => [-> | Hne] /=.
  + move=> /andP[/andP[_ Heq] _].
    rewrite nth_cat ltnn subnn /= in Heq.
    move: Heq => /eqP <-.
    split.
    * by rewrite type_of_shift.
    * rewrite (shift_check_id thy (Z.of_nat (size extra)) 0 arg [::] (leqnn 0) Harg).
      exact: check_open_term_closed_any.
  + move=> /andP[/andP[Hlt Heq] Hct].
    have Hlt2 : i < size extra.
      move: Hlt; rewrite size_cat addn1 ltnS leq_eqVlt => /orP[/eqP Heqi | //].
      by case: (Hne Heqi).
    rewrite nth_cat Hlt2 in Heq.
    by split; last by rewrite Hlt2 Heq Hct.
- by [].
- move=> /andP[/andP[Hf Hx] Hdom].
  have [Etf Hcf] := IHf extra Hf.
  have [Etx Hcx] := IHx extra Hx.
  split.
  + by rewrite /= Etf.
  + rewrite /=; apply/andP; split.
    * by apply/andP; split.
    * by rewrite Etf Etx.
- move=> /andP[Haty Hb].
  have [Etb Hcb] := IHb (aty :: extra) Hb.
  split.
  + by rewrite /= Etb.
  + by rewrite /= Haty Hcb.
Qed.

Lemma subst_bvar_check thy arg body :
  check_open_term thy arg [::] ->
  check_open_term thy body [:: type_of arg] ->
  check_open_term thy (subst_bvar arg body) [::].
Proof.
move=> Harg Hbody.
have [_ Hc] := subst_at_type_check thy arg [::] body Harg Hbody.
rewrite /subst_bvar (shift_check_id thy (-1)%Z 0 (subst_at 0 arg body) [::] (leqnn 0) Hc).
exact: Hc.
Qed.

(** [|- (\v. body) arg = body[arg]]

    Any redex, not just the trivial one: under a locally nameless
    representation [subst_bvar] cannot capture, so the general case
    needs no renaming and is exactly as primitive as the trivial one. *)
Definition BETA (thy : Theory) (t : Term) : option Thm :=
  if check_term thy t then
    match t with
    | TmComb (TmAbs _ body) arg =>
        Some (mkThm fset0 (mk_eq t (subst_bvar arg body)) (th_stamp thy))
    | _ => None
    end
  else None.

Lemma betaWellFormed thy t th' :
  WellFormedTheory thy -> BETA thy t = Some th' -> WellFormedThm thy th'.
Proof.
move=> WFT.
rewrite /BETA.
case: ifP => [Hct | //].
case: t Hct => [w | i ty | n ty | f x | aty body] Hct //.
case: f Hct => [w | i ty | n ty | f2 x2 | aty2 body] Hct //.
move=> [<-].
move: Hct; rewrite /check_term /= => /andP[/andP[/andP[Haty Hbody] Hx] Hxfun].
have Exty : aty2 = type_of x := elimT eqP Hxfun.
have Hbody' : check_open_term thy body [:: type_of x] by rewrite -Exty.
have Hres := subst_bvar_check thy x body Hx Hbody'.
have Etr : type_of (TmComb (TmAbs aty2 body) x) = type_of (subst_bvar x body).
  have [Etb _] := subst_at_type_check thy x [::] body Hx Hbody'.
  rewrite /= in Etb.
  by rewrite /= /subst_bvar type_of_shift Etb.
have Hct2 : check_term thy (TmComb (TmAbs aty2 body) x).
  by rewrite /check_term /= Haty Hbody Hx Hxfun.
split.
  exact: mkEqCheckSound thy (TmComb (TmAbs aty2 body) x) (subst_bvar x body)
                        WFT Hct2 Hres Etr.
split; first by move=> h; rewrite in_fset0.
split; first exact: is_bool_mk_eq.
split; first by move=> h; rewrite in_fset0.
by case: WFT => [_ [_ [_ Hself]]].
Qed.

(** [p |- p] *)
Definition ASSUME (thy : Theory) (p : Term) : option Thm :=
  if check_term thy p && is_bool p then Some (mkThm [fset p] p (th_stamp thy))
  else None.

Lemma assumeWellFormed thy p th' :
  WellFormedTheory thy -> ASSUME thy p = Some th' -> WellFormedThm thy th'.
Proof.
move=> WFT; rewrite /ASSUME.
case: ifP => [/andP[Hct Hbool] | //].
move=> [<-].
split; first exact: Hct.
split; first by move=> h; rewrite in_fset1 => /eqP ->.
split; first exact: Hbool.
split; first by move=> h; rewrite in_fset1 => /eqP ->.
by case: WFT => [_ [_ [_ Hself]]].
Qed.

(** [|- p = q]   [|- p]
    ---------------
         [|- q] *)
Definition EQ_MP (eqth th : Thm) : option Thm :=
  match dest_eq (thm_concl eqth) with
  | Some (p, q) =>
      if p == thm_concl th then
        match combine_stamps (thm_stamp eqth) (thm_stamp th) with
        | Some st => Some (mkThm (thm_hyps eqth `|` thm_hyps th) q st)
        | None => None
        end
      else None
  | None => None
  end.

Lemma eqMpWellFormed thy eqth th th' :
  WellFormedTheory thy -> WellFormedThm thy eqth -> WellFormedThm thy th ->
  EQ_MP eqth th = Some th' -> WellFormedThm thy th'.
Proof.
move=> WFT [Hceq [Hheq [_ [Hbheq Hdeq]]]] [Hct [Hht [Hbt [Hbht Hdt]]]].
rewrite /EQ_MP.
case Ee: (dest_eq (thm_concl eqth)) => [[p q]|] //.
case: (@eqP _ p (thm_concl th)) => [Epq | //] /=.
case Ecs: (combine_stamps (thm_stamp eqth) (thm_stamp th)) => [st|] //.
move=> [<-].
have [Hp [Hq Etpq]] := check_term_dest_eq_inv thy (thm_concl eqth) p q WFT Hceq Ee.
have Ebq : is_bool q by rewrite /is_bool -Etpq Epq; exact: Hbt.
split; first exact: Hq.
split; first by apply: fset_all_union Hheq Hht.
split; first exact: Ebq.
split; first by apply: fset_all_union Hbheq Hbht.
exact: combine_stamps_desc thy (thm_stamp eqth) (thm_stamp th) st Hdeq Hdt Ecs.
Qed.

(** [A |- p]   [B |- q]
    ---------------------------------
    [(A - q) u (B - p) |- p = q] *)
Definition DEDUCT_ANTISYM_RULE (a b : Thm) : option Thm :=
  match combine_stamps (thm_stamp a) (thm_stamp b) with
  | Some st =>
      Some (mkThm ((thm_hyps a `\` [fset thm_concl b]) `|` (thm_hyps b `\` [fset thm_concl a]))
                  (mk_eq (thm_concl a) (thm_concl b)) st)
  | None => None
  end.

Lemma deductAntisymWellFormed thy a b th' :
  WellFormedTheory thy -> WellFormedThm thy a -> WellFormedThm thy b ->
  DEDUCT_ANTISYM_RULE a b = Some th' -> WellFormedThm thy th'.
Proof.
move=> WFT [Hca [Hha [Hba [Hbha Hda]]]] [Hcb [Hhb [Hbb [Hbhb Hdb]]]].
rewrite /DEDUCT_ANTISYM_RULE.
case Ecs: (combine_stamps (thm_stamp a) (thm_stamp b)) => [st|] //.
move=> [<-].
have Etab : type_of (thm_concl a) = type_of (thm_concl b).
  by move: Hba Hbb; rewrite /is_bool => /eqP -> /eqP ->.
split; first exact: mkEqCheckSound thy (thm_concl a) (thm_concl b) WFT Hca Hcb Etab.
split.
  apply: fset_all_union.
  - exact: fset_all_diff Hha.
  - exact: fset_all_diff Hhb.
split; first exact: is_bool_mk_eq.
split.
  apply: fset_all_union.
  - exact: fset_all_diff Hbha.
  - exact: fset_all_diff Hbhb.
exact: combine_stamps_desc thy (thm_stamp a) (thm_stamp b) st Hda Hdb Ecs.
Qed.

(** * Subject reduction for free-variable instantiation *)

Lemma inst_fvar_lookup_inv theta w depth rep' :
  inst_fvar_lookup theta w depth = Some rep' ->
  exists rep, (rep, w) \in theta /\
    rep' = (if depth == 0 then rep else shift (Z.of_nat depth) 0 rep).
Proof.
elim: theta => [| [rep x] rest IH] //=.
case: (@eqP _ x w) => [-> | Hne].
- move=> [<-].
  exists rep; split=> //.
  by rewrite in_cons eqxx.
- move=> /IH [rep0 [Hin ->]].
  exists rep0; split=> //.
  by rewrite in_cons Hin orbT.
Qed.

(** Instantiating free variables preserves type and well-formedness, given
    every replacement in [theta] is itself closed and matches the type of
    the variable it replaces -- exactly [INST]'s own check. *)
Lemma inst_fvar_check thy theta env t :
  (forall rep v, (rep, v) \in theta ->
     check_open_term thy rep [::] /\ type_of rep = fv_ty v) ->
  check_open_term thy t env ->
  type_of (inst_fvar_go theta t (size env)) = type_of t /\
  check_open_term thy (inst_fvar_go theta t (size env)) env.
Proof.
move=> Htheta.
elim: t env => [w | i ty | n ty | f IHf x IHx | aty b IHb] env /=.
- case E: (inst_fvar_lookup theta w (size env)) => [rep'|] //=.
  move=> _.
  have [rep [Hin Erep']] := inst_fvar_lookup_inv theta w (size env) rep' E.
  have [Hrep Etrep] := Htheta rep w Hin.
  have Erep : rep' = rep.
    rewrite Erep'; case: (size env == 0) => //.
    exact: shift_check_id thy (Z.of_nat (size env)) 0 rep [::] (leqnn 0) Hrep.
  rewrite Erep.
  split; first exact: Etrep.
  exact: check_open_term_closed_any.
- by [].
- by [].
- move=> /andP[/andP[Hf Hx] Hdom].
  have [Etf Hcf] := IHf env Hf.
  have [Etx Hcx] := IHx env Hx.
  split.
  + by rewrite /= Etf.
  + rewrite /=; apply/andP; split.
    * by apply/andP; split.
    * by rewrite Etf Etx.
- move=> /andP[Haty Hb].
  have [Etb Hcb] := IHb (aty :: env) Hb.
  split.
  + by rewrite /= Etb.
  + by rewrite /= Haty Hcb.
Qed.

(** Instantiate free variables.  [theta] is a list of [(replacement,
    variable)] pairs.  The replacements are checked against the theory:
    this is the point at which an undeclared constant could otherwise
    sneak in. *)
Definition INST (thy : Theory) (theta : seq (Term * FVar)) (th : Thm) : option Thm :=
  if descends (thm_stamp th) (th_stamp thy) &&
     all (fun p => check_term thy p.1 && (type_of p.1 == fv_ty p.2)) theta
  then Some (mkThm (inst_fvar theta @` (thm_hyps th))
                   (inst_fvar theta (thm_concl th)) (th_stamp thy))
  else None.

Lemma instWellFormed thy theta th th' :
  WellFormedTheory thy -> WellFormedThm thy th ->
  INST thy theta th = Some th' -> WellFormedThm thy th'.
Proof.
move=> WFT [Hct [Hht [Hbt [Hbht Hdt]]]].
rewrite /INST.
case: ifP => [/andP[_ Hall] | //].
move=> [<-].
have Htheta : forall rep v, (rep, v) \in theta ->
    check_open_term thy rep [::] /\ type_of rep = fv_ty v.
  move=> rep v Hin.
  move: Hall => /allP /(_ (rep, v) Hin) /= /andP[Hc Ht].
  by split; [exact: Hc | exact/eqP].
have Hconcl : check_term thy (inst_fvar theta (thm_concl th)).
  by have [_ Hc] := inst_fvar_check thy theta [::] (thm_concl th) Htheta Hct.
have Etconcl : type_of (inst_fvar theta (thm_concl th)) = type_of (thm_concl th).
  by have [Et _] := inst_fvar_check thy theta [::] (thm_concl th) Htheta Hct.
split; first exact: Hconcl.
split.
  apply: fset_all_image => h Hin.
  by have [_ Hc] := inst_fvar_check thy theta [::] h Htheta (Hht h Hin).
split; first by move: Etconcl; rewrite /is_bool => ->.
split.
  apply: fset_all_image => h Hin.
  have [Et _] := inst_fvar_check thy theta [::] h Htheta (Hht h Hin).
  by move: (Hbht h Hin); rewrite /is_bool Et.
by case: WFT => [_ [_ [_ Hself]]].
Qed.

(** * Type instantiation preserves well-formedness

    [INST_TYPE] substitutes type variables throughout a term via
    [inst_type]; unlike [INST]'s free-variable substitution, this needs
    no capture-avoidance machinery at all -- type variables are not a
    binding construct in this locally-nameless representation, they are
    just names threaded structurally through [HType], so [type_subst]
    is exactly the substitution [inst_type] needs at every leaf. *)
Lemma check_type_subst thy (tyin : {fmap Name -> HType}) ty :
  (forall n t, tyin.[? n] = Some t -> check_type thy t) ->
  check_type thy ty -> check_type thy (type_subst tyin ty).
Proof.
move=> Htyin.
elim/HType_rect: ty => [n | n args IH] //=.
- case E: (tyin.[? n]) => [t|] //=.
  by move=> _; exact: Htyin E.
- case Har: (type_arity thy n) => [ar|] //= /andP[Hsz Hall].
  rewrite size_map Hsz {Hsz} /=.
  move: Hall.
  elim: args IH => [| a args' IHa] //= [Ha Hargs] /andP[Ha' Hargs'].
  by rewrite (Ha Ha') (IHa Hargs Hargs').
Qed.

Lemma is_fun_subst tyin ty : is_fun ty -> is_fun (type_subst tyin ty).
Proof. by case: ty => [n | n [|d [|r [|]]]]. Qed.

Lemma dest_fun_subst tyin ty : is_fun ty ->
  dest_fun (type_subst tyin ty) =
  (type_subst tyin (dest_fun ty).1, type_subst tyin (dest_fun ty).2).
Proof.
case: ty => [n | n [|d [|r [|]]]] //=.
by case: (@eqP _ n NFun) => //= ->.
Qed.

(** The combined statement -- well-typedness *and* the [type_of]
    computation both commute with [inst_type]/[type_subst] -- has to be
    proved together: the [TmComb] case's well-typedness half needs to
    know [type_of] of the (already-instantiated) function subterm to
    re-derive [is_fun], which is exactly the second half applied to that
    subterm. *)
Lemma check_open_term_inst_type thy (tyin : {fmap Name -> HType}) t env :
  (forall n ty, tyin.[? n] = Some ty -> check_type thy ty) ->
  check_open_term thy t env ->
  check_open_term thy (inst_type tyin t) [seq type_subst tyin i | i <- env] /\
  type_of (inst_type tyin t) = type_subst tyin (type_of t).
Proof.
move=> Htyin.
elim: t env => [v | i ty | n ty | f IHf x IHx | aty b IHb] env //=.
- by move=> Hct; split=> //; exact: check_type_subst.
- move=> /andP[/andP[Hlt Heq] Hct].
  rewrite size_map Hlt /=.
  have -> : nth (type_subst tyin ty) [seq type_subst tyin i | i <- env] i =
            type_subst tyin (nth ty env i) by rewrite (nth_map ty).
  by rewrite (eqP Heq) eqxx (check_type_subst thy tyin ty Htyin Hct).
- move=> /andP[Hct Hconst].
  split; last by [].
  rewrite (check_type_subst thy tyin ty Htyin Hct) /=.
  move: Hconst; case Hgty: (const_type thy n) => [gty|] //.
  case Hm: (type_match gty ty [fmap]) => [m2|] //= _.
  have Hrel0 : forall n0, ([fmap] : {fmap Name -> HType}).[? n0] =
      omap (type_subst tyin) (([fmap] : {fmap Name -> HType}).[? n0]).
    by move=> n0; rewrite !fnd_fmap0.
  have [m' [Em' _]] := type_match_subst_isSome tyin gty ty [fmap] [fmap] m2
    Hrel0 Hm.
  by rewrite Em'.
- move=> /andP[/andP[Hf Hx] Hdom].
  have [Hf' Ef] := IHf env Hf.
  have [Hx' Ex] := IHx env Hx.
  split.
  + rewrite Hf' Hx' /= Ef.
    case Efun: (is_fun (type_of f)) Hdom => //= Hdom.
    by rewrite (is_fun_subst tyin (type_of f) Efun)
       (dest_fun_subst tyin (type_of f) Efun) /= Ex (eqP Hdom).
  + rewrite Ef.
    case Efun: (is_fun (type_of f)) Hdom => //= Hdom.
    by rewrite (is_fun_subst tyin (type_of f) Efun)
       (dest_fun_subst tyin (type_of f) Efun).
- move=> /andP[Haty Hb].
  have [Hb' Eb] := IHb (aty :: env) Hb.
  split.
  + by rewrite (check_type_subst thy tyin aty Htyin Haty) /=.
  + by rewrite /mk_fun /= Eb.
Qed.

(** Every type substituted in must itself be well-formed in [thy] -- the
    analogue of [INST]'s own per-replacement well-typedness check.
    Iterates over [domf tyin] rather than [codomf tyin] because [HType]
    carries no [choiceType] instance (it is never used as a finmap/finset
    key anywhere in this development, only [==]-compared), so [codomf]
    -- which builds an [{fset HType}] -- is not available; [domf tyin] is
    an [{fset Name}], always on offer. *)
Definition check_tyin (thy : Theory) (tyin : {fmap Name -> HType}) : bool :=
  fset_all (fun n => match tyin.[? n] with Some ty => check_type thy ty | None => true end)
    (domf tyin).

Lemma check_tyinP thy tyin :
  check_tyin thy tyin ->
  forall n ty, tyin.[? n] = Some ty -> check_type thy ty.
Proof.
move=> /fset_allP Hall n ty Hn.
have Hin : n \in domf tyin by rewrite -fndSome Hn.
have := Hall n Hin.
by rewrite Hn.
Qed.

(** Instantiate type variables. *)
Definition INST_TYPE (thy : Theory) (tyin : {fmap Name -> HType}) (th : Thm) : option Thm :=
  if descends (thm_stamp th) (th_stamp thy) && check_tyin thy tyin then
    Some (mkThm (inst_type tyin @` (thm_hyps th)) (inst_type tyin (thm_concl th)) (th_stamp thy))
  else None.

Lemma instTypeWellFormed thy tyin th th' :
  WellFormedTheory thy -> WellFormedThm thy th ->
  INST_TYPE thy tyin th = Some th' -> WellFormedThm thy th'.
Proof.
move=> WFT [Hct [Hht [Hbt [Hbht Hdt]]]].
rewrite /INST_TYPE.
case: ifP => [/andP[_ Hcty] | //].
move=> [<-].
have Htyin := check_tyinP thy tyin Hcty.
have [Hconcl Econcl] := check_open_term_inst_type thy tyin (thm_concl th) [::] Htyin Hct.
split; first exact: Hconcl.
split.
  apply: fset_all_image => h Hin.
  by have [Hc _] := check_open_term_inst_type thy tyin h [::] Htyin (Hht h Hin).
split; first by rewrite /is_bool Econcl (eqP Hbt) /bool_ty /mk_tyapp /= eqxx.
split.
  apply: fset_all_image => h Hin.
  have [_ Eh] := check_open_term_inst_type thy tyin h [::] Htyin (Hht h Hin).
  by rewrite /is_bool Eh (eqP (Hbht h Hin)) /bool_ty /mk_tyapp /= eqxx.
by case: WFT => [_ [_ [_ Hself]]].
Qed.

(** * Theory extension

    [new_type], [new_constant], [new_axiom], [new_basic_definition],
    [new_basic_type_definition] -- transliterating [kernel.rhm]'s own
    "theory extension" section, in the same order. Each mints its own
    fresh [Name] as an explicit parameter (see the note on [next_stamp]
    at the top of this file for why: a real [gensym] discharges freshness
    for free at runtime, so here the caller discharges it as an explicit
    hypothesis instead, only where a lemma actually needs it fresh). *)

(** [check_type]/[check_open_term] only ever consult [thy] through
    [type_arity]/[const_type]; both are fixpoints *on the term/type*, so
    Coq cannot see two [Theory] values agree on those two projections are
    interchangeable by mere computation (the match is stuck on an
    abstract term/type) -- these two lemmas supply the missing induction,
    used everywhere below a [Theory] literal shares some fields with an
    existing one but not others. *)
Lemma check_type_thy_eq thy1 thy2 ty :
  th_tyops thy1 = th_tyops thy2 -> check_type thy1 ty = check_type thy2 ty.
Proof.
move=> Heq.
elim/HType_rect: ty => [n | n args IH] //=.
rewrite /type_arity Heq.
case: ((th_tyops thy2).[? n]) => [ar|] //=.
congr andb.
elim: args IH => [|a args' IHa] //= [Ha Hargs].
by rewrite Ha (IHa Hargs).
Qed.

Lemma check_open_term_thy_eq thy1 thy2 t env :
  th_tyops thy1 = th_tyops thy2 -> th_consts thy1 = th_consts thy2 ->
  check_open_term thy1 t env = check_open_term thy2 t env.
Proof.
move=> Htyops Hconsts.
elim: t env => [v | i ty | n ty | f IHf x IHx | aty b IHb] env //=.
- by rewrite (check_type_thy_eq thy1 thy2 (fv_ty v) Htyops).
- by rewrite (check_type_thy_eq thy1 thy2 ty Htyops).
- by rewrite (check_type_thy_eq thy1 thy2 ty Htyops) /const_type Hconsts.
- by rewrite (IHf env) (IHx env).
- by rewrite (check_type_thy_eq thy1 thy2 aty Htyops) (IHb (aty :: env)).
Qed.

Lemma check_term_thy_eq thy1 thy2 t :
  th_tyops thy1 = th_tyops thy2 -> th_consts thy1 = th_consts thy2 ->
  check_term thy1 t = check_term thy2 t.
Proof. exact: check_open_term_thy_eq. Qed.

(** The monotone analogue: [thy2] need not equal [thy1] on [type_arity]/
    [const_type], only extend it. Every extension principle below adds
    declarations and never removes or changes one, so this is exactly
    the shape each one's "old terms/theorems stay well-formed" fact
    needs. *)
Lemma check_type_monotone thy1 thy2 ty :
  (forall n a, type_arity thy1 n = Some a -> type_arity thy2 n = Some a) ->
  check_type thy1 ty -> check_type thy2 ty.
Proof.
move=> Hmono.
elim/HType_rect: ty => [n | n args IH] //=.
case Har: (type_arity thy1 n) => [ar|] //= /andP[Hsz Hall].
rewrite (Hmono n ar Har) Hsz {Hsz} /=.
move: Hall.
elim: args IH => [|a args' IHa] //= [Ha Hargs] /andP[Ha' Hargs'].
by rewrite (Ha Ha') (IHa Hargs Hargs').
Qed.

Lemma check_open_term_monotone thy1 thy2 t env :
  (forall n a, type_arity thy1 n = Some a -> type_arity thy2 n = Some a) ->
  (forall n ty, const_type thy1 n = Some ty -> const_type thy2 n = Some ty) ->
  check_open_term thy1 t env -> check_open_term thy2 t env.
Proof.
move=> Htyops Hconsts.
elim: t env => [v | i ty | n ty | f IHf x IHx | aty b IHb] env //=.
- exact: (check_type_monotone thy1 thy2 (fv_ty v) Htyops).
- move=> /andP[/andP[Hlt Heq] Hct].
  rewrite Hlt Heq /=.
  exact: (check_type_monotone thy1 thy2 ty Htyops Hct).
- move=> /andP[Hct Hconst].
  rewrite (check_type_monotone thy1 thy2 ty Htyops Hct) /=.
  move: Hconst; case Hgty: (const_type thy1 n) => [gty|] //.
  by rewrite (Hconsts n gty Hgty).
- by move=> /andP[/andP[Hf Hx] Hdom]; rewrite (IHf env Hf) (IHx env Hx) Hdom.
- by move=> /andP[Haty Hb]; rewrite (check_type_monotone thy1 thy2 aty Htyops Haty)
    (IHb (aty :: env) Hb).
Qed.

Lemma check_term_monotone thy1 thy2 t :
  (forall n a, type_arity thy1 n = Some a -> type_arity thy2 n = Some a) ->
  (forall n ty, const_type thy1 n = Some ty -> const_type thy2 n = Some ty) ->
  check_term thy1 t -> check_term thy2 t.
Proof. exact: check_open_term_monotone. Qed.

(** A [Thm] already well-formed in [thy] stays well-formed in any
    one-step extension [thy'], regardless of which of the four
    principles below produced it. Every extension lemma's own "old
    theorems stay usable" fact is an instance of this one. *)
Lemma WellFormedThm_monotone thy thy' th :
  (forall n a, type_arity thy n = Some a -> type_arity thy' n = Some a) ->
  (forall n ty, const_type thy n = Some ty -> const_type thy' n = Some ty) ->
  (forall a, a \in st_ancestors (th_stamp thy) -> a \in st_ancestors (th_stamp thy')) ->
  WellFormedThm thy th -> WellFormedThm thy' th.
Proof.
move=> Htyops Hconsts Hanc [Hct [Hht [Hbt [Hbht Hdt]]]].
split; first exact: (check_term_monotone thy thy' _ Htyops Hconsts Hct).
split.
  move=> h Hin; exact: (check_term_monotone thy thy' h Htyops Hconsts (Hht h Hin)).
split; first exact: Hbt.
split; first exact: Hbht.
exact: Hanc.
Qed.

(** Matching a type against itself, from an accumulator that is already
    self-consistent (binds every name it mentions to its own [HTyVar]),
    always succeeds, and the result stays self-consistent -- needed by
    [new_basic_definition] to show a just-declared constant's own
    (fully concrete, no-op) instantiation passes [check_open_term]'s
    [TmConst] check. *)
Lemma type_match_refl_acc ty :
  forall acc : {fmap Name -> HType},
  (forall n v, acc.[? n] = Some v -> v = HTyVar n) ->
  exists m, type_match ty ty acc = Some m /\
    forall n v, m.[? n] = Some v -> v = HTyVar n.
Proof.
elim/HType_rect: ty => [n | n args IH] acc Hinv.
- rewrite /=.
  case E: (acc.[? n]) => [prev|].
  + have Hp := Hinv n prev E.
    rewrite Hp eqxx.
    by exists acc.
  + exists (acc.[n <- HTyVar n]); split=> //.
    move=> n0 v0; case: (@eqP _ n0 n) => [-> | Hne].
    * by rewrite fnd_set eqxx => [[<-]].
    * rewrite fnd_set (negbTE (introN eqP Hne)) => Hv0.
      exact: Hinv n0 v0 Hv0.
- rewrite /=.
  case: (@andP (n == n) (size args == size args)) => [_ | []]; last by [].
  move: acc Hinv.
  elim: args IH => [| a args' IHa].
  + move=> _ acc Hinv.
    by exists acc.
  + move=> [Ha Hargs] acc Hinv.
    have [a2 [Ea2 Hinva2]] := Ha acc Hinv.
    rewrite Ea2.
    exact: IHa Hargs a2 Hinva2.
Qed.

Lemma type_match_refl ty : exists m, type_match ty ty [fmap] = Some m.
Proof.
have Hinv0 : forall n v, ([fmap] : {fmap Name -> HType}).[? n] = Some v -> v = HTyVar n.
  by move=> n v; rewrite fnd_fmap0.
have [m [Em _]] := type_match_refl_acc ty [fmap] Hinv0.
by exists m.
Qed.

(** Every axiom a theory has accumulated is already well-typed in that
    theory -- [new_axiom]'s own [check_prop] precondition establishes
    this when an axiom is first added, and every non-axiom-adding
    extension principle below preserves it (none of them touch
    [th_axioms], and [WellFormedThm] is monotone under
    [type_arity]/[const_type] growth). [ModelsTheory]'s axiom clause is
    meaningful only relative to this invariant: without it, an axiom
    could be vacuously "modeled" under a theory it is not even
    well-typed in, then become a live, unvalidated obligation once a
    later extension makes it well-typed. *)
Definition AxiomsChecked (thy : Theory) : Prop :=
  forall ax, List.In ax (th_axioms thy) -> WellFormedThm thy ax.

Lemma AxiomsChecked_monotone thy thy' :
  (forall n a, type_arity thy n = Some a -> type_arity thy' n = Some a) ->
  (forall n ty, const_type thy n = Some ty -> const_type thy' n = Some ty) ->
  (forall a, a \in st_ancestors (th_stamp thy) -> a \in st_ancestors (th_stamp thy')) ->
  th_axioms thy' = th_axioms thy ->
  AxiomsChecked thy -> AxiomsChecked thy'.
Proof.
move=> Htyops Hconsts Hanc Heq HAC ax Hin.
apply: (WellFormedThm_monotone thy thy' ax Htyops Hconsts Hanc).
apply: HAC.
by rewrite -Heq.
Qed.

(** The [th_defs]-side analogue of [AxiomsChecked]: every definitional
    equation a theory has recorded is already well-typed in that
    theory. [new_basic_definition] establishes this for the one new
    entry it adds; every other extension principle preserves it (they
    never touch [th_defs], and [WellFormedThm] is monotone). *)
Definition DefsChecked (thy : Theory) : Prop :=
  forall n df, (th_defs thy).[? n] = Some df -> WellFormedThm thy df.

Lemma DefsChecked_monotone thy thy' :
  (forall n a, type_arity thy n = Some a -> type_arity thy' n = Some a) ->
  (forall n ty, const_type thy n = Some ty -> const_type thy' n = Some ty) ->
  (forall a, a \in st_ancestors (th_stamp thy) -> a \in st_ancestors (th_stamp thy')) ->
  th_defs thy' = th_defs thy ->
  DefsChecked thy -> DefsChecked thy'.
Proof.
move=> Htyops Hconsts Hanc Heq HDC n df Hdf.
apply: (WellFormedThm_monotone thy thy' df Htyops Hconsts Hanc).
apply: (HDC n df).
by rewrite -Heq.
Qed.

(** Every stored definition is no more polymorphic than its declared
    result type.  This is the persistent form of [new_basic_definition]'s
    local [Htv] check, needed when definitions are instantiated in later
    extensions. *)
Definition DefsScoped (thy : Theory) : Prop :=
  forall n df, (th_defs thy).[? n] = Some df ->
    forall r, dest_eq (thm_concl df) = Some (mk_const n (type_of r), r) ->
    forall v0, v0 \in term_type_vars r -> v0 \in type_vars (type_of r).

Lemma DefsScoped_monotone thy thy' :
  th_defs thy' = th_defs thy -> DefsScoped thy -> DefsScoped thy'.
Proof.
move=> Edefs HDS n df Hdf r Hdest v0 Hv.
apply: (HDS n df _ r Hdest v0 Hv).
by rewrite -Edefs.
Qed.


Definition new_type (thy : Theory) (fresh : Name) (n : Name) (arity : nat) : option Theory :=
  if type_arity thy n != None then None
  else Some (extend thy fresh (th_tyops thy).[n <- arity] (th_consts thy)
               (th_axioms thy) (th_defs thy)).

(** Matches [idris-hol-kernel]'s own [newTypeMonotone]: extension never
    un-declares a type constructor already declared. *)
Lemma newTypeMonotone thy fresh n arity thy' :
  new_type thy fresh n arity = Some thy' ->
  forall n2 a2, type_arity thy n2 = Some a2 -> type_arity thy' n2 = Some a2.
Proof.
rewrite /new_type; case: ifP => // /eqP Hnone [<-] n2 a2 Ha2.
rewrite /type_arity /extend /= fnd_set.
case: ifP => [Heq | _] //=.
move: Heq => /eqP Heq.
rewrite Heq in Ha2.
by move: Hnone; rewrite Ha2.
Qed.

Lemma newTypeMonotoneConst thy fresh n arity thy' :
  new_type thy fresh n arity = Some thy' ->
  forall n2 ty2, const_type thy n2 = Some ty2 -> const_type thy' n2 = Some ty2.
Proof. by rewrite /new_type; case: ifP => // _ [<-]. Qed.

Lemma newTypeOneGen thy fresh n arity thy' :
  new_type thy fresh n arity = Some thy' ->
  st_gen (th_stamp thy') = (st_gen (th_stamp thy)).+1.
Proof. by rewrite /new_type; case: ifP => // _ [<-]. Qed.

Lemma newTypeAncestors thy fresh n arity thy' :
  new_type thy fresh n arity = Some thy' ->
  forall a, a \in st_ancestors (th_stamp thy) -> a \in st_ancestors (th_stamp thy').
Proof.
rewrite /new_type; case: ifP => // _ [<-] a Ha.
by rewrite /extend /next_stamp /= fset1Ur.
Qed.

Lemma newTypeDescends thy fresh n arity thy' :
  WellFormedTheory thy -> new_type thy fresh n arity = Some thy' ->
  descends (th_stamp thy) (th_stamp thy').
Proof.
move=> [_ [_ [_ Hself]]] Hnt.
exact: (newTypeAncestors thy fresh n arity thy' Hnt) Hself.
Qed.
Lemma newTypeAxiomsChecked thy fresh n arity thy' :
  new_type thy fresh n arity = Some thy' -> AxiomsChecked thy -> AxiomsChecked thy'.
Proof.
move=> Hnt HAC.
apply: (AxiomsChecked_monotone thy thy'
  (newTypeMonotone thy fresh n arity thy' Hnt)
  (newTypeMonotoneConst thy fresh n arity thy' Hnt)
  (newTypeAncestors thy fresh n arity thy' Hnt) _ HAC).
by move: Hnt; rewrite /new_type; case: ifP => // _ [<-].
Qed.
Lemma newTypeDefsChecked thy fresh n arity thy' :
  new_type thy fresh n arity = Some thy' -> DefsChecked thy -> DefsChecked thy'.
Proof.
move=> Hnt HDC.
apply: (DefsChecked_monotone thy thy'
  (newTypeMonotone thy fresh n arity thy' Hnt)
  (newTypeMonotoneConst thy fresh n arity thy' Hnt)
  (newTypeAncestors thy fresh n arity thy' Hnt) _ HDC).
by move: Hnt; rewrite /new_type; case: ifP => // _ [<-].
Qed.

Lemma newTypeDefsScoped thy fresh n arity thy' :
  new_type thy fresh n arity = Some thy' -> DefsScoped thy -> DefsScoped thy'.
Proof.
move=> Hnt HDS; apply: (DefsScoped_monotone thy thy' _ HDS).
by move: Hnt; rewrite /new_type; case: ifP => // _ [<-].
Qed.



Definition new_constant (thy : Theory) (fresh : Name) (n : Name) (ty : HType) : option Theory :=
  if (const_type thy n != None) || ~~ check_type thy ty then None
  else Some (extend thy fresh (th_tyops thy) (th_consts thy).[n <- ty]
               (th_axioms thy) (th_defs thy)).

Lemma newConstantMonotone thy fresh n ty thy' :
  new_constant thy fresh n ty = Some thy' ->
  forall n2 a2, type_arity thy n2 = Some a2 -> type_arity thy' n2 = Some a2.
Proof. by rewrite /new_constant; case: ifP => // _ [<-]. Qed.

Lemma newConstantMonotoneConst thy fresh n ty thy' :
  new_constant thy fresh n ty = Some thy' ->
  forall n2 ty2, const_type thy n2 = Some ty2 -> const_type thy' n2 = Some ty2.
Proof.
rewrite /new_constant; case: ifP => // /norP [/eqP Hnone _] [<-] n2 ty2 Hty2.
rewrite /const_type /extend /= fnd_set.
case: ifP => [Heq | _] //=.
move: Heq => /eqP Heq.
rewrite Heq in Hty2.
by move: Hnone; rewrite Hty2.
Qed.

Lemma newConstantOneGen thy fresh n ty thy' :
  new_constant thy fresh n ty = Some thy' ->
  st_gen (th_stamp thy') = (st_gen (th_stamp thy)).+1.
Proof. by rewrite /new_constant; case: ifP => // _ [<-]. Qed.

Lemma newConstantAncestors thy fresh n ty thy' :
  new_constant thy fresh n ty = Some thy' ->
  forall a, a \in st_ancestors (th_stamp thy) -> a \in st_ancestors (th_stamp thy').
Proof.
rewrite /new_constant; case: ifP => // _ [<-] a Ha.
by rewrite /extend /next_stamp /= fset1Ur.
Qed.

Lemma newConstantDescends thy fresh n ty thy' :
  WellFormedTheory thy -> new_constant thy fresh n ty = Some thy' ->
  descends (th_stamp thy) (th_stamp thy').
Proof.
move=> [_ [_ [_ Hself]]] Hnc.
exact: (newConstantAncestors thy fresh n ty thy' Hnc) Hself.
Qed.
Lemma newConstantAxiomsChecked thy fresh n ty thy' :
  new_constant thy fresh n ty = Some thy' -> AxiomsChecked thy -> AxiomsChecked thy'.
Proof.
move=> Hnc HAC.
apply: (AxiomsChecked_monotone thy thy'
  (newConstantMonotone thy fresh n ty thy' Hnc)
  (newConstantMonotoneConst thy fresh n ty thy' Hnc)
  (newConstantAncestors thy fresh n ty thy' Hnc) _ HAC).
by move: Hnc; rewrite /new_constant; case: ifP => // _ [<-].
Qed.
Lemma newConstantDefsChecked thy fresh n ty thy' :
  new_constant thy fresh n ty = Some thy' -> DefsChecked thy -> DefsChecked thy'.
Proof.
move=> Hnc HDC.
apply: (DefsChecked_monotone thy thy'
  (newConstantMonotone thy fresh n ty thy' Hnc)
  (newConstantMonotoneConst thy fresh n ty thy' Hnc)
  (newConstantAncestors thy fresh n ty thy' Hnc) _ HDC).
by move: Hnc; rewrite /new_constant; case: ifP => // _ [<-].
Qed.



(** The escape hatch: nothing in [new_type]/[new_constant] routes through
    this; it exists purely so a user-level axiom has somewhere to go. *)
Definition new_axiom (thy : Theory) (fresh : Name) (p : Term) : option (Theory * Thm) :=
  if check_prop thy p then
    let st := next_stamp fresh (th_stamp thy) in
    let th := mkThm fset0 p st in
    Some (mkTheory (th_tyops thy) (th_consts thy) (th :: th_axioms thy) (th_defs thy) st, th)
  else None.

Lemma newAxiomAncestors thy fresh p thy' th :
  new_axiom thy fresh p = Some (thy', th) ->
  forall a, a \in st_ancestors (th_stamp thy) -> a \in st_ancestors (th_stamp thy').
Proof.
rewrite /new_axiom; case: ifP => // _ [<- _] a Ha.
by rewrite /= fset1Ur.
Qed.

Lemma newAxiomWellFormed thy fresh p thy' th :
  new_axiom thy fresh p = Some (thy', th) -> WellFormedThm thy' th.
Proof.
rewrite /new_axiom; case: ifP => // /andP[Hct Hbt] [<- <-].
rewrite /WellFormedThm /= -(check_term_thy_eq thy _ p) //.
split; first exact: Hct.
split; first by move=> h; rewrite in_fset0.
split; first exact: Hbt.
split; first by move=> h; rewrite in_fset0.
by rewrite /descends /= fset1U1.
Qed.

Lemma newAxiomOneGen thy fresh p thy' th :
  new_axiom thy fresh p = Some (thy', th) ->
  st_gen (th_stamp thy') = (st_gen (th_stamp thy)).+1 /\ thm_stamp th = th_stamp thy'.
Proof. by rewrite /new_axiom; case: ifP => // _ [<- <-]. Qed.

Lemma newAxiomMonotone thy fresh p thy' th :
  new_axiom thy fresh p = Some (thy', th) ->
  forall n2 a2, type_arity thy n2 = Some a2 -> type_arity thy' n2 = Some a2.
Proof. by rewrite /new_axiom; case: ifP => // _ [<- _]. Qed.

Lemma newAxiomMonotoneConst thy fresh p thy' th :
  new_axiom thy fresh p = Some (thy', th) ->
  forall n2 ty2, const_type thy n2 = Some ty2 -> const_type thy' n2 = Some ty2.
Proof. by rewrite /new_axiom; case: ifP => // _ [<- _]. Qed.

Lemma newAxiomDescends thy fresh p thy' th :
  WellFormedTheory thy -> new_axiom thy fresh p = Some (thy', th) ->
  descends (th_stamp thy) (th_stamp thy').
Proof.
move=> [_ [_ [_ Hself]]] Hna.
exact: (newAxiomAncestors thy fresh p thy' th Hna) Hself.
Qed.
Lemma newAxiomAxiomsChecked thy fresh p thy' th :
  new_axiom thy fresh p = Some (thy', th) -> AxiomsChecked thy -> AxiomsChecked thy'.
Proof.
move=> Hna HAC ax Hin.
have Hna' := Hna.
move: Hna'; rewrite /new_axiom; case: ifP => // Hcp [Ethy' Eth].
rewrite -Ethy' Eth /= in Hin.
move: Hin => -[<- | Hin].
- exact: (newAxiomWellFormed thy fresh p thy' th Hna).
- apply: (WellFormedThm_monotone thy thy' ax
    (newAxiomMonotone thy fresh p thy' th Hna)
    (newAxiomMonotoneConst thy fresh p thy' th Hna)
    (newAxiomAncestors thy fresh p thy' th Hna)).
  exact: HAC.
Qed.
Lemma newAxiomDefsChecked thy fresh p thy' th :
  new_axiom thy fresh p = Some (thy', th) -> DefsChecked thy -> DefsChecked thy'.
Proof.
move=> Hna HDC.
apply: (DefsChecked_monotone thy thy'
  (newAxiomMonotone thy fresh p thy' th Hna)
  (newAxiomMonotoneConst thy fresh p thy' th Hna)
  (newAxiomAncestors thy fresh p thy' th Hna) _ HDC).
by move: Hna; rewrite /new_axiom; case: ifP => // _ [<- _].
Qed.



(** A conservative definition: [c = rhs] where [c] is undeclared, [rhs]
    is closed, and [rhs] has no type variables beyond those of its own
    declared type -- otherwise the constant would be more polymorphic
    than its body, which is unsound (a single body could then be forced
    to disagree with itself at two different instances of the same type
    variable). *)
Definition new_basic_definition (thy : Theory) (fresh : Name) (tm : Term) :
    option (Theory * Thm) :=
  match dest_eq tm with
  | Some (TmFVar v, rhs) =>
      let n := fv_name v in let ty := fv_ty v in
      if (const_type thy n != None) || ~~ check_term thy rhs ||
         (free_vars rhs != [::]) || (ty != type_of rhs) ||
         ~~ all (fun v0 => v0 \in type_vars ty) (term_type_vars rhs)
      then None
      else
        let st := next_stamp fresh (th_stamp thy) in
        let c := mk_const n ty in
        let th := mkThm fset0 (mk_eq c rhs) st in
        Some (mkTheory (th_tyops thy) (th_consts thy).[n <- ty] (th_axioms thy)
                (th_defs thy).[n <- th] st, th)
  | _ => None
  end.

Lemma newBasicDefinitionExtract thy fresh tm thy' th :
  new_basic_definition thy fresh tm = Some (thy', th) ->
  exists v rhs,
    dest_eq tm = Some (TmFVar v, rhs) /\
    const_type thy (fv_name v) = None /\
    check_term thy rhs /\
    free_vars rhs = [::] /\
    fv_ty v = type_of rhs /\
    (forall v0, v0 \in term_type_vars rhs -> v0 \in type_vars (fv_ty v)) /\
    thy' = mkTheory (th_tyops thy) (th_consts thy).[fv_name v <- fv_ty v] (th_axioms thy)
             (th_defs thy).[fv_name v <- th] (next_stamp fresh (th_stamp thy)) /\
    th = mkThm fset0 (mk_eq (mk_const (fv_name v) (fv_ty v)) rhs)
           (next_stamp fresh (th_stamp thy)).
Proof.
rewrite /new_basic_definition.
case Hde: (dest_eq tm) => [[l rhs]|] //.
case: l Hde => // v Hde.
case: ifP => // /negbT; rewrite !negb_or => /andP[/andP[/andP[/andP[Hn Hrhs] Hfv] Hty] Htv]
  [<- <-].
move: Hn Hrhs Hfv Hty Htv => /negPn/eqP Hn /negPn Hrhs /negPn/eqP Hfv /negPn/eqP Hty
  /negPn/allP Htv.
by exists v, rhs.
Qed.

Lemma newBasicDefinitionAncestors thy fresh tm thy' th :
  new_basic_definition thy fresh tm = Some (thy', th) ->
  forall a, a \in st_ancestors (th_stamp thy) -> a \in st_ancestors (th_stamp thy').
Proof.
move=> /newBasicDefinitionExtract [v [rhs [_ [_ [_ [_ [_ [_ [-> _]]]]]]]]] a Ha.
by rewrite /= fset1Ur.
Qed.

Lemma newBasicDefinitionMonotone thy fresh tm thy' th :
  new_basic_definition thy fresh tm = Some (thy', th) ->
  forall n a, type_arity thy n = Some a -> type_arity thy' n = Some a.
Proof.
by move=> /newBasicDefinitionExtract [v [rhs [_ [_ [_ [_ [_ [_ [-> _]]]]]]]]].
Qed.

Lemma newBasicDefinitionMonotoneConst thy fresh tm thy' th :
  new_basic_definition thy fresh tm = Some (thy', th) ->
  forall n2 ty2, const_type thy n2 = Some ty2 -> const_type thy' n2 = Some ty2.
Proof.
move=> /newBasicDefinitionExtract [v [rhs [_ [Hn [_ [_ [_ [_ [-> _]]]]]]]]] n2 ty2 Hty2.
rewrite /const_type /= fnd_set.
case: ifP => [Heq | //].
move: Heq => /eqP Heq.
rewrite Heq in Hty2.
by move: Hn; rewrite Hty2.
Qed.

Lemma newBasicDefinitionOneGen thy fresh tm thy' th :
  new_basic_definition thy fresh tm = Some (thy', th) ->
  st_gen (th_stamp thy') = (st_gen (th_stamp thy)).+1 /\ thm_stamp th = th_stamp thy'.
Proof.
by move=> /newBasicDefinitionExtract [v [rhs [_ [_ [_ [_ [_ [_ [-> ->]]]]]]]]].
Qed.

Lemma newBasicDefinitionWellFormedTheory thy fresh tm thy' th :
  WellFormedTheory thy -> new_basic_definition thy fresh tm = Some (thy', th) ->
  WellFormedTheory thy'.
Proof.
move=> WFT /newBasicDefinitionExtract [v [rhs [_ [Hn [_ [_ [_ [_ [-> _]]]]]]]]].
have HneqNEq : fv_name v <> NEq.
  move=> Heq; move: Hn; rewrite Heq.
  by case: WFT => [_ [_ [-> _]]].
split; first by case: WFT.
split; first by case: WFT => [_ []].
split.
  rewrite /const_type /= fnd_set eq_sym (negbTE (introN eqP HneqNEq)).
  by case: WFT => [_ [_ []]].
by rewrite /= fset1U1.
Qed.

Lemma newBasicDefinitionWellFormed thy fresh tm thy' th :
  WellFormedTheory thy -> new_basic_definition thy fresh tm = Some (thy', th) ->
  WellFormedThm thy' th.
Proof.
move=> WFT Hnbd.
have [v [rhs [_ [Hn [Hrhs [Hfv [Hty [Htv [Ethy' Eth]]]]]]]]] := newBasicDefinitionExtract
  thy fresh tm thy' th Hnbd.
have Htyops : forall n a, type_arity thy n = Some a -> type_arity thy' n = Some a
  := newBasicDefinitionMonotone thy fresh tm thy' th Hnbd.
have Hconsts : forall n2 ty2, const_type thy n2 = Some ty2 -> const_type thy' n2 = Some ty2
  := newBasicDefinitionMonotoneConst thy fresh tm thy' th Hnbd.
have Hrhs' : check_term thy' rhs := check_term_monotone thy thy' rhs Htyops Hconsts Hrhs.
have Hcty : check_type thy (fv_ty v).
  by rewrite Hty; exact: (check_term_type_of thy rhs WFT Hrhs).
have Hcty' : check_type thy' (fv_ty v) := check_type_monotone thy thy' (fv_ty v) Htyops Hcty.
have [m Hm] := type_match_refl (fv_ty v).
have Hc : check_term thy' (mk_const (fv_name v) (fv_ty v)).
  rewrite /check_term /= Hcty' /= /const_type Ethy' /= fnd_set eqxx Hm.
  by [].
have Ectype : type_of (mk_const (fv_name v) (fv_ty v)) = type_of rhs.
  by rewrite /= -Hty.
have WFT' := newBasicDefinitionWellFormedTheory thy fresh tm thy' th WFT Hnbd.
have Hmkeq : check_term thy' (mk_eq (mk_const (fv_name v) (fv_ty v)) rhs) :=
  mkEqCheckSound thy' _ rhs WFT' Hc Hrhs' Ectype.
rewrite Eth /WellFormedThm /=.
split; first exact: Hmkeq.
split; first by move=> h; rewrite in_fset0.
split.
  rewrite /is_bool /mk_eq /=.
  by rewrite eqxx.
split; first by move=> h; rewrite in_fset0.
rewrite /descends Ethy' /= fset1U1 //.
Qed.
Lemma newBasicDefinitionDefsChecked thy fresh tm thy' th :
  WellFormedTheory thy -> new_basic_definition thy fresh tm = Some (thy', th) ->
  DefsChecked thy -> DefsChecked thy'.
Proof.
move=> WFT Hnbd HDC n0 df0 Hlookup.
have [v [rhs [_ [_ [_ [_ [_ [_ [Ethy' Eth]]]]]]]]] := newBasicDefinitionExtract
  thy fresh tm thy' th Hnbd.
rewrite Ethy' /= fnd_set in Hlookup.
move: Hlookup; case: ifP => [/eqP Heq [<-] | _ Hdf0].
- exact: (newBasicDefinitionWellFormed thy fresh tm thy' th WFT Hnbd).
- apply: (WellFormedThm_monotone thy thy' df0
    (newBasicDefinitionMonotone thy fresh tm thy' th Hnbd)
    (newBasicDefinitionMonotoneConst thy fresh tm thy' th Hnbd)
    (newBasicDefinitionAncestors thy fresh tm thy' th Hnbd)).
  exact: (HDC n0 df0 Hdf0).
Qed.


(** * Carving out a new type

    [new_basic_type_definition] carves out a new type in bijection with
    the subset of an existing type picked out by [pred], given a witness
    theorem [|- pred witness] proving the subset is inhabited -- the one
    genuinely conservative type-formation principle. *)

Lemma check_term_comb_inv thy f x :
  check_term thy (TmComb f x) ->
  check_term thy f /\ check_term thy x /\
  is_fun (type_of f) /\ (dest_fun (type_of f)).1 = type_of x.
Proof.
rewrite /check_term /= => /andP[/andP[Hf Hx] Hdom].
split; first exact: Hf.
split; first exact: Hx.
move: Hdom => /andP[Hisfun Heq].
split; first exact: Hisfun.
exact/eqP.
Qed.

Lemma check_term_comb thy f x :
  check_term thy f -> check_term thy x ->
  is_fun (type_of f) -> (dest_fun (type_of f)).1 = type_of x ->
  check_term thy (mk_comb f x).
Proof.
move=> Hf Hx Hisfun Heq.
rewrite /check_term /mk_comb /=.
apply/andP; split.
  apply/andP; split; [exact: Hf | exact: Hx].
apply/andP; split; [exact: Hisfun | by rewrite Heq eqxx].
Qed.

Lemma check_type_htyapp_map thy tyname vs :
  type_arity thy tyname = Some (size vs) ->
  check_type thy (mk_tyapp tyname (map HTyVar vs)).
Proof.
move=> Har.
rewrite /mk_tyapp check_typeE Har size_map eqxx /=.
move: Har => _.
by elim: vs => [|v vs' IH] //=.
Qed.

Definition new_basic_type_definition (thy : Theory) (fresh : Name)
    (tyname absname repname : Name) (th : Thm) : option (Theory * Thm * Thm) :=
  if ~~ descends (thm_stamp th) (th_stamp thy) then None
  else if (const_type thy absname != None) || (const_type thy repname != None) then None
  else if type_arity thy tyname != None then None
  else if absname == repname then None
  else if thm_hyps th != fset0 then None
  else match thm_concl th with
  | TmComb pred witness =>
      if free_vars pred != [::] then None
      else
        let tvs := term_type_vars pred in
        let rty := type_of witness in
        if ~~ all (fun v => v \in tvs) (type_vars rty) then None
        else
          let st := next_stamp fresh (th_stamp thy) in
          let aty := mk_tyapp tyname (map HTyVar tvs) in
          let thy2 := mkTheory (th_tyops thy).[tyname <- size tvs]
                        (th_consts thy).[absname <- mk_fun rty aty].[repname <- mk_fun aty rty]
                        (th_axioms thy) (th_defs thy) st in
          let abs := mk_const absname (mk_fun rty aty) in
          let rep := mk_const repname (mk_fun aty rty) in
          let a := TmFVar (mk_var NAlpha aty) in
          let r := TmFVar (mk_var NRepVar rty) in
          let th_abs_rep := mkThm fset0 (mk_eq (mk_comb abs (mk_comb rep a)) a) st in
          let th_pred := mkThm fset0
            (mk_eq (mk_comb pred r) (mk_eq (mk_comb rep (mk_comb abs r)) r)) st in
          Some (thy2, th_abs_rep, th_pred)
  | _ => None
  end.

Lemma newBasicTypeDefinitionExtract thy fresh tyname absname repname th thy2 th_abs_rep th_pred :
  new_basic_type_definition thy fresh tyname absname repname th
    = Some (thy2, th_abs_rep, th_pred) ->
  exists pred witness,
    descends (thm_stamp th) (th_stamp thy) /\
    const_type thy absname = None /\ const_type thy repname = None /\
    type_arity thy tyname = None /\
    absname <> repname /\
    thm_hyps th = fset0 /\
    thm_concl th = TmComb pred witness /\
    free_vars pred = [::] /\
    (forall v, v \in type_vars (type_of witness) -> v \in term_type_vars pred) /\
    thy2 = mkTheory (th_tyops thy).[tyname <- size (term_type_vars pred)]
             (th_consts thy).[absname <- mk_fun (type_of witness)
                                 (mk_tyapp tyname (map HTyVar (term_type_vars pred)))]
               .[repname <- mk_fun (mk_tyapp tyname (map HTyVar (term_type_vars pred)))
                   (type_of witness)]
             (th_axioms thy) (th_defs thy) (next_stamp fresh (th_stamp thy)) /\
    th_abs_rep = mkThm fset0
      (mk_eq (mk_comb (mk_const absname (mk_fun (type_of witness)
                (mk_tyapp tyname (map HTyVar (term_type_vars pred)))))
              (mk_comb (mk_const repname (mk_fun (mk_tyapp tyname (map HTyVar (term_type_vars pred)))
                  (type_of witness)))
                (TmFVar (mk_var NAlpha (mk_tyapp tyname (map HTyVar (term_type_vars pred)))))))
              (TmFVar (mk_var NAlpha (mk_tyapp tyname (map HTyVar (term_type_vars pred))))))
      (next_stamp fresh (th_stamp thy)) /\
    th_pred = mkThm fset0
      (mk_eq (mk_comb pred (TmFVar (mk_var NRepVar (type_of witness))))
        (mk_eq (mk_comb (mk_const repname (mk_fun (mk_tyapp tyname (map HTyVar (term_type_vars pred)))
                (type_of witness)))
            (mk_comb (mk_const absname (mk_fun (type_of witness)
                (mk_tyapp tyname (map HTyVar (term_type_vars pred)))))
              (TmFVar (mk_var NRepVar (type_of witness)))))
          (TmFVar (mk_var NRepVar (type_of witness)))))
      (next_stamp fresh (th_stamp thy)).
Proof.
rewrite /new_basic_type_definition.
case: ifP => // Hdesc0.
have Hdesc : descends (thm_stamp th) (th_stamp thy).
  by move: Hdesc0; case: descends.
case: ifP => // Habsrep0.
have Habs : const_type thy absname = None.
  by move: Habsrep0; case: (const_type thy absname).
have Hrep : const_type thy repname = None.
  by move: Habsrep0; case: (const_type thy absname) => //; case: (const_type thy repname).
case: ifP => // Htn0.
have Htn : type_arity thy tyname = None.
  by move: Htn0; case: (type_arity thy tyname).
case: ifP => // Hne0.
have Hne : absname <> repname.
  by move=> Heq; move: Hne0; rewrite Heq eqxx.
case: ifP => // Hhyps0.
have Hhyps : thm_hyps th = fset0.
  by apply/eqP; move: Hhyps0; case: eqP.
case Hconcl: (thm_concl th) => [| | | pred witness | ] //.
case: ifP => // Hfv0.
have Hfv : free_vars pred = [::].
  by apply/eqP; move: Hfv0; case: eqP.
case: ifP => // Htv0 [<- <- <-].
have Htv : forall v, v \in type_vars (type_of witness) -> v \in term_type_vars pred.
  by apply/allP; move: Htv0; case: allP.
exists pred, witness.
by do 9?split.
Qed.

Lemma newBasicTypeDefinitionAncestors thy fresh tyname absname repname th
    thy2 th_abs_rep th_pred :
  new_basic_type_definition thy fresh tyname absname repname th
    = Some (thy2, th_abs_rep, th_pred) ->
  forall a, a \in st_ancestors (th_stamp thy) -> a \in st_ancestors (th_stamp thy2).
Proof.
move=> /newBasicTypeDefinitionExtract
  [pred [witness [_ [_ [_ [_ [_ [_ [_ [_ [_ [-> [_ _]]]]]]]]]]]]] a Ha.
by rewrite /= fset1Ur.
Qed.
Lemma newBasicTypeDefinitionMonotone thy fresh tyname absname repname th
    thy2 th_abs_rep th_pred :
  new_basic_type_definition thy fresh tyname absname repname th
    = Some (thy2, th_abs_rep, th_pred) ->
  forall n a, type_arity thy n = Some a -> type_arity thy2 n = Some a.
Proof.
move=> /newBasicTypeDefinitionExtract
  [pred [witness [_ [_ [_ [Htn [_ [_ [_ [_ [_ [-> [_ _]]]]]]]]]]]]] n a Ha.
rewrite /type_arity /= fnd_set.
case: ifP => // /eqP Heq; move: Htn; rewrite -Heq Ha => //.
Qed.

Lemma newBasicTypeDefinitionMonotoneConst thy fresh tyname absname repname th
    thy2 th_abs_rep th_pred :
  new_basic_type_definition thy fresh tyname absname repname th
    = Some (thy2, th_abs_rep, th_pred) ->
  forall n2 ty2, const_type thy n2 = Some ty2 -> const_type thy2 n2 = Some ty2.
Proof.
move=> /newBasicTypeDefinitionExtract
  [pred [witness [_ [Habs [Hrep [_ [Hneq [_ [_ [_ [_ [-> [_ _]]]]]]]]]]]]] n2 ty2 Hty2.
rewrite /const_type /= fnd_set.
case: ifP => [/eqP Heq | _].
  by move: Hrep; rewrite -Heq Hty2.
rewrite fnd_set; case: ifP => [/eqP Heq | _] //.
by move: Habs; rewrite -Heq Hty2.
Qed.

Lemma newBasicTypeDefinitionAxiomsChecked thy fresh tyname absname repname th
    thy2 th_abs_rep th_pred :
  new_basic_type_definition thy fresh tyname absname repname th
    = Some (thy2, th_abs_rep, th_pred) ->
  AxiomsChecked thy -> AxiomsChecked thy2.
Proof.
move=> Hnbtd HAC.
apply: (AxiomsChecked_monotone thy thy2
  (newBasicTypeDefinitionMonotone thy fresh tyname absname repname th thy2 th_abs_rep th_pred Hnbtd)
  (newBasicTypeDefinitionMonotoneConst thy fresh tyname absname repname th thy2 th_abs_rep th_pred Hnbtd)
  (newBasicTypeDefinitionAncestors thy fresh tyname absname repname th thy2 th_abs_rep th_pred Hnbtd)
  _ HAC).
by have [pred [witness [_ [_ [_ [_ [_ [_ [_ [_ [_ [-> [_ _]]]]]]]]]]]]]
  := newBasicTypeDefinitionExtract thy fresh tyname absname repname th thy2 th_abs_rep th_pred Hnbtd.
Qed.
Lemma newBasicTypeDefinitionDefsChecked thy fresh tyname absname repname th
    thy2 th_abs_rep th_pred :
  new_basic_type_definition thy fresh tyname absname repname th
    = Some (thy2, th_abs_rep, th_pred) ->
  DefsChecked thy -> DefsChecked thy2.
Proof.
move=> Hnbtd HDC.
apply: (DefsChecked_monotone thy thy2
  (newBasicTypeDefinitionMonotone thy fresh tyname absname repname th thy2 th_abs_rep th_pred Hnbtd)
  (newBasicTypeDefinitionMonotoneConst thy fresh tyname absname repname th thy2 th_abs_rep th_pred Hnbtd)
  (newBasicTypeDefinitionAncestors thy fresh tyname absname repname th thy2 th_abs_rep th_pred Hnbtd)
  _ HDC).
by have [pred [witness [_ [_ [_ [_ [_ [_ [_ [_ [_ [-> [_ _]]]]]]]]]]]]]
  := newBasicTypeDefinitionExtract thy fresh tyname absname repname th thy2 th_abs_rep th_pred Hnbtd.
Qed.



Lemma newBasicTypeDefinitionWellFormedTheory thy fresh tyname absname repname th
    thy2 th_abs_rep th_pred :
  WellFormedTheory thy ->
  new_basic_type_definition thy fresh tyname absname repname th
    = Some (thy2, th_abs_rep, th_pred) ->
  WellFormedTheory thy2.
Proof.
move=> WFT /newBasicTypeDefinitionExtract
  [pred [witness [_ [Habs [Hrep [Htn [_ [_ [_ [_ [_ [-> [_ _]]]]]]]]]]]]].
have HabsNEq : absname <> NEq.
  move=> Heq; move: Habs; rewrite Heq.
  by case: WFT => [_ [_ [HNEq _]]]; rewrite HNEq.
have HrepNEq : repname <> NEq.
  move=> Heq; move: Hrep; rewrite Heq.
  by case: WFT => [_ [_ [HNEq _]]]; rewrite HNEq.
have HtnNBool : tyname <> NBool.
  move=> Heq; move: Htn; rewrite Heq.
  by case: WFT => [HNBool _]; rewrite HNBool.
have HtnNFun : tyname <> NFun.
  move=> Heq; move: Htn; rewrite Heq.
  by case: WFT => [_ [HNFun _]]; rewrite HNFun.
split.
  rewrite /type_arity /= fnd_set eq_sym (negbTE (introN eqP HtnNBool)).
  by case: WFT => [HNBool _].
split.
  rewrite /type_arity /= fnd_set eq_sym (negbTE (introN eqP HtnNFun)).
  by case: WFT => [_ [HNFun _]].
split.
  rewrite /const_type /= fnd_set eq_sym (negbTE (introN eqP HrepNEq))
    fnd_set eq_sym (negbTE (introN eqP HabsNEq)).
  by case: WFT => [_ [_ [HNEq _]]].
by rewrite /= fset1U1.
Qed.

Lemma newBasicTypeDefinitionWellFormed thy fresh tyname absname repname th
    thy2 th_abs_rep th_pred :
  WellFormedTheory thy -> WellFormedThm thy th ->
  new_basic_type_definition thy fresh tyname absname repname th
    = Some (thy2, th_abs_rep, th_pred) ->
  WellFormedThm thy2 th_abs_rep /\ WellFormedThm thy2 th_pred.
Proof.
move=> WFT [Hct [Hht [Hbt [Hbht Hdt]]]] Hnbtd.
have [pred [witness [Hdesc [Habs [Hrep [Htn [Hneq [Hhyps [Hconcl [Hfv [Htv [Ethy2 [Eabsrep Epred]]]]]]]]]]]]]
  := newBasicTypeDefinitionExtract thy fresh tyname absname repname th thy2 th_abs_rep th_pred Hnbtd.
set tvs := term_type_vars pred.
set rty := type_of witness.
set aty := mk_tyapp tyname (map HTyVar tvs).
have Hctpw : check_term thy (TmComb pred witness) by rewrite -Hconcl.
have [Hcpred [Hcwit [Hisfun Hdom1]]] := check_term_comb_inv thy pred witness Hctpw.
have Hbtpw : type_of (TmComb pred witness) = bool_ty.
  by move: Hbt; rewrite Hconcl /is_bool => /eqP.
have Htypred : type_of pred = mk_fun rty bool_ty.
  have [d [r Efty]] := is_fun_HTyApp (type_of pred) Hisfun.
  have Hd : d = rty by move: Hdom1; rewrite Efty /dest_fun /=.
  have Hr : r = bool_ty.
    by move: Hbtpw; rewrite /= Efty /=.
  by rewrite Efty Hd Hr.
have Htyops : forall n a, type_arity thy n = Some a -> type_arity thy2 n = Some a.
  move=> n a Ha; rewrite Ethy2 /type_arity /= fnd_set.
  case: ifP => // /eqP Heq; move: Htn; rewrite -Heq Ha => //.
have Hconsts : forall n2 ty2, const_type thy n2 = Some ty2 -> const_type thy2 n2 = Some ty2.
  move=> n2 ty2 Hty2; rewrite Ethy2 /const_type /= fnd_set.
  case: ifP => [/eqP Heq | _].
    by move: Hrep; rewrite -Heq Hty2.
  rewrite fnd_set; case: ifP => [/eqP Heq | _] //.
  by move: Habs; rewrite -Heq Hty2.
have WFT2 := newBasicTypeDefinitionWellFormedTheory thy fresh tyname absname repname th
  thy2 th_abs_rep th_pred WFT Hnbtd.
have Hcrty_thy2 : check_type thy2 rty :=
  check_type_monotone thy thy2 rty Htyops (check_term_type_of thy witness WFT Hcwit).
have Har_tyname : type_arity thy2 tyname = Some (size tvs).
  by rewrite Ethy2 /type_arity /= fnd_set eqxx.
have Hcaty : check_type thy2 aty := check_type_htyapp_map thy2 tyname tvs Har_tyname.
have Hconst_abs : const_type thy2 absname = Some (mk_fun rty aty).
  rewrite Ethy2 /const_type /= fnd_set (negbTE (introN eqP Hneq)) fnd_set eqxx //.
have Hconst_rep : const_type thy2 repname = Some (mk_fun aty rty).
  by rewrite Ethy2 /const_type /= fnd_set eqxx.
have Habsty : check_term thy2 (mk_const absname (mk_fun rty aty)).
  have Hcfun : check_type thy2 (mk_fun rty aty) :=
    check_type_mk_fun thy2 rty aty WFT2 Hcrty_thy2 Hcaty.
  have [m Hm] := type_match_refl (mk_fun rty aty).
  rewrite /check_term /=; apply/andP; split; first exact: Hcfun.
  by rewrite Hconst_abs Hm.
have Hrepty : check_term thy2 (mk_const repname (mk_fun aty rty)).
  have Hcfun : check_type thy2 (mk_fun aty rty) :=
    check_type_mk_fun thy2 aty rty WFT2 Hcaty Hcrty_thy2.
  have [m Hm] := type_match_refl (mk_fun aty rty).
  rewrite /check_term /=; apply/andP; split; first exact: Hcfun.
  by rewrite Hconst_rep Hm.
have Ha : check_term thy2 (TmFVar (mk_var NAlpha aty)).
  rewrite /check_term /=.
  exact: Hcaty.
have Hr : check_term thy2 (TmFVar (mk_var NRepVar rty)).
  rewrite /check_term /=.
  exact: Hcrty_thy2.
have Hrepa1 : check_term thy2 (mk_comb (mk_const repname (mk_fun aty rty))
    (TmFVar (mk_var NAlpha aty))).
  apply: check_term_comb => //.
have Hrepa2 : type_of (mk_comb (mk_const repname (mk_fun aty rty))
    (TmFVar (mk_var NAlpha aty))) = rty by [].
have Habsrepa1 : check_term thy2 (mk_comb (mk_const absname (mk_fun rty aty))
    (mk_comb (mk_const repname (mk_fun aty rty)) (TmFVar (mk_var NAlpha aty)))).
  apply: check_term_comb => //.
have Habsrepa2 : type_of (mk_comb (mk_const absname (mk_fun rty aty))
    (mk_comb (mk_const repname (mk_fun aty rty)) (TmFVar (mk_var NAlpha aty)))) = aty by [].
have Hmkeq_abs_rep : check_term thy2 (mk_eq
    (mk_comb (mk_const absname (mk_fun rty aty))
      (mk_comb (mk_const repname (mk_fun aty rty)) (TmFVar (mk_var NAlpha aty))))
    (TmFVar (mk_var NAlpha aty))).
  apply: (mkEqCheckSound thy2 _ _ WFT2 Habsrepa1 Ha).
  by rewrite Habsrepa2.
have HWF1 : WellFormedThm thy2 th_abs_rep.
  rewrite Eabsrep /WellFormedThm /=.
  split; first exact: Hmkeq_abs_rep.
  split; first by move=> h; rewrite in_fset0.
  split; first by rewrite /is_bool /mk_eq /=.
  split; first by move=> h; rewrite in_fset0.
  by rewrite /descends Ethy2 /= fset1U1.
have Hcpred2 : check_term thy2 pred := check_term_monotone thy thy2 pred Htyops Hconsts Hcpred.
have Hpredr1 : check_term thy2 (mk_comb pred (TmFVar (mk_var NRepVar rty))).
  apply: check_term_comb => //.
have Hpredr2 : type_of (mk_comb pred (TmFVar (mk_var NRepVar rty))) = bool_ty.
  by rewrite /mk_comb /= Htypred.
have Habsr1 : check_term thy2 (mk_comb (mk_const absname (mk_fun rty aty))
    (TmFVar (mk_var NRepVar rty))).
  apply: check_term_comb => //.
have Habsr2 : type_of (mk_comb (mk_const absname (mk_fun rty aty))
    (TmFVar (mk_var NRepVar rty))) = aty by [].
have Hrepabsr1 : check_term thy2 (mk_comb (mk_const repname (mk_fun aty rty))
    (mk_comb (mk_const absname (mk_fun rty aty)) (TmFVar (mk_var NRepVar rty)))).
  apply: check_term_comb => //.
have Hrepabsr2 : type_of (mk_comb (mk_const repname (mk_fun aty rty))
    (mk_comb (mk_const absname (mk_fun rty aty)) (TmFVar (mk_var NRepVar rty)))) = rty by [].
have Hmkeq_inner : check_term thy2 (mk_eq
    (mk_comb (mk_const repname (mk_fun aty rty))
      (mk_comb (mk_const absname (mk_fun rty aty)) (TmFVar (mk_var NRepVar rty))))
    (TmFVar (mk_var NRepVar rty))).
  apply: (mkEqCheckSound thy2 _ _ WFT2 Hrepabsr1 Hr).
  by rewrite Hrepabsr2.
have Ectype_outer : type_of (mk_comb pred (TmFVar (mk_var NRepVar rty))) =
    type_of (mk_eq
      (mk_comb (mk_const repname (mk_fun aty rty))
        (mk_comb (mk_const absname (mk_fun rty aty)) (TmFVar (mk_var NRepVar rty))))
      (TmFVar (mk_var NRepVar rty))).
  by rewrite Hpredr2 (eqP (is_bool_mk_eq _ _)).
have Hmkeq_pred : check_term thy2 (mk_eq (mk_comb pred (TmFVar (mk_var NRepVar rty)))
    (mk_eq
      (mk_comb (mk_const repname (mk_fun aty rty))
        (mk_comb (mk_const absname (mk_fun rty aty)) (TmFVar (mk_var NRepVar rty))))
      (TmFVar (mk_var NRepVar rty)))) :=
  mkEqCheckSound thy2 _ _ WFT2 Hpredr1 Hmkeq_inner Ectype_outer.
have HWF2 : WellFormedThm thy2 th_pred.
  rewrite Epred /WellFormedThm /=.
  split; first exact: Hmkeq_pred.
  split; first by move=> h; rewrite in_fset0.
  split; first by rewrite /is_bool /mk_eq /=.
  split; first by move=> h; rewrite in_fset0.
  by rewrite /descends Ethy2 /= fset1U1.
split; [exact: HWF1 | exact: HWF2].
Qed.

(** * Soundness regressions

    Reproduces, as Coq lemmas, the specific attacks
    [tests/kernel.rhm]'s "Soundness regressions" section documents;
    they are the reason the checks they exercise exist. *)

Lemma newBasicTypeDefinitionRejectSameName thy fresh tyname n th :
  new_basic_type_definition thy fresh tyname n n th = None.
Proof.
rewrite /new_basic_type_definition.
case: ifP => // _.
case: ifP => // _.
case: ifP => // _.
by rewrite eqxx.
Qed.

Lemma newBasicTypeDefinitionRejectAbsDeclared thy fresh tyname absname repname th :
  const_type thy absname <> None ->
  new_basic_type_definition thy fresh tyname absname repname th = None.
Proof.
move=> Habs.
rewrite /new_basic_type_definition.
case: ifP => // _.
case: ifP => // Hor.
move: Hor Habs; case: (const_type thy absname) => [ty|] //.
Qed.

Lemma newBasicTypeDefinitionRejectRepDeclared thy fresh tyname absname repname th :
  const_type thy repname <> None ->
  new_basic_type_definition thy fresh tyname absname repname th = None.
Proof.
move=> Hrep.
rewrite /new_basic_type_definition.
case: ifP => // _.
case: ifP => // Hor.
move: Hor Hrep; case: (const_type thy repname) => [ty|] //.
by rewrite orbT.
Qed.

Lemma newBasicTypeDefinitionRejectTypeDeclared thy fresh tyname absname repname th :
  type_arity thy tyname <> None ->
  new_basic_type_definition thy fresh tyname absname repname th = None.
Proof.
move=> Htn.
rewrite /new_basic_type_definition.
case: ifP => // _.
case: ifP => // _.
case: ifP => // Hta.
by move: Hta Htn; case: (type_arity thy tyname).
Qed.

Lemma newBasicTypeDefinitionRejectHyps thy fresh tyname absname repname th :
  thm_hyps th <> fset0 ->
  new_basic_type_definition thy fresh tyname absname repname th = None.
Proof.
move=> Hhyps.
rewrite /new_basic_type_definition.
case: ifP => // _.
case: ifP => // _.
case: ifP => // _.
case: ifP => // _.
case: ifP => // Hh.
by move: Hh Hhyps; case: eqP.
Qed.

Lemma newBasicTypeDefinitionOneGen thy fresh tyname absname repname th
    thy2 th_abs_rep th_pred :
  new_basic_type_definition thy fresh tyname absname repname th
    = Some (thy2, th_abs_rep, th_pred) ->
  st_gen (th_stamp thy2) = (st_gen (th_stamp thy)).+1 /\
  thm_stamp th_abs_rep = th_stamp thy2 /\ thm_stamp th_pred = th_stamp thy2.
Proof.
by move=> /newBasicTypeDefinitionExtract
  [pred [witness [_ [_ [_ [_ [_ [_ [_ [_ [_ [-> [-> ->]]]]]]]]]]]]].
Qed.

(** A bound variable may not lie about its binder's type:
    [Abs(num, Comb(p, BVar(0, bool)))] is locally closed and mentions
    only declared types, but its own binder disagrees with the
    variable's stated type -- exactly the attack the [TmBVar] case of
    [check_open_term] exists to reject. *)
Lemma check_term_liar_rejected thy p num_ty :
  num_ty <> bool_ty ->
  check_term thy (TmAbs num_ty
    (TmComb (mk_const p (mk_fun num_ty bool_ty)) (TmBVar 0 bool_ty))) = false.
Proof.
move=> Hne.
rewrite /check_term /= (negbTE (introN eqP Hne)).
by rewrite !andbF.
Qed.

(** Forked theories: two sibling extensions of one base can each
    define a constant of the same name differently, and neither
    descends from the other, so [TRANS]'ing theorems from the two
    branches together must be rejected -- otherwise [|- c = zero] from
    one branch could combine with [|- c = one] from the other to
    derive [|- zero = one]. [fresh1]/[fresh2] being genuinely fresh
    relative to [thy] (never in its ancestor set) is exactly
    [next_stamp]'s own freshness precondition, the same one the note
    at the top of this file explains a real [gensym] would discharge
    at runtime rather than as a hypothesis here. *)
Lemma trans_forked_rejected thy fresh1 fresh2 n rhs1 rhs2 thy1 th1 thy2 th2 :
  fresh1 <> fresh2 ->
  fresh1 \notin st_ancestors (th_stamp thy) ->
  fresh2 \notin st_ancestors (th_stamp thy) ->
  new_basic_definition thy fresh1 (mk_eq (TmFVar (mkFVar n (type_of rhs1))) rhs1)
    = Some (thy1, th1) ->
  new_basic_definition thy fresh2 (mk_eq (TmFVar (mkFVar n (type_of rhs2))) rhs2)
    = Some (thy2, th2) ->
  combine_stamps (thm_stamp th1) (thm_stamp th2) = None.
Proof.
move=> Hnefresh Hfresh1 Hfresh2
  /newBasicDefinitionExtract [v1 [r1 [_ [_ [_ [_ [_ [_ [_ Eth1]]]]]]]]]
  /newBasicDefinitionExtract [v2 [r2 [_ [_ [_ [_ [_ [_ [_ Eth2]]]]]]]]].
rewrite Eth1 Eth2 /combine_stamps /descends /=.
have Hd12 : (fresh1 \in fresh2 |` st_ancestors (th_stamp thy)) = false.
  rewrite in_fset1U (negbTE (introN eqP Hnefresh)) (negbTE Hfresh1) //.
have Hd21 : (fresh2 \in fresh1 |` st_ancestors (th_stamp thy)) = false.
  rewrite in_fset1U eq_sym (negbTE (introN eqP Hnefresh)) (negbTE Hfresh2) //.
by rewrite Hd12 Hd21.
Qed.

(** A rule that takes a theory stamps its result with *that* theory,
    never the input theorem's older one -- otherwise a theorem
    mentioning a constant declared only in a later extension would
    keep the older stamp and could be carried back into a theory that
    never declared it. *)
Lemma instStampsWithTheory thy theta th th' :
  INST thy theta th = Some th' -> thm_stamp th' = th_stamp thy.
Proof. by rewrite /INST; case: ifP => // _ [<-]. Qed.

Lemma absStampsWithTheory thy v th th' :
  ABS thy v th = Some th' -> thm_stamp th' = th_stamp thy.
Proof.
rewrite /ABS; case: ifP => // _.
by case: (dest_eq (thm_concl th)) => [[l r]|] // [<-].
Qed.

Lemma reflStampsWithTheory thy t th' :
  REFL thy t = Some th' -> thm_stamp th' = th_stamp thy.
Proof. by rewrite /REFL; case: ifP => // _ [<-]. Qed.

Lemma betaStampsWithTheory thy t th' :
  BETA thy t = Some th' -> thm_stamp th' = th_stamp thy.
Proof.
rewrite /BETA; case: ifP => // _.
by case: t => [| | | [] | ] // aty body arg [<-].
Qed.

Lemma assumeStampsWithTheory thy p th' :
  ASSUME thy p = Some th' -> thm_stamp th' = th_stamp thy.
Proof. by rewrite /ASSUME; case: ifP => // _ [<-]. Qed.

(** The pure port makes the root identity explicit, just as every extension
    takes its fresh identity explicitly. *)
Definition initial_stamp : Stamp := mkStamp (NUser 0) 0 [fset NUser 0].

(** The kernel's initial theory: exactly [bool], [fun], and polymorphic
    equality, with no axioms or definitions. *)
Definition initial_theory : Theory :=
  mkTheory (([fmap] : {fmap Name -> nat}).[NBool <- 0].[NFun <- 2])
    (([fmap] : {fmap Name -> HType}).[NEq <- mk_fun (HTyVar NAlpha) (mk_fun (HTyVar NAlpha) bool_ty)])
    [::] [fmap] initial_stamp.

Lemma initial_theory_WellFormedTheory : WellFormedTheory initial_theory.
Proof.
rewrite /WellFormedTheory /initial_theory /initial_stamp /type_arity /const_type /=.
have Hbf : NBool != NFun. by [].
split.
- rewrite fnd_set fnd_set (negbTE Hbf) eqxx. by [].
split.
- rewrite fnd_set eqxx. by [].
split.
- rewrite fnd_set eqxx. by [].
by rewrite in_fset1 eqxx.
Qed.

Lemma initial_theory_AxiomsChecked : AxiomsChecked initial_theory.
Proof. by move=> ax; rewrite /initial_theory /=. Qed.

Lemma initial_theory_DefsChecked : DefsChecked initial_theory.
Proof. by move=> n df; rewrite /initial_theory /= fnd_fmap0. Qed.
