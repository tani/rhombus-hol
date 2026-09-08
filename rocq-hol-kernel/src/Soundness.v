(** Soundness and conservativity of the LCF kernel.

    Per-rule: [ruleValid] proves each of the ten primitive rules preserves
    [Valid] (well-formed *and* semantically valid in every model of the
    ambient theory). Per-extension-principle: [...Conservative] proves
    each of [new_type]/[new_constant]/[new_basic_definition]/
    [new_basic_type_definition] extends any model of the theory before to
    a model of the theory after; [new_axiom] is the deliberate escape
    hatch and gets no such lemma (see the plan). *)

From mathcomp Require Import all_boot finmap.
From Stdlib Require Import PropExtensionality ZArith FunctionalExtensionality ProofIrrelevance JMeq.
From RocqHolKernel Require Import Names HType Term Kernel Semantics.
Open Scope fmap_scope.
Open Scope fset_scope.

(** * REFL

    [|- t = t] is valid in every model: [SafeDenote_mk_eq] reduces the
    obligation to [SafeDenote t Hct = SafeDenote t Hct] at a trivial
    (reflexive) type-equality cast, true by [erefl]. *)
Lemma reflValid F thy t th' :
  WellFormedTheory thy -> REFL thy t = Some th' -> Valid F thy th'.
Proof.
move=> WFT Hrefl.
split; first exact: (reflWellFormed thy t th' WFT Hrefl).
move=> HM tv venv _.
move: Hrefl; rewrite /REFL.
case Hct: (check_term thy t) => //.
move=> [<-] Hcc Hbc.
apply: (SafeDenote_mk_eq F thy tv venv t t Hct Hct (erefl (type_of t)) Hbc HM.1 Hcc).2.
by [].
Qed.

(** * ASSUME

    [p |- p] is valid in every model: the conclusion IS the (sole)
    hypothesis, so the hypotheses-hold obligation instantiated at [p]
    itself is exactly the goal, up to aligning [check_term]/[is_bool]
    witnesses via [denoteProp_irrel]. *)
Lemma assumeValid F thy p th' :
  WellFormedTheory thy -> ASSUME thy p = Some th' -> Valid F thy th'.
Proof.
move=> WFT Hassume.
split; first exact: (assumeWellFormed thy p th' WFT Hassume).
move=> HM tv venv.
move: Hassume; rewrite /ASSUME.
case: ifP => [/andP[Hct Hbool] | //].
move=> [<-] Hhyps Hcc Hbc.
rewrite -(denoteProp_irrel F thy tv venv p Hct Hcc Hbool Hbc).
apply (Hhyps p Hct Hbool).
by rewrite in_fset1.
Qed.

(** * TRANS

    [|- l = m]   [|- m = r]
    -------------------
         [|- l = r]

    [trans_eq_shape] recovers [thm_concl a = mk_eq l m]/[thm_concl b =
    mk_eq m r] as *terms*, not just [dest_eq]'s own decomposition,
    letting [SafeDenote_mk_eq] apply to each premise; [trans_eq_rect_comp]
    composes the two resulting type-equality casts before closing with
    [HType_UIP]. *)
Lemma trans_eq_shape thy t l r :
  WellFormedTheory thy -> check_term thy t -> dest_eq t = Some (l, r) ->
  t = mk_eq l r.
Proof.
move=> WFT Hct Hdest.
have [ty Et] := dest_eq_inv t l r Hdest.
rewrite Et in Hct.
rewrite /check_term /= in Hct.
move: Hct => /andP[/andP[/andP[/andP[Hc Hl] Hinner] Hr] Houter].
move: Hc => /andP[Hty Hmatch].
case: WFT => [_ [_ [Hconst _]]].
rewrite Hconst in Hmatch.
case Hm: (type_match (mk_fun (HTyVar NAlpha) (mk_fun (HTyVar NAlpha) bool_ty)) ty [fmap]) => [m|] in Hmatch; last by [].
have [dom Ety] := type_match_alpha_gen_inv ty m Hm.
move: Hinner Houter.
rewrite Ety /dest_fun /=.
move=> Hinner Houter.
have Edom : dom = type_of l.
  by apply/eqP.
rewrite Et Ety Edom /mk_eq /mk_comb /=.
by case: (@eqP _ (type_of l) (type_of l)) => [_ | []].
Qed.

Lemma trans_eq_rect_comp (P : HType -> Type) a b c (x : P a)
    (eab : a = b) (ebc : b = c) :
  eq_rect b P (eq_rect a P x b eab) c ebc =
  eq_rect a P x c (eq_trans eab ebc).
Proof.
move: c ebc.
case: b / eab => c ebc.
by case: c / ebc.
Qed.

Lemma transValid F thy a b th' :
  WellFormedTheory thy -> Valid F thy a -> Valid F thy b -> TRANS a b = Some th' -> Valid F thy th'.
Proof.
move=> WFT Va Vb Htrans.
split; first exact: (transWellFormed thy a b th' WFT Va.1 Vb.1 Htrans).
move=> HM tv venv.
move: Htrans; rewrite /TRANS.
case Ea: (dest_eq (thm_concl a)) => [[l m1]|] //.
case Eb: (dest_eq (thm_concl b)) => [[m2 r]|] //.
case: (@eqP _ m1 m2) => [Em |] //=.
move: Eb.
case: m2 / Em => Eb.
case Est: (combine_stamps (thm_stamp a) (thm_stamp b)) => [st|] //.
move=> [<-] Hhyps Hcc Hbc.
have [Hca [Hha0 [Hba [Hbha Hsta]]]] := Va.1.
have [Hcb [Hhb0 [Hbb [Hbstb Hstb]]]] := Vb.1.
have [Hl [Hm1 Etlm]] := check_term_dest_eq_inv thy (thm_concl a) l m1 WFT Hca Ea.
have [Hm2 [Hr Etmr]] := check_term_dest_eq_inv thy (thm_concl b) m1 r WFT Hcb Eb.
have Eca : thm_concl a = mk_eq l m1 := trans_eq_shape thy (thm_concl a) l m1 WFT Hca Ea.
have Ecb : thm_concl b = mk_eq m1 r := trans_eq_shape thy (thm_concl b) m1 r WFT Hcb Eb.
have Hha : forall h (Hch : check_term thy h) (Hbh : is_bool h), h \in thm_hyps a -> denoteProp F thy tv venv h Hch Hbh.
  move=> h Hch Hbh Hina.
  apply: (Hhyps h Hch Hbh).
  change (h \in (thm_hyps a `|` thm_hyps b)).
  by rewrite in_fsetU Hina.
have Hhb : forall h (Hch : check_term thy h) (Hbh : is_bool h), h \in thm_hyps b -> denoteProp F thy tv venv h Hch Hbh.
  move=> h Hch Hbh Hinb.
  apply: (Hhyps h Hch Hbh).
  change (h \in (thm_hyps a `|` thm_hyps b)).
  by rewrite in_fsetU Hinb orbT.
have Ha := Va.2 HM tv venv Hha.
have Hb := Vb.2 HM tv venv Hhb.
have Hpa0 := Ha Hca Hba.
have Hpa : denoteProp F thy tv venv (mk_eq l m1)
    (mkEqCheckSound thy l m1 WFT Hl Hm1 Etlm) (is_bool_mk_eq l m1).
  move: Hca Hba Hpa0.
  rewrite Eca => Hca Hba Hpa0.
  rewrite -(denoteProp_irrel F thy tv venv (mk_eq l m1) Hca
    (mkEqCheckSound thy l m1 WFT Hl Hm1 Etlm) Hba (is_bool_mk_eq l m1)).
  exact: Hpa0.
have Hpb0 := Hb Hcb Hbb.
have Hpb : denoteProp F thy tv venv (mk_eq m1 r)
    (mkEqCheckSound thy m1 r WFT Hm2 Hr Etmr) (is_bool_mk_eq m1 r).
  move: Hcb Hbb Hpb0.
  rewrite Ecb => Hcb Hbb Hpb0.
  rewrite -(denoteProp_irrel F thy tv venv (mk_eq m1 r) Hcb
    (mkEqCheckSound thy m1 r WFT Hm2 Hr Etmr) Hbb (is_bool_mk_eq m1 r)).
  exact: Hpb0.
have Elr : type_of l = type_of r by rewrite Etlm Etmr.
apply: (SafeDenote_mk_eq F thy tv venv l r Hl Hr Elr Hbc HM.1 Hcc).2.
have Epa := (SafeDenote_mk_eq F thy tv venv l m1 Hl Hm1 Etlm
  (is_bool_mk_eq l m1) HM.1 (mkEqCheckSound thy l m1 WFT Hl Hm1 Etlm)).1 Hpa.
have Epb := (SafeDenote_mk_eq F thy tv venv m1 r Hm2 Hr Etmr
  (is_bool_mk_eq m1 r) HM.1 (mkEqCheckSound thy m1 r WFT Hm2 Hr Etmr)).1 Hpb.
rewrite (SafeDenote_irrel_thy F thy thy tv venv m1 Hm2 Hm1) in Epb.
rewrite Epa Epb.
rewrite (trans_eq_rect_comp (interpType (frTyOp F) tv) (type_of r)
  (type_of m1) (type_of l) (SafeDenote F thy tv venv r Hr)
  (esym Etmr) (esym Etlm)).
by rewrite (HType_UIP _ _ (eq_trans (esym Etmr) (esym Etlm)) (esym Elr)).
Qed.

(** * EQ_MP

    [|- p = q]   [|- p]
    ---------------
         [|- q] *)
Lemma eqMp_eq_concl_is_mk_eq thy t p q :
  WellFormedTheory thy -> check_term thy t -> dest_eq t = Some (p, q) ->
  t = mk_eq p q.
Proof.
move=> WFT Hct Hde.
have [ty Et] := dest_eq_inv t p q Hde.
rewrite Et in Hct.
move: Hct; rewrite /check_term /=.
move=> /andP[/andP[/andP[/andP[Hconst Hp] Hinner] Hq] _].
move: Hinner => /andP[_ Hdom].
move: Hconst => /andP[Hty Hmatch].
have [dom Ety] : exists dom, ty = mk_fun dom (mk_fun dom bool_ty).
  move: Hmatch.
  case: WFT => [_ [_ [HNEq _]]].
  rewrite HNEq.
  case Hm: (type_match (mk_fun (HTyVar NAlpha) (mk_fun (HTyVar NAlpha) bool_ty)) ty [fmap]) => [m |] //= _.
  exact: type_match_alpha_gen_inv Hm.
have Edom : dom = type_of p.
  move: Hdom; rewrite Ety /dest_fun /=.
  by move=> /eqP.
rewrite Et Ety Edom /mk_eq /mk_comb /=.
by [].
Qed.

Lemma eqMp_eq_rect_through (Q : HType -> Type) A B C (x : Q B)
    (eAB : A = B) (eAC : A = C) (eBC : B = C) :
  eq_rect A Q (eq_rect B Q x A (esym eAB)) C eAC =
    eq_rect B Q x C eBC.
Proof.
move: eAC eBC x.
case: B / eAB => eAC eBC x.
rewrite (HType_UIP _ _ eAC eBC).
by [].
Qed.

Lemma eqMp_denoteProp_transport F thy tv venv p q
    (Hp : check_term thy p) (Hq : check_term thy q)
    (Htpq : type_of p = type_of q) (Hbp : is_bool p) (Hbq : is_bool q) :
  denoteProp F thy tv venv p Hp Hbp ->
  SafeDenote F thy tv venv p Hp =
    eq_rect (type_of q) (interpType (frTyOp F) tv) (SafeDenote F thy tv venv q Hq)
      (type_of p) (esym Htpq) ->
  denoteProp F thy tv venv q Hq Hbq.
Proof.
move=> Hdenp Hdeneq.
rewrite /denoteProp in Hdenp |-.
have Ebp : type_of p = bool_ty := elimT eqP Hbp.
rewrite (HType_UIP _ _ (elimT eqP Hbp) Ebp) in Hdenp.
rewrite Hdeneq in Hdenp.
rewrite (eqMp_eq_rect_through (interpType (frTyOp F) tv)
  (type_of p) (type_of q) bool_ty (SafeDenote F thy tv venv q Hq)
  Htpq Ebp (elimT eqP Hbq)) in Hdenp.
exact: Hdenp.
Qed.

Lemma eqMpValid F thy eqth th th' :
  WellFormedTheory thy -> Valid F thy eqth -> Valid F thy th -> EQ_MP eqth th = Some th' -> Valid F thy th'.
Proof.
move=> WFT Veq Vth Heq.
split; first exact: (eqMpWellFormed thy eqth th th' WFT Veq.1 Vth.1 Heq).
move=> HM tv venv Hhyps.
move: Hhyps.
move: Heq; rewrite /EQ_MP.
case Ee: (dest_eq (thm_concl eqth)) => [[p q]|] //.
case: (@eqP _ p (thm_concl th)) => [Epq | //] /=.
case Ecs: (combine_stamps (thm_stamp eqth) (thm_stamp th)) => [st |] //.
move=> [<-] Hhyps Hcc Hbc.
rewrite /= in Hhyps.
have [Hceq [Hheq [Hbeq [Hbheq Hdeq]]]] := Veq.1.
have [Hct [Hht [Hbt [Hbht Hdt]]]] := Vth.1.
have [Hp [Hq Etpq]] := check_term_dest_eq_inv thy (thm_concl eqth) p q WFT Hceq Ee.
have Heqterm : thm_concl eqth = mk_eq p q :=
  eqMp_eq_concl_is_mk_eq thy (thm_concl eqth) p q WFT Hceq Ee.
have HhypsEq : forall h (Hch : check_term thy h) (Hbh : is_bool h), h \in thm_hyps eqth ->
    denoteProp F thy tv venv h Hch Hbh.
  move=> h Hch Hbh Hhin.
  have HinU : h \in thm_hyps eqth `|` thm_hyps th.
    by rewrite in_fsetU; apply/orP; left.
  exact: (Hhyps h Hch Hbh HinU).
have HhypsTh : forall h (Hch : check_term thy h) (Hbh : is_bool h), h \in thm_hyps th ->
    denoteProp F thy tv venv h Hch Hbh.
  move=> h Hch Hbh Hhin.
  have HinU : h \in thm_hyps eqth `|` thm_hyps th.
    by rewrite in_fsetU; apply/orP; right.
  exact: (Hhyps h Hch Hbh HinU).
have HvalidEq := Veq.2 HM tv venv HhypsEq Hceq Hbeq.
have HvalidTh := Vth.2 HM tv venv HhypsTh Hct Hbt.
have Hmkct := mkEqCheckSound thy p q WFT Hp Hq Etpq.
have Hmkbool := is_bool_mk_eq p q.
have HvalidMKEq : denoteProp F thy tv venv (mk_eq p q) Hmkct Hmkbool.
  move: HvalidEq.
  move: Hbeq.
  move: Hceq.
  rewrite Heqterm.
  move=> Hceq Hbeq HvalidEq.
  rewrite -(denoteProp_irrel F thy tv venv (mk_eq p q) Hceq Hmkct Hbeq Hmkbool).
  exact: HvalidEq.
have HdenEq : SafeDenote F thy tv venv p Hp =
    eq_rect (type_of q) (interpType (frTyOp F) tv) (SafeDenote F thy tv venv q Hq)
      (type_of p) (esym Etpq) :=
  (SafeDenote_mk_eq F thy tv venv p q Hp Hq Etpq Hmkbool HM.1 Hmkct).1 HvalidMKEq.
have Hbp : is_bool p by rewrite Epq.
have HvalidP : denoteProp F thy tv venv p Hp Hbp.
  move: HvalidTh.
  move: Hbt.
  move: Hct.
  rewrite -Epq.
  move=> Hct Hbt HvalidTh.
  rewrite -(denoteProp_irrel F thy tv venv p Hct Hp Hbt Hbp).
  exact: HvalidTh.
have Hbq : is_bool q by exact: Hbc.
have HvalidQ : denoteProp F thy tv venv q Hq Hbq :=
  eqMp_denoteProp_transport F thy tv venv p q Hp Hq Etpq Hbp Hbq HvalidP HdenEq.
rewrite -(denoteProp_irrel F thy tv venv q Hq Hcc Hbq Hbc).
exact: HvalidQ.
Qed.

(** * DEDUCT_ANTISYM_RULE

    [A |- p]   [B |- q]
    ---------------------------------
    [(A - q) u (B - p) |- p = q]

    The genuinely propositional-logic step: mutual implication between
    [denoteProp p] and [denoteProp q] (each direction discharging the
    other's own conclusion as a hypothesis it is now entitled to use)
    gives [denoteProp p = denoteProp q] as *propositions* via
    [propositional_extensionality], which then transports back across
    the [bool_ty] cast to the [SafeDenote]-level equality
    [SafeDenote_mk_eq] needs. *)
Lemma deductAntisymValid F thy a b th' :
  WellFormedTheory thy -> Valid F thy a -> Valid F thy b ->
  DEDUCT_ANTISYM_RULE a b = Some th' -> Valid F thy th'.
Proof.
move=> WFT Hva Hvb Hrule.
split; first exact: (deductAntisymWellFormed thy a b th' WFT Hva.1 Hvb.1 Hrule).
move=> HM tv venv.
move: Hrule; rewrite /DEDUCT_ANTISYM_RULE.
case Ecs: (combine_stamps (thm_stamp a) (thm_stamp b)) => [st|] //.
move=> [<-] Hhyps Hcc Hbc.
have Hpa : check_term thy (thm_concl a) := Hva.1.1.
have Hpb : is_bool (thm_concl a) := Hva.1.2.2.1.
have Hqa : check_term thy (thm_concl b) := Hvb.1.1.
have Hqb : is_bool (thm_concl b) := Hvb.1.2.2.1.
have Hty : type_of (thm_concl a) = type_of (thm_concl b).
  by move: Hpb Hqb; rewrite /is_bool => /eqP -> /eqP ->.
apply: (SafeDenote_mk_eq F thy tv venv (thm_concl a) (thm_concl b)
  Hpa Hqa Hty Hbc HM.1 Hcc).2.
have HPQ : denoteProp F thy tv venv (thm_concl a) Hpa Hpb <->
    denoteProp F thy tv venv (thm_concl b) Hqa Hqb.
  split.
  - move=> HpaV.
    apply: (Hvb.2 HM tv venv _ Hqa Hqb) => h Hch Hbh Hin.
    case: (@eqP _ h (thm_concl a)) => [Hhp | Hne].
    + have Hph : thm_concl a = h := esym Hhp.
      clear Hhp.
      move: Hch Hbh Hin.
      case: h / Hph => Hch Hbh Hin.
      by rewrite (denoteProp_irrel F thy tv venv (thm_concl a) Hch Hpa Hbh Hpb).
    + apply: (Hhyps h Hch Hbh).
      change (h \in ((thm_hyps a `\` [fset thm_concl b]) `|`
        (thm_hyps b `\` [fset thm_concl a]))).
      rewrite in_fsetU; apply/orP; right.
      rewrite in_fsetD Hin andbT.
      apply/negP=> Hmem.
      apply: Hne.
      rewrite in_fset1 in Hmem.
      move/eqP: Hmem => HmemEq.
      exact: HmemEq.
  - move=> HqbV.
    apply: (Hva.2 HM tv venv _ Hpa Hpb) => h Hch Hbh Hin.
    case: (@eqP _ h (thm_concl b)) => [Hhq | Hne].
    + have Hqh : thm_concl b = h := esym Hhq.
      clear Hhq.
      move: Hch Hbh Hin.
      case: h / Hqh => Hch Hbh Hin.
      by rewrite (denoteProp_irrel F thy tv venv (thm_concl b) Hch Hqa Hbh Hqb).
    + apply: (Hhyps h Hch Hbh).
      change (h \in ((thm_hyps a `\` [fset thm_concl b]) `|`
        (thm_hyps b `\` [fset thm_concl a]))).
      rewrite in_fsetU; apply/orP; left.
      rewrite in_fsetD Hin andbT.
      apply/negP=> Hmem.
      apply: Hne.
      rewrite in_fset1 in Hmem.
      move/eqP: Hmem => HmemEq.
      exact: HmemEq.
have cast_bool_inj :
  forall (ty : HType) (x y : interpType (frTyOp F) tv ty) (e : ty = bool_ty),
  eq_rect ty (interpType (frTyOp F) tv) x bool_ty e =
  eq_rect ty (interpType (frTyOp F) tv) y bool_ty e -> x = y.
  move=> ty x y e.
  case: bool_ty / e => H.
  exact: H.
have cast_prop_eq :
  forall (ta tb : HType) (x : interpType (frTyOp F) tv ta)
    (y : interpType (frTyOp F) tv tb) (Ety : ta = tb)
    (Eta : ta = bool_ty) (Etb : tb = bool_ty),
  eq_rect ta (interpType (frTyOp F) tv) x bool_ty Eta =
  eq_rect tb (interpType (frTyOp F) tv) y bool_ty Etb ->
  x = eq_rect tb (interpType (frTyOp F) tv) y ta (esym Ety).
  move=> ta tb x y Ety Eta Etb.
  move: y Etb.
  case: tb / Ety => y Etb Heq.
  rewrite (HType_UIP _ _ Etb Eta) in Heq.
  exact: (cast_bool_inj ta x y Eta Heq).
have Hprop : denoteProp F thy tv venv (thm_concl a) Hpa Hpb =
    denoteProp F thy tv venv (thm_concl b) Hqa Hqb :=
  propositional_extensionality _ _ HPQ.
apply: (cast_prop_eq (type_of (thm_concl a)) (type_of (thm_concl b))
  (SafeDenote F thy tv venv (thm_concl a) Hpa)
  (SafeDenote F thy tv venv (thm_concl b) Hqa) Hty
  (elimT eqP Hpb) (elimT eqP Hqb)).
by rewrite /denoteProp in Hprop.
Qed.

(** * MK_COMB

    [|- f = g]   [|- x = y]
    ------------------------
       [|- f x = g y]

    [applyFun_transport] transports [applyFun] across the two functional
    equalities [f = g]/[x = y] (as *terms*, hence as denoted values via
    [SafeDenote_mk_eq] on each premise); [transport_sandwich] then closes
    the resulting triangle of casts between [SafeDenote (mk_comb f x)],
    [applyFun ... f x] and its [g]/[y] counterpart. *)
Lemma applyFun_transport F tv
    (A B C D : HType) (EAB : A = B) (ECD : C = D)
    (Eout : (dest_fun A).2 = (dest_fun B).2)
    (HisA : is_fun A) (HisB : is_fun B)
    (HdomA : (dest_fun A).1 = C) (HdomB : (dest_fun B).1 = D)
    (vf : interpType (frTyOp F) tv A) (vg : interpType (frTyOp F) tv B)
    (vx : interpType (frTyOp F) tv C) (vy : interpType (frTyOp F) tv D) :
  vf = eq_rect B (interpType (frTyOp F) tv) vg A (esym EAB) ->
  vx = eq_rect D (interpType (frTyOp F) tv) vy C (esym ECD) ->
  applyFun F tv A C HisA HdomA vf vx =
    eq_rect (dest_fun B).2 (interpType (frTyOp F) tv)
      (applyFun F tv B D HisB HdomB vg vy) (dest_fun A).2 (esym Eout).
Proof.
move=> Hf Hx.
case: B / EAB vg HisB HdomB Hf Eout => vg HisB HdomB Hf Eout.
case: D / ECD vy HdomB Hx => vy HdomB Hx.
rewrite (HType_UIP _ _ Eout (erefl (dest_fun A).2)).
rewrite (proof_irrelevance _ HisB HisA) (HType_UIP _ _ HdomB HdomA) Hf Hx.
by [].
Qed.

Lemma transport_sandwich F tv
    (RA RB RFA RFB : HType)
    (ERA : RA = RFA) (ERB : RB = RFB) (Eapp : RFA = RFB) (EComb : RA = RB)
    (sf : interpType (frTyOp F) tv RA) (sg : interpType (frTyOp F) tv RB)
    (af : interpType (frTyOp F) tv RFA) (ag : interpType (frTyOp F) tv RFB) :
  eq_rect RA (interpType (frTyOp F) tv) sf RFA ERA = af ->
  eq_rect RB (interpType (frTyOp F) tv) sg RFB ERB = ag ->
  af = eq_rect RFB (interpType (frTyOp F) tv) ag RFA (esym Eapp) ->
  sf = eq_rect RB (interpType (frTyOp F) tv) sg RA (esym EComb).
Proof.
move=> Hsf Hsg Happ.
move: Happ.
move: Eapp.
case: RFA / ERA af Hsf => af Hsf Eapp Happ.
move: Happ.
move: Eapp.
case: RFB / ERB ag Hsg => ag Hsg Eapp Happ.
move: Happ.
move: Eapp.
case: RB / EComb sg ag Hsg => sg ag Hsg Eapp Happ.
rewrite (HType_UIP _ _ Eapp (erefl RA)) in Happ.
have Hsf' : sf = af by move: Hsf; rewrite /=.
have Hsg' : sg = ag by move: Hsg; rewrite /=.
have Happ' : af = ag by move: Happ; rewrite /=.
by rewrite Hsf' Hsg' Happ'.
Qed.

Lemma mkCombValid F thy fth xth th' :
  WellFormedTheory thy -> Valid F thy fth -> Valid F thy xth ->
  MK_COMB fth xth = Some th' -> Valid F thy th'.
Proof.
move=> WFT Vf Vx Hmk.
split; first exact: (mkCombWellFormed thy fth xth th' WFT Vf.1 Vx.1 Hmk).
move=> HM tv venv.
have [Hcf [Hhf [Hbf [Hbhf Hdf]]]] := Vf.1.
have [Hcx [Hhx [Hbx [Hbhx Hdx]]]] := Vx.1.
move: Hmk; rewrite /MK_COMB.
case Ef: (dest_eq (thm_concl fth)) => [[f g]|] //.
case Ex: (dest_eq (thm_concl xth)) => [[x y]|] //.
have Hfconcl : thm_concl fth = mk_eq f g := trans_eq_shape thy (thm_concl fth) f g WFT Hcf Ef.
have Hxconcl : thm_concl xth = mk_eq x y := trans_eq_shape thy (thm_concl xth) x y WFT Hcx Ex.
have [Hf [Hg Efg]] := check_term_dest_eq_inv thy (thm_concl fth) f g WFT Hcf Ef.
have [Hx [Hy Exy]] := check_term_dest_eq_inv thy (thm_concl xth) x y WFT Hcx Ex.
case: ifP => [/andP[Hisfun Hdom] | //].
case Ecs: (combine_stamps (thm_stamp fth) (thm_stamp xth)) => [st | ] //.
move=> [<-] Hhyps Hcc Hbc.
have HdomE : (dest_fun (type_of f)).1 = type_of x by exact/eqP.
have Hf0 := Hf.
have Hg0 := Hg.
have Hx0 := Hx.
have Hy0 := Hy.
rewrite /check_term in Hf Hg Hx Hy.
have Hcfx : check_term thy (mk_comb f x).
  by rewrite /check_term /mk_comb /= Hf Hx Hisfun Hdom.
have Hcgy : check_term thy (mk_comb g y).
  by rewrite /check_term /mk_comb /= Hg Hy -Efg -Exy Hisfun Hdom.
have Efgx : type_of (mk_comb f x) = type_of (mk_comb g y).
  by rewrite /mk_comb /= Hisfun -Efg Hisfun.
have Hhypf :
  forall h (Hch : check_term thy h) (Hbh : is_bool h), h \in thm_hyps fth ->
    denoteProp F thy tv venv h Hch Hbh.
  move=> h Hch Hbh Hhin.
  apply: (Hhyps h Hch Hbh).
  by rewrite /= in_fsetU Hhin.
have Hdenf0 : denoteProp F thy tv venv (thm_concl fth) Hcf Hbf :=
  Vf.2 HM tv venv Hhypf Hcf Hbf.
move: Hdenf0.
move: Hcf Hbf.
case: (thm_concl fth) / (esym Hfconcl) => Hcf Hbf Hdenf0.
have Hdenf : denoteProp F thy tv venv (mk_eq f g)
    (mkEqCheckSound thy f g WFT Hf0 Hg0 Efg) (is_bool_mk_eq f g).
  rewrite -(denoteProp_irrel F thy tv venv (mk_eq f g) Hcf
    (mkEqCheckSound thy f g WFT Hf0 Hg0 Efg) Hbf (is_bool_mk_eq f g)).
  exact: Hdenf0.
have Hhypx :
  forall h (Hch : check_term thy h) (Hbh : is_bool h), h \in thm_hyps xth ->
    denoteProp F thy tv venv h Hch Hbh.
  move=> h Hch Hbh Hhin.
  apply: (Hhyps h Hch Hbh).
  by rewrite /= in_fsetU Hhin orbT.
have Hdenx0 : denoteProp F thy tv venv (thm_concl xth) Hcx Hbx :=
  Vx.2 HM tv venv Hhypx Hcx Hbx.
move: Hdenx0.
move: Hcx Hbx.
case: (thm_concl xth) / (esym Hxconcl) => Hcx Hbx Hdenx0.
have Hdenx : denoteProp F thy tv venv (mk_eq x y)
    (mkEqCheckSound thy x y WFT Hx0 Hy0 Exy) (is_bool_mk_eq x y).
  rewrite -(denoteProp_irrel F thy tv venv (mk_eq x y) Hcx
    (mkEqCheckSound thy x y WFT Hx0 Hy0 Exy) Hbx (is_bool_mk_eq x y)).
  exact: Hdenx0.
have Hfg : SafeDenote F thy tv venv f Hf0 =
    eq_rect (type_of g) (interpType (frTyOp F) tv)
      (SafeDenote F thy tv venv g Hg0) (type_of f) (esym Efg).
  apply: (SafeDenote_mk_eq F thy tv venv f g Hf0 Hg0 Efg
    (is_bool_mk_eq f g) HM.1 (mkEqCheckSound thy f g WFT Hf0 Hg0 Efg)).1.
  exact: Hdenf.
have Hxy : SafeDenote F thy tv venv x Hx0 =
    eq_rect (type_of y) (interpType (frTyOp F) tv)
      (SafeDenote F thy tv venv y Hy0) (type_of x) (esym Exy).
  apply: (SafeDenote_mk_eq F thy tv venv x y Hx0 Hy0 Exy
    (is_bool_mk_eq x y) HM.1 (mkEqCheckSound thy x y WFT Hx0 Hy0 Exy)).1.
  exact: Hdenx.
apply: (SafeDenote_mk_eq F thy tv venv (mk_comb f x) (mk_comb g y)
  Hcfx Hcgy Efgx Hbc HM.1 Hcc).2.
have Hcomb_f := SafeDenote_comb F thy tv venv f x Hisfun HdomE Hf0 Hx0 Hcfx.
have Hisfung : is_fun (type_of g) by rewrite -Efg.
have Hdomg : (dest_fun (type_of g)).1 = type_of y by rewrite -Efg -Exy.
have Hcomb_g := SafeDenote_comb F thy tv venv g y Hisfung Hdomg Hg0 Hy0 Hcgy.
have Eapp : (dest_fun (type_of f)).2 = (dest_fun (type_of g)).2 by rewrite -Efg.
have Happ := applyFun_transport F tv (type_of f) (type_of g) (type_of x) (type_of y)
  Efg Exy Eapp Hisfun Hisfung HdomE Hdomg
  (SafeDenote F thy tv venv f Hf0) (SafeDenote F thy tv venv g Hg0)
  (SafeDenote F thy tv venv x Hx0) (SafeDenote F thy tv venv y Hy0) Hfg Hxy.
exact: (transport_sandwich F tv
  (type_of (mk_comb f x)) (type_of (mk_comb g y))
  (dest_fun (type_of f)).2 (dest_fun (type_of g)).2
  (type_of_mk_comb_isfun f x Hisfun) (type_of_mk_comb_isfun g y Hisfung)
  Eapp Efgx
  (SafeDenote F thy tv venv (mk_comb f x) Hcfx)
  (SafeDenote F thy tv venv (mk_comb g y) Hcgy)
  (applyFun F tv (type_of f) (type_of x) Hisfun HdomE
     (SafeDenote F thy tv venv f Hf0) (SafeDenote F thy tv venv x Hx0))
  (applyFun F tv (type_of g) (type_of y) Hisfung Hdomg
     (SafeDenote F thy tv venv g Hg0) (SafeDenote F thy tv venv y Hy0))
  Hcomb_f Hcomb_g Happ).
Qed.

(** * INST

    Free-variable instantiation semantics: [venv_inst] substitutes,
    for each [FVar], its [theta]-supplied replacement's denotation (or
    falls back to the ambient [venv] when [theta] does not mention that
    variable) -- the semantic analogue of [inst_fvar]. Built directly
    by structural recursion on [theta] (mirroring [inst_fvar_lookup]'s
    own recursion) rather than via [ssreflect]'s [have], so it stays a
    transparent, computable definition instead of an opaque
    [ssr_have_upoly]-wrapped one. *)
Lemma in_cons_widen (T : eqType) (a : T) (s : seq T) (y : T) :
  y \in s -> y \in a :: s.
Proof. move=> Hy; by rewrite in_cons Hy orbT. Qed.

Fixpoint venv_inst (F : Frame) (thy : Theory) (tv : Name -> {T : Type & T})
    (theta : seq (Term * FVar))
    (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v))
    {struct theta} :
    (forall rep v, (rep, v) \in theta -> check_term thy rep /\ type_of rep = fv_ty v) ->
    forall v : FVar, interpType (frTyOp F) tv (fv_ty v).
Proof.
case: theta => [| [rep x] rest] Htheta v.
- exact: (venv v).
- case: (@eqP _ x v) => [Exv | Hne].
  + move: (Htheta rep x (mem_head (rep, x) rest)) => [Hcheck Etype].
    move: Etype; rewrite Exv => Etype.
    exact: (eq_rect (type_of rep) (interpType (frTyOp F) tv)
      (SafeDenote F thy tv venv rep Hcheck) (fv_ty v) Etype).
  + exact: (venv_inst F thy tv rest venv
      (fun rep0 v0 Hin => Htheta rep0 v0 (in_cons_widen _ (rep, x) rest (rep0, v0) Hin)) v).
Defined.

Lemma venv_inst_none F thy tv theta venv Htheta v :
  inst_fvar_lookup theta v 0 = None ->
  venv_inst F thy tv theta venv Htheta v = venv v.
Proof.
elim: theta Htheta => [| [rep x] rest IH] Htheta //=.
case: (@eqP _ x v) => [Exv | Hne] //=.
move=> Hlook.
exact: IH.
Qed.

Lemma SafeDenote_congr F thy tv venv t1 t2 (Et : t1 = t2)
    (H1 : check_term thy t1) (H2 : check_term thy t2) ty
    (E1 : type_of t1 = ty) (E2 : type_of t2 = ty) :
  eq_rect (type_of t1) (interpType (frTyOp F) tv) (SafeDenote F thy tv venv t1 H1) ty E1 =
  eq_rect (type_of t2) (interpType (frTyOp F) tv) (SafeDenote F thy tv venv t2 H2) ty E2.
Proof.
move: H2 E2. case: t2 / Et => H2 E2.
by rewrite (proof_irrelevance _ H1 H2) (HType_UIP _ _ E1 E2).
Qed.

Lemma venv_inst_some F thy tv theta venv Htheta v rep
    (Hcheck : check_term thy rep) (Etype : type_of rep = fv_ty v)
    (Hlook : inst_fvar_lookup theta v 0 = Some rep) :
  venv_inst F thy tv theta venv Htheta v =
    eq_rect (type_of rep) (interpType (frTyOp F) tv)
      (SafeDenote F thy tv venv rep Hcheck) (fv_ty v) Etype.
Proof.
elim: theta Htheta Hlook => [| [rep0 x] rest IH] Htheta //=.
case: (@eqP _ x v) => [Exv | Hne].
- case=> Erep0.
  move: (Htheta rep0 x (mem_head (rep0, x) rest)) => [Hcheck0 Etype0].
  clear IH.
  move: Etype.
  case: v / Exv => Etype.
  exact: (SafeDenote_congr F thy tv venv rep0 rep Erep0 Hcheck0 Hcheck (fv_ty x) Etype0 Etype).
- exact: IH.
Qed.

Lemma inst_fvar_lookup0_mem theta v rep :
  inst_fvar_lookup theta v 0 = Some rep -> (rep, v) \in theta.
Proof.
elim: theta => [| [rep0 x] rest IH] //=.
case: (@eqP _ x v) => [-> | Hne].
- move=> [<-]; by rewrite in_cons eqxx.
- move=> /IH Hin; by rewrite in_cons Hin orbT.
Qed.

Lemma inst_fvar_lookup_depth theta w depth :
  inst_fvar_lookup theta w depth =
  omap (fun rep => if depth == 0 then rep else shift (Z.of_nat depth) 0 rep) (inst_fvar_lookup theta w 0).
Proof.
elim: theta => [| [rep x] rest IH] //=.
case E: (x == w) => //=.
Qed.
Fixpoint denv_app (F : Frame) (tv : Name -> {T : Type & T}) (env1 env2 : seq HType)
    (d1 : DEnv F tv env1) (d2 : DEnv F tv env2) {struct d1} : DEnv F tv (env1 ++ env2).
Proof.
case: d1 => [| ty env1' x d1'].
- exact: d2.
- exact: (DEnvCons F tv ty (env1' ++ env2) x (denv_app F tv env1' env2 d1' d2)).
Defined.

Lemma lt_size0_false i : i < size ([::] : seq HType) -> False.
Proof. by rewrite ltn0. Qed.

Fixpoint dnth_denv_app (F : Frame) (tv : Name -> {T : Type & T}) (env1 : seq HType)
    (d1 : DEnv F tv env1) {struct d1} :
    forall (env2 : seq HType) (d2 : DEnv F tv env2) i
      (Hi : i < size env1) (Hi' : i < size (env1 ++ env2))
      (E : nth (HTyVar NAlpha) (env1 ++ env2) i =
           nth (HTyVar NAlpha) env1 i),
    eq_rect (nth (HTyVar NAlpha) (env1 ++ env2) i) (interpType (frTyOp F) tv)
      (dnth F tv (env1 ++ env2) (denv_app F tv env1 env2 d1 d2) i Hi')
      (nth (HTyVar NAlpha) env1 i) E =
    dnth F tv env1 d1 i Hi.
Proof.
elim: d1 => [|ty env0 x d0 IH].
- move=> env2 d2 [|i] Hi Hi' E.
  + exact: False_rect _ (lt_size0_false 0 Hi).
  + exact: False_rect _ (lt_size0_false i.+1 Hi).
move=> env2 d2 [|i] Hi Hi' E.
- rewrite (proof_irrelevance _ E (erefl ty)).
  exact: erefl.
exact: (IH env2 d2 i Hi Hi' E).
Defined.

Lemma eq_rect_transport (T : Type) (P : T -> Type) A B C
    (x : P A) (y : P B) (e : A = B) (e1 : A = C) (e2 : B = C) :
  eq_rect A P x B e = y ->
  eq_rect A P x C e1 = eq_rect B P y C e2.
Proof.
move=> H.
move: y H e1 e2.
case: B / e => y H e1 e2.
move: y H e2.
case: C / e1 => y H e2.
rewrite (proof_irrelevance _ e2 (erefl A)).
by [].
Qed.

Lemma eq_rect_bvar_cast (T : Type) (P : T -> Type) A B C
    (x : P A) (e : B = C) (d : B = A) :
  eq_rect B (fun z => P z -> P C)
    (eq_rect_r (fun z => P z -> P C) id e) A d x =
  eq_rect A P x C (eq_trans (esym d) e).
Proof.
destruct e.
destruct d.
reflexivity.
Qed.

Lemma eq_rect_injective (T : Type) (P : T -> Type) (A B : T)
    (x y : P A) (e : A = B) :
  eq_rect A P x B e = eq_rect A P y B e -> x = y.
Proof. move: y. by case: B / e. Qed.


Lemma denote_checked_prefix_irrel F thy tv venv :
  forall t env1 (d1 : DEnv F tv env1) env2 (d2 : DEnv F tv env2)
    (Hct : check_open_term thy t env1)
    (Hwt1 : WellTypedShape t (env1 ++ env2))
    (Hwt2 : WellTypedShape t env1),
  denote F tv venv (env1 ++ env2) (denv_app F tv env1 env2 d1 d2) t Hwt1 =
  denote F tv venv env1 d1 t Hwt2.
Proof.
move=> t.
elim: t => [v | i ty | n ty | f IHf x IHx | aty b IHb] env1 d1 env2 d2 Hct Hwt1 Hwt2.
- rewrite (denote_irrel F tv venv (env1 ++ env2)
    (denv_app F tv env1 env2 d1 d2) (TmFVar v) Hwt1 I).
  rewrite (denote_irrel F tv venv env1 d1 (TmFVar v) Hwt2 I).
  by [].
- move: Hct Hwt1 Hwt2 => /andP[/andP[Hlt Heq] _] [Hlt1 Hnth1] [Hlt2 Hnth2].
  have Hnth : nth ty env1 i = ty by exact/eqP.
  have Hltapp : i < size (env1 ++ env2).
    by rewrite size_cat; exact: ltn_addr (size env2) Hlt.
  have Hnthapp : nth ty (env1 ++ env2) i = ty.
    by rewrite nth_cat Hlt.
  have Eapp : nth (HTyVar NAlpha) (env1 ++ env2) i =
      nth (HTyVar NAlpha) env1 i by rewrite nth_cat Hlt.
  have Hlookup := dnth_denv_app F tv env1 d1 env2 d2 i Hlt Hltapp Eapp.
  have Eleft : nth (HTyVar NAlpha) (env1 ++ env2) i = ty.
    by rewrite -(set_nth_default (HTyVar NAlpha) ty Hltapp) Hnthapp.
  have Eright : nth (HTyVar NAlpha) env1 i = ty.
    by rewrite -(set_nth_default (HTyVar NAlpha) ty Hlt) Hnth.
  have Htyped := eq_rect_transport HType (interpType (frTyOp F) tv)
    _ _ ty _ _ Eapp Eleft Eright Hlookup.
  rewrite (denote_irrel F tv venv (env1 ++ env2)
    (denv_app F tv env1 env2 d1 d2) (TmBVar i ty) (conj Hlt1 Hnth1)
    (conj Hltapp Hnthapp)).
  rewrite (denote_irrel F tv venv env1 d1 (TmBVar i ty) (conj Hlt2 Hnth2)
    (conj Hlt Hnth)).
  rewrite /denote /=.
  rewrite (eq_rect_bvar_cast HType (interpType (frTyOp F) tv) _ _ ty
    (dnth F tv (env1 ++ env2) (denv_app F tv env1 env2 d1 d2) i Hltapp)
    Hnthapp (set_nth_default (HTyVar NAlpha) ty Hltapp)).
  rewrite (eq_rect_bvar_cast HType (interpType (frTyOp F) tv) _ _ ty
    (dnth F tv env1 d1 i Hlt) Hnth
    (set_nth_default (HTyVar NAlpha) ty Hlt)).
  have Eleft' : eq_trans
    (esym (set_nth_default (HTyVar NAlpha) ty Hltapp)) Hnthapp = Eleft
    := proof_irrelevance _ _ _.
  have Eright' : eq_trans
    (esym (set_nth_default (HTyVar NAlpha) ty Hlt)) Hnth = Eright
    := proof_irrelevance _ _ _.
  rewrite Eleft' Eright'.
  exact: Htyped.
- rewrite (denote_irrel F tv venv (env1 ++ env2)
    (denv_app F tv env1 env2 d1 d2) (TmConst n ty) Hwt1 I).
  rewrite (denote_irrel F tv venv env1 d1 (TmConst n ty) Hwt2 I).
  by [].
- move: Hct => /andP[/andP[Hf Hx] _].
  have Hfun1 := Hwt1.2.2.1.
  have Heq1 := Hwt1.2.2.2.
  have E1 := denote_comb F tv venv (env1 ++ env2)
    (denv_app F tv env1 env2 d1 d2) f x Hfun1 Heq1
    Hwt1.1 Hwt1.2.1 Hwt1.
  have E2 := denote_comb F tv venv env1 d1 f x Hfun1 Heq1
    Hwt2.1 Hwt2.2.1 Hwt2.
  apply: (eq_rect_injective HType (interpType (frTyOp F) tv)
    (type_of (TmComb f x)) (dest_fun (type_of f)).2
    _ _ (type_of_mk_comb_isfun f x Hfun1)).
  rewrite E1 E2.
  exact: (f_equal2 (applyFun F tv (type_of f) (type_of x) Hfun1 Heq1)
    (IHf env1 d1 env2 d2 Hf Hwt1.1 Hwt2.1)
    (IHx env1 d1 env2 d2 Hx Hwt1.2.1 Hwt2.2.1)).
- move: Hct Hwt1 Hwt2 => /andP[_ Hb] Hwb1 Hwb2.
  apply: functional_extensionality => a.
  exact: (IHb (aty :: env1) (DEnvCons F tv aty env1 a d1) env2 d2 Hb Hwb1 Hwb2).
Qed.

Lemma denote_closed_env_indep F thy tv venv env d t
    (Hct : check_term thy t) (Hwt : WellTypedShape t env) :
  denote F tv venv env d t Hwt = SafeDenote F thy tv venv t Hct.
Proof.
have Hwt0 := check_open_term_WellTypedShape thy t [::] Hct.
have H := denote_checked_prefix_irrel F thy tv venv t [::]
  (DEnvNil F tv) env d Hct Hwt Hwt0.
rewrite /= in H.
rewrite /SafeDenote.
rewrite -(denote_irrel F tv venv [::] (DEnvNil F tv) t Hwt0
  (check_open_term_WellTypedShape thy t [::] Hct)).
exact: H.
Qed.

Lemma inst_fvar_lookup_closed thy theta
    (Htheta : forall rep v, (rep, v) \in theta ->
      check_term thy rep /\ type_of rep = fv_ty v)
    v depth :
  inst_fvar_lookup theta v depth = inst_fvar_lookup theta v 0.
Proof.
rewrite inst_fvar_lookup_depth.
case E: (inst_fvar_lookup theta v 0) => [rep|] //=.
have Hin := inst_fvar_lookup0_mem theta v rep E.
have [Hrep _] := Htheta rep v Hin.
case: (depth == 0) => //=.
by rewrite (shift_check_id thy (Z.of_nat depth) 0 rep [::]) //=.
Qed.

Lemma theta_check_open thy (theta : seq (Term * FVar))
    (Htheta : forall rep v, (rep, v) \in theta ->
      check_term thy rep /\ type_of rep = fv_ty v) :
  forall rep v, (rep, v) \in theta ->
    check_open_term thy rep [::] /\ type_of rep = fv_ty v.
Proof. by move=> rep v Hin; exact: (Htheta rep v Hin). Qed.

Lemma denote_inst_fvar_fvar F thy tv venv theta
    (Htheta : forall rep v, (rep, v) \in theta ->
      check_term thy rep /\ type_of rep = fv_ty v)
    env d depth v
    (Hwt : WellTypedShape (TmFVar v) env)
    (Hwt' : WellTypedShape (inst_fvar_go theta (TmFVar v) depth) env)
    (Ety : type_of (inst_fvar_go theta (TmFVar v) depth) = fv_ty v) :
  eq_rect (type_of (inst_fvar_go theta (TmFVar v) depth))
    (interpType (frTyOp F) tv)
    (denote F tv venv env d (inst_fvar_go theta (TmFVar v) depth) Hwt')
    (fv_ty v) Ety =
  venv_inst F thy tv theta venv Htheta v.
Proof.
case E0: (inst_fvar_lookup theta v 0) => [rep|].
- have Ed : inst_fvar_lookup theta v depth = Some rep.
    rewrite inst_fvar_lookup_depth E0 /=.
    case: (depth == 0) => //=.
    have Hin := inst_fvar_lookup0_mem theta v rep E0.
    have [Hrep _] := Htheta rep v Hin.
    by rewrite (shift_check_id thy (Z.of_nat depth) 0 rep [::]) //=.
  move: Hwt Hwt' Ety.
  rewrite /inst_fvar_go Ed /=.
  move=> Hwt Hwt' Ety.
  have Hin := inst_fvar_lookup0_mem theta v rep E0.
  have [Hrep Erep] := Htheta rep v Hin.
  rewrite (denote_closed_env_indep F thy tv venv env d rep Hrep Hwt').
  rewrite (HType_UIP _ _ Ety Erep).
  rewrite (venv_inst_some F thy tv theta venv Htheta v rep Hrep Erep E0).
  have Ep : Hrep = (Htheta rep v Hin).1.
    apply: proof_irrelevance.
  have Et : Erep = (Htheta rep v Hin).2.
    apply: proof_irrelevance.
  by rewrite Ep Et.
- have Ed : inst_fvar_lookup theta v depth = None.
    by rewrite inst_fvar_lookup_depth E0 /=.
  move: Hwt Hwt' Ety.
  rewrite /inst_fvar_go Ed /=.
  move=> Hwt Hwt' Ety.
  rewrite (venv_inst_none F thy tv theta venv Htheta v E0).
  by rewrite (HType_UIP _ _ Ety (erefl (fv_ty v))).
Qed.

Lemma cast_reverse (A : Type) (P : A -> Type) a b
    (x : P a) (y : P b) (E : a = b) :
  x = eq_rect b P y a (esym E) ->
  eq_rect a P x b E = y.
Proof.
move=> H.
move: y H.
case: b / E => y H.
by rewrite /= in H; exact: H.
Qed.

Lemma cast_forward_reverse (A : Type) (P : A -> Type) a b
    (x : P a) (y : P b) (E : a = b) :
  eq_rect a P x b E = y ->
  x = eq_rect b P y a (esym E).
Proof.
move=> H.
move: y H.
case: b / E => y H.
by rewrite /= in H; exact: H.
Qed.

Lemma abs_transport F tv aty A B (E : A = B)
    (f : interpType (frTyOp F) tv (mk_fun aty A))
    (g : interpType (frTyOp F) tv (mk_fun aty B)) :
  (forall a, eq_rect A (interpType (frTyOp F) tv) (f a) B E = g a) ->
  eq_rect (mk_fun aty A) (interpType (frTyOp F) tv) f (mk_fun aty B)
    (f_equal (mk_fun aty) E) = g.
Proof.
move=> H.
move: g H.
case: B / E => g H.
rewrite /=.
apply: functional_extensionality => a.
exact: (H a).
Qed.

Lemma denote_inst_fvar F thy tv venv theta
    (Htheta : forall rep v, (rep, v) \in theta ->
      check_term thy rep /\ type_of rep = fv_ty v) :
  forall t env d (Hct : check_open_term thy t env)
    (HctI : check_open_term thy (inst_fvar_go theta t (size env)) env)
    (Hwt : WellTypedShape t env)
    (HwtI : WellTypedShape (inst_fvar_go theta t (size env)) env)
    (Et : type_of (inst_fvar_go theta t (size env)) = type_of t),
  eq_rect (type_of (inst_fvar_go theta t (size env)))
    (interpType (frTyOp F) tv)
    (denote F tv venv env d (inst_fvar_go theta t (size env)) HwtI)
    (type_of t) Et =
  denote F tv (venv_inst F thy tv theta venv Htheta) env d t Hwt.
Proof.
have HthetaO := theta_check_open thy theta Htheta.
elim=> [v | i ty | n ty | f IHf x IHx | aty b IHb] env d Hct HctI Hwt HwtI Et.
- exact: (denote_inst_fvar_fvar F thy tv venv theta Htheta env d (size env) v Hwt HwtI Et).
- rewrite (HType_UIP _ _ Et (erefl ty)).
  exact: (denote_irrel F tv venv env d (TmBVar i ty) HwtI Hwt).
- rewrite (HType_UIP _ _ Et (erefl (type_of (TmConst n ty)))).
  exact: (denote_irrel F tv venv env d (TmConst n ty) HwtI Hwt).
- have /andP[/andP[Hf Hx] Hdom] := Hct.
  have /andP[/andP[HfI HxI] HdomI] := HctI.
  have [Hwf [Hwx [Hfun Heq]]] := Hwt.
  have [Etf HcfI] := inst_fvar_check thy theta env f HthetaO Hf.
  have [Etx HcxI] := inst_fvar_check thy theta env x HthetaO Hx.
  have HwfI := check_open_term_WellTypedShape thy
    (inst_fvar_go theta f (size env)) env HcfI.
  have HwxI := check_open_term_WellTypedShape thy
    (inst_fvar_go theta x (size env)) env HcxI.
  have HwtIC := check_open_term_WellTypedShape thy
    (TmComb (inst_fvar_go theta f (size env))
      (inst_fvar_go theta x (size env))) env HctI.
  rewrite (denote_irrel F tv venv env d
    (TmComb (inst_fvar_go theta f (size env))
      (inst_fvar_go theta x (size env))) HwtI HwtIC).
  have [_ [_ [HfunI HeqI]]] := HwtIC.
  have EI := denote_comb F tv venv env d
    (inst_fvar_go theta f (size env)) (inst_fvar_go theta x (size env))
    HfunI HeqI HwfI HwxI HwtIC.
  have EO := denote_comb F tv (venv_inst F thy tv theta venv Htheta) env d f x
    Hfun Heq Hwf Hwx Hwt.
  have Eapp : (dest_fun (type_of (inst_fvar_go theta f (size env)))).2 =
      (dest_fun (type_of f)).2.
    by rewrite Etf.
  have Hdenf := cast_forward_reverse HType (interpType (frTyOp F) tv)
    (type_of (inst_fvar_go theta f (size env))) (type_of f)
    (denote F tv venv env d (inst_fvar_go theta f (size env)) HwfI)
    (denote F tv (venv_inst F thy tv theta venv Htheta) env d f Hwf)
    Etf (IHf env d Hf HcfI Hwf HwfI Etf).
  have Hdenx := cast_forward_reverse HType (interpType (frTyOp F) tv)
    (type_of (inst_fvar_go theta x (size env))) (type_of x)
    (denote F tv venv env d (inst_fvar_go theta x (size env)) HwxI)
    (denote F tv (venv_inst F thy tv theta venv Htheta) env d x Hwx)
    Etx (IHx env d Hx HcxI Hwx HwxI Etx).
  have Happ := applyFun_transport F tv
    (type_of (inst_fvar_go theta f (size env))) (type_of f)
    (type_of (inst_fvar_go theta x (size env))) (type_of x)
    Etf Etx Eapp HfunI Hfun HeqI Heq
    (denote F tv venv env d (inst_fvar_go theta f (size env)) HwfI)
    (denote F tv (venv_inst F thy tv theta venv Htheta) env d f Hwf)
    (denote F tv venv env d (inst_fvar_go theta x (size env)) HwxI)
    (denote F tv (venv_inst F thy tv theta venv Htheta) env d x Hwx)
    Hdenf Hdenx.
  have Hsand := transport_sandwich F tv
    (type_of (TmComb (inst_fvar_go theta f (size env))
      (inst_fvar_go theta x (size env)))) (type_of (TmComb f x))
    (dest_fun (type_of (inst_fvar_go theta f (size env)))).2
    (dest_fun (type_of f)).2
    (type_of_mk_comb_isfun (inst_fvar_go theta f (size env))
      (inst_fvar_go theta x (size env)) HfunI)
    (type_of_mk_comb_isfun f x Hfun)
    Eapp Et
    (denote F tv venv env d
      (TmComb (inst_fvar_go theta f (size env))
        (inst_fvar_go theta x (size env))) HwtIC)
    (denote F tv (venv_inst F thy tv theta venv Htheta) env d
      (TmComb f x) Hwt)
    (applyFun F tv (type_of (inst_fvar_go theta f (size env)))
      (type_of (inst_fvar_go theta x (size env))) HfunI HeqI
      (denote F tv venv env d (inst_fvar_go theta f (size env)) HwfI)
      (denote F tv venv env d (inst_fvar_go theta x (size env)) HwxI))
    (applyFun F tv (type_of f) (type_of x) Hfun Heq
      (denote F tv (venv_inst F thy tv theta venv Htheta) env d f Hwf)
      (denote F tv (venv_inst F thy tv theta venv Htheta) env d x Hwx))
    EI EO Happ.
  exact: (cast_reverse HType (interpType (frTyOp F) tv)
    (type_of (TmComb (inst_fvar_go theta f (size env))
      (inst_fvar_go theta x (size env)))) (type_of (TmComb f x))
    (denote F tv venv env d
      (TmComb (inst_fvar_go theta f (size env))
        (inst_fvar_go theta x (size env))) HwtIC)
    (denote F tv (venv_inst F thy tv theta venv Htheta) env d
      (TmComb f x) Hwt) Et Hsand).
- have /andP[Haty Hb] := Hct.
  have [Etb HcbI] := inst_fvar_check thy theta (aty :: env) b HthetaO Hb.
  rewrite /= in Etb HcbI.
  have Hwb : WellTypedShape b (aty :: env) := Hwt.
  have Hwbi := check_open_term_WellTypedShape thy
    (inst_fvar_go theta b (size env).+1) (aty :: env) HcbI.
  have HwabsI := check_open_term_WellTypedShape thy
    (TmAbs aty (inst_fvar_go theta b (size env).+1)) env HctI.
  rewrite (denote_irrel F tv venv env d
    (TmAbs aty (inst_fvar_go theta b (size env).+1)) HwtI HwabsI).
  have Eabs : type_of (TmAbs aty (inst_fvar_go theta b (size env).+1)) =
      type_of (TmAbs aty b) :=
    f_equal (mk_fun aty) Etb.
  rewrite (HType_UIP _ _ Et Eabs).
  rewrite /inst_fvar_go (HType_UIP _ _ Eabs (f_equal (mk_fun aty) Etb)).
  apply: (abs_transport F tv aty
    (type_of (inst_fvar_go theta b (size env).+1)) (type_of b) Etb).
  move=> a.
  rewrite (denote_abs F tv venv env d aty
    (inst_fvar_go theta b (size env).+1) HwabsI).
  rewrite (denote_abs F tv (venv_inst F thy tv theta venv Htheta) env d aty b Hwt).
  rewrite (denote_irrel F tv venv (aty :: env)
    (DEnvCons F tv aty env a d)
    (inst_fvar_go theta b (size env).+1) HwabsI Hwbi).
  rewrite (denote_irrel F tv (venv_inst F thy tv theta venv Htheta) (aty :: env)
    (DEnvCons F tv aty env a d) b Hwt Hwb).
  exact: (IHb (aty :: env) (DEnvCons F tv aty env a d) Hb HcbI Hwb Hwbi Etb).
Qed.

Lemma denoteProp_inst_fvar F thy tv venv theta
    (Htheta : forall rep v, (rep, v) \in theta ->
      check_term thy rep /\ type_of rep = fv_ty v)
    t (Hct : check_term thy t)
    (HctI : check_term thy (inst_fvar theta t))
    (Hbt : is_bool t) (HbtI : is_bool (inst_fvar theta t))
    (Et : type_of (inst_fvar theta t) = type_of t) :
  denoteProp F thy tv venv (inst_fvar theta t) HctI HbtI =
  denoteProp F thy tv (venv_inst F thy tv theta venv Htheta) t Hct Hbt.
Proof.
have Hwt := check_open_term_WellTypedShape thy t [::] Hct.
have HwtI := check_open_term_WellTypedShape thy (inst_fvar theta t) [::] HctI.
have Hden := denote_inst_fvar F thy tv venv theta Htheta t [::]
  (DEnvNil F tv) Hct HctI Hwt HwtI Et.
have HdenS :
  eq_rect (type_of (inst_fvar theta t)) (interpType (frTyOp F) tv)
    (SafeDenote F thy tv venv (inst_fvar theta t) HctI) (type_of t) Et =
  SafeDenote F thy tv (venv_inst F thy tv theta venv Htheta) t Hct.
  rewrite /SafeDenote.
  rewrite (denote_irrel F tv venv [::] (DEnvNil F tv) (inst_fvar theta t)
    (check_open_term_WellTypedShape thy (inst_fvar theta t) [::] HctI) HwtI).
  rewrite (denote_irrel F tv (venv_inst F thy tv theta venv Htheta)
    [::] (DEnvNil F tv) t
    (check_open_term_WellTypedShape thy t [::] Hct) Hwt).
  exact: Hden.
rewrite /denoteProp.
exact: (eq_rect_transport HType (interpType (frTyOp F) tv)
  (type_of (inst_fvar theta t)) (type_of t) bool_ty
  (SafeDenote F thy tv venv (inst_fvar theta t) HctI)
  (SafeDenote F thy tv (venv_inst F thy tv theta venv Htheta) t Hct)
  Et (elimT eqP HbtI) (elimT eqP Hbt) HdenS).
Qed.

Lemma instValid F thy theta th th' :
  WellFormedTheory thy -> Valid F thy th ->
  INST thy theta th = Some th' -> Valid F thy th'.
Proof.
move=> WFT Vth Hinst.
split; first exact: (instWellFormed thy theta th th' WFT Vth.1 Hinst).
move=> HM tv venv.
move: Hinst; rewrite /INST.
case: ifP => [/andP[_ Hall] | //].
move=> [<-] Hhyps Hcc Hbc.
have [Hct [Hht [Hbt [Hbht Hstamp]]]] := Vth.1.
have Htheta : forall rep v, (rep, v) \in theta ->
    check_term thy rep /\ type_of rep = fv_ty v.
  move=> rep v Hin.
  move: Hall => /allP /(_ (rep, v) Hin) /= /andP[Hrep Hty].
  by split=> //; exact/eqP.
have HthetaO := theta_check_open thy theta Htheta.
have Horig :
  forall h (Hch : check_term thy h) (Hbh : is_bool h), h \in thm_hyps th ->
    denoteProp F thy tv (venv_inst F thy tv theta venv Htheta) h Hch Hbh.
  move=> h Hch Hbh Hhin.
  have [Et HchI] := inst_fvar_check thy theta [::] h HthetaO Hch.
  have HbhI : is_bool (inst_fvar theta h).
    by move: Hbh; rewrite /is_bool Et.
  have Hinsthyp := Hhyps (inst_fvar theta h) HchI HbhI.
  have Him : inst_fvar theta h \in inst_fvar theta @` (thm_hyps th).
    apply/imfsetP.
    by exists h.
  move: (Hinsthyp Him).
  rewrite (denoteProp_inst_fvar F thy tv venv theta Htheta h Hch HchI Hbh HbhI Et).
  by [].
have [Etconcl HccI] := inst_fvar_check thy theta [::] (thm_concl th) HthetaO Hct.
have Hden := Vth.2 HM tv (venv_inst F thy tv theta venv Htheta)
  Horig Hct Hbt.
rewrite (denoteProp_inst_fvar F thy tv venv theta Htheta (thm_concl th)
  Hct Hcc Hbt Hbc Etconcl).
exact: Hden.
Qed.

Definition venv_upd (F : Frame) (tv : Name -> {T : Type & T})
    (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v))
    (v0 : FVar) (a0 : interpType (frTyOp F) tv (fv_ty v0))
    : forall v : FVar, interpType (frTyOp F) tv (fv_ty v) :=
  fun v =>
    match FVar_eqP v v0 with
    | ReflectT Heq =>
        eq_rect_r (fun v1 => interpType (frTyOp F) tv (fv_ty v1)) a0 Heq
    | ReflectF _ => venv v
    end.

Lemma venv_upd_same F tv venv v0 a0 :
  venv_upd F tv venv v0 a0 v0 = a0.
Proof.
rewrite /venv_upd.
case: FVar_eqP => [Heq|Hne] //=.
by rewrite (proof_irrelevance _ Heq (erefl v0)).
Qed.

Lemma venv_upd_other F tv venv v0 a0 v : v <> v0 ->
  venv_upd F tv venv v0 a0 v = venv v.
Proof. by move=> Hne; rewrite /venv_upd; case: FVar_eqP. Qed.

Fixpoint DEnv_snoc F tv env (d : DEnv F tv env) ty
    (x : interpType (frTyOp F) tv ty) : DEnv F tv (rcons env ty) :=
  match d in DEnv _ _ e return DEnv F tv (rcons e ty) with
  | DEnvNil => DEnvCons F tv ty [::] x (DEnvNil F tv)
  | DEnvCons ty0 e x0 d0 =>
      DEnvCons F tv ty0 (rcons e ty) x0 (DEnv_snoc F tv e d0 ty x)
  end.

Lemma dnth_snoc F tv env d ty x i (Hi : i < size env)
    (Hi' : i < size (rcons env ty))
    (Hnth : nth (HTyVar NAlpha) (rcons env ty) i =
            nth (HTyVar NAlpha) env i) :
  eq_rect (nth (HTyVar NAlpha) (rcons env ty) i)
    (interpType (frTyOp F) tv)
    (dnth F tv (rcons env ty) (DEnv_snoc F tv env d ty x) i Hi')
    (nth (HTyVar NAlpha) env i) Hnth =
  dnth F tv env d i Hi.
Proof.
move: i Hi Hi' Hnth.
elim: d => [|ty0 env0 x0 d IH] i Hi Hi' Hnth.
- move: Hi Hi' Hnth; case: i => [|i] //=.
- move: Hi Hi' Hnth; case: i => [|i] Hi Hi' Hnth /=.
  + by rewrite (proof_irrelevance _ Hnth (erefl ty0)).
  + exact: IH.
Qed.

Lemma dnth_snoc_last F tv env d ty x
    (Hlt : size env < size (rcons env ty))
    (Hnth : nth (HTyVar NAlpha) (rcons env ty) (size env) = ty) :
  eq_rect (nth (HTyVar NAlpha) (rcons env ty) (size env))
    (interpType (frTyOp F) tv)
    (dnth F tv (rcons env ty) (DEnv_snoc F tv env d ty x) (size env) Hlt)
    ty Hnth = x.
Proof.
move: Hlt Hnth.
elim: d => [|ty0 env0 x0 d IH] Hlt Hnth /=.
- by rewrite (proof_irrelevance _ Hnth (erefl ty)).
- exact: IH.
Qed.
Lemma bvar_cast_eq (A : Type) (Q : A -> Type) (D N T : A) (x : Q D)
    (eNT : N = T) (eND : N = D) (eDT : D = T) :
  eq_rect N (fun a => Q a -> Q T)
    (eq_rect_r (fun a => Q a -> Q T) (@id (Q T)) eNT) D eND x =
  eq_rect D Q x T eDT.
Proof.
move: N eNT eND x.
case: T / eDT => N eNT eND x.
move: eND x.
case: D / eNT => eND x.
by rewrite (proof_irrelevance _ eND (erefl N)).
Qed.

Lemma eq_rect_trans (A : Type) (Q : A -> Type) (X Y Z : A)
    (x : Q X) (eXY : X = Y) (eYZ : Y = Z) :
  eq_rect Y Q (eq_rect X Q x Y eXY) Z eYZ =
  eq_rect X Q x Z (eq_trans eXY eYZ).
Proof.
destruct eXY.
destruct eYZ.
reflexivity.
Qed.

Lemma denote_snoc_last F tv venv env d ty x
    (Hwt : WellTypedShape (TmBVar (size env) ty) (rcons env ty)) :
  denote F tv venv (rcons env ty) (DEnv_snoc F tv env d ty x)
    (TmBVar (size env) ty) Hwt = x.
Proof.
move: Hwt; rewrite /WellTypedShape => -[Hlt Hty].
rewrite /denote /=.
have Hnth : nth (HTyVar NAlpha) (rcons env ty) (size env) = ty.
  by rewrite nth_rcons ltnn eqxx.
rewrite (bvar_cast_eq HType (interpType (frTyOp F) tv)
  _ _ _ _ Hty (set_nth_default (HTyVar NAlpha) ty Hlt) Hnth).
exact: (dnth_snoc_last F tv env d ty x Hlt Hnth).
Qed.

(** Flip the endpoint of a transport equation -- avoids fighting
    [esym]/[esym]-involution proof terms directly. *)
Lemma transport_flip (T : Type) (P : T -> Type) (A B : T) (e : A = B)
    (a : P A) (b : P B) :
  a = eq_rect B P b A (esym e) -> b = eq_rect A P a B e.
Proof. by case: B / e a b => a b ->. Qed.

(** Transport a function value along an equality of its codomain type,
    with a fixed [mk_fun] domain -- what the [TmAbs] case of
    [denote_abstract_at] needs to push its [eq_rect] under the lambda. *)
Lemma eq_rect_mk_fun_codom F tv aty A B (e : A = B)
    (f : interpType (frTyOp F) tv aty -> interpType (frTyOp F) tv A) :
  eq_rect (mk_fun aty A) (interpType (frTyOp F) tv) f (mk_fun aty B)
    (f_equal (mk_fun aty) e) =
  fun a => eq_rect A (interpType (frTyOp F) tv) (f a) B e.
Proof. by case: B / e. Qed.

Lemma denote_abstract_at F tv venv v0 a0 env d t
    (Hwt : WellTypedShape t env)
    (Hwt' : WellTypedShape (abstract_at (size env) v0 t) (rcons env (fv_ty v0)))
    (Ety : type_of (abstract_at (size env) v0 t) = type_of t) :
  denote F tv (venv_upd F tv venv v0 a0) env d t Hwt =
  eq_rect (type_of (abstract_at (size env) v0 t)) (interpType (frTyOp F) tv)
    (denote F tv venv (rcons env (fv_ty v0))
       (DEnv_snoc F tv env d (fv_ty v0) a0)
       (abstract_at (size env) v0 t) Hwt')
    (type_of t) Ety.
Proof.
elim: t env d Hwt Hwt' Ety => [w | i ty | n ty | f IHf x IHx | aty b IHb]
    env d Hwt Hwt' Ety.
- case Eeq: (w == v0).
  + move/eqP: Eeq => Ewv.
    move: a0 Hwt Hwt' Ety; case: v0 / Ewv => a0 Hwt Hwt' Ety.
    move: Hwt' Ety; rewrite /abstract_at /= eqxx => Hwt' Ety.
    rewrite (proof_irrelevance _ Ety (erefl _)) (venv_upd_same F tv venv w a0).
    exact: (esym (denote_snoc_last F tv venv env d (fv_ty w) a0 Hwt')).
  + have Ewv : w <> v0.
      move=> E; have Ew : w == v0 by apply/eqP.
      by rewrite Ew in Eeq.
    move: Hwt' Ety; rewrite /abstract_at Eeq /= => Hwt' Ety.
    rewrite (proof_irrelevance _ Ety (erefl _)) /denote /=
      (venv_upd_other F tv venv v0 a0 w Ewv).
    by [].
- move: Hwt' Ety; rewrite /abstract_at /= => Hwt' Ety.
  move: Hwt; rewrite /WellTypedShape => -[Hlt Hnth].
  move: Hwt'; rewrite /WellTypedShape => -[Hlt' Hnth'].
  rewrite (proof_irrelevance _ Ety (erefl _)).
  rewrite /denote /=.
  have Hnth0 : nth (HTyVar NAlpha) (rcons env (fv_ty v0)) i =
      nth (HTyVar NAlpha) env i by rewrite nth_rcons Hlt.
  have Hlast : nth (HTyVar NAlpha) (rcons env (fv_ty v0)) i = ty :=
    eq_trans Hnth0 (eq_trans (esym (set_nth_default (HTyVar NAlpha) ty Hlt)) Hnth).
  have Hsrc : nth (HTyVar NAlpha) env i = ty :=
    eq_trans (esym (set_nth_default (HTyVar NAlpha) ty Hlt)) Hnth.
  rewrite (bvar_cast_eq HType (interpType (frTyOp F) tv)
    _ _ _ _ Hnth (set_nth_default (HTyVar NAlpha) ty Hlt) Hsrc).
  rewrite (bvar_cast_eq HType (interpType (frTyOp F) tv)
    _ _ _ _ Hnth' (set_nth_default (HTyVar NAlpha) ty Hlt') Hlast).
  rewrite (proof_irrelevance _ Hlast (eq_trans Hnth0 Hsrc)).
  rewrite - (eq_rect_trans HType (interpType (frTyOp F) tv)
    _ _ _ (dnth F tv (rcons env (fv_ty v0))
      (DEnv_snoc F tv env d (fv_ty v0) a0) i Hlt') Hnth0 Hsrc).
  by rewrite (dnth_snoc F tv env d (fv_ty v0) a0 i Hlt Hlt' Hnth0).
- move: Hwt' Ety; rewrite /abstract_at /= => Hwt' Ety.
  rewrite (proof_irrelevance _ Ety (erefl _)) /denote /=.
  by [].
- move: Hwt Hwt'; rewrite /WellTypedShape /= => Hwt Hwt'.
  have Hf := Hwt.1.
  have Hx := Hwt.2.1.
  have Hisfun := Hwt.2.2.1.
  have Hdom := Hwt.2.2.2.
  have Hf' := Hwt'.1.
  have Hx' := Hwt'.2.1.
  have Hisfun' := Hwt'.2.2.1.
  have Hdom' := Hwt'.2.2.2.
  have Ef := IHf env d Hf Hf' (type_of_abstract_at (size env) v0 f).
  have Ex := IHx env d Hx Hx' (type_of_abstract_at (size env) v0 x).
  have EAB : type_of f = type_of (abstract_at (size env) v0 f) :=
    esym (type_of_abstract_at (size env) v0 f).
  have ECD : type_of x = type_of (abstract_at (size env) v0 x) :=
    esym (type_of_abstract_at (size env) v0 x).
  have Eout : (dest_fun (type_of f)).2 =
      (dest_fun (type_of (abstract_at (size env) v0 f))).2.
    by rewrite (type_of_abstract_at (size env) v0 f).
  have Ef0 : denote F tv (venv_upd F tv venv v0 a0) env d f Hf =
    eq_rect (type_of (abstract_at (size env) v0 f)) (interpType (frTyOp F) tv)
      (denote F tv venv (rcons env (fv_ty v0))
        (DEnv_snoc F tv env d (fv_ty v0) a0) (abstract_at (size env) v0 f) Hf')
      (type_of f) (esym EAB).
    by rewrite (proof_irrelevance _ (esym EAB) (type_of_abstract_at (size env) v0 f)).
  have Ex0 : denote F tv (venv_upd F tv venv v0 a0) env d x Hx =
    eq_rect (type_of (abstract_at (size env) v0 x)) (interpType (frTyOp F) tv)
      (denote F tv venv (rcons env (fv_ty v0))
        (DEnv_snoc F tv env d (fv_ty v0) a0) (abstract_at (size env) v0 x) Hx')
      (type_of x) (esym ECD).
    by rewrite (proof_irrelevance _ (esym ECD) (type_of_abstract_at (size env) v0 x)).
  have Happ := applyFun_transport F tv (type_of f) (type_of (abstract_at (size env) v0 f))
    (type_of x) (type_of (abstract_at (size env) v0 x)) EAB ECD Eout
    Hisfun Hisfun' Hdom Hdom'
    (denote F tv (venv_upd F tv venv v0 a0) env d f Hf)
    (denote F tv venv (rcons env (fv_ty v0)) (DEnv_snoc F tv env d (fv_ty v0) a0)
      (abstract_at (size env) v0 f) Hf')
    (denote F tv (venv_upd F tv venv v0 a0) env d x Hx)
    (denote F tv venv (rcons env (fv_ty v0)) (DEnv_snoc F tv env d (fv_ty v0) a0)
      (abstract_at (size env) v0 x) Hx') Ef0 Ex0.
  have Hd1 := denote_comb F tv (venv_upd F tv venv v0 a0) env d f x Hisfun Hdom Hf Hx Hwt.
  have Hd2 := denote_comb F tv venv (rcons env (fv_ty v0)) (DEnv_snoc F tv env d (fv_ty v0) a0)
    (abstract_at (size env) v0 f) (abstract_at (size env) v0 x) Hisfun' Hdom' Hf' Hx' Hwt'.
  have Hfinal := transport_sandwich F tv
    (type_of (TmComb f x)) (type_of (abstract_at (size env) v0 (TmComb f x)))
    (dest_fun (type_of f)).2 (dest_fun (type_of (abstract_at (size env) v0 f))).2
    (type_of_mk_comb_isfun f x Hisfun)
    (type_of_mk_comb_isfun (abstract_at (size env) v0 f) (abstract_at (size env) v0 x) Hisfun')
    Eout (esym Ety)
    (denote F tv (venv_upd F tv venv v0 a0) env d (TmComb f x) Hwt)
    (denote F tv venv (rcons env (fv_ty v0)) (DEnv_snoc F tv env d (fv_ty v0) a0)
      (abstract_at (size env) v0 (TmComb f x)) Hwt')
    (applyFun F tv (type_of f) (type_of x) Hisfun Hdom
      (denote F tv (venv_upd F tv venv v0 a0) env d f Hf)
      (denote F tv (venv_upd F tv venv v0 a0) env d x Hx))
    (applyFun F tv (type_of (abstract_at (size env) v0 f)) (type_of (abstract_at (size env) v0 x))
      Hisfun' Hdom'
      (denote F tv venv (rcons env (fv_ty v0)) (DEnv_snoc F tv env d (fv_ty v0) a0)
        (abstract_at (size env) v0 f) Hf')
      (denote F tv venv (rcons env (fv_ty v0)) (DEnv_snoc F tv env d (fv_ty v0) a0)
        (abstract_at (size env) v0 x) Hx'))
    Hd1 Hd2 Happ.
  rewrite (HType_UIP _ _ (esym (esym Ety)) Ety) in Hfinal.
  exact: Hfinal.
- move: Hwt' Ety; rewrite /abstract_at -/abstract_at /= => Hwt' Ety.
  have Ety_b : type_of (abstract_at (size env).+1 v0 b) = type_of b :=
    type_of_abstract_at (size env).+1 v0 b.
  rewrite (HType_UIP _ _ Ety (f_equal (mk_fun aty) Ety_b)).
  rewrite (eq_rect_mk_fun_codom F tv aty (type_of (abstract_at (size env).+1 v0 b)) (type_of b) Ety_b).
  apply: functional_extensionality => a.
  exact: (IHb (aty :: env) (DEnvCons F tv aty env a d) Hwt Hwt' Ety_b).
Qed.

(** [SafeDenote] of [mk_abs v0 body] applied to a value, expressed via
    [SafeDenote] of [body] under [venv_upd] -- the reusable replacement
    for unfolding [denote]'s own [TmAbs]/[abstract_fvar] structure by
    hand. Specializes [denote_abstract_at] at [env := [::]]. *)
Lemma SafeDenote_abs F thy tv venv v0 body a0
    (Hb : check_term thy body)
    (Hab : check_term thy (mk_abs v0 body)) :
  (SafeDenote F thy tv venv (mk_abs v0 body) Hab) a0 =
  eq_rect (type_of body) (interpType (frTyOp F) tv)
    (SafeDenote F thy tv (venv_upd F tv venv v0 a0) body Hb)
    (type_of (abstract_fvar v0 body)) (esym (type_of_abstract_at 0 v0 body)).
Proof.
rewrite /SafeDenote /mk_abs /=.
have Hwt := check_open_term_WellTypedShape thy (mk_abs v0 body) [::] Hab.
have Hwt2 : WellTypedShape (abstract_at 0 v0 body) (rcons [::] (fv_ty v0)) := Hwt.
have Hwtb := check_open_term_WellTypedShape thy body [::] Hb.
have Hd := denote_abstract_at F tv venv v0 a0 [::] (DEnvNil F tv) body Hwtb Hwt2
  (type_of_abstract_at 0 v0 body).
rewrite (HType_UIP _ _ (type_of_abstract_at 0 v0 body)
  (esym (esym (type_of_abstract_at 0 v0 body)))) in Hd.
have Hflip := transport_flip _ _ (type_of body) (type_of (abstract_at 0 v0 body))
  (esym (type_of_abstract_at 0 v0 body))
  (denote F tv (venv_upd F tv venv v0 a0) [::] (DEnvNil F tv) body Hwtb)
  (denote F tv venv (rcons [::] (fv_ty v0)) (DEnv_snoc F tv [::] (DEnvNil F tv) (fv_ty v0) a0)
    (abstract_at 0 v0 body) Hwt2)
  Hd.
rewrite /abstract_fvar.
rewrite (proof_irrelevance _ (check_open_term_WellTypedShape thy (TmAbs (fv_ty v0) (abstract_at 0 v0 body)) [::] Hab) Hwt2).
rewrite (proof_irrelevance _ (check_open_term_WellTypedShape thy body [::] Hb) Hwtb).
exact: Hflip.
Qed.

(** [denote] does not look at [venv]'s entry for [v0] when [v0] is not
    free in [t] -- what [ABS]'s soundness needs to carry the hypothesis
    side-condition [~~ vfree_in v0 h] across [venv_upd]. No type
    transport is needed here (unlike [denote_abstract_at]): [t] itself
    is unchanged, so both sides share the same [type_of t]. *)
Lemma denote_venv_upd_irrel F tv venv v0 a0 env d t
    (Hwt : WellTypedShape t env) (Hfree : ~~ vfree_in v0 t) :
  denote F tv (venv_upd F tv venv v0 a0) env d t Hwt =
  denote F tv venv env d t Hwt.
Proof.
elim: t env d Hwt Hfree => [w | i ty | n ty | f IHf x IHx | aty b IHb]
    env d Hwt Hfree.
- have Hne : w <> v0.
    move=> Heq; move: Hfree; rewrite /vfree_in Heq eqxx.
    by [].
  by rewrite /denote /= (venv_upd_other F tv venv v0 a0 w Hne).
- by [].
- by [].
- move: Hwt; rewrite /WellTypedShape /= => Hwt.
  move: Hfree; rewrite /vfree_in -/vfree_in => /norP[HfreeF HfreeX].
  have Hf := Hwt.1.
  have Hx := Hwt.2.1.
  have Hisfun := Hwt.2.2.1.
  have Hdom := Hwt.2.2.2.
  have Hd1 := denote_comb F tv (venv_upd F tv venv v0 a0) env d f x Hisfun Hdom Hf Hx Hwt.
  have Hd2 := denote_comb F tv venv env d f x Hisfun Hdom Hf Hx Hwt.
  rewrite (IHf env d Hf HfreeF) (IHx env d Hx HfreeX) in Hd1.
  have Heq : applyFun F tv (type_of f) (type_of x) Hisfun Hdom
      (denote F tv venv env d f Hf) (denote F tv venv env d x Hx) =
    applyFun F tv (type_of f) (type_of x) Hisfun Hdom
      (denote F tv venv env d f Hf) (denote F tv venv env d x Hx) := erefl.
  have Hcomb : eq_rect (type_of (TmComb f x)) (interpType (frTyOp F) tv)
      (denote F tv (venv_upd F tv venv v0 a0) env d (TmComb f x) Hwt)
      (dest_fun (type_of f)).2 (type_of_mk_comb_isfun f x Hisfun) =
    eq_rect (type_of (TmComb f x)) (interpType (frTyOp F) tv)
      (denote F tv venv env d (TmComb f x) Hwt)
      (dest_fun (type_of f)).2 (type_of_mk_comb_isfun f x Hisfun).
    by rewrite Hd1 Hd2.
  exact: (eq_rect_injective HType (interpType (frTyOp F) tv)
    (type_of (TmComb f x)) (dest_fun (type_of f)).2
    (denote F tv (venv_upd F tv venv v0 a0) env d (TmComb f x) Hwt)
    (denote F tv venv env d (TmComb f x) Hwt)
    (type_of_mk_comb_isfun f x Hisfun) Hcomb).
- move: Hwt Hfree; rewrite /WellTypedShape /vfree_in -/vfree_in /= => Hwt Hfree.
  apply: functional_extensionality => a.
  exact: (IHb (aty :: env) (DEnvCons F tv aty env a d) Hwt Hfree).
Qed.

Lemma SafeDenote_venv_upd_irrel F thy tv venv v0 a0 t
    (Hct : check_term thy t) (Hfree : ~~ vfree_in v0 t) :
  SafeDenote F thy tv (venv_upd F tv venv v0 a0) t Hct =
  SafeDenote F thy tv venv t Hct.
Proof.
rewrite /SafeDenote.
exact: (denote_venv_upd_irrel F tv venv v0 a0 [::] (DEnvNil F tv) t
  (check_open_term_WellTypedShape thy t [::] Hct) Hfree).
Qed.

Lemma denoteProp_venv_upd_irrel F thy tv venv v0 a0 t
    (Hct : check_term thy t) (Hbt : is_bool t) (Hfree : ~~ vfree_in v0 t) :
  denoteProp F thy tv (venv_upd F tv venv v0 a0) t Hct Hbt =
  denoteProp F thy tv venv t Hct Hbt.
Proof.
rewrite /denoteProp.
by rewrite (SafeDenote_venv_upd_irrel F thy tv venv v0 a0 t Hct Hfree).
Qed.

Lemma absValid F thy v th th' :
  WellFormedTheory thy -> Valid F thy th ->
  ABS thy v th = Some th' -> Valid F thy th'.
Proof.
move=> WFT Vth Hrule.
split; first exact: (absWellFormed thy v th th' WFT Vth.1 Hrule).
move=> HM tv venv.
move: Hrule; rewrite /ABS.
case: ifP => [/andP[/andP[Hdesc Hvty] Hnfree] | //].
case Hde: (dest_eq (thm_concl th)) => [[l r]|] //.
move=> [<-] Hhyps Hcc Hbc.
move: Hnfree => /fset_allP Hnfree.
have [Hct [Hht [Hbt [Hbht Hdt]]]] := Vth.1.
have [Hl [Hr Elr]] := check_term_dest_eq_inv thy (thm_concl th) l r WFT Hct Hde.
have Hcl := check_term_mk_abs thy v l Hvty Hl.
have Hcr := check_term_mk_abs thy v r Hvty Hr.
have Etlr : type_of (mk_abs v l) = type_of (mk_abs v r).
  by rewrite /mk_abs /= !type_of_abstract_at Elr.
have Ety_lr : type_of (abstract_fvar v r) = type_of (abstract_fvar v l).
  by rewrite !type_of_abstract_at; exact: esym Elr.
apply: (SafeDenote_mk_eq F thy tv venv (mk_abs v l) (mk_abs v r) Hcl Hcr Etlr Hbc HM.1 Hcc).2.
rewrite (HType_UIP _ _ (esym Etlr) (f_equal (mk_fun (fv_ty v)) Ety_lr)).
rewrite (eq_rect_mk_fun_codom F tv (fv_ty v) (type_of (abstract_fvar v r)) (type_of (abstract_fvar v l))
  Ety_lr (SafeDenote F thy tv venv (mk_abs v r) Hcr)).
apply: functional_extensionality => a0.
have HhypsA : forall h (Hch : check_term thy h) (Hbh : is_bool h),
    h \in thm_hyps th -> denoteProp F thy tv (venv_upd F tv venv v a0) h Hch Hbh.
  move=> h Hch Hbh Hhin.
  rewrite (denoteProp_venv_upd_irrel F thy tv venv v a0 h Hch Hbh (Hnfree h Hhin)).
  exact: (Hhyps h Hch Hbh Hhin).
have Hconcl : thm_concl th = mk_eq l r := trans_eq_shape thy (thm_concl th) l r WFT Hct Hde.
have Hden0 := Vth.2 HM tv (venv_upd F tv venv v a0) HhypsA Hct Hbt.
move: Hden0.
move: Hct Hbt.
case: (thm_concl th) / (esym Hconcl) => Hct Hbt Hden0.
have Hden : denoteProp F thy tv (venv_upd F tv venv v a0) (mk_eq l r)
    (mkEqCheckSound thy l r WFT Hl Hr Elr) (is_bool_mk_eq l r).
  rewrite -(denoteProp_irrel F thy tv (venv_upd F tv venv v a0) (mk_eq l r) Hct
    (mkEqCheckSound thy l r WFT Hl Hr Elr) Hbt (is_bool_mk_eq l r)).
  exact: Hden0.
have Hlr := (SafeDenote_mk_eq F thy tv (venv_upd F tv venv v a0) l r Hl Hr Elr
  (is_bool_mk_eq l r) HM.1 (mkEqCheckSound thy l r WFT Hl Hr Elr)).1 Hden.
rewrite (SafeDenote_abs F thy tv venv v l a0 Hl Hcl)
  (SafeDenote_abs F thy tv venv v r a0 Hr Hcr) Hlr.
rewrite (eq_rect_trans HType (interpType (frTyOp F) tv) (type_of r) (type_of l) (type_of (abstract_fvar v l))
  (SafeDenote F thy tv (venv_upd F tv venv v a0) r Hr) (esym Elr) (esym (type_of_abstract_at 0 v l))).
rewrite (eq_rect_trans HType (interpType (frTyOp F) tv) (type_of r) (type_of (abstract_fvar v r)) (type_of (abstract_fvar v l))
  (SafeDenote F thy tv (venv_upd F tv venv v a0) r Hr) (esym (type_of_abstract_at 0 v r)) Ety_lr).
by rewrite (HType_UIP _ _ (eq_trans (esym Elr) (esym (type_of_abstract_at 0 v l)))
  (eq_trans (esym (type_of_abstract_at 0 v r)) Ety_lr)).
Qed.




Lemma WellTypedShape_weaken t env extra :
  WellTypedShape t env -> WellTypedShape t (env ++ extra).
Proof.
elim: t env => [w | i ty | n ty | f IHf x IHx | aty b IHb] env //=.
- move=> [Hlt Hnth].
  split.
  + rewrite size_cat; exact: leq_trans Hlt (leq_addr _ _).
  + by rewrite nth_cat Hlt.
- move=> [Hf [Hx Hr]].
  split; first exact: IHf.
  split; first exact: IHx.
  exact: Hr.
- move=> Hb.
  by rewrite -cat_cons; exact: IHb.
Qed.

Lemma shift_wts_id d cutoff t env :
  size env <= cutoff -> WellTypedShape t env -> shift d cutoff t = t.
Proof.
elim: t cutoff env => [w | i ty | n ty | f IHf x IHx | aty b IHb] cutoff env //=.
- move=> Hle [Hlt _].
  have Hic : i < cutoff by exact: leq_trans Hlt Hle.
  by rewrite Hic.
- move=> Hle [Hf [Hx _]].
  by rewrite (IHf cutoff env Hle Hf) (IHx cutoff env Hle Hx).
- move=> Hle Hb.
  have Hle2 : (size env).+1 <= cutoff.+1 by rewrite ltnS.
  by rewrite (IHb cutoff.+1 (aty :: env) Hle2 Hb).
Qed.

Lemma type_of_subst_at arg extra body :
  WellTypedShape body (extra ++ [:: type_of arg]) ->
  type_of (subst_at (size extra) arg body) = type_of body.
Proof.
elim: body extra => [w | i ty | n ty | f IHf x IHx | aty b IHb] extra /=.
- by [].
- case: (@eqP _ i (size extra)) => [-> | Hne] /=.
  + move=> [_ Heq].
    rewrite nth_cat ltnn subnn /= in Heq.
    by rewrite type_of_shift -Heq.
  + by [].
- by [].
- move=> [Hf [Hx _]].
  by rewrite /= (IHf extra Hf).
- move=> Hb.
  by rewrite /= (IHb (aty :: extra) Hb).
Qed.

Lemma WellTypedShape_subst_at arg extra body :
  WellTypedShape arg [::] ->
  WellTypedShape body (extra ++ [:: type_of arg]) ->
  WellTypedShape (subst_at (size extra) arg body) extra.
Proof.
move=> Harg.
elim: body extra => [w | i ty | n ty | f IHf x IHx | aty b IHb] extra /=.
- by [].
- case: (@eqP _ i (size extra)) => [-> | Hne] /=.
  + move=> [_ Heq].
    rewrite nth_cat ltnn subnn /= in Heq.
    rewrite (shift_wts_id (Z.of_nat (size extra)) 0 arg [::] (leqnn 0) Harg).
    exact: (WellTypedShape_weaken arg [::] extra Harg).
  + move=> [Hlt Heq].
    have Hlt2 : i < size extra.
      move: Hlt; rewrite size_cat addn1 ltnS leq_eqVlt => /orP[/eqP Heqi | //].
      by case: (Hne Heqi).
    rewrite nth_cat Hlt2 in Heq.
    by split.
- by [].
- move=> [Hf [Hx Hr]].
  split; first exact: IHf.
  split; first exact: IHx.
  by rewrite (type_of_subst_at arg extra f Hf) (type_of_subst_at arg extra x Hx).
- move=> Hb.
  exact: (IHb (aty :: extra) Hb).
Qed.

Lemma type_of_subst_bvar arg body :
  WellTypedShape body [:: type_of arg] ->
  type_of (subst_bvar arg body) = type_of body.
Proof.
move=> Hb.
rewrite /subst_bvar type_of_shift.
exact: (type_of_subst_at arg [::] body Hb).
Qed.

Lemma dnth_denv_app_last F tv extra (dextra : DEnv F tv extra) ty v
    (Hlt : size extra < size (extra ++ [:: ty]))
    (Hnth : nth (HTyVar NAlpha) (extra ++ [:: ty]) (size extra) = ty) :
  eq_rect (nth (HTyVar NAlpha) (extra ++ [:: ty]) (size extra))
    (interpType (frTyOp F) tv)
    (dnth F tv (extra ++ [:: ty])
      (denv_app F tv extra [:: ty] dextra
        (DEnvCons F tv ty [::] v (DEnvNil F tv))) (size extra) Hlt)
    ty Hnth = v.
Proof.
move: Hlt Hnth.
elim: dextra => [|ty0 env0 x0 d0 IH] Hlt Hnth /=.
- by rewrite (proof_irrelevance _ Hnth (erefl ty)).
- exact: IH.
Qed.

Lemma denote_subst_bvar_last F tv venv extra dextra arg
    (Harg : WellTypedShape arg [::])
    (Hwt : WellTypedShape (TmBVar (size extra) (type_of arg)) (extra ++ [:: type_of arg])) :
  denote F tv venv (extra ++ [:: type_of arg])
    (denv_app F tv extra [:: type_of arg] dextra
      (DEnvCons F tv (type_of arg) [::]
        (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv)))
    (TmBVar (size extra) (type_of arg)) Hwt =
  denote F tv venv [::] (DEnvNil F tv) arg Harg.
Proof.
move: Hwt; rewrite /WellTypedShape => -[Hlt Hnth].
rewrite /denote /=.
have Hnth0 : nth (HTyVar NAlpha) (extra ++ [:: type_of arg]) (size extra) =
    type_of arg by rewrite nth_cat ltnn subnn.
rewrite (bvar_cast_eq HType (interpType (frTyOp F) tv)
  _ _ _ _ Hnth (set_nth_default (HTyVar NAlpha) (type_of arg) Hlt) Hnth0).
exact: (dnth_denv_app_last F tv extra dextra (type_of arg)
  (denote F tv venv [::] (DEnvNil F tv) arg Harg) Hlt Hnth0).
Qed.

Lemma denote_prefix_irrel_wts F tv venv :
  forall t env1 (d1 : DEnv F tv env1) env2 (d2 : DEnv F tv env2)
    (Hwt1 : WellTypedShape t (env1 ++ env2))
    (Hwt2 : WellTypedShape t env1),
  denote F tv venv (env1 ++ env2) (denv_app F tv env1 env2 d1 d2) t Hwt1 =
  denote F tv venv env1 d1 t Hwt2.
Proof.
move=> t.
elim: t => [v | i ty | n ty | f IHf x IHx | aty b IHb] env1 d1 env2 d2 Hwt1 Hwt2.
- rewrite (denote_irrel F tv venv (env1 ++ env2)
    (denv_app F tv env1 env2 d1 d2) (TmFVar v) Hwt1 I).
  rewrite (denote_irrel F tv venv env1 d1 (TmFVar v) Hwt2 I).
  by [].
- move: Hwt1 Hwt2 => [Hlt1 Hnth1] [Hlt2 Hnth2].
  have Hnth : nth ty env1 i = ty := Hnth2.
  have Hltapp : i < size (env1 ++ env2).
    by rewrite size_cat; exact: ltn_addr (size env2) Hlt2.
  have Hnthapp : nth ty (env1 ++ env2) i = ty.
    by rewrite nth_cat Hlt2.
  have Eapp : nth (HTyVar NAlpha) (env1 ++ env2) i =
      nth (HTyVar NAlpha) env1 i by rewrite nth_cat Hlt2.
  have Hlookup := dnth_denv_app F tv env1 d1 env2 d2 i Hlt2 Hltapp Eapp.
  have Eleft : nth (HTyVar NAlpha) (env1 ++ env2) i = ty.
    by rewrite -(set_nth_default (HTyVar NAlpha) ty Hltapp) Hnthapp.
  have Eright : nth (HTyVar NAlpha) env1 i = ty.
    by rewrite -(set_nth_default (HTyVar NAlpha) ty Hlt2) Hnth.
  have Htyped := eq_rect_transport HType (interpType (frTyOp F) tv)
    _ _ ty _ _ Eapp Eleft Eright Hlookup.
  rewrite (denote_irrel F tv venv (env1 ++ env2)
    (denv_app F tv env1 env2 d1 d2) (TmBVar i ty) (conj Hlt1 Hnth1)
    (conj Hltapp Hnthapp)).
  rewrite (denote_irrel F tv venv env1 d1 (TmBVar i ty) (conj Hlt2 Hnth2)
    (conj Hlt2 Hnth)).
  rewrite /denote /=.
  rewrite (eq_rect_bvar_cast HType (interpType (frTyOp F) tv) _ _ ty
    (dnth F tv (env1 ++ env2) (denv_app F tv env1 env2 d1 d2) i Hltapp)
    Hnthapp (set_nth_default (HTyVar NAlpha) ty Hltapp)).
  rewrite (eq_rect_bvar_cast HType (interpType (frTyOp F) tv) _ _ ty
    (dnth F tv env1 d1 i Hlt2) Hnth
    (set_nth_default (HTyVar NAlpha) ty Hlt2)).
  have Eleft' : eq_trans
    (esym (set_nth_default (HTyVar NAlpha) ty Hltapp)) Hnthapp = Eleft
    := proof_irrelevance _ _ _.
  have Eright' : eq_trans
    (esym (set_nth_default (HTyVar NAlpha) ty Hlt2)) Hnth = Eright
    := proof_irrelevance _ _ _.
  rewrite Eleft' Eright'.
  exact: Htyped.
- rewrite (denote_irrel F tv venv (env1 ++ env2)
    (denv_app F tv env1 env2 d1 d2) (TmConst n ty) Hwt1 I).
  rewrite (denote_irrel F tv venv env1 d1 (TmConst n ty) Hwt2 I).
  by [].
- have Hfun1 := Hwt1.2.2.1.
  have Heq1 := Hwt1.2.2.2.
  have E1 := denote_comb F tv venv (env1 ++ env2)
    (denv_app F tv env1 env2 d1 d2) f x Hfun1 Heq1
    Hwt1.1 Hwt1.2.1 Hwt1.
  have E2 := denote_comb F tv venv env1 d1 f x Hfun1 Heq1
    Hwt2.1 Hwt2.2.1 Hwt2.
  apply: (eq_rect_injective HType (interpType (frTyOp F) tv)
    (type_of (TmComb f x)) (dest_fun (type_of f)).2
    _ _ (type_of_mk_comb_isfun f x Hfun1)).
  rewrite E1 E2.
  exact: (f_equal2 (applyFun F tv (type_of f) (type_of x) Hfun1 Heq1)
    (IHf env1 d1 env2 d2 Hwt1.1 Hwt2.1)
    (IHx env1 d1 env2 d2 Hwt1.2.1 Hwt2.2.1)).
- apply: functional_extensionality => a.
  exact: (IHb (aty :: env1) (DEnvCons F tv aty env1 a d1) env2 d2 Hwt1 Hwt2).
Qed.

Lemma denote_subst_at F tv venv arg
    (Harg : WellTypedShape arg [::]) :
  forall body extra (dextra : DEnv F tv extra)
    (Hbody : WellTypedShape body (extra ++ [:: type_of arg]))
    (Hsub : WellTypedShape (subst_at (size extra) arg body) extra)
    (Ety : type_of (subst_at (size extra) arg body) = type_of body),
  eq_rect (type_of (subst_at (size extra) arg body)) (interpType (frTyOp F) tv)
    (denote F tv venv extra dextra (subst_at (size extra) arg body) Hsub)
    (type_of body) Ety =
  denote F tv venv (extra ++ [:: type_of arg])
    (denv_app F tv extra [:: type_of arg] dextra
      (DEnvCons F tv (type_of arg) [::]
        (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv)))
    body Hbody.
Proof.
elim=> [w | i ty | n ty | f IHf x IHx | aty b IHb] extra dextra Hbody Hsub Ety.
- rewrite (HType_UIP _ _ Ety (erefl (type_of (TmFVar w)))).
  exact: (denote_irrel F tv venv extra dextra (TmFVar w) Hsub
    (WellTypedShape_weaken (TmFVar w) [::] extra I)).
- case: (@eqP _ i (size extra)) => [Eiw | Hne].
  + move: Hbody Hsub Ety; rewrite Eiw /= eqxx => Hbody Hsub Ety.
    have Heq : type_of arg = ty.
      move: Hbody.2; rewrite nth_cat ltnn subnn /=; by [].
move: Ety Hbody Hsub.
rewrite (shift_wts_id (Z.of_nat (size extra)) 0 arg [::] (leqnn 0) Harg).
move=> Ety Hbody Hsub.
case: ty / Heq Ety Hbody Hsub => Ety Hbody Hsub.
    rewrite (HType_UIP _ _ Ety (erefl (type_of arg))).
    rewrite (denote_irrel F tv venv extra dextra arg Hsub
      (WellTypedShape_weaken arg [::] extra Harg)).
    have Hcheck := denote_subst_bvar_last F tv venv extra dextra arg Harg Hbody.
    have Hbridge := denote_prefix_irrel_wts F tv venv arg [::] (DEnvNil F tv) extra dextra
      (WellTypedShape_weaken arg [::] extra Harg) Harg.
    rewrite Hbridge.
    symmetry.
    exact: Hcheck.
  + move: Hbody Hsub Ety.
    rewrite /= (negbTE (introN eqP Hne)) /=.
    move=> Hbody Hsub Ety.
    rewrite (HType_UIP _ _ Ety (erefl ty)).
    symmetry.
    exact: (denote_prefix_irrel_wts F tv venv (TmBVar i ty) extra dextra
      [:: type_of arg]
      (DEnvCons F tv (type_of arg) [::]
        (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))
      Hbody Hsub).
- rewrite (HType_UIP _ _ Ety (erefl (type_of (TmConst n ty)))).
  exact: (denote_irrel F tv venv extra dextra (TmConst n ty) Hsub
    (WellTypedShape_weaken (TmConst n ty) [::] extra I)).
- move: Hbody Hsub; rewrite /WellTypedShape /= => Hbody Hsub.
  have Hf := Hbody.1.
  have Hx := Hbody.2.1.
  have Hisfun := Hbody.2.2.1.
  have Hdom := Hbody.2.2.2.
  have Hsf := Hsub.1.
  have Hsx := Hsub.2.1.
  have Hisfuns := Hsub.2.2.1.
  have Hdoms := Hsub.2.2.2.
  have EAB : type_of (subst_at (size extra) arg f) = type_of f :=
    type_of_subst_at arg extra f Hf.
  have ECD : type_of (subst_at (size extra) arg x) = type_of x :=
    type_of_subst_at arg extra x Hx.
  have Eout : (dest_fun (type_of (subst_at (size extra) arg f))).2 =
      (dest_fun (type_of f)).2.
    by rewrite EAB.
  have Ef := IHf extra dextra Hf Hsf EAB.
  have Ex := IHx extra dextra Hx Hsx ECD.
  have Ef' : denote F tv venv extra dextra (subst_at (size extra) arg f) Hsf =
      eq_rect (type_of f) (interpType (frTyOp F) tv)
        (denote F tv venv (extra ++ [:: type_of arg])
          (denv_app F tv extra [:: type_of arg] dextra
            (DEnvCons F tv (type_of arg) [::]
              (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) f Hf)
        (type_of (subst_at (size extra) arg f)) (esym EAB).
    have Hbr : denote F tv venv (extra ++ [:: type_of arg])
          (denv_app F tv extra [:: type_of arg] dextra
            (DEnvCons F tv (type_of arg) [::]
              (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) f Hf =
        eq_rect (type_of (subst_at (size extra) arg f)) (interpType (frTyOp F) tv)
          (denote F tv venv extra dextra (subst_at (size extra) arg f) Hsf)
          (type_of f) (esym (esym EAB)).
      by rewrite (HType_UIP _ _ (esym (esym EAB)) EAB).
    exact: (transport_flip _ _ (type_of f) (type_of (subst_at (size extra) arg f))
      (esym EAB)
      (denote F tv venv (extra ++ [:: type_of arg])
        (denv_app F tv extra [:: type_of arg] dextra
          (DEnvCons F tv (type_of arg) [::]
            (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) f Hf)
      (denote F tv venv extra dextra (subst_at (size extra) arg f) Hsf)
      Hbr).
  have Ex' : denote F tv venv extra dextra (subst_at (size extra) arg x) Hsx =
      eq_rect (type_of x) (interpType (frTyOp F) tv)
        (denote F tv venv (extra ++ [:: type_of arg])
          (denv_app F tv extra [:: type_of arg] dextra
            (DEnvCons F tv (type_of arg) [::]
              (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) x Hx)
        (type_of (subst_at (size extra) arg x)) (esym ECD).
    have Hbr : denote F tv venv (extra ++ [:: type_of arg])
          (denv_app F tv extra [:: type_of arg] dextra
            (DEnvCons F tv (type_of arg) [::]
              (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) x Hx =
        eq_rect (type_of (subst_at (size extra) arg x)) (interpType (frTyOp F) tv)
          (denote F tv venv extra dextra (subst_at (size extra) arg x) Hsx)
          (type_of x) (esym (esym ECD)).
      by rewrite (HType_UIP _ _ (esym (esym ECD)) ECD).
    exact: (transport_flip _ _ (type_of x) (type_of (subst_at (size extra) arg x))
      (esym ECD)
      (denote F tv venv (extra ++ [:: type_of arg])
        (denv_app F tv extra [:: type_of arg] dextra
          (DEnvCons F tv (type_of arg) [::]
            (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) x Hx)
      (denote F tv venv extra dextra (subst_at (size extra) arg x) Hsx)
      Hbr).
  have Happ := applyFun_transport F tv (type_of (subst_at (size extra) arg f))
    (type_of f) (type_of (subst_at (size extra) arg x)) (type_of x)
    EAB ECD Eout Hisfuns Hisfun Hdoms Hdom
    (denote F tv venv extra dextra (subst_at (size extra) arg f) Hsf)
    (denote F tv venv (extra ++ [:: type_of arg])
      (denv_app F tv extra [:: type_of arg] dextra
        (DEnvCons F tv (type_of arg) [::]
          (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) f Hf)
    (denote F tv venv extra dextra (subst_at (size extra) arg x) Hsx)
    (denote F tv venv (extra ++ [:: type_of arg])
      (denv_app F tv extra [:: type_of arg] dextra
        (DEnvCons F tv (type_of arg) [::]
          (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) x Hx)
    Ef' Ex'.
  have Hd1 := denote_comb F tv venv extra dextra
    (subst_at (size extra) arg f) (subst_at (size extra) arg x)
    Hisfuns Hdoms Hsf Hsx Hsub.
  have Hd2 := denote_comb F tv venv (extra ++ [:: type_of arg])
    (denv_app F tv extra [:: type_of arg] dextra
      (DEnvCons F tv (type_of arg) [::]
        (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv)))
    f x Hisfun Hdom Hf Hx Hbody.
  have Hfinal := transport_sandwich F tv
    (type_of (subst_at (size extra) arg (TmComb f x))) (type_of (TmComb f x))
    (dest_fun (type_of (subst_at (size extra) arg f))).2 (dest_fun (type_of f)).2
    (type_of_mk_comb_isfun (subst_at (size extra) arg f)
      (subst_at (size extra) arg x) Hisfuns)
    (type_of_mk_comb_isfun f x Hisfun)
    Eout Ety
    (denote F tv venv extra dextra (TmComb (subst_at (size extra) arg f)
      (subst_at (size extra) arg x)) Hsub)
    (denote F tv venv (extra ++ [:: type_of arg])
      (denv_app F tv extra [:: type_of arg] dextra
        (DEnvCons F tv (type_of arg) [::]
          (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv)))
      (TmComb f x) Hbody)
    (applyFun F tv (type_of (subst_at (size extra) arg f))
      (type_of (subst_at (size extra) arg x)) Hisfuns Hdoms
      (denote F tv venv extra dextra (subst_at (size extra) arg f) Hsf)
      (denote F tv venv extra dextra (subst_at (size extra) arg x) Hsx))
    (applyFun F tv (type_of f) (type_of x) Hisfun Hdom
      (denote F tv venv (extra ++ [:: type_of arg])
        (denv_app F tv extra [:: type_of arg] dextra
          (DEnvCons F tv (type_of arg) [::]
            (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) f Hf)
      (denote F tv venv (extra ++ [:: type_of arg])
        (denv_app F tv extra [:: type_of arg] dextra
          (DEnvCons F tv (type_of arg) [::]
            (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))) x Hx))
    Hd1 Hd2 Happ.
  exact: (cast_reverse HType (interpType (frTyOp F) tv)
    (type_of (subst_at (size extra) arg (TmComb f x))) (type_of (TmComb f x))
    (denote F tv venv extra dextra (TmComb (subst_at (size extra) arg f)
      (subst_at (size extra) arg x)) Hsub)
    (denote F tv venv (extra ++ [:: type_of arg])
      (denv_app F tv extra [:: type_of arg] dextra
        (DEnvCons F tv (type_of arg) [::]
          (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv)))
      (TmComb f x) Hbody)
    Ety Hfinal).
- rewrite (HType_UIP _ _ Ety
    (f_equal (mk_fun aty) (type_of_subst_at arg (aty :: extra) b Hbody))).
  apply: (abs_transport F tv aty
    (type_of (subst_at (size extra).+1 arg b)) (type_of b)
    (type_of_subst_at arg (aty :: extra) b Hbody)).
  move=> a.
  rewrite (denote_abs F tv venv extra dextra aty
    (subst_at (size extra).+1 arg b) Hsub).
  rewrite (denote_abs F tv venv (extra ++ [:: type_of arg])
    (denv_app F tv extra [:: type_of arg] dextra
      (DEnvCons F tv (type_of arg) [::]
        (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv)))
    aty b Hbody).
  exact: (IHb (aty :: extra) (DEnvCons F tv aty extra a dextra) Hbody Hsub
    (type_of_subst_at arg (aty :: extra) b Hbody)).
Qed.

Lemma SafeDenote_subst_bvar F tv venv arg body
    (Harg : WellTypedShape arg [::])
    (Hbody : WellTypedShape body [:: type_of arg])
    (Hsub : WellTypedShape (subst_bvar arg body) [::]) :
  denote F tv venv [::] (DEnvNil F tv) (subst_bvar arg body) Hsub =
  eq_rect (type_of body) (interpType (frTyOp F) tv)
    (denote F tv venv [:: type_of arg]
      (DEnvCons F tv (type_of arg) [::]
        (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))
      body Hbody)
    (type_of (subst_bvar arg body)) (esym (type_of_subst_bvar arg body Hbody)).
Proof.
have HsubAt : WellTypedShape (subst_at 0 arg body) [::] :=
  WellTypedShape_subst_at arg [::] body Harg Hbody.
have Ety0 : type_of (subst_at 0 arg body) = type_of body :=
  type_of_subst_at arg [::] body Hbody.
have Hd := denote_subst_at F tv venv arg Harg body [::] (DEnvNil F tv)
  Hbody HsubAt Ety0.
have Ebvar : subst_bvar arg body = subst_at 0 arg body.
  by rewrite /subst_bvar (shift_wts_id (-1)%Z 0 (subst_at 0 arg body) [::] (leqnn 0) HsubAt).
have Etbvar : type_of (subst_bvar arg body) = type_of (subst_at 0 arg body) :=
  f_equal type_of Ebvar.
have Hd2 : eq_rect (type_of (subst_bvar arg body)) (interpType (frTyOp F) tv)
    (denote F tv venv [::] (DEnvNil F tv) (subst_bvar arg body) Hsub)
    (type_of (subst_at 0 arg body)) Etbvar =
    denote F tv venv [::] (DEnvNil F tv) (subst_at 0 arg body) HsubAt.
  move: Hsub Etbvar; case: (subst_bvar arg body) / (esym Ebvar) => Hsub Etbvar.
  rewrite (HType_UIP _ _ Etbvar (erefl (type_of (subst_at 0 arg body)))).
  exact: (denote_irrel F tv venv [::] (DEnvNil F tv) (subst_at 0 arg body) Hsub HsubAt).
have Hd3 : denote F tv venv [::] (DEnvNil F tv) (subst_bvar arg body) Hsub =
    eq_rect (type_of (subst_at 0 arg body)) (interpType (frTyOp F) tv)
      (denote F tv venv [::] (DEnvNil F tv) (subst_at 0 arg body) HsubAt)
      (type_of (subst_bvar arg body)) (esym Etbvar) :=
  cast_forward_reverse HType (interpType (frTyOp F) tv)
    (type_of (subst_bvar arg body)) (type_of (subst_at 0 arg body))
    (denote F tv venv [::] (DEnvNil F tv) (subst_bvar arg body) Hsub)
    (denote F tv venv [::] (DEnvNil F tv) (subst_at 0 arg body) HsubAt)
    Etbvar Hd2.
rewrite Hd3.
exact: (eq_rect_transport HType (interpType (frTyOp F) tv)
  (type_of (subst_at 0 arg body)) (type_of body) (type_of (subst_bvar arg body))
  (denote F tv venv [::] (DEnvNil F tv) (subst_at 0 arg body) HsubAt)
  (denote F tv venv [:: type_of arg]
    (DEnvCons F tv (type_of arg) [::]
      (denote F tv venv [::] (DEnvNil F tv) arg Harg) (DEnvNil F tv))
    body Hbody)
  Ety0 (esym Etbvar) (esym (type_of_subst_bvar arg body Hbody)) Hd).
Qed.


Lemma betaValid F thy t th' :
  WellFormedTheory thy -> BETA thy t = Some th' -> Valid F thy th'.
Proof.
move=> WFT Hbeta.
split; first exact: (betaWellFormed thy t th' WFT Hbeta).
move=> HM tv venv.
move: Hbeta; rewrite /BETA.
case: ifP => [Hct | //].
case: t Hct => [w | i ty | n ty | f x | aty body] Hct //.
case: f Hct => [w | i ty | n ty | f2 x2 | aty2 body2] Hct //.
move=> [<-] Hhyps Hcc Hbc.
move: Hct; rewrite /check_term /= => /andP[/andP[/andP[Haty Hbody] Hx] Hxfun].
have Exty : aty2 = type_of x := elimT eqP Hxfun.
have Exty' := esym Exty.
clear Exty.
move: Haty Hbody Hxfun Hcc Hbc Hhyps.
case: aty2 / Exty' => Haty Hbody Hxfun Hcc Hbc Hhyps.
have Hf : check_term thy (TmAbs (type_of x) body2).
  by rewrite /check_term /= Haty Hbody.
have Hres := subst_bvar_check thy x body2 Hx Hbody.
have Etr : type_of (TmComb (TmAbs (type_of x) body2) x) = type_of (subst_bvar x body2).
  have [Etb _] := subst_at_type_check thy x [::] body2 Hx Hbody.
  rewrite /= in Etb.
  by rewrite /= /subst_bvar type_of_shift Etb.
have Hfx : check_term thy (TmComb (TmAbs (type_of x) body2) x).
  by rewrite /check_term /= Haty Hbody Hx Hxfun.
apply: (SafeDenote_mk_eq F thy tv venv (TmComb (TmAbs (type_of x) body2) x)
  (subst_bvar x body2) Hfx Hres Etr Hbc HM.1 Hcc).2.
have Hisfun : is_fun (type_of (TmAbs (type_of x) body2)) := erefl.
have Hdom : (dest_fun (type_of (TmAbs (type_of x) body2))).1 = type_of x := erefl.
have Hcomb := SafeDenote_comb F thy tv venv (TmAbs (type_of x) body2) x
  Hisfun Hdom Hf Hx Hfx.
have Etbody : type_of (TmComb (TmAbs (type_of x) body2) x) = type_of body2 :=
  type_of_mk_comb_isfun (TmAbs (type_of x) body2) x Hisfun.
have Hwb : WellTypedShape body2 [:: type_of x] :=
  check_open_term_WellTypedShape thy body2 [:: type_of x] Hbody.
have Hwarg : WellTypedShape x [::] :=
  check_open_term_WellTypedShape thy x [::] Hx.
have Hab : denote F tv venv [::] (DEnvNil F tv) (TmAbs (type_of x) body2)
    (check_open_term_WellTypedShape thy (TmAbs (type_of x) body2) [::] Hf) =
  fun a => denote F tv venv [:: type_of x]
    (DEnvCons F tv (type_of x) [::] a (DEnvNil F tv)) body2 Hwb.
  rewrite (denote_abs F tv venv [::] (DEnvNil F tv) (type_of x) body2
    (check_open_term_WellTypedShape thy (TmAbs (type_of x) body2) [::] Hf)).
  apply: functional_extensionality => a.
  exact: (denote_irrel F tv venv [:: type_of x]
    (DEnvCons F tv (type_of x) [::] a (DEnvNil F tv)) body2
    (check_open_term_WellTypedShape thy (TmAbs (type_of x) body2) [::] Hf) Hwb).
have Happ : applyFun F tv (type_of (TmAbs (type_of x) body2)) (type_of x)
    Hisfun Hdom
    (SafeDenote F thy tv venv (TmAbs (type_of x) body2) Hf)
    (SafeDenote F thy tv venv x Hx) =
  denote F tv venv [:: type_of x]
    (DEnvCons F tv (type_of x) [::]
      (denote F tv venv [::] (DEnvNil F tv) x Hwarg) (DEnvNil F tv)) body2 Hwb.
  rewrite (applyFun_mk_fun F tv (type_of x) (type_of body2) (type_of x)
    Hisfun Hdom
    (SafeDenote F thy tv venv (TmAbs (type_of x) body2) Hf)
    (SafeDenote F thy tv venv x Hx)).
  rewrite (HType_UIP _ _ (esym Hdom) (erefl (type_of x))) /=.
  rewrite /SafeDenote Hab /=.
  by rewrite (denote_irrel F tv venv [::] (DEnvNil F tv) x
    (check_open_term_WellTypedShape thy x [::] Hx) Hwarg).

have HdenoteEq :
  eq_rect (type_of (TmComb (TmAbs (type_of x) body2) x))
    (interpType (frTyOp F) tv)
    (SafeDenote F thy tv venv (TmComb (TmAbs (type_of x) body2) x) Hfx)
    (type_of body2) Etbody =
  denote F tv venv [:: type_of x]
    (DEnvCons F tv (type_of x) [::]
      (denote F tv venv [::] (DEnvNil F tv) x Hwarg) (DEnvNil F tv)) body2 Hwb.
  rewrite (HType_UIP _ _ (type_of_mk_comb_isfun (TmAbs (type_of x) body2) x Hisfun) Etbody)
    in Hcomb.
  rewrite Hcomb Happ.
  by [].
have HsubBridge := SafeDenote_subst_bvar F tv venv x body2 Hwarg Hwb
  (check_open_term_WellTypedShape thy (subst_bvar x body2) [::] Hres).
rewrite /SafeDenote.
have Hbridge2 : eq_rect (type_of (subst_bvar x body2)) (interpType (frTyOp F) tv)
    (SafeDenote F thy tv venv (subst_bvar x body2) Hres) (type_of body2)
    (type_of_subst_bvar x body2 Hwb) =
  denote F tv venv [:: type_of x]
    (DEnvCons F tv (type_of x) [::]
      (denote F tv venv [::] (DEnvNil F tv) x Hwarg) (DEnvNil F tv)) body2 Hwb :=
  cast_reverse HType (interpType (frTyOp F) tv)
    (type_of (subst_bvar x body2)) (type_of body2)
    (SafeDenote F thy tv venv (subst_bvar x body2) Hres)
    (denote F tv venv [:: type_of x]
      (DEnvCons F tv (type_of x) [::]
        (denote F tv venv [::] (DEnvNil F tv) x Hwarg) (DEnvNil F tv)) body2 Hwb)
    (type_of_subst_bvar x body2 Hwb) HsubBridge.
have HcastEq :
  eq_rect (type_of (subst_bvar x body2)) (interpType (frTyOp F) tv)
    (SafeDenote F thy tv venv (subst_bvar x body2) Hres)
    (type_of (TmComb (TmAbs (type_of x) body2) x)) (esym Etr) =
  eq_rect (type_of body2) (interpType (frTyOp F) tv)
    (denote F tv venv [:: type_of x]
      (DEnvCons F tv (type_of x) [::]
        (denote F tv venv [::] (DEnvNil F tv) x Hwarg) (DEnvNil F tv)) body2 Hwb)
    (type_of (TmComb (TmAbs (type_of x) body2) x)) (esym Etbody).
  exact: (eq_rect_transport HType (interpType (frTyOp F) tv)
    (type_of (subst_bvar x body2)) (type_of body2)
    (type_of (TmComb (TmAbs (type_of x) body2) x))
    (SafeDenote F thy tv venv (subst_bvar x body2) Hres)
    (denote F tv venv [:: type_of x]
      (DEnvCons F tv (type_of x) [::]
        (denote F tv venv [::] (DEnvNil F tv) x Hwarg) (DEnvNil F tv)) body2 Hwb)
    (type_of_subst_bvar x body2 Hwb) (esym Etr) (esym Etbody) Hbridge2).
rewrite HcastEq.
exact: (cast_forward_reverse HType (interpType (frTyOp F) tv)
  (type_of (TmComb (TmAbs (type_of x) body2) x)) (type_of body2)
  (SafeDenote F thy tv venv (TmComb (TmAbs (type_of x) body2) x) Hfx)
  (denote F tv venv [:: type_of x]
    (DEnvCons F tv (type_of x) [::]
      (denote F tv venv [::] (DEnvNil F tv) x Hwarg) (DEnvNil F tv)) body2 Hwb)
  Etbody HdenoteEq).
Qed.

Lemma eq_rect_cancel (A B : Type) (x : A) (e : A = B) :
  eq_rect B (fun T : Type => T) (eq_rect A (fun T : Type => T) x B e)
    A (esym e) = x.
Proof. move: x; by case: B / e. Qed.

Lemma eq_rect_arrow2 (X1 X2 Y1 Y2 : Type) (eX : X1 = X2) (eY : Y1 = Y2)
    (f : X1 -> Y1) (Earrow : (X1 -> Y1) = (X2 -> Y2)) (a : X2) :
  eq_rect (X1 -> Y1) (fun T => T) f (X2 -> Y2) Earrow a =
  eq_rect Y1 (fun T => T) (f (eq_rect X2 (fun T => T) a X1 (esym eX)))
    Y2 eY.
Proof.
move: f Earrow a.
case: X2 / eX.
case: Y2 / eY.
move=> f Earrow a.
by rewrite (proof_irrelevance _ Earrow (erefl (X1 -> Y1))).
Qed.

Lemma applyFun_subst F tv tyin D R
    (Hisfun : is_fun (mk_fun D R))
    (Hisfun' : is_fun (type_subst tyin (mk_fun D R)))
    (Heq' : (dest_fun (type_subst tyin (mk_fun D R))).1 = type_subst tyin D)
    (fv : interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R))
    (xv : interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) D) :
  applyFun F tv (type_subst tyin (mk_fun D R)) (type_subst tyin D) Hisfun' Heq'
    (eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R)) (fun T : Type => T) fv
       (interpType (frTyOp F) tv (type_subst tyin (mk_fun D R))) (esym (interpType_subst F tv tyin (mk_fun D R))))
    (eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) D) (fun T : Type => T) xv
       (interpType (frTyOp F) tv (type_subst tyin D)) (esym (interpType_subst F tv tyin D)))
  =
  eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) R) (fun T : Type => T)
    (applyFun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R) D Hisfun (erefl D) fv xv)
    (interpType (frTyOp F) tv (type_subst tyin R))
    (esym (interpType_subst F tv tyin R)).
Proof.
rewrite (applyFun_mk_fun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) D R D Hisfun (erefl D) fv xv).
rewrite (applyFun_mk_fun F tv (type_subst tyin D) (type_subst tyin R) (type_subst tyin D)
  Hisfun' Heq').
rewrite (proof_irrelevance _ Heq' (erefl (type_subst tyin D))) /=.
have eD := esym (interpType_subst F tv tyin D).
have eR := esym (interpType_subst F tv tyin R).
have eDR := esym (interpType_subst F tv tyin (mk_fun D R)).
rewrite (proof_irrelevance _ (esym (interpType_subst F tv tyin (mk_fun D R))) eDR).
rewrite (proof_irrelevance _ (esym (interpType_subst F tv tyin D)) eD).
rewrite (proof_irrelevance _ (esym (interpType_subst F tv tyin R)) eR).
rewrite (eq_rect_arrow2 (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) D)
  (interpType (frTyOp F) tv (type_subst tyin D))
  (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) R)
  (interpType (frTyOp F) tv (type_subst tyin R))
  eD eR fv eDR).
by rewrite (eq_rect_cancel _ _ _ eD).
Qed.

Definition venv_subst (F : Frame) (tv : Name -> {T : Type & T}) (tyin : {fmap Name -> HType})
    (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v)) :
    forall w : FVar, interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (fv_ty w) :=
  fun w =>
    eq_rect _ (fun T : Type => T)
      (venv (mkFVar (fv_name w) (type_subst tyin (fv_ty w))))
      _ (interpType_subst F tv tyin (fv_ty w)).

Fixpoint DEnv_subst (F : Frame) (tv : Name -> {T : Type & T}) (tyin : {fmap Name -> HType})
    (env : seq HType) (d : DEnv F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) env) {struct d} :
    DEnv F tv (map (type_subst tyin) env) :=
  match d in DEnv _ _ e return DEnv F tv (map (type_subst tyin) e) with
  | DEnvNil => DEnvNil F tv
  | DEnvCons ty env0 v d0 =>
      DEnvCons F tv (type_subst tyin ty) (map (type_subst tyin) env0)
        (eq_rect _ (fun T : Type => T) v _ (esym (interpType_subst F tv tyin ty)))
        (DEnv_subst F tv tyin env0 d0)
  end.

Lemma type_of_inst_type tyin t env :
  WellTypedShape t env ->
  type_of (inst_type tyin t) = type_subst tyin (type_of t).
Proof.
elim: t env => [v | i ty | n ty | f IHf x IHx | aty b IHb] env //=.
- move=> [Hf [Hx [Hisfun Hdom]]].
  have Ef := IHf env Hf.
  by rewrite /= Ef Hisfun (is_fun_subst tyin (type_of f) Hisfun)
    (dest_fun_subst tyin (type_of f) Hisfun).
- move=> Hb.
  by rewrite /= (IHb (aty :: env) Hb).
Qed.

Lemma nth_map_type_subst tyin env i
    (Hi : i < size env) (Hi' : i < size (map (type_subst tyin) env)) :
  nth (HTyVar NAlpha) (map (type_subst tyin) env) i =
    type_subst tyin (nth (HTyVar NAlpha) env i).
Proof.
rewrite -(set_nth_default (HTyVar NAlpha)
  (type_subst tyin (HTyVar NAlpha)) Hi').
exact: (nth_map (HTyVar NAlpha) (type_subst tyin (HTyVar NAlpha))
  (type_subst tyin) Hi).
Qed.

Lemma WellTypedShape_inst_type tyin t env :
  WellTypedShape t env -> WellTypedShape (inst_type tyin t) (map (type_subst tyin) env).
Proof.
elim: t env => [v | i ty | n ty | f IHf x IHx | aty b IHb] env //=.
- move=> [Hlt Hnth].
  have Hlt' : i < size (map (type_subst tyin) env) by rewrite size_map.
  split=> //.
  by rewrite (nth_map ty (type_subst tyin ty) (type_subst tyin) Hlt) Hnth.
- move=> [Hf [Hx [Hisfun Hdom]]].
  split; first exact: IHf.
  split; first exact: IHx.
  have Ef := type_of_inst_type tyin f env Hf.
  split.
  + by rewrite Ef (is_fun_subst tyin (type_of f) Hisfun).
  + have Ex := type_of_inst_type tyin x env Hx.
    by rewrite Ef Ex (dest_fun_subst tyin (type_of f) Hisfun) Hdom.
- move=> Hb.
  by rewrite -map_cons; exact: (IHb (aty :: env) Hb).
Qed.

Lemma dnth_DEnv_subst F tv tyin env (d : DEnv F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) env) i
    (Hi : i < size env) (Hi' : i < size (map (type_subst tyin) env)) :
  eq_rect (nth (HTyVar NAlpha) (map (type_subst tyin) env) i) (interpType (frTyOp F) tv)
    (dnth F tv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) i Hi')
    (type_subst tyin (nth (HTyVar NAlpha) env i))
    (nth_map_type_subst tyin env i Hi Hi')
  =
  eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (nth (HTyVar NAlpha) env i))
    (fun T => T)
    (dnth F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) env d i Hi)
    (interpType (frTyOp F) tv (type_subst tyin (nth (HTyVar NAlpha) env i)))
    (esym (interpType_subst F tv tyin (nth (HTyVar NAlpha) env i))).
Proof.
move: i Hi Hi'.
elim: d => [|ty env0 v d0 IH] [|i] Hi Hi' //=.
- rewrite (proof_irrelevance _ (nth_map_type_subst tyin (ty :: env0) 0 Hi Hi')
    (erefl (type_subst tyin ty))) /=.
  by [].
- have Hi0 : i < size env0 by exact: Hi.
  have Hi0' : i < size (map (type_subst tyin) env0) by exact: Hi'.
  rewrite (proof_irrelevance _ Hi Hi0) (proof_irrelevance _ Hi' Hi0').
  rewrite (proof_irrelevance _
    (nth_map_type_subst tyin (ty :: env0) i.+1 Hi0 Hi0')
    (nth_map_type_subst tyin env0 i Hi0 Hi0')).
  exact: IH i Hi0 Hi0'.
Qed.

Lemma eq_rect_JMeq (Ty : Type) (P : Ty -> Type) (A B : Ty) (e : A = B) (x : P A) :
  JMeq (eq_rect A P x B e) x.
Proof. by case: B / e. Qed.

Lemma eq_rect_LR_to_JMeq (Idx : Type) (P : Idx -> Type) (A B : Idx) (C : Type)
    (e1 : A = B) (e2 : C = P B) (x : P A) (y : C) :
  eq_rect A P x B e1 = eq_rect C (fun T => T) y (P B) e2 -> JMeq x y.
Proof.
move=> Heq.
apply: (JMeq_trans (JMeq_sym (eq_rect_JMeq Idx P A B e1 x))).
rewrite Heq.
exact: (eq_rect_JMeq Type (fun T => T) C (P B) e2 y).
Qed.

Lemma eq_rect_L_to_JMeq (Idx : Type) (P : Idx -> Type) (A B : Idx) (e1 : A = B) (x : P A) (y : P B) :
  eq_rect A P x B e1 = y -> JMeq x y.
Proof.
move=> Heq.
apply: (JMeq_trans (JMeq_sym (eq_rect_JMeq Idx P A B e1 x))).
by rewrite Heq.
Qed.

Lemma JMeq_fun (A A' B B' : Type) (f : A -> B) (f' : A' -> B') :
  A = A' -> B = B' ->
  (forall (a : A) (a' : A'), JMeq a a' -> JMeq (f a) (f' a')) -> JMeq f f'.
Proof.
move=> EA EB.
move: f'.
case: A' / EA.
case: B' / EB => f' H.
have Hext : f = f' by apply: functional_extensionality => a; apply/JMeq_eq/H/JMeq_refl.
by rewrite Hext.
Qed.

Lemma applyFun_JMeq F tv fty fty' xty xty'
    (Hisfun : is_fun fty) (Hisfun' : is_fun fty')
    (Heq : (dest_fun fty).1 = xty) (Heq' : (dest_fun fty').1 = xty')
    (fv : interpType (frTyOp F) tv fty) (fv' : interpType (frTyOp F) tv fty')
    (xv : interpType (frTyOp F) tv xty) (xv' : interpType (frTyOp F) tv xty') :
  fty = fty' -> JMeq fv fv' -> JMeq xv xv' ->
  JMeq (applyFun F tv fty xty Hisfun Heq fv xv) (applyFun F tv fty' xty' Hisfun' Heq' fv' xv').
Proof.
move=> Ef.
move: Hisfun' Heq' fv'.
case: fty' / Ef => Hisfun' Heq' fv' Hfv Hxv.
have Ex : xty = xty' by rewrite -Heq -Heq'.
move: Heq' xv' Hxv.
case: xty' / Ex => Heq' xv' Hxv.
have -> : fv' = fv by apply/JMeq_eq; apply: JMeq_sym; exact: Hfv.
have -> : xv' = xv by apply/JMeq_eq; apply: JMeq_sym; exact: Hxv.
rewrite (proof_irrelevance _ Hisfun' Hisfun) (proof_irrelevance _ Heq' Heq).
exact: JMeq_refl.
Qed.

Lemma applyFun_subst_JMeq F tv tyin D R xty0
    (Hisfun0 : is_fun (mk_fun D R)) (Heq0 : (dest_fun (mk_fun D R)).1 = xty0)
    (Hisfun1 : is_fun (type_subst tyin (mk_fun D R)))
    (Heq1 : (dest_fun (type_subst tyin (mk_fun D R))).1 = type_subst tyin xty0)
    (fv1 : interpType (frTyOp F) tv (type_subst tyin (mk_fun D R)))
    (fv0 : interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R))
    (xv1 : interpType (frTyOp F) tv (type_subst tyin xty0))
    (xv0 : interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) xty0) :
  JMeq fv1 fv0 -> JMeq xv1 xv0 ->
  JMeq (applyFun F tv (type_subst tyin (mk_fun D R)) (type_subst tyin xty0) Hisfun1 Heq1 fv1 xv1)
       (applyFun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R) xty0 Hisfun0 Heq0 fv0 xv0).
Proof.
move=> Hfv Hxv.
have ED : D = xty0 by rewrite -Heq0.
move: Heq1 Heq0 xv0 xv1 Hxv.
case: xty0 / ED => Heq1 Heq0 xv0 xv1 Hxv.
rewrite (proof_irrelevance _ Heq0 (erefl D)).
have Ef1 : fv1 = eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R)) (fun T => T) fv0
    (interpType (frTyOp F) tv (type_subst tyin (mk_fun D R))) (esym (interpType_subst F tv tyin (mk_fun D R))).
  apply/JMeq_eq; apply: (JMeq_trans Hfv); apply: JMeq_sym.
  exact: (eq_rect_JMeq Type (fun T => T)
    (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R))
    (interpType (frTyOp F) tv (type_subst tyin (mk_fun D R)))
    (esym (interpType_subst F tv tyin (mk_fun D R))) fv0).
have Ex1 : xv1 = eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) D) (fun T => T) xv0
    (interpType (frTyOp F) tv (type_subst tyin D)) (esym (interpType_subst F tv tyin D)).
  apply/JMeq_eq; apply: (JMeq_trans Hxv); apply: JMeq_sym.
  exact: (eq_rect_JMeq Type (fun T => T)
    (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) D)
    (interpType (frTyOp F) tv (type_subst tyin D))
    (esym (interpType_subst F tv tyin D)) xv0).
rewrite Ef1 Ex1.
rewrite (applyFun_subst F tv tyin D R Hisfun0 Hisfun1 Heq1 fv0 xv0).
exact: (eq_rect_JMeq Type (fun T => T)
  (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) R)
  (interpType (frTyOp F) tv (type_subst tyin R))
  (esym (interpType_subst F tv tyin R))
  (applyFun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R) D Hisfun0 (erefl D) fv0 xv0)).
Qed.

Lemma denote_inst_type F thy tv venv tyin t (HM : ModelsTheoryNat F thy) :
  forall env (d : DEnv F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) env)
    (Hcheck : check_open_term thy t env)
    (Hwt : WellTypedShape t env)
    (Hwt' : WellTypedShape (inst_type tyin t) (map (type_subst tyin) env)),
  eq_rect (type_of (inst_type tyin t)) (interpType (frTyOp F) tv)
    (denote F tv venv (map (type_subst tyin) env)
       (DEnv_subst F tv tyin env d) (inst_type tyin t) Hwt')
    (type_subst tyin (type_of t)) (type_of_inst_type tyin t env Hwt)
  =
  eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of t)) (fun T => T)
    (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d t Hwt)
    (interpType (frTyOp F) tv (type_subst tyin (type_of t)))
    (esym (interpType_subst F tv tyin (type_of t))).
Proof.
elim: t => [v | i ty | n ty | f IHf x IHx | aty b IHb] env d Hcheck Hwt Hwt'.
- rewrite (HType_UIP _ _ (type_of_inst_type tyin (TmFVar v) env Hwt) (erefl (type_subst tyin (fv_ty v)))).
  rewrite (denote_irrel F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
    (inst_type tyin (TmFVar v)) Hwt' I).
  rewrite /venv_subst /=.
  symmetry.
  exact: (eq_rect_cancel _ _ _ (interpType_subst F tv tyin (fv_ty v))).
- move: Hwt => [Hlt Hnth].
  have Ety0 : nth (HTyVar NAlpha) env i = ty :=
    eq_trans (esym (set_nth_default (HTyVar NAlpha) ty Hlt)) Hnth.
  move: Hnth Hwt' Hcheck.
  case: ty / Ety0 => Hnth Hwt' Hcheck.
  have Hi' : i < size (map (type_subst tyin) env) by rewrite size_map.
  have Hnth'' : nth (type_subst tyin (nth (HTyVar NAlpha) env i))
      (map (type_subst tyin) env) i = type_subst tyin (nth (HTyVar NAlpha) env i).
    by rewrite (nth_map (nth (HTyVar NAlpha) env i) (type_subst tyin (nth (HTyVar NAlpha) env i))
      (type_subst tyin) Hlt) Hnth.
  rewrite (HType_UIP _ _
    (type_of_inst_type tyin (TmBVar i (nth (HTyVar NAlpha) env i)) env (conj Hlt Hnth))
    (erefl (type_subst tyin (nth (HTyVar NAlpha) env i)))).
  rewrite (denote_irrel F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
    (inst_type tyin (TmBVar i (nth (HTyVar NAlpha) env i))) Hwt' (conj Hi' Hnth'')).
  rewrite (denote_bvar F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
    i (type_subst tyin (nth (HTyVar NAlpha) env i)) Hi' Hnth'').
  rewrite (denote_bvar F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d
    i (nth (HTyVar NAlpha) env i) Hlt Hnth).
  rewrite (eq_rect_trans HType (interpType (frTyOp F) tv)
    (nth (HTyVar NAlpha) (map (type_subst tyin) env) i)
    (nth (type_subst tyin (nth (HTyVar NAlpha) env i)) (map (type_subst tyin) env) i)
    (type_subst tyin (nth (HTyVar NAlpha) env i))
    (dnth F tv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) i Hi')
    (esym (set_nth_default (HTyVar NAlpha) (type_subst tyin (nth (HTyVar NAlpha) env i)) Hi'))
    Hnth'').
  rewrite (eq_rect_trans HType (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin))
    (nth (HTyVar NAlpha) env i) (nth (nth (HTyVar NAlpha) env i) env i)
    (nth (HTyVar NAlpha) env i)
    (dnth F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) env d i Hlt)
    (esym (set_nth_default (HTyVar NAlpha) (nth (HTyVar NAlpha) env i) Hlt))
    Hnth).
  rewrite (proof_irrelevance _
    (eq_trans (esym (set_nth_default (HTyVar NAlpha) (nth (HTyVar NAlpha) env i) Hlt)) Hnth)
    (erefl (nth (HTyVar NAlpha) env i))).
  rewrite (proof_irrelevance _
    (eq_trans
       (esym (set_nth_default (HTyVar NAlpha) (type_subst tyin (nth (HTyVar NAlpha) env i)) Hi'))
       Hnth'')
    (nth_map_type_subst tyin env i Hlt Hi')).
  rewrite /=.
  by rewrite (dnth_DEnv_subst F tv tyin env d i Hlt Hi').
- move: Hcheck => /andP[_ Hcn].
  case Egty: (const_type thy n) Hcn => [gty|] // Hcn.
  case Em: (type_match gty ty [fmap]) Hcn => [m|] // _.
  rewrite (HType_UIP _ _ (type_of_inst_type tyin (TmConst n ty) env Hwt) (erefl (type_subst tyin ty))).
  rewrite (denote_irrel F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
    (inst_type tyin (TmConst n ty)) Hwt' I).
  exact: (HM n gty Egty ty m Em tv tyin).
- move: Hcheck => /andP[/andP[Hcf Hcx] _].
  have Hf := Hwt.1.
  have Hx := Hwt.2.1.
  have Hisfun := Hwt.2.2.1.
  have Heq := Hwt.2.2.2.
  have HfI := Hwt'.1.
  have HxI := Hwt'.2.1.
  have HisfunI := Hwt'.2.2.1.
  have HeqI := Hwt'.2.2.2.
  have [D [R EfDR']] := is_fun_HTyApp (type_of f) Hisfun.
  have Etf := type_of_inst_type tyin f env Hf.
  have Etx := type_of_inst_type tyin x env Hx.
  have ED : type_of x = D := eq_trans (esym Heq) (f_equal (fun ty => (dest_fun ty).1) EfDR').
  have Ef1 : type_of (inst_type tyin f) = type_subst tyin (mk_fun D R) :=
    eq_trans Etf (f_equal (type_subst tyin) EfDR').
  have Ex1 : type_of (inst_type tyin x) = type_subst tyin D :=
    eq_trans Etx (f_equal (type_subst tyin) ED).
  have Hisfun1 : is_fun (type_subst tyin (mk_fun D R)) :=
    eq_rect (type_of f) (fun ty => is_fun (type_subst tyin ty)) (is_fun_subst tyin (type_of f) Hisfun)
      (mk_fun D R) EfDR'.
  have Heq1 : (dest_fun (type_subst tyin (mk_fun D R))).1 = type_subst tyin D.
    move: (dest_fun_subst tyin (type_of f) Hisfun) => Hds.
    have -> : (dest_fun (type_subst tyin (mk_fun D R))).1 = (dest_fun (type_subst tyin (type_of f))).1.
      by rewrite EfDR'.
    by rewrite Hds Heq ED.
  (* Step 1: recursive JMeq facts for f and x *)
  have Hvf_jm : JMeq
      (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin f) HfI)
      (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d f Hf) :=
    eq_rect_LR_to_JMeq HType (interpType (frTyOp F) tv)
      (type_of (inst_type tyin f)) (type_subst tyin (type_of f))
      (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of f))
      (type_of_inst_type tyin f env Hf) (esym (interpType_subst F tv tyin (type_of f)))
      (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin f) HfI)
      (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d f Hf)
      (IHf env d Hcf Hf HfI).
  have Hvx_jm : JMeq
      (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin x) HxI)
      (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d x Hx) :=
    eq_rect_LR_to_JMeq HType (interpType (frTyOp F) tv)
      (type_of (inst_type tyin x)) (type_subst tyin (type_of x))
      (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of x))
      (type_of_inst_type tyin x env Hx) (esym (interpType_subst F tv tyin (type_of x)))
      (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin x) HxI)
      (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d x Hx)
      (IHx env d Hcx Hx HxI).
  pose fv1 := eq_rect (type_of (inst_type tyin f)) (interpType (frTyOp F) tv)
    (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin f) HfI)
    (type_subst tyin (mk_fun D R)) Ef1.
  pose xv1 := eq_rect (type_of (inst_type tyin x)) (interpType (frTyOp F) tv)
    (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin x) HxI)
    (type_subst tyin D) Ex1.
  pose fv0 := eq_rect (type_of f) (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin))
    (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d f Hf)
    (mk_fun D R) EfDR'.
  pose xv0 := eq_rect (type_of x) (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin))
    (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d x Hx)
    D ED.
  have Hcast1 : JMeq
      (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin f) HfI) fv1.
    apply: JMeq_sym. exact: (eq_rect_JMeq _ (interpType (frTyOp F) tv) _ _ Ef1 _).
  have Hcast2 : JMeq
      (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin x) HxI) xv1.
    apply: JMeq_sym. exact: (eq_rect_JMeq _ (interpType (frTyOp F) tv) _ _ Ex1 _).
  have Hcast3 : JMeq (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d f Hf) fv0.
    apply: JMeq_sym.
    exact: (eq_rect_JMeq _ (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin)) _ _ EfDR' _).
  have Hcast4 : JMeq (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d x Hx) xv0.
    apply: JMeq_sym.
    exact: (eq_rect_JMeq _ (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin)) _ _ ED _).
  have Hfv01 : JMeq fv1 fv0 := JMeq_trans (JMeq_sym Hcast1) (JMeq_trans Hvf_jm Hcast3).
  have Hxv01 : JMeq xv1 xv0 := JMeq_trans (JMeq_sym Hcast2) (JMeq_trans Hvx_jm Hcast4).
  (* Step 2: relate the two applyFun calls by JMeq, through mk_fun D R *)
  have Happ_jm1 : JMeq
      (applyFun F tv (type_of (inst_type tyin f)) (type_of (inst_type tyin x)) HisfunI HeqI
        (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin f) HfI)
        (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin x) HxI))
      (applyFun F tv (type_subst tyin (mk_fun D R)) (type_subst tyin D) Hisfun1 Heq1 fv1 xv1) :=
    applyFun_JMeq F tv (type_of (inst_type tyin f)) (type_subst tyin (mk_fun D R))
      (type_of (inst_type tyin x)) (type_subst tyin D)
      HisfunI Hisfun1 HeqI Heq1 _ fv1 _ xv1 Ef1 Hcast1 Hcast2.
  have Hisfun_DR : is_fun (mk_fun D R) :=
    eq_rect (type_of f) is_fun Hisfun (mk_fun D R) EfDR'.
  have Happ_jm2 : JMeq
      (applyFun F tv (type_subst tyin (mk_fun D R)) (type_subst tyin D) Hisfun1 Heq1 fv1 xv1)
      (applyFun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R) D Hisfun_DR (erefl D) fv0 xv0) :=
    applyFun_subst_JMeq F tv tyin D R D Hisfun_DR (erefl D) Hisfun1 Heq1 fv1 fv0 xv1 xv0 Hfv01 Hxv01.
  have Happ_jm3 : JMeq
      (applyFun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R) D Hisfun_DR (erefl D) fv0 xv0)
      (applyFun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of f) (type_of x) Hisfun Heq
        (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d f Hf)
        (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d x Hx)) :=
    applyFun_JMeq F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (mk_fun D R) (type_of f) D (type_of x)
      Hisfun_DR Hisfun (erefl D) Heq fv0 _ xv0 _ (esym EfDR') (JMeq_sym Hcast3) (JMeq_sym Hcast4).
  have Happ_jm : JMeq
      (applyFun F tv (type_of (inst_type tyin f)) (type_of (inst_type tyin x)) HisfunI HeqI
        (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin f) HfI)
        (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin x) HxI))
      (applyFun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of f) (type_of x) Hisfun Heq
        (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d f Hf)
        (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d x Hx)) :=
    JMeq_trans Happ_jm1 (JMeq_trans Happ_jm2 Happ_jm3).
  (* Step 3: bridge through denote_comb on both sides *)
  have Hd1 := denote_comb F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
    (inst_type tyin f) (inst_type tyin x) HisfunI HeqI HfI HxI
    (conj HfI (conj HxI (conj HisfunI HeqI))).
  have Hd2 := denote_comb F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d
    f x Hisfun Heq Hf Hx (conj Hf (conj Hx (conj Hisfun Heq))).
  have Hd1_jm : JMeq
      (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
        (mk_comb (inst_type tyin f) (inst_type tyin x)) (conj HfI (conj HxI (conj HisfunI HeqI))))
      (applyFun F tv (type_of (inst_type tyin f)) (type_of (inst_type tyin x)) HisfunI HeqI
        (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin f) HfI)
        (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin x) HxI)) :=
    eq_rect_L_to_JMeq HType (interpType (frTyOp F) tv)
      (type_of (mk_comb (inst_type tyin f) (inst_type tyin x))) (dest_fun (type_of (inst_type tyin f))).2
      (type_of_mk_comb_isfun (inst_type tyin f) (inst_type tyin x) HisfunI)
      (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
        (mk_comb (inst_type tyin f) (inst_type tyin x)) (conj HfI (conj HxI (conj HisfunI HeqI))))
      (applyFun F tv (type_of (inst_type tyin f)) (type_of (inst_type tyin x)) HisfunI HeqI
        (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin f) HfI)
        (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d) (inst_type tyin x) HxI))
      Hd1.
  have Hd2_jm : JMeq
      (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d
        (mk_comb f x) (conj Hf (conj Hx (conj Hisfun Heq))))
      (applyFun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of f) (type_of x) Hisfun Heq
        (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d f Hf)
        (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d x Hx)) :=
    eq_rect_L_to_JMeq HType (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin))
      (type_of (mk_comb f x)) (dest_fun (type_of f)).2
      (type_of_mk_comb_isfun f x Hisfun)
      (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d
        (mk_comb f x) (conj Hf (conj Hx (conj Hisfun Heq))))
      (applyFun F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of f) (type_of x) Hisfun Heq
        (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d f Hf)
        (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d x Hx))
      Hd2.
  have Hcomb_jm : JMeq
      (denote F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
        (mk_comb (inst_type tyin f) (inst_type tyin x)) (conj HfI (conj HxI (conj HisfunI HeqI))))
      (denote F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d
        (mk_comb f x) (conj Hf (conj Hx (conj Hisfun Heq)))) :=
    JMeq_trans Hd1_jm (JMeq_trans Happ_jm (JMeq_sym Hd2_jm)).
  rewrite (denote_irrel F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
    (inst_type tyin (TmComb f x)) Hwt' (conj HfI (conj HxI (conj HisfunI HeqI)))).
  rewrite (denote_irrel F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d
    (TmComb f x) Hwt (conj Hf (conj Hx (conj Hisfun Heq)))).
  apply/JMeq_eq.
  apply: (JMeq_trans (eq_rect_JMeq HType (interpType (frTyOp F) tv)
    (type_of (inst_type tyin (TmComb f x))) (type_subst tyin (type_of (TmComb f x)))
    (type_of_inst_type tyin (TmComb f x) env Hwt) _)).
  apply: (JMeq_trans Hcomb_jm).
  apply: JMeq_sym.
  exact: (eq_rect_JMeq Type (fun T => T)
    (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of (TmComb f x)))
    (interpType (frTyOp F) tv (type_subst tyin (type_of (TmComb f x))))
    (esym (interpType_subst F tv tyin (type_of (TmComb f x)))) _).
- move: Hcheck => /andP[_ Hcb].
  rewrite (denote_abs F tv venv (map (type_subst tyin) env) (DEnv_subst F tv tyin env d)
    (type_subst tyin aty) (inst_type tyin b) Hwt').
  rewrite (denote_abs F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) env d aty b Hwt).
  apply/JMeq_eq.
  apply: (JMeq_trans (eq_rect_JMeq HType (interpType (frTyOp F) tv)
    (type_of (inst_type tyin (TmAbs aty b))) (type_subst tyin (type_of (TmAbs aty b)))
    (type_of_inst_type tyin (TmAbs aty b) env Hwt) _)).
  apply: JMeq_sym.
  apply: (JMeq_trans (eq_rect_JMeq Type (fun T => T)
    (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of (TmAbs aty b)))
    (interpType (frTyOp F) tv (type_subst tyin (type_of (TmAbs aty b))))
    (esym (interpType_subst F tv tyin (type_of (TmAbs aty b)))) _)).
  apply: JMeq_sym.
  apply: (JMeq_fun (interpType (frTyOp F) tv (type_subst tyin aty))
    (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) aty)
    (interpType (frTyOp F) tv (type_of (inst_type tyin b)))
    (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of b))
    _ _
    (interpType_subst F tv tyin aty)
    (eq_trans (f_equal (interpType (frTyOp F) tv) (type_of_inst_type tyin b (aty :: env) Hwt))
      (interpType_subst F tv tyin (type_of b)))) => a' a Ha'.
  have -> : a' = eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) aty) (fun T => T) a
      (interpType (frTyOp F) tv (type_subst tyin aty)) (esym (interpType_subst F tv tyin aty)).
    apply/JMeq_eq; apply: (JMeq_trans Ha'); apply: JMeq_sym.
    exact: (eq_rect_JMeq Type (fun T => T)
      (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) aty)
      (interpType (frTyOp F) tv (type_subst tyin aty))
      (esym (interpType_subst F tv tyin aty)) a).
  exact: (eq_rect_LR_to_JMeq HType (interpType (frTyOp F) tv) _ _ _ _ _ _ _
    (IHb (aty :: env) (DEnvCons F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) aty env a d) Hcb Hwt Hwt')).
Qed.

Lemma SafeDenote_inst_type F thy tv venv tyin t (HM : ModelsTheoryNat F thy) (Hct : check_term thy t)
    (HctI : check_term thy (inst_type tyin t)) :
  eq_rect (type_of (inst_type tyin t)) (interpType (frTyOp F) tv)
    (SafeDenote F thy tv venv (inst_type tyin t) HctI)
    (type_subst tyin (type_of t))
    (type_of_inst_type tyin t [::] (check_open_term_WellTypedShape thy t [::] Hct))
  =
  eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of t)) (fun T => T)
    (SafeDenote F thy (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) t Hct)
    (interpType (frTyOp F) tv (type_subst tyin (type_of t)))
    (esym (interpType_subst F tv tyin (type_of t))).
Proof.
rewrite /SafeDenote.
have Hcheck : check_open_term thy t [::] := Hct.
exact: (denote_inst_type F thy tv venv tyin t HM [::] (DEnvNil F (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin))
  Hcheck
  (check_open_term_WellTypedShape thy t [::] Hct)
  (check_open_term_WellTypedShape thy (inst_type tyin t) [::] HctI)).
Qed.

Lemma denoteProp_inst_type F thy tv venv tyin t (HM : ModelsTheoryNat F thy)
    (Hct : check_term thy t) (HctI : check_term thy (inst_type tyin t))
    (Hbt : is_bool t) (HbtI : is_bool (inst_type tyin t)) :
  denoteProp F thy tv venv (inst_type tyin t) HctI HbtI =
  denoteProp F thy (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) t Hct Hbt.
Proof.
rewrite /denoteProp.
apply/JMeq_eq.
apply: (JMeq_trans (eq_rect_JMeq HType (interpType (frTyOp F) tv)
  (type_of (inst_type tyin t)) bool_ty (elimT eqP HbtI)
  (SafeDenote F thy tv venv (inst_type tyin t) HctI))).
apply: JMeq_sym.
apply: (JMeq_trans (eq_rect_JMeq HType (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin))
  (type_of t) bool_ty (elimT eqP Hbt)
  (SafeDenote F thy (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) t Hct))).
apply: JMeq_sym.
exact: (eq_rect_LR_to_JMeq HType (interpType (frTyOp F) tv)
  (type_of (inst_type tyin t)) (type_subst tyin (type_of t))
  (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (type_of t))
  (type_of_inst_type tyin t [::] (check_open_term_WellTypedShape thy t [::] Hct))
  (esym (interpType_subst F tv tyin (type_of t)))
  (SafeDenote F thy tv venv (inst_type tyin t) HctI)
  (SafeDenote F thy (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) t Hct)
  (SafeDenote_inst_type F thy tv venv tyin t HM Hct HctI)).
Qed.

Lemma instTypeValid F thy tyin th th' :
  WellFormedTheory thy -> Valid F thy th ->
  INST_TYPE thy tyin th = Some th' -> Valid F thy th'.
Proof.
move=> WFT Vth Hinst.
split; first exact: (instTypeWellFormed thy tyin th th' WFT Vth.1 Hinst).
move=> HM tv venv.
move: Hinst; rewrite /INST_TYPE.
case: ifP => [/andP[_ Hcty] | //].
move=> [<-] Hhyps Hcc Hbc.
have [Hct [Hht [Hbt [Hbht Hstamp]]]] := Vth.1.
have Htyin := check_tyinP thy tyin Hcty.
have Horig :
  forall h (Hch : check_term thy h) (Hbh : is_bool h), h \in thm_hyps th ->
    denoteProp F thy (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) h Hch Hbh.
  move=> h Hch Hbh Hhin.
  have [HchI EhI] := check_open_term_inst_type thy tyin h [::] Htyin Hch.
  have HbhI : is_bool (inst_type tyin h).
    rewrite /is_bool EhI.
    move: Hbh; rewrite /is_bool => /eqP ->.
    by [].

  have Him : inst_type tyin h \in inst_type tyin @` (thm_hyps th).
    apply/imfsetP.
    by exists h.
  have Hinsthyp := Hhyps (inst_type tyin h) HchI HbhI Him.
  rewrite (denoteProp_inst_type F thy tv venv tyin h HM.2.2.2 Hch HchI Hbh HbhI) in Hinsthyp.
  exact: Hinsthyp.
have Hden := Vth.2 HM (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) (venv_subst F tv tyin venv) Horig Hct Hbt.
have [HccI EccI] := check_open_term_inst_type thy tyin (thm_concl th) [::] Htyin Hct.
rewrite (denoteProp_inst_type F thy tv venv tyin (thm_concl th) HM.2.2.2 Hct Hcc Hbt Hbc).
exact: Hden.
Qed.

Lemma ModelsTheory_defclause_from_base F thy n r (Hr : check_term thy r)
    (gty : HType) (Egty : const_type thy n = Some gty)
    (m : {fmap Name -> HType}) (Em : type_match gty (type_of r) [fmap] = Some m)
    (HM4 : ModelsTheoryNat F thy)
    (Hbase : forall tv (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v)),
       frConst F n tv (type_of r) = SafeDenote F thy tv venv r Hr) :
  forall tv (venv : forall v : FVar, interpType (frTyOp F) tv (fv_ty v))
    (sigma : {fmap Name -> HType})
    (Htyin : forall n0 ty0, sigma.[? n0] = Some ty0 -> check_type thy ty0),
  frConst F n tv (type_subst sigma (type_of r)) =
    eq_rect (type_of (inst_type sigma r)) (interpType (frTyOp F) tv)
      (SafeDenote F thy tv venv (inst_type sigma r)
         (proj1 (check_open_term_inst_type thy sigma r [::] Htyin Hr)))
      (type_subst sigma (type_of r))
      (proj2 (check_open_term_inst_type thy sigma r [::] Htyin Hr)).
Proof.
move=> tv venv sigma Htyin.
rewrite (HM4 n gty Egty (type_of r) m Em tv sigma).
move: (proj1 (check_open_term_inst_type thy sigma r [::] Htyin Hr))
  (proj2 (check_open_term_inst_type thy sigma r [::] Htyin Hr)) => HctI EtI.
rewrite (Hbase (tv_subst (frTyOp F) (frTyOp_inhab F) tv sigma) (venv_subst F tv sigma venv)).
apply/JMeq_eq.
apply: (JMeq_trans (eq_rect_JMeq Type (fun T => T)
  (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv sigma) (type_of r))
  (interpType (frTyOp F) tv (type_subst sigma (type_of r)))
  (esym (interpType_subst F tv sigma (type_of r)))
  (SafeDenote F thy (tv_subst (frTyOp F) (frTyOp_inhab F) tv sigma) (venv_subst F tv sigma venv) r Hr))).
apply: JMeq_sym.
apply: (JMeq_trans (eq_rect_JMeq HType (interpType (frTyOp F) tv)
  (type_of (inst_type sigma r)) (type_subst sigma (type_of r)) EtI
  (SafeDenote F thy tv venv (inst_type sigma r) HctI))).
apply: JMeq_sym.
have SDI := SafeDenote_inst_type F thy tv venv sigma r HM4 Hr HctI.
rewrite (HType_UIP _ _
  (type_of_inst_type sigma r [::] (check_open_term_WellTypedShape thy r [::] Hr))
  EtI) in SDI.
change id with (fun T : Type => T) in SDI.
apply: JMeq_sym.
apply: (eq_rect_LR_to_JMeq HType (interpType (frTyOp F) tv)
  (type_of (inst_type sigma r)) (type_subst sigma (type_of r))
  (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv sigma) (type_of r))
  EtI (esym (interpType_subst F tv sigma (type_of r)))
  (SafeDenote F thy tv venv (inst_type sigma r) HctI)
  (SafeDenote F thy (tv_subst (frTyOp F) (frTyOp_inhab F) tv sigma) (venv_subst F tv sigma venv) r Hr)).
exact: SDI.
Qed.

Lemma type_subst_id t : type_subst [fmap] t = t.
Proof.
elim/HType_rect: t => [n | n args IH] //=.
- by rewrite fnd_fmap0.
- congr HTyApp.
  elim: args IH => [|a args' IHa] //= [Ha Hargs].
  by rewrite Ha (IHa Hargs).
Qed.

Lemma inst_type_id t : inst_type [fmap] t = t.
Proof.
elim: t => [v | i ty | n ty | f IHf x IHx | aty b IHb] //=.
- by rewrite type_subst_id; case: v.
- by rewrite type_subst_id.
- by rewrite type_subst_id.
- by rewrite IHf IHx.
- by rewrite type_subst_id IHb.
Qed.

Lemma check_type_id_triv thy : forall n0 ty0, ([fmap] : {fmap Name -> HType}).[? n0] = Some ty0 -> check_type thy ty0.
Proof. by move=> n0 ty0; rewrite fnd_fmap0. Qed.

(** [SafeDenote]/[denoteProp] do not care which theory's [check_term]
    witness they are handed, as long as the term itself is unchanged --
    the theory-crossing analogue of [denoteProp_irrel]. *)
Lemma denoteProp_irrel_thy F thy thy' tv venv t
    (Hct : check_term thy t) (Hct' : check_term thy' t)
    (Hbt : is_bool t) (Hbt' : is_bool t) :
  denoteProp F thy tv venv t Hct Hbt = denoteProp F thy' tv venv t Hct' Hbt'.
Proof.
rewrite /denoteProp (SafeDenote_irrel_thy F thy thy' tv venv t Hct Hct').
by rewrite (proof_irrelevance _ (elimT eqP Hbt) (elimT eqP Hbt')).
Qed.

Lemma new_type_conservative F thy fresh n arity thy' :
  WellFormedTheory thy -> AxiomsChecked thy -> DefsChecked thy ->
  new_type thy fresh n arity = Some thy' ->
  ModelsTheory F thy -> ModelsTheory F thy'.
Proof.
move=> WFT HAC HDC Hnt [HNEq [Hax [Hdf HNat]]].
have Htyops := newTypeMonotone thy fresh n arity thy' Hnt.
have Hconsts := newTypeMonotoneConst thy fresh n arity thy' Hnt.
have Eax : th_axioms thy' = th_axioms thy.
  by move: Hnt; rewrite /new_type; case: ifP => // _ [<-].
have Edf : th_defs thy' = th_defs thy.
  by move: Hnt; rewrite /new_type; case: ifP => // _ [<-].
have Econsts : th_consts thy' = th_consts thy.
  by move: Hnt; rewrite /new_type; case: ifP => // _ [<-].
split; first exact: HNEq.
split.
- move=> ax Hin tv venv Hct Hbt.
  move: Hin; rewrite Eax => Hin.
  have Hct0 : check_term thy (thm_concl ax) := (HAC ax Hin).1.
  rewrite (denoteProp_irrel_thy F thy' thy tv venv (thm_concl ax) Hct Hct0 Hbt Hbt).
  exact: (Hax ax Hin tv venv Hct0 Hbt).
split.
- move=> n0 df; rewrite Edf => Hn0 r Hdest Hr' tv venv sigma Htyin.
  have HWFdf := HDC n0 df Hn0.
  have [Hcdf _] := HWFdf.
  have Hct_concl : check_term thy (thm_concl df) := Hcdf.
  have [ty Ety] := dest_eq_inv (thm_concl df) (mk_const n0 (type_of r)) r Hdest.
  have [Hcn0 [Hr0 _]] : check_term thy (mk_const n0 (type_of r)) /\ check_term thy r /\
      type_of (mk_const n0 (type_of r)) = type_of r.
    apply: (check_term_eq_inv thy ty (mk_const n0 (type_of r)) r WFT).
    by rewrite -Ety.
  have [gty [Egty [m Em]]] : exists gty, const_type thy n0 = Some gty /\
      exists m, type_match gty (type_of r) [fmap] = Some m.
    move: Hcn0; rewrite /check_term /=.
    move=> /andP[_ Hmatch].
    case Egty0: (const_type thy n0) Hmatch => [gty0|] //.
    case Em0: (type_match gty0 (type_of r) [fmap]) => [m0|] // _.
    exists gty0; split=> //; exists m0; exact: Em0.
  have Egty' : const_type thy' n0 = Some gty. by rewrite /const_type Econsts.
  have HNat' : ModelsTheoryNat F thy'.
    move=> n1 gty1 Egty1 ty1 m1 Em1 tv1 tyin1.
    apply: (HNat n1 gty1 _ ty1 m1 Em1 tv1 tyin1).
    by move: Egty1; rewrite /const_type Econsts.
  have Hbase : forall tv0 venv0, frConst F n0 tv0 (type_of r) = SafeDenote F thy tv0 venv0 r Hr0.
    move=> tv0 venv0.
    have Hc0 := Hdf n0 df Hn0 r Hdest Hr0 tv0 venv0 [fmap] (check_type_id_triv thy).
    move: Hc0.
    move: (proj1 (check_open_term_inst_type thy [fmap] r [::] (check_type_id_triv thy) Hr0))
      (proj2 (check_open_term_inst_type thy [fmap] r [::] (check_type_id_triv thy) Hr0)).
    case: (inst_type [fmap] r) / (esym (inst_type_id r)) => HctI0 EtI0 Hc0.
    move: EtI0 Hc0.
    case: (type_subst [fmap] (type_of r)) / (esym (type_subst_id (type_of r))) => EtI0 Hc0.
    rewrite (proof_irrelevance _ HctI0 Hr0) (HType_UIP _ _ EtI0 (erefl (type_of r))) /= in Hc0.
    by rewrite Hc0.
  have Hbase' : forall tv0 venv0, frConst F n0 tv0 (type_of r) = SafeDenote F thy' tv0 venv0 r Hr'.
    move=> tv0 venv0.
    rewrite (Hbase tv0 venv0).
    exact: (SafeDenote_irrel_thy F thy thy' tv0 venv0 r Hr0 Hr').
  exact: (ModelsTheory_defclause_from_base F thy' n0 r Hr' gty Egty' m Em HNat' Hbase' tv venv sigma Htyin).
- move=> n1 gty1 Egty1 ty1 m1 Em1 tv1 tyin1.
  apply: (HNat n1 gty1 _ ty1 m1 Em1 tv1 tyin1).
  by move: Egty1; rewrite /const_type Econsts.
Qed.

Lemma new_constant_conservative F thy fresh n ty thy'
    (fc_n : forall tv (ty0 : HType), interpType (frTyOp F) tv ty0)
    (fc_n_nat : forall tv (tyin : {fmap Name -> HType}) ty0,
       fc_n tv (type_subst tyin ty0) =
         eq_rect (interpType (frTyOp F) (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) ty0) (fun T => T)
           (fc_n (tv_subst (frTyOp F) (frTyOp_inhab F) tv tyin) ty0)
           (interpType (frTyOp F) tv (type_subst tyin ty0))
           (esym (interpType_subst_gen (frTyOp F) (frTyOp_inhab F) (frTyOp_subst F) tv tyin ty0))) :
  WellFormedTheory thy -> AxiomsChecked thy -> DefsChecked thy ->
  new_constant thy fresh n ty = Some thy' ->
  ModelsTheory F thy ->
  exists fc' : forall (n0 : Name) (tv : Name -> {T : Type & T}) (ty0 : HType), interpType (frTyOp F) tv ty0,
    ModelsTheory (frame_override F fc') thy' /\
    (forall tv ty0, fc' n tv ty0 = fc_n tv ty0) /\
    (forall n0 tv ty0, n0 <> n -> fc' n0 tv ty0 = frConst F n0 tv ty0).
Proof.
move=> WFT HAC HDC Hnc [HNEq [Hax [Hdf HNat]]].
have Htyops := newConstantMonotone thy fresh n ty thy' Hnc.
have Hconsts := newConstantMonotoneConst thy fresh n ty thy' Hnc.
have Hfresh : const_type thy n = None.
  move: Hnc; rewrite /new_constant.
  case: ifP => Hcond; first by [].
  move: Hcond => /negbT /norP [Hn0 _] _.
  exact/eqP/negbNE.
have Eax : th_axioms thy' = th_axioms thy.
  by move: Hnc; rewrite /new_constant; case: ifP => // _ [<-].
have Edf : th_defs thy' = th_defs thy.
  by move: Hnc; rewrite /new_constant; case: ifP => // _ [<-].
have Econsts : th_consts thy' = (th_consts thy).[n <- ty].
  by move: Hnc; rewrite /new_constant; case: ifP => // _ [<-].
have EconstsAt : forall n0, n0 <> n -> const_type thy' n0 = const_type thy n0.
  move=> n0 Hne.
  by rewrite /const_type Econsts fnd_set (negbTE (introN eqP Hne)).
pose frConst' := fun (m : Name) (tv : Name -> {T : Type & T}) (ty0 : HType) =>
  if m == n then fc_n tv ty0 else frConst F m tv ty0.
pose F' := frame_override F frConst'.
have HfrConstn : forall tv ty0, frConst' n tv ty0 = fc_n tv ty0.
  by move=> tv ty0; rewrite /frConst' /= eqxx.
have HfrConstOther : forall n0 tv ty0, n0 <> n -> frConst' n0 tv ty0 = frConst F n0 tv ty0.
  move=> n0 tv ty0 Hne.
  by rewrite /frConst' /= (negbTE (introN eqP Hne)).
have HneNEq : n <> NEq.
  move=> Heq; move: Hfresh; rewrite Heq.
  by case: WFT => [_ [_ [-> _]]].
have HModels : ModelsTheory F' thy'.
  rewrite /ModelsTheory /ModelsTheoryNat /F' /frame_override /=.
  split.
  - move=> dom tv.
    rewrite (HfrConstOther NEq tv (mk_fun dom (mk_fun dom bool_ty)) (nesym HneNEq)).
    exact: HNEq.
  split.
  - move=> ax Hin tv venv Hct Hbt.
    move: Hin; rewrite Eax => Hin.
    have Hct0 : check_term thy (thm_concl ax) := (HAC ax Hin).1.
    rewrite (denoteProp_irrel_thy F' thy' thy tv venv (thm_concl ax) Hct Hct0 Hbt Hbt).
    rewrite (denoteProp_frame_agree F frConst' n thy HfrConstOther Hfresh
      (thm_concl ax) tv venv Hct0 Hbt).
    exact: (Hax ax Hin tv venv Hct0 Hbt).
  split.
  - move=> n0 df; rewrite Edf => Hn0 r Hdest Hr' tv venv sigma Htyin.
    have HWFdf := HDC n0 df Hn0.
    have [Hcdf _] := HWFdf.
    have Hct_concl : check_term thy (thm_concl df) := Hcdf.
    have [ty1 Ety] := dest_eq_inv (thm_concl df) (mk_const n0 (type_of r)) r Hdest.
    have [Hcn0 [Hr0 _]] : check_term thy (mk_const n0 (type_of r)) /\ check_term thy r /\
        type_of (mk_const n0 (type_of r)) = type_of r.
      apply: (check_term_eq_inv thy ty1 (mk_const n0 (type_of r)) r WFT).
      by rewrite -Ety.
    have [gty1 [Egty1 [m1 Em1]]] : exists gty1, const_type thy n0 = Some gty1 /\
        exists m1, type_match gty1 (type_of r) [fmap] = Some m1.
      move: Hcn0; rewrite /check_term /=.
      move=> /andP[_ Hmatch].
      case Egty0: (const_type thy n0) Hmatch => [gty0|] //.
      case Em0: (type_match gty0 (type_of r) [fmap]) => [m0|] // _.
      exists gty0; split=> //; exists m0; exact: Em0.
    have Hn0ne : n0 <> n.
      move=> Heq; move: Egty1; rewrite Heq Hfresh //.
    have Egty1' : const_type thy' n0 = Some gty1.
      by rewrite (EconstsAt n0 Hn0ne).
    have HNat' : ModelsTheoryNat F' thy'.
      rewrite /ModelsTheoryNat /F' /frame_override /= => n2 gty2 Egty2 ty2 m2 Em2 tv2 tyin2.
      case: (@eqP _ n2 n) => [-> | Hne2].
      + rewrite !HfrConstn. exact: (fc_n_nat tv2 tyin2 ty2).
      + rewrite !(HfrConstOther n2 _ _ Hne2).
        have Egty2' : const_type thy n2 = Some gty2.
          by rewrite -(EconstsAt n2 Hne2).
        exact: (HNat n2 gty2 Egty2' ty2 m2 Em2 tv2 tyin2).
    have Hbase : forall tv0 venv0, frConst F n0 tv0 (type_of r) = SafeDenote F thy tv0 venv0 r Hr0.
      move=> tv0 venv0.
      have Hc0 := Hdf n0 df Hn0 r Hdest Hr0 tv0 venv0 [fmap] (check_type_id_triv thy).
      move: Hc0.
      move: (proj1 (check_open_term_inst_type thy [fmap] r [::] (check_type_id_triv thy) Hr0))
        (proj2 (check_open_term_inst_type thy [fmap] r [::] (check_type_id_triv thy) Hr0)).
      case: (inst_type [fmap] r) / (esym (inst_type_id r)) => HctI0 EtI0 Hc0.
      move: EtI0 Hc0.
      case: (type_subst [fmap] (type_of r)) / (esym (type_subst_id (type_of r))) => EtI0 Hc0.
      rewrite (proof_irrelevance _ HctI0 Hr0) (HType_UIP _ _ EtI0 (erefl (type_of r))) /= in Hc0.
      by rewrite Hc0.
    have Hbase' : forall tv0 venv0, frConst F' n0 tv0 (type_of r) = SafeDenote F' thy' tv0 venv0 r Hr'.
      move=> tv0 venv0.
      rewrite /F' /frame_override /=.
      rewrite (HfrConstOther n0 tv0 (type_of r) Hn0ne) (Hbase tv0 venv0).
      rewrite -(SafeDenote_frame_agree F frConst' n thy HfrConstOther Hfresh r tv0 venv0 Hr0).
      exact: (SafeDenote_irrel_thy F' thy thy' tv0 venv0 r Hr0 Hr').
    exact: (ModelsTheory_defclause_from_base F' thy' n0 r Hr' gty1 Egty1' m1 Em1 HNat' Hbase' tv venv sigma Htyin).
  - move=> n0 gty0 Egty0 ty0 m0 Em0 tv0 tyin0.
    case: (@eqP _ n0 n) => [-> | Hne].
    + rewrite !HfrConstn.
      exact: (fc_n_nat tv0 tyin0 ty0).
    + rewrite !(HfrConstOther n0 _ _ Hne).
      have Egty0' : const_type thy n0 = Some gty0.
        by rewrite -(EconstsAt n0 Hne).
      exact: (HNat n0 gty0 Egty0' ty0 m0 Em0 tv0 tyin0).
exists frConst'; split; first exact: HModels.
split; first exact: HfrConstn.
exact: HfrConstOther.
Qed.

(** [new_basic_definition_conservative] is deliberately not yet proved.
    Such a proof must construct the fresh constant's family [fc'] from
    the definiens [rhs]: at every type instance obtained by
    [type_match], it denotes the corresponding [inst_type m rhs], with
    the necessary transport back to the matched occurrence type.

    The missing ingredient is a structural JMeq naturality theorem for
    that construction.  It must relate [denote (inst_type m' rhs)] at
    [tv] to [denote (inst_type m rhs)] at [tv_subst _ _ tv tyin], where
    [m'] is the type-match substitution composed from [m] and [tyin].
    Its proof needs term-type-variable domain-coverage facts, a related
    [DEnv] invariant for bound variables, and [ModelsTheoryNat] chains
    at constant occurrences, followed by the usual combination and
    abstraction transport cases.  Those supporting lemmas have not yet
    been built.

    This is ordinary, albeit substantial, proof engineering; it is not
    an architectural obstruction.  In particular it is distinct from
    the unresolved [new_basic_type_definition_conservative] issue,
    whose obstacle is the current [frTyOp_inhab] design. *)

(** [new_basic_type_definition_conservative] is deliberately not proved.
    The kernel-level facts are proved in [Kernel.v]: [newBasicTypeDefinitionExtract]
    recovers the successful extension's exact shape and side conditions,
    [newBasicTypeDefinitionMonotone]/[newBasicTypeDefinitionMonotoneConst]
    preserve prior declarations, and [newBasicTypeDefinitionWellFormedTheory]/
    [newBasicTypeDefinitionWellFormed] establish well-formedness of the
    extended theory and both generated theorems.

    What is absent is semantic conservativity: no construction extends an
    arbitrary [Frame] model of the source theory to a [Frame] model of the
    extended theory validating the generated abstraction/representation
    theorems.  The present [Frame.frTyOp_inhab] requires an inhabitant for
    every raw, witness-less [seq Type] argument list, but the intended
    content-bearing subset interpretation needs an inhabitant for each type
    argument to form its local type-variable valuation.  Consequently that
    construction cannot satisfy the current interface for an arbitrary list
    containing, for example, an empty type; repairing it requires changing
    [frTyOp]'s argument interface from [seq Type] to [seq {T : Type & T}]
    project-wide, which is out of scope here. *)

Definition frTyOp0 (tv : Name -> {T : Type & T}) (n : Name)
    (htyargs : seq HType) (args : seq Type) : Type := unit.
Lemma frTyOp0_inhab : forall tv n htyargs args, frTyOp0 tv n htyargs args.
Proof. by move=> tv n htyargs args; exact tt. Qed.
Lemma frTyOp0_subst : forall tv (tyin : {fmap Name -> HType}) n args,
  frTyOp0 tv n (map (type_subst tyin) args)
    (map (interpType frTyOp0 tv) (map (type_subst tyin) args)) =
  frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin) n args
    (map (interpType frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin)) args).
Proof. by move=> tv tyin n args; []. Qed.

Definition eq_shape_dom (ty : HType) : option HType :=
  match ty with
  | HTyApp NFun [:: dom1; HTyApp NFun [:: dom2; HTyApp NBool [::]]] =>
      if dom1 == dom2 then Some dom1 else None
  | _ => None
  end.
Lemma eq_shape_dom_sound ty dom :
  eq_shape_dom ty = Some dom -> ty = mk_fun dom (mk_fun dom bool_ty).
Proof.
case: ty => [n | n args] //=;
  case: n => [| | | | | id] //=;
  case: args => [|dom1 args] //=;
  case: args => [|inner args] //=;
  case: args => [|] //=;
  case: inner => [n | n args] //=;
  case: n => [| | | | | id] //=;
  case: args => [|dom2 args] //=;
  case: args => [|bt args] //=;
  case: args => [|] //=;
  case: bt => [n | n args] //=;
  case: n => [| | | | | id] //=;
  case: args => [|] //=;
  case: ifP => // /eqP -> [<-].
by [].
Qed.
Lemma eq_shape_dom_complete dom :
  eq_shape_dom (mk_fun dom (mk_fun dom bool_ty)) = Some dom.
Proof. by rewrite /eq_shape_dom /mk_fun /mk_tyapp /= eqxx. Qed.

Definition HType_eq_dec (x y : HType) : {x = y} + {x <> y}.
Proof.
case E: (x == y).
- left. exact/eqP/E.
- right => Hxy; subst y.
  by rewrite eqxx in E.
Defined.
Lemma HType_eq_dec_refl x : HType_eq_dec x x = left erefl.
Proof.
case: (HType_eq_dec x x) => [H | H].
- by rewrite (proof_irrelevance _ H erefl).
- exact (False_rect _ (H erefl)).
Qed.
Lemma eq_transport_eq (A B : Type) (E : A = B) :
  @eq A =
    eq_rect (B -> B -> Prop) id (@eq B) (A -> A -> Prop)
      (esym (f_equal (fun T : Type => T -> T -> Prop) E)).
Proof. destruct E. by []. Qed.

Definition frConst0 (n : Name) (tv : Name -> {T : Type & T}) (ty : HType) :
    interpType frTyOp0 tv ty :=
  match ty as ty0 return interpType frTyOp0 tv ty0 with
  | HTyApp NFun [:: dom1; HTyApp NFun [:: dom2; HTyApp NBool [::]]] =>
      match HType_eq_dec dom1 dom2 with
      | left H =>
          eq_rect dom1
            (fun dom2 => interpType frTyOp0 tv dom1 -> interpType frTyOp0 tv dom2 -> Prop)
            (fun x y => x = y) dom2 H
      | right _ =>
          interpType_witness_gen frTyOp0 frTyOp0_inhab tv
            (mk_fun dom1 (mk_fun dom2 bool_ty))
      end
  | ty0 => interpType_witness_gen frTyOp0 frTyOp0_inhab tv ty0
  end.
Definition Frame0 : Frame := mkFrame frTyOp0 frTyOp0_inhab frTyOp0_subst frConst0.
Lemma frConst0_eq dom tv :
  frConst0 NEq tv (mk_fun dom (mk_fun dom bool_ty)) =
    @eq (interpType frTyOp0 tv dom).
Proof.
rewrite /mk_fun /mk_tyapp /frConst0 /= HType_eq_dec_refl.
by [].
Qed.
Lemma eq_shape_dom_type_subst ty dom tyin :
  eq_shape_dom ty = Some dom ->
  eq_shape_dom (type_subst tyin ty) = Some (type_subst tyin dom).
Proof.
move=> Hshape.
rewrite (eq_shape_dom_sound ty dom Hshape).
by rewrite /type_subst /mk_fun /mk_tyapp /= /eq_shape_dom eqxx.
Qed.

Lemma initial_const_type_inv n gty :
  const_type initial_theory n = Some gty ->
  n = NEq /\ gty = mk_fun (HTyVar NAlpha) (mk_fun (HTyVar NAlpha) bool_ty).
Proof.
rewrite /const_type /initial_theory /= fnd_set.
case: ifP => [/eqP -> [<-] | Hneq].
- by [].
- by rewrite fnd_fmap0.
Qed.

Lemma Frame0_models_initial : ModelsTheory Frame0 initial_theory.
Proof.
split; first exact: frConst0_eq.
split.
- by move=> ax; rewrite /initial_theory /=.
split.
- by move=> n df; rewrite /initial_theory /= fnd_fmap0.
rewrite /ModelsTheoryNat /Frame0 /= => n gty Egty ty m Em tv tyin.
have [En Eg] := initial_const_type_inv n gty Egty.
subst n; subst gty.
have Et : type_subst m (mk_fun (HTyVar NAlpha) (mk_fun (HTyVar NAlpha) bool_ty)) = ty.
  apply: (type_match_sound _ ty [fmap] m _ Em).
  by move=> n0 v; rewrite fnd_fmap0.
have Ety : ty = mk_fun (type_subst m (HTyVar NAlpha))
    (mk_fun (type_subst m (HTyVar NAlpha)) bool_ty).
  rewrite -Et /type_subst /mk_fun /mk_tyapp /=.
  by [].
subst ty.
rewrite Ety.
set D := type_subst m (HTyVar NAlpha).
have Einner : interpType frTyOp0 tv (type_subst tyin D) =
    interpType frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin) D :=
  interpType_subst_gen frTyOp0 frTyOp0_inhab frTyOp0_subst tv tyin D.
have Eouter : interpType frTyOp0 tv (type_subst tyin (mk_fun D (mk_fun D bool_ty))) =
    interpType frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin)
      (mk_fun D (mk_fun D bool_ty)).
  exact: (f_equal (fun T : Type => T -> T -> Prop) Einner).
rewrite (proof_irrelevance _
  (interpType_subst_gen frTyOp0 frTyOp0_inhab frTyOp0_subst tv tyin
    (mk_fun D (mk_fun D bool_ty))) Eouter).
rewrite /type_subst /mk_fun /mk_tyapp /frConst0 /=.
rewrite !HType_eq_dec_refl /=.
rewrite (proof_irrelevance _ Eouter
  (f_equal (fun T : Type => T -> T -> Prop) Einner)).
change (@eq (interpType frTyOp0 tv (type_subst tyin D)) =
  eq_rect
    (interpType frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin) D ->
      interpType frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin) D -> Prop)
    id
    (@eq (interpType frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin) D))
    (interpType frTyOp0 tv (type_subst tyin D) ->
      interpType frTyOp0 tv (type_subst tyin D) -> Prop)
    (esym (f_equal (fun T : Type => T -> T -> Prop) Einner))).
exact: (eq_transport_eq _ _ Einner).
Qed.

(** * The master corollary: reachability restricted to [new_type]/
    [new_constant]

    Both extension principles change [th_tyops]/[th_consts] only, never
    [frTyOp] -- [new_type_conservative] keeps the very same [Frame], and
    [new_constant_conservative]'s [frame_override] only ever replaces
    [frConst]. Restricting the witness [Frame] to the shape
    [mkFrame frTyOp0 frTyOp0_inhab frTyOp0_subst _] captures this
    invariant *by construction* (definitionally, not as a side
    condition to prove and re-prove at every step): [frTyOp] of any such
    [Frame] is [frTyOp0] outright, so [fc_n0]/[fc_n0_nat] below -- built
    once from [interpType_witness_gen]'s own generic naturality, not
    from anything specific to one step -- serves as every [new_constant]
    step's caller-supplied semantic family, with no per-step witness
    construction needed. *)

Lemma unit_singleton (u v : unit) : u = v.
Proof. by case: u; case: v. Qed.

(** [interpType_witness_gen]'s own value, for the constant-[unit]
    [frTyOp0], commutes with type substitution -- the naturality
    [fc_n_nat] demands of any semantic family, specialised to the
    canonical witness. The [NFun]/[:: A; B]] case is the only
    non-trivial one (an arrow type, needing [eq_rect_arrow2]); every
    other [HTyApp] shape denotes a genuine, argument-independent
    singleton ([unit] or, for [NBool], the fixed witness [True] of
    [Prop]), so naturality there is immediate. *)
Lemma interpType_witness_frTyOp0_natural tv tyin ty :
  interpType_witness_gen frTyOp0 frTyOp0_inhab tv (type_subst tyin ty) =
    eq_rect (interpType frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin) ty) (fun T => T)
      (interpType_witness_gen frTyOp0 frTyOp0_inhab (tv_subst frTyOp0 frTyOp0_inhab tv tyin) ty)
      (interpType frTyOp0 tv (type_subst tyin ty))
      (esym (interpType_subst_gen frTyOp0 frTyOp0_inhab frTyOp0_subst tv tyin ty)).
Proof.
elim/HType_rect: ty => [n | n args IH].
- rewrite /=.
  rewrite /interpType_witness_gen /=.
  move: (esym _).
  rewrite /interpType_subst_gen /= /tv_subst /=.
  case: (tyin.[? n]) => [t|] //= e;
    by rewrite (proof_irrelevance _ e erefl).
- move: n args IH => [| | | | | id] args IH.
  + (* NFun *)
    case: args IH => [| A [| B [| C rest]]] //= IH.
    * apply: unit_singleton.
    * apply: unit_singleton.
    * move: IH => [IHA [IHB _]].
      have eA := esym (interpType_subst_gen frTyOp0 frTyOp0_inhab frTyOp0_subst tv tyin A).
      have eB := esym (interpType_subst_gen frTyOp0 frTyOp0_inhab frTyOp0_subst tv tyin B).
      apply: functional_extensionality => x.
      rewrite (proof_irrelevance _
        (esym (interpType_subst_gen frTyOp0 frTyOp0_inhab frTyOp0_subst tv tyin (HTyApp NFun [:: A; B])))
        (f_equal2 (fun X Y => X -> Y) eA eB)).
      rewrite (eq_rect_arrow2 (interpType frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin) A)
        (interpType frTyOp0 tv (type_subst tyin A))
        (interpType frTyOp0 (tv_subst frTyOp0 frTyOp0_inhab tv tyin) B)
        (interpType frTyOp0 tv (type_subst tyin B))
        eA eB
        (fun _ => interpType_witness_gen frTyOp0 frTyOp0_inhab (tv_subst frTyOp0 frTyOp0_inhab tv tyin) B)
        (f_equal2 (fun X Y => X -> Y) eA eB) x).
      rewrite (proof_irrelevance _ eB
        (esym (interpType_subst_gen frTyOp0 frTyOp0_inhab frTyOp0_subst tv tyin B))).
      exact: IHB.
    * apply: unit_singleton.
  + (* NBool *)
    by rewrite (proof_irrelevance _
      (esym (interpType_subst_gen frTyOp0 frTyOp0_inhab frTyOp0_subst tv tyin (HTyApp NBool args)))
      erefl).
  + (* NEq *)
    apply: unit_singleton.
  + (* NAlpha *)
    apply: unit_singleton.
  + (* NRepVar *)
    apply: unit_singleton.
  + (* NUser id *)
    apply: unit_singleton.
Qed.

Definition fc_n0 : forall tv (ty0 : HType), interpType (frTyOp Frame0) tv ty0 :=
  interpType_witness_gen frTyOp0 frTyOp0_inhab.

Lemma fc_n0_nat : forall tv (tyin : {fmap Name -> HType}) ty0,
  fc_n0 tv (type_subst tyin ty0) =
    eq_rect (interpType (frTyOp Frame0) (tv_subst (frTyOp Frame0) (frTyOp_inhab Frame0) tv tyin) ty0) (fun T => T)
      (fc_n0 (tv_subst (frTyOp Frame0) (frTyOp_inhab Frame0) tv tyin) ty0)
      (interpType (frTyOp Frame0) tv (type_subst tyin ty0))
      (esym (interpType_subst_gen (frTyOp Frame0) (frTyOp_inhab Frame0) (frTyOp_subst Frame0) tv tyin ty0)).
Proof. exact: interpType_witness_frTyOp0_natural. Qed.

Lemma newTypeWellFormedTheory thy fresh n arity thy' :
  WellFormedTheory thy -> new_type thy fresh n arity = Some thy' -> WellFormedTheory thy'.
Proof.
move=> [Hbool [Hfun [Heq Hself]]] Hnt.
have Htyops := newTypeMonotone thy fresh n arity thy' Hnt.
have Hconsts := newTypeMonotoneConst thy fresh n arity thy' Hnt.
split; first exact: (Htyops NBool 0 Hbool).
split; first exact: (Htyops NFun 2 Hfun).
split; first exact: (Hconsts NEq _ Heq).
move: Hnt; rewrite /new_type.
case: ifP => // _ [<-] /=.
by rewrite in_fset1U eqxx.
Qed.

Lemma newConstantWellFormedTheory thy fresh n ty thy' :
  WellFormedTheory thy -> new_constant thy fresh n ty = Some thy' -> WellFormedTheory thy'.
Proof.
move=> [Hbool [Hfun [Heq Hself]]] Hnc.
have Htyops := newConstantMonotone thy fresh n ty thy' Hnc.
have Hconsts := newConstantMonotoneConst thy fresh n ty thy' Hnc.
split; first exact: (Htyops NBool 0 Hbool).
split; first exact: (Htyops NFun 2 Hfun).
split; first exact: (Hconsts NEq _ Heq).
move: Hnc; rewrite /new_constant.
case: ifP => // _ [<-] /=.
by rewrite in_fset1U eqxx.
Qed.

(** Reachability restricted to the ten primitive rules (which never
    change the theory) plus [new_type]/[new_constant] -- deliberately
    NOT the general four-principle reachability the plan originally
    aimed for: [new_axiom] is the plan's own stated escape hatch, and
    [new_basic_definition]/[new_basic_type_definition] are excluded per
    the comments on [new_basic_definition_conservative]/
    [new_basic_type_definition_conservative] above. A theory built using
    either of those two is outside this relation, and this corollary
    says nothing about it. *)
Inductive ReachedFromTypeConst : Theory -> Theory -> Prop :=
  | RFTC_refl thy : ReachedFromTypeConst thy thy
  | RFTC_type thy1 thy2 thy3 fresh n arity :
      ReachedFromTypeConst thy1 thy2 -> new_type thy2 fresh n arity = Some thy3 ->
      ReachedFromTypeConst thy1 thy3
  | RFTC_const thy1 thy2 thy3 fresh n ty :
      ReachedFromTypeConst thy1 thy2 -> new_constant thy2 fresh n ty = Some thy3 ->
      ReachedFromTypeConst thy1 thy3.

Lemma ReachedFromTypeConst_WFT thy0 thy :
  ReachedFromTypeConst thy0 thy ->
  WellFormedTheory thy0 -> AxiomsChecked thy0 -> DefsChecked thy0 ->
  WellFormedTheory thy /\ AxiomsChecked thy /\ DefsChecked thy.
Proof.
elim=> [thy1
       | thy1 thy2 thy3 fresh n arity _ IH Hnt
       | thy1 thy2 thy3 fresh n ty _ IH Hnc] WFT0 HAC0 HDC0.
- by [].
- have [WFT2 [HAC2 HDC2]] := IH WFT0 HAC0 HDC0.
  split; first exact: (newTypeWellFormedTheory thy2 fresh n arity thy3 WFT2 Hnt).
  split; first exact: (newTypeAxiomsChecked thy2 fresh n arity thy3 Hnt HAC2).
  exact: (newTypeDefsChecked thy2 fresh n arity thy3 Hnt HDC2).
- have [WFT2 [HAC2 HDC2]] := IH WFT0 HAC0 HDC0.
  split; first exact: (newConstantWellFormedTheory thy2 fresh n ty thy3 WFT2 Hnc).
  split; first exact: (newConstantAxiomsChecked thy2 fresh n ty thy3 Hnc HAC2).
  exact: (newConstantDefsChecked thy2 fresh n ty thy3 Hnc HDC2).
Qed.

(** The master corollary. Restricted, on purpose: only [new_type]/
    [new_constant] are covered -- see [ReachedFromTypeConst]'s own
    comment, and the stated-gap comments on [new_basic_definition_conservative]/
    [new_basic_type_definition_conservative] above, for exactly why
    [new_axiom]/[new_basic_definition]/[new_basic_type_definition] are
    excluded. This is NOT the full four-principle
    [definitional_theories_have_models] the project's plan originally
    aimed for. *)
Lemma type_and_constant_theories_have_models thy0 thy :
  ReachedFromTypeConst thy0 thy ->
  WellFormedTheory thy0 -> AxiomsChecked thy0 -> DefsChecked thy0 ->
  forall frConsti0,
    ModelsTheory (mkFrame frTyOp0 frTyOp0_inhab frTyOp0_subst frConsti0) thy0 ->
  exists frConsti, ModelsTheory (mkFrame frTyOp0 frTyOp0_inhab frTyOp0_subst frConsti) thy.
Proof.
elim=> [thy1
       | thy1 thy2 thy3 fresh n arity HRF IH Hnt
       | thy1 thy2 thy3 fresh n ty HRF IH Hnc] WFT0 HAC0 HDC0 frConsti0 HM0.
- by exists frConsti0.
- have [WFT2 [HAC2 HDC2]] := ReachedFromTypeConst_WFT thy1 thy2 HRF WFT0 HAC0 HDC0.
  have [frConsti2 HM2] := IH WFT0 HAC0 HDC0 frConsti0 HM0.
  exists frConsti2.
  exact: (new_type_conservative (mkFrame frTyOp0 frTyOp0_inhab frTyOp0_subst frConsti2)
    thy2 fresh n arity thy3 WFT2 HAC2 HDC2 Hnt HM2).
- have [WFT2 [HAC2 HDC2]] := ReachedFromTypeConst_WFT thy1 thy2 HRF WFT0 HAC0 HDC0.
  have [frConsti2 HM2] := IH WFT0 HAC0 HDC0 frConsti0 HM0.
  have [frConst3 [HM3 _]] :=
    new_constant_conservative (mkFrame frTyOp0 frTyOp0_inhab frTyOp0_subst frConsti2)
      thy2 fresh n ty thy3 fc_n0 fc_n0_nat WFT2 HAC2 HDC2 Hnc HM2.
  by exists frConst3.
Qed.

(** [initial_theory] itself, threaded through the master corollary: any
    theory reached from [initial_theory] via only [new_type]/
    [new_constant] has a model. *)
Corollary type_and_constant_theories_have_models_from_initial thy :
  ReachedFromTypeConst initial_theory thy ->
  exists frConsti, ModelsTheory (mkFrame frTyOp0 frTyOp0_inhab frTyOp0_subst frConsti) thy.
Proof.
move=> HRF.
apply: (type_and_constant_theories_have_models initial_theory thy HRF
  initial_theory_WellFormedTheory initial_theory_AxiomsChecked initial_theory_DefsChecked
  frConst0).
exact: Frame0_models_initial.
Qed.
