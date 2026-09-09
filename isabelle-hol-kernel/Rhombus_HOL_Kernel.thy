(* SPDX-License-Identifier: 0BSD AND BSD-2-Clause AND BSD-3-Clause *)
(* Conservatively covered by HOL Light and HOL4 notices; see THIRD_PARTY_NOTICES. *)

theory Rhombus_HOL_Kernel
  imports Rhombus_HOL_Substitution
begin

section \<open>Executable primitive rules\<close>

text \<open>Rhombus correspondence: kernel.rhm's ten primitive inference rules. Each branch mirrors the source; option replaces source exceptions.\<close>

definition checked_thm :: "htheory \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> stamp \<Rightarrow> hthm option" where
  "checked_thm thy hs c st =
    (let th = \<lparr>hyps = hs, concl = c, thm_stamp = st\<rparr>
     in if wf_thm thy th then Some th else None)"

definition checked_eq_thm ::
  "htheory \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> stamp \<Rightarrow> hthm option" where
  "checked_eq_thm thy hs l r st =
    (case mk_eq l r of None \<Rightarrow> None | Some eq \<Rightarrow> checked_thm thy hs eq st)"

definition refl :: "htheory \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "refl thy t = checked_eq_thm thy [] t t (thy_stamp thy)"

definition trans :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "trans thy a b =
    (case (dest_eq (concl a), dest_eq (concl b),
           combine_stamps (thm_stamp a) (thm_stamp b)) of
       (Some (l, m), Some (m', r), Some st) \<Rightarrow>
          if m = m' then checked_eq_thm thy (hyp_union (hyps a) (hyps b)) l r st
          else None
     | _ \<Rightarrow> None)"

definition mk_comb_rule :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "mk_comb_rule thy fth xth =
    (case (dest_eq (concl fth), dest_eq (concl xth),
           combine_stamps (thm_stamp fth) (thm_stamp xth)) of
       (Some (f, g), Some (x, y), Some st) \<Rightarrow>
          checked_eq_thm thy (hyp_union (hyps fth) (hyps xth))
            (Comb f x) (Comb g y) st
     | _ \<Rightarrow> None)"

definition abs_rule :: "htheory \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "abs_rule thy n ty th =
    (case dest_eq (concl th) of
       None \<Rightarrow> None
     | Some (l, r) \<Rightarrow>
         if descends (thm_stamp th) (thy_stamp thy) \<and>
            check_term thy (FVar n ty) \<and>
            (\<forall>h\<in>set (hyps th). \<not> vfree_in n ty h)
         then checked_eq_thm thy (hyps th)
           (Abs ty (abstract_fvar n ty l)) (Abs ty (abstract_fvar n ty r))
           (thy_stamp thy)
         else None)"

definition beta :: "htheory \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "beta thy t =
    (case t of Comb (Abs aty body) arg \<Rightarrow>
       if check_term thy t then checked_eq_thm thy [] t (subst_bvar arg body)
         (thy_stamp thy)
       else None
     | _ \<Rightarrow> None)"

definition assume_rule :: "htheory \<Rightarrow> hterm \<Rightarrow> hthm option" where
  "assume_rule thy p =
    (if check_prop thy p then checked_thm thy [p] p (thy_stamp thy) else None)"

definition eq_mp :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "eq_mp thy eqth th =
    (case (dest_eq (concl eqth),
           combine_stamps (thm_stamp eqth) (thm_stamp th)) of
       (Some (p, q), Some st) \<Rightarrow>
          if p = concl th then
            checked_thm thy (hyp_union (hyps eqth) (hyps th)) q st
          else None
     | _ \<Rightarrow> None)"

definition deduct_antisym_rule :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "deduct_antisym_rule thy a b =
    (case combine_stamps (thm_stamp a) (thm_stamp b) of
       None \<Rightarrow> None
     | Some st \<Rightarrow> checked_eq_thm thy
         (hyp_union (hyp_remove (concl b) (hyps a))
                    (hyp_remove (concl a) (hyps b)))
         (concl a) (concl b) st)"

fun decode_term_subst ::
  "(hterm \<times> hterm) list \<Rightarrow> (hterm \<times> (hname \<times> htype)) list option" where
  "decode_term_subst [] = Some []"
| "decode_term_subst ((rep, FVar n ty) # rest) =
    map_option ((#) (rep, (n, ty))) (decode_term_subst rest)"
| "decode_term_subst ((_ , _) # _) = None"

definition inst :: "htheory \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "inst thy raw th =
    (case decode_term_subst raw of
       None \<Rightarrow> None
     | Some \<theta> \<Rightarrow>
         if descends (thm_stamp th) (thy_stamp thy) \<and> wf_term_subst thy \<theta> then
           checked_thm thy (rehash_hyps (map (inst_fvar \<theta>) (hyps th)))
             (inst_fvar \<theta> (concl th)) (thy_stamp thy)
         else None)"

definition inst_type_rule ::
  "htheory \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "inst_type_rule thy \<theta> th =
    (if descends (thm_stamp th) (thy_stamp thy) \<and> type_subst_ok thy \<theta> then
       checked_thm thy (rehash_hyps (map (inst_type \<theta>) (hyps th)))
         (inst_type \<theta> (concl th)) (thy_stamp thy)
     else None)"

lemma type_subst_empty [simp]: "type_subst (\<lambda>_. None) ty = ty"
proof (induction ty)
  case (TyApp n args)
  then have "map (type_subst (\<lambda>_. None)) args = map id args"
    by (intro map_cong) auto
  then show ?case by simp
qed simp

lemma type_subst_ok_empty [simp]: "type_subst_ok thy (\<lambda>_. None)"
  by (simp add: type_subst_ok_def)

section \<open>Rule requests and declarative results\<close>

datatype inference =
    IRefl htheory hterm
  | ITrans htheory hthm hthm
  | IMkComb htheory hthm hthm
  | IAbs htheory hname htype hthm
  | IBeta htheory hterm
  | IAssume htheory hterm
  | IEqMp htheory hthm hthm
  | IDeductAntisym htheory hthm hthm
  | IInst htheory "(hterm \<times> hterm) list" hthm
  | IInstType htheory "hname \<Rightarrow> htype option" hthm

fun ambient_theory :: "inference \<Rightarrow> htheory" where
  "ambient_theory (IRefl thy _) = thy"
| "ambient_theory (ITrans thy _ _) = thy"
| "ambient_theory (IMkComb thy _ _) = thy"
| "ambient_theory (IAbs thy _ _ _) = thy"
| "ambient_theory (IBeta thy _) = thy"
| "ambient_theory (IAssume thy _) = thy"
| "ambient_theory (IEqMp thy _ _) = thy"
| "ambient_theory (IDeductAntisym thy _ _) = thy"
| "ambient_theory (IInst thy _ _) = thy"
| "ambient_theory (IInstType thy _ _) = thy"

fun run_rule :: "inference \<Rightarrow> hthm option" where
  "run_rule (IRefl thy t) = refl thy t"
| "run_rule (ITrans thy a b) = trans thy a b"
| "run_rule (IMkComb thy a b) = mk_comb_rule thy a b"
| "run_rule (IAbs thy n ty th) = abs_rule thy n ty th"
| "run_rule (IBeta thy t) = beta thy t"
| "run_rule (IAssume thy p) = assume_rule thy p"
| "run_rule (IEqMp thy a b) = eq_mp thy a b"
| "run_rule (IDeductAntisym thy a b) = deduct_antisym_rule thy a b"
| "run_rule (IInst thy \<theta> th) = inst thy \<theta> th"
| "run_rule (IInstType thy \<theta> th) = inst_type_rule thy \<theta> th"

fun wf_inputs :: "inference \<Rightarrow> bool" where
  "wf_inputs (IRefl thy t) = check_term thy t"
| "wf_inputs (ITrans thy a b) = (wf_thm thy a \<and> wf_thm thy b)"
| "wf_inputs (IMkComb thy a b) = (wf_thm thy a \<and> wf_thm thy b)"
| "wf_inputs (IAbs thy n ty th) =
    (wf_thm thy th \<and> check_term thy (FVar n ty) \<and>
      (\<forall>h\<in>set (hyps th). \<not> vfree_in n ty h))"
| "wf_inputs (IBeta thy t) = check_term thy t"
| "wf_inputs (IAssume thy p) = check_prop thy p"
| "wf_inputs (IEqMp thy a b) = (wf_thm thy a \<and> wf_thm thy b)"
| "wf_inputs (IDeductAntisym thy a b) = (wf_thm thy a \<and> wf_thm thy b)"
| "wf_inputs (IInst thy raw th) =
    (wf_thm thy th \<and> (\<exists>\<theta>. decode_term_subst raw = Some \<theta> \<and> wf_term_subst thy \<theta>))"
| "wf_inputs (IInstType thy \<theta> th) = (wf_thm thy th \<and> type_subst_ok thy \<theta>)"

definition thm_shape ::
  "htheory \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> stamp \<Rightarrow> hthm \<Rightarrow> bool" where
  "thm_shape thy hs c st th \<longleftrightarrow>
    th = \<lparr>hyps = hs, concl = c, thm_stamp = st\<rparr> \<and> wf_thm thy th"

definition eq_shape ::
  "htheory \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> stamp \<Rightarrow> hthm \<Rightarrow> bool" where
  "eq_shape thy hs l r st th \<longleftrightarrow>
    (\<exists>ty. type_of l = Some ty \<and> type_of r = Some ty \<and>
      thm_shape thy hs (eq_term ty l r) st th)"

lemma checked_thm_iff [simp]:
  "checked_thm thy hs c st = Some th \<longleftrightarrow> thm_shape thy hs c st th"
  by (auto simp: checked_thm_def thm_shape_def Let_def split: if_splits)

lemma checked_eq_thm_iff [simp]:
  "checked_eq_thm thy hs l r st = Some th \<longleftrightarrow> eq_shape thy hs l r st th"
  by (auto simp: checked_eq_thm_def eq_shape_def mk_eq_def
      split: option.splits if_splits prod.splits)

text \<open>The specification below is phrased only with sequents, equality shapes, lineage, and side conditions; no premise mentions an executable rule.\<close>

inductive rule_spec :: "inference \<Rightarrow> hthm \<Rightarrow> bool" where
  Refl_spec:
    "eq_shape thy [] t t (thy_stamp thy) th \<Longrightarrow> rule_spec (IRefl thy t) th"
| Trans_spec:
    "\<lbrakk>dest_eq (concl a) = Some (l, m); dest_eq (concl b) = Some (m, r);
      combine_stamps (thm_stamp a) (thm_stamp b) = Some st;
      eq_shape thy (hyp_union (hyps a) (hyps b)) l r st th\<rbrakk>
     \<Longrightarrow> rule_spec (ITrans thy a b) th"
| MkComb_spec:
    "\<lbrakk>dest_eq (concl a) = Some (f, g); dest_eq (concl b) = Some (x, y);
      combine_stamps (thm_stamp a) (thm_stamp b) = Some st;
      eq_shape thy (hyp_union (hyps a) (hyps b)) (Comb f x) (Comb g y) st th\<rbrakk>
     \<Longrightarrow> rule_spec (IMkComb thy a b) th"
| Abs_spec:
    "\<lbrakk>dest_eq (concl old) = Some (l, r);
      descends (thm_stamp old) (thy_stamp thy); check_term thy (FVar n ty);
      \<forall>h\<in>set (hyps old). \<not> vfree_in n ty h;
      eq_shape thy (hyps old) (Abs ty (abstract_fvar n ty l))
        (Abs ty (abstract_fvar n ty r)) (thy_stamp thy) th\<rbrakk>
     \<Longrightarrow> rule_spec (IAbs thy n ty old) th"
| Beta_spec:
    "\<lbrakk>check_term thy (Comb (Abs aty body) arg);
      eq_shape thy [] (Comb (Abs aty body) arg) (subst_bvar arg body)
        (thy_stamp thy) th\<rbrakk>
     \<Longrightarrow> rule_spec (IBeta thy (Comb (Abs aty body) arg)) th"
| Assume_spec:
    "\<lbrakk>check_prop thy p; thm_shape thy [p] p (thy_stamp thy) th\<rbrakk>
     \<Longrightarrow> rule_spec (IAssume thy p) th"
| EqMp_spec:
    "\<lbrakk>dest_eq (concl eqth) = Some (p, q); p = concl old;
      combine_stamps (thm_stamp eqth) (thm_stamp old) = Some st;
      thm_shape thy (hyp_union (hyps eqth) (hyps old)) q st th\<rbrakk>
     \<Longrightarrow> rule_spec (IEqMp thy eqth old) th"
| DeductAntisym_spec:
    "\<lbrakk>combine_stamps (thm_stamp a) (thm_stamp b) = Some st;
      eq_shape thy
        (hyp_union (hyp_remove (concl b) (hyps a))
                   (hyp_remove (concl a) (hyps b)))
        (concl a) (concl b) st th\<rbrakk>
     \<Longrightarrow> rule_spec (IDeductAntisym thy a b) th"
| Inst_spec:
    "\<lbrakk>decode_term_subst raw = Some \<theta>;
      descends (thm_stamp old) (thy_stamp thy); wf_term_subst thy \<theta>;
      thm_shape thy (rehash_hyps (map (inst_fvar \<theta>) (hyps old)))
        (inst_fvar \<theta> (concl old)) (thy_stamp thy) th\<rbrakk>
     \<Longrightarrow> rule_spec (IInst thy raw old) th"
| InstType_spec:
    "\<lbrakk>descends (thm_stamp old) (thy_stamp thy); type_subst_ok thy \<theta>;
      thm_shape thy (rehash_hyps (map (inst_type \<theta>) (hyps old)))
        (inst_type \<theta> (concl old)) (thy_stamp thy) th\<rbrakk>
     \<Longrightarrow> rule_spec (IInstType thy \<theta> old) th"

lemma thm_shape_wf: "thm_shape thy hs c st th \<Longrightarrow> wf_thm thy th"
  by (auto simp: thm_shape_def)

lemma eq_shape_wf: "eq_shape thy hs l r st th \<Longrightarrow> wf_thm thy th"
  by (auto simp: eq_shape_def thm_shape_def)

theorem run_rule_preserves_wf:
  assumes "run_rule i = Some th" "wf_inputs i"
  shows "wf_thm (ambient_theory i) th"
  using assms
  by (cases i)
     (auto simp: refl_def trans_def mk_comb_rule_def abs_rule_def beta_def
       assume_rule_def eq_mp_def deduct_antisym_rule_def inst_def inst_type_rule_def
       split: option.splits prod.splits hterm.splits if_splits
       dest: thm_shape_wf eq_shape_wf)

theorem run_rule_sound:
  assumes "run_rule i = Some th"
  shows "rule_spec i th"
  using assms
  by (cases i)
     (auto simp: refl_def trans_def mk_comb_rule_def abs_rule_def beta_def
       assume_rule_def eq_mp_def deduct_antisym_rule_def inst_def inst_type_rule_def
       split: option.splits prod.splits hterm.splits if_splits
       intro: rule_spec.intros)

theorem run_rule_complete:
  assumes "rule_spec i th"
  shows "run_rule i = Some th"
  using assms
  by cases
     (auto simp: refl_def trans_def mk_comb_rule_def abs_rule_def beta_def
       assume_rule_def eq_mp_def deduct_antisym_rule_def inst_def inst_type_rule_def
       split: option.splits prod.splits hterm.splits if_splits)

section \<open>Finite derivations and lineage\<close>

fun input_thms :: "inference \<Rightarrow> hthm list" where
  "input_thms (IRefl _ _) = []"
| "input_thms (ITrans _ a b) = [a, b]"
| "input_thms (IMkComb _ a b) = [a, b]"
| "input_thms (IAbs _ _ _ th) = [th]"
| "input_thms (IBeta _ _) = []"
| "input_thms (IAssume _ _) = []"
| "input_thms (IEqMp _ a b) = [a, b]"
| "input_thms (IDeductAntisym _ a b) = [a, b]"
| "input_thms (IInst _ _ th) = [th]"
| "input_thms (IInstType _ _ th) = [th]"

inductive derives :: "htheory \<Rightarrow> hthm \<Rightarrow> bool" where
  Axiom: "\<lbrakk>th \<in> set (axiom_list thy); wf_thm thy th\<rbrakk> \<Longrightarrow> derives thy th"
| Primitive: "\<lbrakk>ambient_theory i = thy; rule_spec i th;
    list_all (derives thy) (input_thms i)\<rbrakk> \<Longrightarrow> derives thy th"

lemma rule_spec_wf:
  "rule_spec i th \<Longrightarrow> wf_thm (ambient_theory i) th"
  by (induction rule: rule_spec.induct)
     (auto dest: thm_shape_wf eq_shape_wf)

theorem derives_wf: "derives thy th \<Longrightarrow> wf_thm thy th"
  by (induction rule: derives.induct)
     (auto dest: rule_spec_wf)

lemma combine_stamps_returns_later:
  "combine_stamps a b = Some st \<Longrightarrow>
    (descends a b \<and> st = b) \<or> (\<not> descends a b \<and> descends b a \<and> st = a)"
  by (auto simp: combine_stamps_def split: if_splits)

lemma trans_rejects_siblings:
  assumes "\<not> descends (thm_stamp a) (thm_stamp b)"
    "\<not> descends (thm_stamp b) (thm_stamp a)"
  shows "trans thy a b = None"
  using assms by (simp add: trans_def combine_stamps_def split: option.splits prod.splits)

lemma abs_rule_current_stamp:
  "abs_rule thy n ty old = Some th \<Longrightarrow> thm_stamp th = thy_stamp thy"
  by (auto simp: abs_rule_def eq_shape_def thm_shape_def
      split: option.splits if_splits)

lemma inst_rule_current_stamp:
  "inst thy \<theta> old = Some th \<Longrightarrow> thm_stamp th = thy_stamp thy"
  by (auto simp: inst_def thm_shape_def split: option.splits if_splits)

lemma inst_type_rule_current_stamp:
  "inst_type_rule thy \<theta> old = Some th \<Longrightarrow> thm_stamp th = thy_stamp thy"
  by (auto simp: inst_type_rule_def thm_shape_def split: if_splits)

section \<open>Concrete executable checks\<close>

lemma ill_typed_binder_rejected:
  "\<not> check_term (initial_theory 0)
    (Abs (TyVar NAlpha)
      (Comb (FVar (NUser 10 ''not'') (mk_fun bool_ty bool_ty))
        (BVar 0 bool_ty)))"
  by eval

lemma well_typed_beta_succeeds:
  "\<exists>th. beta (initial_theory 0)
      (Comb (Abs bool_ty (BVar 0 bool_ty))
        (FVar (NUser 11 ''p'') bool_ty)) = Some th \<and>
    wf_thm (initial_theory 0) th"
proof -
  let ?t = "Comb (Abs bool_ty (BVar 0 bool_ty))
    (FVar (NUser 11 ''p'') bool_ty)"
  have present: "beta (initial_theory 0) ?t \<noteq> None" by eval
  then obtain th where run: "beta (initial_theory 0) ?t = Some th"
    by (cases "beta (initial_theory 0) ?t") auto
  have checked: "check_term (initial_theory 0) ?t"
    using run by (auto simp: beta_def split: hterm.splits if_splits)
  have input: "wf_inputs (IBeta (initial_theory 0) ?t)"
    using checked by simp
  have "wf_thm (initial_theory 0) th"
    using run_rule_preserves_wf[of "IBeta (initial_theory 0) ?t" th]
      run input by simp
  with run show ?thesis by blast
qed

lemma sibling_extensions_do_not_combine:
  "combine_stamps (next_stamp 1 (fresh_stamp 0))
      (next_stamp 2 (fresh_stamp 0)) = None"
  by eval

end
