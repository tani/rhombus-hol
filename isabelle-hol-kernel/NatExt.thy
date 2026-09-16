(* SPDX-License-Identifier: 0BSD *)
(* A trusted, natively-computed Nat extension principle. *)

theory NatExt
  imports Rhombus_HOL_Base_Model
begin

section \<open>One reserved Nat, not a name-parameterized family\<close>

text \<open>@{term NAlpha}/@{term NRepVar} are already reserved @{term hname}s the
kernel writes for itself. This adds three more, for one fixed natural-number
type and its two constructors -- not a mechanism that installs a
differently-named Nat wherever a caller points it. A single, fixed instance
is what keeps the extension's soundness argument concrete: every fact below
is about these three names, never a bound variable ranging over names, so
there is nothing to instantiate wrongly and no shape-recognition to get
wrong either.\<close>

definition nat_ty_name :: hname where "nat_ty_name = NUser 900 ''Nat''"
definition nat_zero_name :: hname where "nat_zero_name = NUser 901 ''zero''"
definition nat_succ_name :: hname where "nat_succ_name = NUser 902 ''succ''"

definition nat_aty :: htype where "nat_aty = TyApp nat_ty_name []"
definition nat_sty :: htype where "nat_sty = mk_fun nat_aty nat_aty"
definition nat_zero_c :: hterm where "nat_zero_c = Const nat_zero_name nat_aty"
definition nat_succ_c :: hterm where "nat_succ_c = Const nat_succ_name nat_sty"

lemma nat_names_distinct [simp]:
  "nat_ty_name \<noteq> NFun" "nat_ty_name \<noteq> NBool"
  "nat_zero_name \<noteq> NEq" "nat_succ_name \<noteq> NEq"
  "nat_zero_name \<noteq> nat_succ_name"
  by (simp_all add: nat_ty_name_def nat_zero_name_def nat_succ_name_def)

section \<open>The extension\<close>

text \<open>Introduces @{term nat_ty_name} and its two constructors in one step,
together with three theorems about them (zero is not a successor, succ is
injective, and the structural induction schema). No definitional equation is
recorded for zero/succ in @{term def_tab} -- their soundness comes from a
model built directly below, using HOLZF's Nat as the domain, exactly as
@{term new_basic_type_definition} hands back th1/th2 without a def_tab
lookup.\<close>

definition nat_n0 :: hname where "nat_n0 = NUser 903 ''n''"
definition nat_m0 :: hname where "nat_m0 = NUser 904 ''m''"
definition nat_p0 :: hname where "nat_p0 = NUser 905 ''P''"
definition nat_pty :: htype where "nat_pty = mk_fun nat_aty bool_ty"

lemma nat_vars_distinct [simp]:
  "nat_m0 \<noteq> nat_n0" "nat_m0 \<noteq> nat_p0" "nat_n0 \<noteq> nat_p0"
  "nat_n0 \<noteq> nat_m0" "nat_p0 \<noteq> nat_m0" "nat_p0 \<noteq> nat_n0"
  by (simp_all add: nat_m0_def nat_n0_def nat_p0_def)

definition zns_concl :: hterm where
  "zns_concl =
    target_forall nat_n0 nat_aty
      (eq_term bool_ty
        (eq_term nat_aty nat_zero_c (Comb nat_succ_c (FVar nat_n0 nat_aty)))
        false_term)"

definition si_concl :: hterm where
  "si_concl =
    target_forall nat_m0 nat_aty (target_forall nat_n0 nat_aty
      (target_imp
        (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
          (Comb nat_succ_c (FVar nat_n0 nat_aty)))
        (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))))"

definition ind_concl :: hterm where
  "ind_concl =
    target_forall nat_p0 nat_pty
      (target_imp
        (target_conj (Comb (FVar nat_p0 nat_pty) nat_zero_c)
          (target_forall nat_n0 nat_aty
            (target_imp (Comb (FVar nat_p0 nat_pty) (FVar nat_n0 nat_aty))
              (Comb (FVar nat_p0 nat_pty) (Comb nat_succ_c (FVar nat_n0 nat_aty))))))
        (target_forall nat_n0 nat_aty (Comb (FVar nat_p0 nat_pty) (FVar nat_n0 nat_aty))))"

definition new_nat_type ::
  "nat \<Rightarrow> htheory \<Rightarrow> (htheory \<times> hthm \<times> hthm \<times> hthm) option" where
  "new_nat_type fresh thy =
    (if tyops thy nat_ty_name \<noteq> None \<or> const_tab thy nat_zero_name \<noteq> None \<or>
        const_tab thy nat_succ_name \<noteq> None
     then None
     else
       let st = next_stamp fresh (thy_stamp thy);
           thy' = thy\<lparr>tyops := (tyops thy)(nat_ty_name := Some 0),
             const_tab := (const_tab thy)
               (nat_zero_name := Some nat_aty, nat_succ_name := Some nat_sty),
             thy_stamp := st\<rparr>;
           zns_th = \<lparr>hyps = [], concl = zns_concl, thm_stamp = st\<rparr>;
           si_th = \<lparr>hyps = [], concl = si_concl, thm_stamp = st\<rparr>;
           ind_th = \<lparr>hyps = [], concl = ind_concl, thm_stamp = st\<rparr>
       in
         if wf_thm thy' zns_th \<and> wf_thm thy' si_th \<and> wf_thm thy' ind_th
         then Some (thy', zns_th, si_th, ind_th) else None)"

lemma new_nat_type_extract:
  assumes run: "new_nat_type fresh thy = Some (thy', zns_th, si_th, ind_th)"
  shows "tyops thy nat_ty_name = None" "const_tab thy nat_zero_name = None"
    "const_tab thy nat_succ_name = None"
    "thy' = thy\<lparr>tyops := (tyops thy)(nat_ty_name := Some 0),
      const_tab := (const_tab thy)
        (nat_zero_name := Some nat_aty, nat_succ_name := Some nat_sty),
      thy_stamp := next_stamp fresh (thy_stamp thy)\<rparr>"
    "wf_thm thy' zns_th" "wf_thm thy' si_th" "wf_thm thy' ind_th"
    "zns_th = \<lparr>hyps = [], concl = zns_concl, thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    "si_th = \<lparr>hyps = [], concl = si_concl, thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    "ind_th = \<lparr>hyps = [], concl = ind_concl, thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
  using run
  by (auto simp: new_nat_type_def Let_def split: if_splits)

section \<open>Generic quantifier/connective semantics\<close>

text \<open>The @{term holds_target_forall_iff} family in the base-model theory is
stated only for the specific standard frame and base theory built there.
Their proofs use nothing but the generic evaluation lemmas already in the
semantics theory; restated here for an arbitrary well-formed @{term F}/
@{term thy} -- this genericity is over the ambient theory the extension is
applied to, not over what Nat is called, which is fixed above. @{term
true_term}/@{term false_term}'s evaluation never touches @{term
tyop_denote}/@{term const_denote} at all -- @{term const_sem}'s @{term NEq}
branch is the same @{term zeq} computation for every frame -- so those go
generic the same way.\<close>

lemma eval_true_term_general [simp]:
  "eval_term F \<rho> \<nu> env true_term = ztrue"
  by (simp add: const_sem_def true_term_def eq_bool_ty_def eq_term_def eq_const_def
      mk_fun_def bool_ty_def zeq_apply zeq_in_fun)

lemma eval_constant_true_function_general [simp]:
  "eval_term F \<rho> \<nu> env constant_true_function =
    Lambda zbool (\<lambda>_. Lambda zbool (\<lambda>_. ztrue))"
  by (simp add: constant_true_function_def)

lemma eval_false_term_general [simp]:
  "eval_term F \<rho> \<nu> env false_term = zfalse"
proof -
  have eq_member: "Elem (zeq zbool) (Fun zbool (Fun zbool zbool))"
    using zeq_in_fun .
  have const_member:
    "Elem (Lambda zbool (\<lambda>_. Lambda zbool (\<lambda>_. ztrue)))
      (Fun zbool (Fun zbool zbool))"
    by (simp add: Elem_Lambda_Fun)
  show ?thesis
    using zeq_apply[OF eq_member const_member] equality_not_constant_true
    by (simp add: const_sem_def false_term_def eq_bool_ty_def eq_term_def eq_const_def
        mk_fun_def bool_ty_def)
qed

lemma holds_target_forall_iff_general:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and body_check: "check_term thy body"
    and left_check: "check_term thy (target_abs n ty body)"
    and left_type: "type_of (target_abs n ty body) = Some (mk_fun ty bool_ty)"
    and right_check: "check_term thy (Abs ty true_term)"
    and right_type: "type_of (Abs ty true_term) = Some (mk_fun ty bool_ty)"
  shows "holds F \<rho> \<nu> (target_forall n ty body) \<longleftrightarrow>
    (\<forall>z. Elem z (interp_type F \<rho> ty) \<longrightarrow>
      eval_term F \<rho> (\<nu>((n, ty) := z)) [] body = ztrue)"
proof -
  let ?A = "interp_type F \<rho> ty"
  let ?g = "\<lambda>z. eval_term F \<rho> (\<nu>((n, ty) := z)) [] body"
  have outer: "holds F \<rho> \<nu>
      (eq_term (mk_fun ty bool_ty) (target_abs n ty body) (Abs ty true_term)) \<longleftrightarrow>
      eval_term F \<rho> \<nu> [] (target_abs n ty body) =
        eval_term F \<rho> \<nu> [] (Abs ty true_term)"
    using holds_eq_iff[OF thy_wf frame_ok type_ok free_ok const_ok
        left_check left_type right_check right_type] .
  have left_eval: "eval_term F \<rho> \<nu> [] (target_abs n ty body) = Lambda ?A ?g"
    using eval_target_abs[OF body_check] .
  have right_eval: "eval_term F \<rho> \<nu> [] (Abs ty true_term) = Lambda ?A (\<lambda>_. ztrue)"
    by simp
  have lambda_eq: "Lambda ?A ?g = Lambda ?A (\<lambda>_. ztrue) \<longleftrightarrow>
      (\<forall>z. Elem z ?A \<longrightarrow> ?g z = ztrue)"
  proof
    assume equal: "Lambda ?A ?g = Lambda ?A (\<lambda>_. ztrue)"
    show "\<forall>z. Elem z ?A \<longrightarrow> ?g z = ztrue"
    proof (intro allI impI)
      fix z assume z_in: "Elem z ?A"
      have "app (Lambda ?A ?g) z = app (Lambda ?A (\<lambda>_. ztrue)) z"
        using equal by simp
      then show "?g z = ztrue" using z_in by (simp add: Lambda_app)
    qed
  next
    assume pointwise: "\<forall>z. Elem z ?A \<longrightarrow> ?g z = ztrue"
    show "Lambda ?A ?g = Lambda ?A (\<lambda>_. ztrue)"
      using pointwise by (simp add: Lambda_ext)
  qed
  show ?thesis
    using outer left_eval right_eval lambda_eq by (simp add: target_forall_def)
qed

lemma holds_target_conj_iff_general:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and p_check: "check_term thy p" and p_type: "type_of p = Some bool_ty"
    and q_check: "check_term thy q" and q_type: "type_of q = Some bool_ty"
    and p_fresh: "\<not> vfree_in conj_fn conj_fty p"
    and q_fresh: "\<not> vfree_in conj_fn conj_fty q"
    and body_check: "check_term thy (Comb (Comb (FVar conj_fn conj_fty) p) q)"
    and rhs_body_check: "check_term thy
      (Comb (Comb (FVar conj_fn conj_fty) true_term) true_term)"
    and lhs_check: "check_term thy (conj_lhs p q)"
    and lhs_type: "type_of (conj_lhs p q) = Some (mk_fun conj_fty bool_ty)"
    and rhs_check: "check_term thy conj_rhs"
    and rhs_type: "type_of conj_rhs = Some (mk_fun conj_fty bool_ty)"
  shows "holds F \<rho> \<nu> (target_conj p q) \<longleftrightarrow>
    (holds F \<rho> \<nu> p \<and> holds F \<rho> \<nu> q)"
proof -
  let ?P = "eval_term F \<rho> \<nu> [] p"
  let ?Q = "eval_term F \<rho> \<nu> [] q"
  let ?Funs = "Fun zbool (Fun zbool zbool)"
  have empty: "bound_valuation_ok F \<rho> [] []" by (simp add: bound_valuation_ok_def)
  have p_open: "check_open_term thy [] p" using p_check by (simp add: check_term_def)
  have q_open: "check_open_term thy [] q" using q_check by (simp add: check_term_def)
  have p_in: "Elem ?P zbool"
    using eval_type_sound[OF thy_wf frame_ok type_ok free_ok const_ok empty p_open p_type]
    by (simp add: bool_ty_def)
  have q_in: "Elem ?Q zbool"
    using eval_type_sound[OF thy_wf frame_ok type_ok free_ok const_ok empty q_open q_type]
    by (simp add: bool_ty_def)
  have left_eval: "eval_term F \<rho> \<nu> [] (conj_lhs p q) =
      Lambda ?Funs (\<lambda>f. app (app f ?P) ?Q)"
  proof -
    note abs_raw = eval_target_abs[OF body_check, of F \<rho> \<nu> conj_fn conj_fty]
    have pointwise: "eval_term F \<rho> (\<nu>((conj_fn, conj_fty) := f)) []
        (Comb (Comb (FVar conj_fn conj_fty) p) q) = app (app f ?P) ?Q" for f
    proof -
      have ep: "eval_term F \<rho> (\<nu>((conj_fn, conj_fty) := f)) [] p = ?P"
        using eval_not_vfree_update[OF p_fresh, of F \<rho> \<nu> f "[]"] .
      have eq: "eval_term F \<rho> (\<nu>((conj_fn, conj_fty) := f)) [] q = ?Q"
        using eval_not_vfree_update[OF q_fresh, of F \<rho> \<nu> f "[]"] .
      show ?thesis using ep eq by simp
    qed
    show ?thesis using abs_raw pointwise
      by (simp add: conj_lhs_def conj_fty_def mk_fun_def bool_ty_def Lambda_ext)
  qed
  have right_eval: "eval_term F \<rho> \<nu> [] conj_rhs =
      Lambda ?Funs (\<lambda>f. app (app f ztrue) ztrue)"
  proof -
    note abs_raw = eval_target_abs[OF rhs_body_check, of F \<rho> \<nu> conj_fn conj_fty]
    show ?thesis using abs_raw
      by (simp add: conj_rhs_def conj_fty_def mk_fun_def bool_ty_def Lambda_ext)
  qed
  have outer: "holds F \<rho> \<nu> (eq_term (mk_fun conj_fty bool_ty) (conj_lhs p q) conj_rhs) \<longleftrightarrow>
      eval_term F \<rho> \<nu> [] (conj_lhs p q) = eval_term F \<rho> \<nu> [] conj_rhs"
    using holds_eq_iff[OF thy_wf frame_ok type_ok free_ok const_ok
        lhs_check lhs_type rhs_check rhs_type] .
  have function_eq: "Lambda ?Funs (\<lambda>f. app (app f ?P) ?Q) =
      Lambda ?Funs (\<lambda>f. app (app f ztrue) ztrue) \<longleftrightarrow> (?P = ztrue \<and> ?Q = ztrue)"
  proof
    assume equal: "Lambda ?Funs (\<lambda>f. app (app f ?P) ?Q) =
      Lambda ?Funs (\<lambda>f. app (app f ztrue) ztrue)"
    let ?fst = "Lambda zbool (\<lambda>a. Lambda zbool (\<lambda>_. a))"
    let ?snd = "Lambda zbool (\<lambda>_. Lambda zbool id)"
    have fst_in: "Elem ?fst ?Funs" by (simp add: Elem_Lambda_Fun)
    have snd_in: "Elem ?snd ?Funs" by (simp add: Elem_Lambda_Fun)
    have fst_equal: "app (Lambda ?Funs (\<lambda>f. app (app f ?P) ?Q)) ?fst =
        app (Lambda ?Funs (\<lambda>f. app (app f ztrue) ztrue)) ?fst"
      using equal by simp
    have snd_equal: "app (Lambda ?Funs (\<lambda>f. app (app f ?P) ?Q)) ?snd =
        app (Lambda ?Funs (\<lambda>f. app (app f ztrue) ztrue)) ?snd"
      using equal by simp
    have "?P = ztrue" using fst_equal fst_in p_in q_in by (simp add: Lambda_app)
    moreover have "?Q = ztrue" using snd_equal snd_in p_in q_in by (simp add: Lambda_app)
    ultimately show "?P = ztrue \<and> ?Q = ztrue" by blast
  next
    assume both: "?P = ztrue \<and> ?Q = ztrue"
    then show "Lambda ?Funs (\<lambda>f. app (app f ?P) ?Q) =
      Lambda ?Funs (\<lambda>f. app (app f ztrue) ztrue)" by simp
  qed
  show ?thesis using outer left_eval right_eval function_eq
    by (simp add: target_conj_def holds_def)
qed

lemma holds_target_imp_iff_general:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and conj_check: "check_term thy (target_conj p q)"
    and conj_type: "type_of (target_conj p q) = Some bool_ty"
    and p_check: "check_term thy p" and p_type: "type_of p = Some bool_ty"
    and conj_sem: "holds F \<rho> \<nu> (target_conj p q) \<longleftrightarrow>
      (holds F \<rho> \<nu> p \<and> holds F \<rho> \<nu> q)"
  shows "holds F \<rho> \<nu> (target_imp p q) \<longleftrightarrow>
    (holds F \<rho> \<nu> p \<longrightarrow> holds F \<rho> \<nu> q)"
proof -
  let ?C = "eval_term F \<rho> \<nu> [] (target_conj p q)"
  let ?P = "eval_term F \<rho> \<nu> [] p"
  have empty: "bound_valuation_ok F \<rho> [] []" by (simp add: bound_valuation_ok_def)
  have conj_open: "check_open_term thy [] (target_conj p q)"
    using conj_check by (simp add: check_term_def)
  have p_open: "check_open_term thy [] p" using p_check by (simp add: check_term_def)
  have c_in: "Elem ?C zbool"
    using eval_type_sound[OF thy_wf frame_ok type_ok free_ok const_ok empty conj_open conj_type]
    by (simp add: bool_ty_def)
  have p_in: "Elem ?P zbool"
    using eval_type_sound[OF thy_wf frame_ok type_ok free_ok const_ok empty p_open p_type]
    by (simp add: bool_ty_def)
  have outer: "holds F \<rho> \<nu> (eq_term bool_ty (target_conj p q) p) \<longleftrightarrow> ?C = ?P"
    using holds_eq_iff[OF thy_wf frame_ok type_ok free_ok const_ok
        conj_check conj_type p_check p_type] .
  have truth: "(?C = ?P) \<longleftrightarrow>
      (?P = ztrue \<longrightarrow> eval_term F \<rho> \<nu> [] q = ztrue)"
    using c_in p_in conj_sem ztrue_neq_zfalse by (auto simp: holds_def)
  show ?thesis using outer truth by (simp add: target_imp_def holds_def)
qed

lemma eq_type_match_ok [simp]:
  "type_match (mk_fun (TyVar NAlpha) (mk_fun (TyVar NAlpha) bool_ty))
     (mk_fun a (mk_fun a bool_ty)) (\<lambda>_. None) \<noteq> None"
  by (simp add: type_match_def mk_fun_def bool_ty_def)

section \<open>Generic well-typedness building blocks\<close>

text \<open>@{term type_of} never consults @{term thy}, so its facts are plain
computation. @{term check_term} does, but only through @{term check_type}
and @{term const_tab} lookups; the lemmas below let those be discharged from
@{term wf_theory} plus whatever the caller already knows about its own
extra constants, without re-deriving the @{term NEq}/@{term NFun}/@{term
NBool} plumbing at every use site.\<close>

lemma wf_theory_bool_ty_check [simp]: "wf_theory thy \<Longrightarrow> check_type thy bool_ty"
  by (simp add: wf_theory_def bool_ty_def)

lemma wf_theory_eq_const_check:
  assumes "wf_theory thy" "check_type thy a"
  shows "check_term thy (eq_const a)"
    "type_of (eq_const a) = Some (mk_fun a (mk_fun a bool_ty))"
  using assms eq_type_match_ok[of a]
  by (simp_all add: eq_const_def check_term_def wf_theory_def mk_fun_def)

lemma wf_theory_eq_term_check:
  assumes wf: "wf_theory thy" and a_check: "check_type thy a"
    and l_check: "check_term thy l" and l_type: "type_of l = Some a"
    and r_check: "check_term thy r" and r_type: "type_of r = Some a"
  shows "check_term thy (eq_term a l r)" "type_of (eq_term a l r) = Some bool_ty"
  using wf_theory_eq_const_check[OF wf a_check] l_check l_type r_check r_type
  by (simp_all add: eq_term_def check_term_def mk_fun_def)

lemma wf_theory_eq_bool_ty_check [simp]: "wf_theory thy \<Longrightarrow> check_type thy eq_bool_ty"
  by (simp add: eq_bool_ty_def wf_theory_def mk_fun_def bool_ty_def)

lemma wf_theory_true_term_check [simp]:
  assumes "wf_theory thy"
  shows "check_term thy true_term" "type_of true_term = Some bool_ty"
  using assms eq_type_match_ok[of bool_ty] eq_type_match_ok[of eq_bool_ty]
  by (simp_all add: true_term_def check_term_def eq_term_def eq_const_def
      eq_bool_ty_def mk_fun_def bool_ty_def wf_theory_def)

lemma wf_theory_false_term_check [simp]:
  assumes wf: "wf_theory thy"
  shows "check_term thy false_term" "type_of false_term = Some bool_ty"
proof -
  have l_check: "check_term thy (eq_const bool_ty)"
    and l_type: "type_of (eq_const bool_ty) = Some eq_bool_ty"
    using wf_theory_eq_const_check[OF wf wf_theory_bool_ty_check[OF wf]]
    by (simp_all add: eq_bool_ty_def)
  have true_weak: "check_open_term thy [bool_ty, bool_ty] true_term"
    using wf_theory_true_term_check[OF wf]
      check_open_term_weaken[of thy "[]" true_term "[bool_ty, bool_ty]"]
    by (simp add: check_term_def)
  have r_check: "check_term thy constant_true_function"
    using wf_theory_bool_ty_check[OF wf] true_weak
    by (simp add: check_term_def constant_true_function_def)
  have r_type: "type_of constant_true_function = Some eq_bool_ty"
    using wf_theory_true_term_check[OF wf]
    by (simp add: constant_true_function_def eq_bool_ty_def mk_fun_def)
  show "check_term thy false_term" "type_of false_term = Some bool_ty"
    using wf_theory_eq_term_check[OF wf wf_theory_eq_bool_ty_check[OF wf]
        l_check l_type r_check r_type]
    by (simp_all add: false_term_def)
qed

lemma target_abs_ok:
  assumes ty_check: "check_type thy ty" and body_check: "check_term thy body"
    and body_type: "type_of body = Some bool_ty"
  shows "check_term thy (target_abs n ty body)"
    "type_of (target_abs n ty body) = Some (mk_fun ty bool_ty)"
proof -
  have fvar: "check_open_term thy [] (FVar n ty)" using ty_check by simp
  show "check_term thy (target_abs n ty body)"
    unfolding target_abs_def
    using abstract_fvar_preserves_check[OF fvar body_check[unfolded check_term_def]]
    by (simp add: check_term_def)
  show "type_of (target_abs n ty body) = Some (mk_fun ty bool_ty)"
    by (simp add: target_abs_def abstract_fvar_def body_type)
qed

lemma wf_theory_target_forall_check:
  assumes wf: "wf_theory thy" and ty_check: "check_type thy ty"
    and body_check: "check_term thy body" and body_type: "type_of body = Some bool_ty"
  shows "check_term thy (target_forall n ty body)"
    "type_of (target_forall n ty body) = Some bool_ty"
proof -
  have abs_check: "check_term thy (target_abs n ty body)"
    and abs_type: "type_of (target_abs n ty body) = Some (mk_fun ty bool_ty)"
    using target_abs_ok[OF ty_check body_check body_type] by simp_all
  have right_check: "check_term thy (Abs ty true_term)"
    using wf_theory_true_term_check[OF wf] ty_check
      check_open_term_weaken[of thy "[]" true_term "[ty]"]
    by (simp add: check_term_def)
  have right_type: "type_of (Abs ty true_term) = Some (mk_fun ty bool_ty)"
    using wf_theory_true_term_check[OF wf] by simp
  have a_check: "check_type thy (mk_fun ty bool_ty)"
    using wf ty_check by (simp add: wf_theory_def mk_fun_def)
  show "check_term thy (target_forall n ty body)"
    "type_of (target_forall n ty body) = Some bool_ty"
    using wf_theory_eq_term_check[OF wf a_check abs_check abs_type right_check right_type]
    by (simp_all add: target_forall_def)
qed

lemma wf_theory_target_conj_check:
  assumes wf: "wf_theory thy"
    and p_check: "check_term thy p" and p_type: "type_of p = Some bool_ty"
    and q_check: "check_term thy q" and q_type: "type_of q = Some bool_ty"
  shows "check_term thy (target_conj p q)" "type_of (target_conj p q) = Some bool_ty"
proof -
  have body_check: "check_term thy (Comb (Comb (FVar conj_fn conj_fty) p) q)"
    using p_check q_check wf
    by (simp add: check_term_def conj_fty_def wf_theory_def mk_fun_def bool_ty_def p_type q_type)
  have body_type: "type_of (Comb (Comb (FVar conj_fn conj_fty) p) q) = Some bool_ty"
    using p_type q_type by (simp add: conj_fty_def mk_fun_def)
  have conj_fty_check: "check_type thy conj_fty"
    using wf by (simp add: conj_fty_def wf_theory_def mk_fun_def)
  have lhs_check: "check_term thy (conj_lhs p q)"
    and lhs_type: "type_of (conj_lhs p q) = Some (mk_fun conj_fty bool_ty)"
    using target_abs_ok[OF conj_fty_check body_check body_type]
    by (simp_all add: conj_lhs_def)
  have rhs_body_check: "check_term thy (Comb (Comb (FVar conj_fn conj_fty) true_term) true_term)"
    using wf_theory_true_term_check[OF wf] wf
    by (simp add: check_term_def conj_fty_def wf_theory_def mk_fun_def bool_ty_def)
  have rhs_body_type: "type_of (Comb (Comb (FVar conj_fn conj_fty) true_term) true_term) =
      Some bool_ty"
    using wf_theory_true_term_check[OF wf] by (simp add: conj_fty_def mk_fun_def)
  have rhs_check: "check_term thy conj_rhs"
    and rhs_type: "type_of conj_rhs = Some (mk_fun conj_fty bool_ty)"
    using target_abs_ok[OF conj_fty_check rhs_body_check rhs_body_type]
    by (simp_all add: conj_rhs_def)
  have a_check: "check_type thy (mk_fun conj_fty bool_ty)"
    using wf conj_fty_check by (simp add: wf_theory_def mk_fun_def)
  show "check_term thy (target_conj p q)" "type_of (target_conj p q) = Some bool_ty"
    using wf_theory_eq_term_check[OF wf a_check lhs_check lhs_type rhs_check rhs_type]
    by (simp_all add: target_conj_def)
qed

lemma wf_theory_target_imp_check:
  assumes wf: "wf_theory thy"
    and p_check: "check_term thy p" and p_type: "type_of p = Some bool_ty"
    and q_check: "check_term thy q" and q_type: "type_of q = Some bool_ty"
  shows "check_term thy (target_imp p q)" "type_of (target_imp p q) = Some bool_ty"
proof -
  have conj_check: "check_term thy (target_conj p q)"
    and conj_type: "type_of (target_conj p q) = Some bool_ty"
    using wf_theory_target_conj_check[OF wf p_check p_type q_check q_type] by simp_all
  show "check_term thy (target_imp p q)" "type_of (target_imp p q) = Some bool_ty"
    using wf_theory_eq_term_check[OF wf wf_theory_bool_ty_check[OF wf]
        conj_check conj_type p_check p_type]
    by (simp_all add: target_imp_def)
qed

lemma interp_type_mk_fun [simp]:
  "interp_type F \<rho> (mk_fun a b) = Fun (interp_type F \<rho> a) (interp_type F \<rho> b)"
  by (simp add: mk_fun_def)

lemma conj_fn_distinct [simp]:
  "conj_fn \<noteq> nat_m0" "conj_fn \<noteq> nat_n0" "conj_fn \<noteq> nat_p0"
  "nat_m0 \<noteq> conj_fn" "nat_n0 \<noteq> conj_fn" "nat_p0 \<noteq> conj_fn"
  by (simp_all add: conj_fn_def nat_m0_def nat_n0_def nat_p0_def)

text \<open>@{term holds_target_imp_iff_general} needs @{term holds_target_conj_iff_general}
already applied as one of its own hypotheses. These package both together so
call sites only ever need to supply @{term p}/@{term q}'s own check/type/
freshness facts, not the intervening @{term target_conj}/@{term conj_lhs}/
@{term conj_rhs} plumbing.\<close>

lemma wf_theory_target_conj_holds:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>" and const_ok: "const_interpretation_ok F thy \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and p_check: "check_term thy p" and p_type: "type_of p = Some bool_ty"
    and q_check: "check_term thy q" and q_type: "type_of q = Some bool_ty"
    and p_fresh: "\<not> vfree_in conj_fn conj_fty p"
    and q_fresh: "\<not> vfree_in conj_fn conj_fty q"
  shows "holds F \<rho> \<nu> (target_conj p q) \<longleftrightarrow> (holds F \<rho> \<nu> p \<and> holds F \<rho> \<nu> q)"
proof -
  have body_check: "check_term thy (Comb (Comb (FVar conj_fn conj_fty) p) q)"
    using p_check q_check thy_wf
    by (simp add: check_term_def conj_fty_def wf_theory_def mk_fun_def bool_ty_def p_type q_type)
  have body_type: "type_of (Comb (Comb (FVar conj_fn conj_fty) p) q) = Some bool_ty"
    using p_type q_type by (simp add: conj_fty_def mk_fun_def)
  have conj_fty_check: "check_type thy conj_fty"
    using thy_wf by (simp add: conj_fty_def wf_theory_def mk_fun_def)
  have lhs_check: "check_term thy (conj_lhs p q)"
    and lhs_type: "type_of (conj_lhs p q) = Some (mk_fun conj_fty bool_ty)"
    using target_abs_ok[OF conj_fty_check body_check body_type]
    by (simp_all add: conj_lhs_def)
  have rhs_body_check: "check_term thy (Comb (Comb (FVar conj_fn conj_fty) true_term) true_term)"
    using wf_theory_true_term_check[OF thy_wf] thy_wf
    by (simp add: check_term_def conj_fty_def wf_theory_def mk_fun_def bool_ty_def)
  have rhs_body_type: "type_of (Comb (Comb (FVar conj_fn conj_fty) true_term) true_term) =
      Some bool_ty"
    using wf_theory_true_term_check[OF thy_wf] by (simp add: conj_fty_def mk_fun_def)
  have rhs_check: "check_term thy conj_rhs"
    and rhs_type: "type_of conj_rhs = Some (mk_fun conj_fty bool_ty)"
    using target_abs_ok[OF conj_fty_check rhs_body_check rhs_body_type]
    by (simp_all add: conj_rhs_def)
  show ?thesis
    using holds_target_conj_iff_general[OF thy_wf frame_ok type_ok const_ok free_ok
        p_check p_type q_check q_type p_fresh q_fresh body_check rhs_body_check
        lhs_check lhs_type rhs_check rhs_type] .
qed

lemma wf_theory_target_imp_holds:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>" and const_ok: "const_interpretation_ok F thy \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and p_check: "check_term thy p" and p_type: "type_of p = Some bool_ty"
    and q_check: "check_term thy q" and q_type: "type_of q = Some bool_ty"
    and p_fresh: "\<not> vfree_in conj_fn conj_fty p"
    and q_fresh: "\<not> vfree_in conj_fn conj_fty q"
  shows "holds F \<rho> \<nu> (target_imp p q) \<longleftrightarrow> (holds F \<rho> \<nu> p \<longrightarrow> holds F \<rho> \<nu> q)"
proof -
  have conj_sem: "holds F \<rho> \<nu> (target_conj p q) \<longleftrightarrow> (holds F \<rho> \<nu> p \<and> holds F \<rho> \<nu> q)"
    using wf_theory_target_conj_holds[OF thy_wf frame_ok type_ok const_ok free_ok
        p_check p_type q_check q_type p_fresh q_fresh] .
  have conj_check: "check_term thy (target_conj p q)"
    and conj_type: "type_of (target_conj p q) = Some bool_ty"
    using wf_theory_target_conj_check[OF thy_wf p_check p_type q_check q_type] by simp_all
  show ?thesis
    using holds_target_imp_iff_general[OF thy_wf frame_ok type_ok const_ok free_ok
        conj_check conj_type p_check p_type conj_sem] .
qed

text \<open>Every abstraction @{term new_nat_type} builds is over a bound name
distinct from @{term conj_fn}, and @{term conj_lhs}/@{term conj_rhs} always
abstract exactly @{term conj_fn} away -- so @{term target_conj}/@{term
target_imp}/@{term target_forall} never re-expose it, regardless of what
@{term p}/@{term q}/@{term body} are.\<close>

lemma vfree_in_abstract_at_other:
  assumes "(n, ty) \<noteq> (m, uy)"
  shows "vfree_in m uy (abstract_at j n ty t) = vfree_in m uy t"
  using assms by (induction t arbitrary: j) auto

lemma vfree_in_target_conj_self [simp]:
  "\<not> vfree_in conj_fn conj_fty (target_conj p q)"
proof -
  have lhs_free: "\<not> vfree_in conj_fn conj_fty (conj_lhs p q)"
    by (simp add: conj_lhs_def target_abs_def abstract_fvar_def abstract_at_removes_fvar)
  have rhs_free: "\<not> vfree_in conj_fn conj_fty conj_rhs"
    by (simp add: conj_rhs_def target_abs_def abstract_fvar_def abstract_at_removes_fvar)
  show ?thesis
    using lhs_free rhs_free by (simp add: target_conj_def eq_term_def eq_const_def)
qed

lemma vfree_in_target_imp_other [simp]:
  "vfree_in conj_fn conj_fty (target_imp p q) = vfree_in conj_fn conj_fty p"
  by (simp add: target_imp_def eq_term_def eq_const_def)

lemma vfree_in_target_forall_other [simp]:
  assumes "n \<noteq> conj_fn \<or> ty \<noteq> conj_fty"
  shows "vfree_in conj_fn conj_fty (target_forall n ty body) = vfree_in conj_fn conj_fty body"
proof -
  have true_free: "\<not> vfree_in conj_fn conj_fty true_term"
    by (simp add: true_term_def eq_term_def eq_const_def)
  have abs_free: "vfree_in conj_fn conj_fty (abstract_fvar n ty body) = vfree_in conj_fn conj_fty body"
    using vfree_in_abstract_at_other[where n=n and ty=ty and m=conj_fn and uy=conj_fty
        and j=0 and t=body] assms
    by (simp add: abstract_fvar_def)
  show ?thesis
    using abs_free true_free
    by (simp add: target_forall_def target_abs_def eq_term_def eq_const_def)
qed

lemma vfree_in_conj_fn_fvar_other [simp]:
  "n \<noteq> conj_fn \<Longrightarrow> \<not> vfree_in conj_fn conj_fty (FVar n ty)"
  by simp



section \<open>Peano's properties for HOLZF's Nat, for free\<close>

lemma Elem_self_SucNat: "Elem N (SucNat N)"
  by (auto simp: SucNat_def union Singleton_def Upair Sum)

lemma HOLZF_zero_not_succ: "Empty \<noteq> SucNat N"
  using Elem_self_SucNat Empty by metis

lemma HOLZF_succ_inj:
  assumes M: "Elem M Nat" and N: "Elem N Nat" and eq: "SucNat M = SucNat N"
  shows "M = N"
proof -
  have "Nat2nat (SucNat M) = Nat2nat (SucNat N)" using eq by simp
  then have "Suc (Nat2nat M) = Suc (Nat2nat N)"
    using Nat2nat_SucNat[OF M] Nat2nat_SucNat[OF N] by simp
  then have "Nat2nat M = Nat2nat N" by simp
  then have "nat2Nat (Nat2nat M) = nat2Nat (Nat2nat N)" by simp
  then show ?thesis using nat2Nat_Nat2nat[OF M] nat2Nat_Nat2nat[OF N] by simp
qed

lemma HOLZF_nat_induct:
  assumes zero: "P Empty"
    and step: "\<And>N. Elem N Nat \<Longrightarrow> P N \<Longrightarrow> P (SucNat N)"
    and elem: "Elem N Nat"
  shows "P N"
proof -
  from elem obtain n where n: "N = nat2Nat n"
    by (auto simp: Nat_def Sep)
  have "P (nat2Nat n)"
  proof (induction n)
    case 0
    then show ?case by (simp add: zero)
  next
    case (Suc n)
    have en: "Elem (nat2Nat n) Nat" by auto
    then have "P (nat2Nat n)" using Suc by blast
    then show ?case using step[OF en] by simp
  qed
  with n show ?thesis by simp
qed

section \<open>Model extension: @{term new_nat_type} is conservative\<close>

definition nat_frame :: "frame \<Rightarrow> frame" where
  "nat_frame F = add_type_frame F nat_ty_name (\<lambda>_. Nat)"

definition nat_ext_frame :: "frame \<Rightarrow> frame" where
  "nat_ext_frame F =
    add_definition_frame
      (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty))
      nat_succ_name nat_sty (\<lambda>_. Lambda Nat SucNat)"

lemma nat_frame_wf:
  assumes "frame_wf F"
  shows "frame_wf (nat_frame F)"
  unfolding nat_frame_def
  using add_type_frame_wf[OF assms nat_names_distinct(1) nat_names_distinct(2)]
  by (fastforce simp: inhabited_def intro: Elem_Empty_Nat)

lemma interp_nat_aty [simp]: "interp_type (nat_frame F) \<rho> nat_aty = Nat"
  by (simp add: nat_frame_def nat_aty_def add_type_frame_def)

lemma interp_nat_aty_def [simp]:
  "interp_type (add_definition_frame G n g C) \<rho> nat_aty =
    interp_type G \<rho> nat_aty"
  by simp

lemma interp_nat_sty_of [simp]:
  "interp_type G \<rho> nat_aty = Nat \<Longrightarrow> interp_type G \<rho> nat_sty = Fun Nat Nat"
  by (simp add: nat_sty_def mk_fun_def)

lemma nat_ext_frame_wf:
  assumes "frame_wf F"
  shows "frame_wf (nat_ext_frame F)"
  unfolding nat_ext_frame_def
  by (rule add_definition_frame_wf,
      rule add_definition_frame_wf[OF nat_frame_wf[OF assms]]; simp)

lemma interp_nat_aty_ext [simp]: "interp_type (nat_ext_frame F) \<rho> nat_aty = Nat"
  by (simp add: nat_ext_frame_def)

lemma interp_nat_sty_ext [simp]: "interp_type (nat_ext_frame F) \<rho> nat_sty = Fun Nat Nat"
  by simp

lemma nat_aty_self_match: "type_match nat_aty nat_aty (\<lambda>_. None) = Some (\<lambda>_. None)"
  by (simp add: nat_aty_def type_match_def)

lemma nat_sty_self_match: "type_match nat_sty nat_sty (\<lambda>_. None) = Some (\<lambda>_. None)"
  by (simp add: nat_sty_def nat_aty_def mk_fun_def type_match_def)


lemma const_sem_zero_ext:
  "const_sem (nat_ext_frame F) \<rho> nat_zero_name nat_aty = Empty"
proof -
  have step2: "const_sem (nat_ext_frame F) \<rho> nat_zero_name nat_aty =
      const_sem (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty))
        \<rho> nat_zero_name nat_aty"
    unfolding nat_ext_frame_def
    using const_sem_add_definition_other[of nat_zero_name nat_succ_name
        "add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)"
        nat_sty "\<lambda>_. Lambda Nat SucNat" \<rho> nat_aty]
    by (simp add: nat_names_distinct)
  show ?thesis
    using step2 const_sem_add_definition_same[OF nat_names_distinct(3) nat_aty_self_match,
        of "nat_frame F" "\<lambda>_. Empty" \<rho>]
    by simp
qed

lemma const_sem_succ_ext:
  "const_sem (nat_ext_frame F) \<rho> nat_succ_name nat_sty = Lambda Nat SucNat"
  unfolding nat_ext_frame_def
  using const_sem_add_definition_same[OF nat_names_distinct(4) nat_sty_self_match,
      of "add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)"
        "\<lambda>_. Lambda Nat SucNat" \<rho>]
  by simp

lemma const_scheme_zero_ext [simp]:
  "const_scheme (nat_ext_frame F) nat_zero_name = Some nat_aty"
  by (simp add: nat_ext_frame_def add_definition_frame_def)

lemma const_scheme_succ_ext [simp]:
  "const_scheme (nat_ext_frame F) nat_succ_name = Some nat_sty"
  by (simp add: nat_ext_frame_def add_definition_frame_def)

lemma const_scheme_nat_ext_other [simp]:
  "m \<noteq> nat_zero_name \<Longrightarrow> m \<noteq> nat_succ_name \<Longrightarrow>
    const_scheme (nat_ext_frame F) m = const_scheme F m"
  by (simp add: nat_ext_frame_def nat_frame_def add_definition_frame_def
      add_type_frame_def)

theorem new_nat_type_conservative:
  assumes run: "new_nat_type fresh thy = Some (thy', zns_th, si_th, ind_th)"
    and thy_wf: "wf_theory thy"
    and contents_wf: "theory_contents_wf thy"
    and model: "models_theory F thy"
  shows "models_theory (nat_ext_frame F) thy'"
    and "valid_sequent (nat_ext_frame F) thy' (hyps zns_th) (concl zns_th)"
    and "valid_sequent (nat_ext_frame F) thy' (hyps si_th) (concl si_th)"
    and "valid_sequent (nat_ext_frame F) thy' (hyps ind_th) (concl ind_th)"
proof -
  have fresh_ty: "tyops thy nat_ty_name = None"
    and fresh_zero: "const_tab thy nat_zero_name = None"
    and fresh_succ: "const_tab thy nat_succ_name = None"
    and thy'_eq: "thy' = thy\<lparr>tyops := (tyops thy)(nat_ty_name := Some 0),
      const_tab := (const_tab thy)
        (nat_zero_name := Some nat_aty, nat_succ_name := Some nat_sty),
      thy_stamp := next_stamp fresh (thy_stamp thy)\<rparr>"
    and zns_wf: "wf_thm thy' zns_th"
    and si_wf: "wf_thm thy' si_th"
    and ind_wf: "wf_thm thy' ind_th"
    using new_nat_type_extract[OF run] by blast+

  have old_frame: "frame_wf F"
    and old_const_ok: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    and old_axioms: "\<forall>th\<in>set (axiom_list thy). valid_sequent F thy (hyps th) (concl th)"
    and old_defs: "\<forall>n th. def_tab thy n = Some th \<longrightarrow>
      valid_sequent F thy (hyps th) (concl th)"
    using model by (auto simp: models_theory_def)

  have ext_wf: "frame_wf (nat_ext_frame F)" using nat_ext_frame_wf[OF old_frame] .

  have new_const_ok: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
      const_interpretation_ok (nat_ext_frame F) thy' \<rho>"
  proof (intro allI impI)
    fix \<rho> assume rho_ok: "type_valuation_ok \<rho>"
    show "const_interpretation_ok (nat_ext_frame F) thy' \<rho>"
      unfolding const_interpretation_ok_def
    proof (intro allI impI)
      fix m generic \<sigma>
      assume sigma_ok: "type_valuation_ok \<sigma>" and tab': "const_tab thy' m = Some generic"
      show "const_scheme (nat_ext_frame F) m = Some generic \<and>
          Elem (const_denote (nat_ext_frame F) m \<sigma>) (interp_type (nat_ext_frame F) \<sigma> generic)"
      proof (cases "m = nat_zero_name")
        case True
        have generic_eq: "generic = nat_aty" using tab' thy'_eq True by simp
        have denote_eq: "const_denote (nat_ext_frame F) nat_zero_name \<sigma> = Empty"
          by (simp add: nat_ext_frame_def add_definition_frame_def)
        show ?thesis
          using True generic_eq denote_eq Elem_Empty_Nat by simp
      next
        case not_zero: False
        show ?thesis
        proof (cases "m = nat_succ_name")
          case True
          have generic_eq: "generic = nat_sty" using tab' thy'_eq not_zero True by simp
          have succ_maps: "Elem (Lambda Nat SucNat) (Fun Nat Nat)"
            using Elem_SucNat_Nat by (simp add: Elem_Lambda_Fun)
          have denote_eq: "const_denote (nat_ext_frame F) nat_succ_name \<sigma> = Lambda Nat SucNat"
            using not_zero
            by (simp add: nat_ext_frame_def add_definition_frame_def)
          show ?thesis
            using True generic_eq denote_eq succ_maps by simp
        next
          case not_succ: False
          have old_tab: "const_tab thy m = Some generic"
            using tab' thy'_eq not_zero not_succ by simp
          have old_entry: "const_scheme F m = Some generic \<and>
              Elem (const_denote F m \<sigma>) (interp_type F \<sigma> generic)"
            using old_const_ok sigma_ok old_tab by (auto simp: const_interpretation_ok_def)
          have generic_checked: "check_type thy generic"
            using thy_wf old_tab by (auto simp: wf_theory_def)
          have scheme_eq: "const_scheme (nat_ext_frame F) m = const_scheme F m"
            using not_zero not_succ by simp
          have denote_eq: "const_denote (nat_ext_frame F) m \<sigma> = const_denote F m \<sigma>"
            using not_zero not_succ
            by (simp add: nat_ext_frame_def nat_frame_def add_definition_frame_def
                add_type_frame_def)
          have interp_eq: "interp_type (nat_ext_frame F) \<sigma> generic = interp_type F \<sigma> generic"
            using interp_type_add_type_unchanged[OF fresh_ty generic_checked,
                of F "\<lambda>_. Nat" \<sigma>]
            by (simp add: nat_ext_frame_def nat_frame_def)
          show ?thesis
            using scheme_eq old_entry denote_eq interp_eq by simp
        qed
      qed
    qed
  qed
  have nat_frame_const_ok: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
      const_interpretation_ok (nat_frame F) thy \<rho>"
  proof (intro allI impI)
    fix \<rho> assume rho_ok: "type_valuation_ok \<rho>"
    show "const_interpretation_ok (nat_frame F) thy \<rho>"
      unfolding const_interpretation_ok_def
    proof (intro allI impI)
      fix n g \<sigma> assume "type_valuation_ok \<sigma>" and tab: "const_tab thy n = Some g"
      have gc: "check_type thy g" using thy_wf tab by (auto simp: wf_theory_def)
      have old: "const_scheme F n = Some g \<and> Elem (const_denote F n \<sigma>) (interp_type F \<sigma> g)"
        using old_const_ok \<open>type_valuation_ok \<sigma>\<close> tab by (auto simp: const_interpretation_ok_def)
      have "interp_type (nat_frame F) \<sigma> g = interp_type F \<sigma> g"
        using interp_type_add_type_unchanged[OF fresh_ty gc, of F "\<lambda>_. Nat" \<sigma>]
        by (simp add: nat_frame_def)
      then show "const_scheme (nat_frame F) n = Some g \<and>
          Elem (const_denote (nat_frame F) n \<sigma>) (interp_type (nat_frame F) \<sigma> g)"
        using old by (simp add: nat_frame_def add_type_frame_def)
    qed
  qed

  have zero_frame_const_ok: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
      const_interpretation_ok
        (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) thy \<rho>"
  proof (intro allI impI)
    fix \<rho> assume rho_ok: "type_valuation_ok \<rho>"
    show "const_interpretation_ok
        (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) thy \<rho>"
      unfolding const_interpretation_ok_def
    proof (intro allI impI)
      fix n g \<sigma> assume "type_valuation_ok \<sigma>" and tab: "const_tab thy n = Some g"
      have neq: "n \<noteq> nat_zero_name" using tab fresh_zero by auto
      have old: "const_scheme (nat_frame F) n = Some g \<and>
          Elem (const_denote (nat_frame F) n \<sigma>) (interp_type (nat_frame F) \<sigma> g)"
        using nat_frame_const_ok \<open>type_valuation_ok \<sigma>\<close> tab
        by (auto simp: const_interpretation_ok_def)
      have scheme_eq: "const_scheme
          (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) n = Some g"
        using old neq by (simp add: add_definition_frame_def)
      have denote_eq: "const_denote
          (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) n \<sigma> =
        const_denote (nat_frame F) n \<sigma>"
        using neq by (simp add: add_definition_frame_def)
      have interp_same: "interp_type
          (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) \<sigma> g =
        interp_type (nat_frame F) \<sigma> g" by simp
      show "const_scheme
          (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) n = Some g \<and>
        Elem (const_denote
            (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) n \<sigma>)
          (interp_type
            (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) \<sigma> g)"
        using scheme_eq denote_eq interp_same old by simp
    qed
  qed

  have contents: "list_all (check_prop thy) (hyps th)" "check_prop thy (concl th)"
    if "th \<in> set (axiom_list thy)" for th
    using contents_wf that by (auto simp: theory_contents_wf_def list_all_iff wf_thm_def)

  have def_contents: "list_all (check_prop thy) (hyps th)" "check_prop thy (concl th)"
    if "def_tab thy n = Some th" for n th
    using contents_wf that by (auto simp: theory_contents_wf_def wf_thm_def)

  have axiom_step1: "valid_sequent (nat_frame F) thy (hyps th) (concl th)"
    if "th \<in> set (axiom_list thy)" for th
    using valid_sequent_add_type_unchanged[OF fresh_ty old_frame
        contents(1)[OF that] contents(2)[OF that] old_const_ok]
      old_axioms that
    by (simp add: nat_frame_def)
  have axiom_step2: "valid_sequent
      (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) thy
      (hyps th) (concl th)"
    if "th \<in> set (axiom_list thy)" for th
    using valid_sequent_add_definition_unchanged[OF fresh_zero
        contents(1)[OF that] contents(2)[OF that] nat_frame_const_ok]
      axiom_step1[OF that] by simp
  have axiom_preserved: "valid_sequent (nat_ext_frame F) thy' (hyps th) (concl th)"
    if "th \<in> set (axiom_list thy)" for th
    using valid_sequent_add_definition_unchanged[OF fresh_succ
        contents(1)[OF that] contents(2)[OF that] zero_frame_const_ok]
      axiom_step2[OF that]
    by (simp add: nat_ext_frame_def)

  have def_step1: "valid_sequent (nat_frame F) thy (hyps th) (concl th)"
    if "def_tab thy n = Some th" for n th
    using valid_sequent_add_type_unchanged[OF fresh_ty old_frame
        def_contents(1)[OF that] def_contents(2)[OF that] old_const_ok]
      old_defs that
    by (simp add: nat_frame_def)
  have def_step2: "valid_sequent
      (add_definition_frame (nat_frame F) nat_zero_name nat_aty (\<lambda>_. Empty)) thy
      (hyps th) (concl th)"
    if "def_tab thy n = Some th" for n th
    using valid_sequent_add_definition_unchanged[OF fresh_zero
        def_contents(1)[OF that] def_contents(2)[OF that] nat_frame_const_ok]
      def_step1[OF that] by simp
  have def_preserved: "valid_sequent (nat_ext_frame F) thy' (hyps th) (concl th)"
    if "def_tab thy n = Some th" for n th
    using valid_sequent_add_definition_unchanged[OF fresh_succ
        def_contents(1)[OF that] def_contents(2)[OF that] zero_frame_const_ok]
      def_step2[OF that]
    by (simp add: nat_ext_frame_def)


  have axiom_thy'_eq: "axiom_list thy' = axiom_list thy"
    and def_thy'_eq: "def_tab thy' = def_tab thy"
    using thy'_eq by simp_all

  have thy'_wf: "wf_theory thy'"
  proof -
    have old_type_checked: "check_type thy ty \<Longrightarrow> check_type thy' ty" for ty
      using thy'_eq fresh_ty by (induction ty) (auto simp: list_all_iff)
    have sym1: "NFun \<noteq> nat_ty_name" using nat_names_distinct(1) by (rule not_sym)
    have sym2: "NBool \<noteq> nat_ty_name" using nat_names_distinct(2) by (rule not_sym)
    have sym3: "NEq \<noteq> nat_zero_name" using nat_names_distinct(3) by (rule not_sym)
    have sym4: "NEq \<noteq> nat_succ_name" using nat_names_distinct(4) by (rule not_sym)
    show ?thesis
      using thy_wf thy'_eq old_type_checked nat_names_distinct sym1 sym2 sym3 sym4
      by (auto simp: wf_theory_def nat_aty_def nat_sty_def mk_fun_def)
  qed

  have zns_hyps: "hyps zns_th = []" and zns_ceq: "concl zns_th = zns_concl"
    and si_hyps: "hyps si_th = []" and si_ceq: "concl si_th = si_concl"
    and ind_hyps: "hyps ind_th = []" and ind_ceq: "concl ind_th = ind_concl"
    using new_nat_type_extract[OF run] by simp_all

  have thy'_ty: "tyops thy' nat_ty_name = Some 0" using thy'_eq by simp
  have thy'_zero: "const_tab thy' nat_zero_name = Some nat_aty"
    using thy'_eq nat_names_distinct(5) by simp
  have thy'_succ: "const_tab thy' nat_succ_name = Some nat_sty" using thy'_eq by simp
  have nat_aty_check: "check_type thy' nat_aty" using thy'_ty by (simp add: nat_aty_def)
  have nat_sty_check: "check_type thy' nat_sty"
    using nat_aty_check thy'_wf by (simp add: nat_sty_def mk_fun_def wf_theory_def)
  have nat_pty_check: "check_type thy' nat_pty"
    using nat_aty_check thy'_wf by (simp add: nat_pty_def mk_fun_def wf_theory_def)
  have zero_c_check: "check_term thy' nat_zero_c" "type_of nat_zero_c = Some nat_aty"
    using thy'_zero nat_aty_check nat_aty_self_match
    by (simp_all add: nat_zero_c_def check_term_def)
  have succ_c_check: "check_term thy' nat_succ_c" "type_of nat_succ_c = Some nat_sty"
    using thy'_succ nat_sty_check nat_sty_self_match
    by (simp_all add: nat_succ_c_def check_term_def)
  have succ_app_check: "check_term thy' (Comb nat_succ_c (FVar v nat_aty))" for v
    using succ_c_check nat_aty_check
    by (simp add: check_term_def nat_succ_c_def nat_sty_def mk_fun_def)
  have succ_app_type: "type_of (Comb nat_succ_c (FVar v nat_aty)) = Some nat_aty" for v
    using succ_c_check by (simp add: nat_succ_c_def nat_sty_def mk_fun_def)
  have fvar_check: "check_term thy' (FVar v nat_aty)" for v
    using nat_aty_check by (simp add: check_term_def)
  have fvar_type: "type_of (FVar v nat_aty) = Some nat_aty" for v by simp

  show goal1: "models_theory (nat_ext_frame F) thy'"
    unfolding models_theory_def
    using ext_wf new_const_ok axiom_preserved def_preserved
    by (simp add: axiom_thy'_eq def_thy'_eq)

  show "valid_sequent (nat_ext_frame F) thy' (hyps zns_th) (concl zns_th)"
    unfolding zns_hyps zns_ceq valid_sequent_def
  proof (intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok (nat_ext_frame F) thy' \<rho>"
      and free_ok: "free_valuation_ok (nat_ext_frame F) \<rho> \<nu>"
    show "holds (nat_ext_frame F) \<rho> \<nu> zns_concl"
    proof -
      have inner_check: "check_term thy'
          (eq_term nat_aty nat_zero_c (Comb nat_succ_c (FVar nat_n0 nat_aty)))"
        and inner_type: "type_of
          (eq_term nat_aty nat_zero_c (Comb nat_succ_c (FVar nat_n0 nat_aty))) = Some bool_ty"
        using wf_theory_eq_term_check[OF thy'_wf nat_aty_check zero_c_check(1) zero_c_check(2)
            succ_app_check succ_app_type]
        by simp_all
      have body_check: "check_term thy' (eq_term bool_ty
          (eq_term nat_aty nat_zero_c (Comb nat_succ_c (FVar nat_n0 nat_aty))) false_term)"
        and body_type: "type_of (eq_term bool_ty
          (eq_term nat_aty nat_zero_c (Comb nat_succ_c (FVar nat_n0 nat_aty))) false_term) =
          Some bool_ty"
        using wf_theory_eq_term_check[OF thy'_wf wf_theory_bool_ty_check[OF thy'_wf]
            inner_check inner_type wf_theory_false_term_check(1)[OF thy'_wf]
            wf_theory_false_term_check(2)[OF thy'_wf]]
        by simp_all
      have left_check: "check_term thy' (target_abs nat_n0 nat_aty (eq_term bool_ty
          (eq_term nat_aty nat_zero_c (Comb nat_succ_c (FVar nat_n0 nat_aty))) false_term))"
        and left_type: "type_of (target_abs nat_n0 nat_aty (eq_term bool_ty
          (eq_term nat_aty nat_zero_c (Comb nat_succ_c (FVar nat_n0 nat_aty))) false_term)) =
          Some (mk_fun nat_aty bool_ty)"
        using target_abs_ok[OF nat_aty_check body_check body_type] by simp_all
      have right_check: "check_term thy' (Abs nat_aty true_term)"
        using wf_theory_true_term_check[OF thy'_wf]
          nat_aty_check check_open_term_weaken[of thy' "[]" true_term "[nat_aty]"]
        by (simp add: check_term_def)
      have right_type: "type_of (Abs nat_aty true_term) = Some (mk_fun nat_aty bool_ty)"
        using wf_theory_true_term_check[OF thy'_wf] by simp
      have outer: "holds (nat_ext_frame F) \<rho> \<nu> zns_concl \<longleftrightarrow>
          (\<forall>z. Elem z Nat \<longrightarrow>
            eval_term (nat_ext_frame F) \<rho> (\<nu>((nat_n0, nat_aty) := z)) [] (eq_term bool_ty
              (eq_term nat_aty nat_zero_c (Comb nat_succ_c (FVar nat_n0 nat_aty))) false_term) =
            ztrue)"
        unfolding zns_concl_def
        using holds_target_forall_iff_general[OF thy'_wf ext_wf type_ok const_ok free_ok
            body_check left_check left_type right_check right_type]
        by simp
      have eval_body: "eval_term (nat_ext_frame F) \<rho> (\<nu>((nat_n0, nat_aty) := z)) [] (eq_term bool_ty
            (eq_term nat_aty nat_zero_c (Comb nat_succ_c (FVar nat_n0 nat_aty))) false_term) =
          ztrue"
        if z_in: "Elem z Nat" for z
      proof -
        let ?\<nu>' = "\<nu>((nat_n0, nat_aty) := z)"
        have free_ok': "free_valuation_ok (nat_ext_frame F) \<rho> ?\<nu>'"
          using free_valuation_update[OF free_ok] z_in by simp
        have succ_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>' [] (Comb nat_succ_c (FVar nat_n0 nat_aty)) =
            SucNat z"
          by (simp add: nat_succ_c_def const_sem_succ_ext Lambda_app z_in)
        have zero_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>' [] nat_zero_c = Empty"
          by (simp add: nat_zero_c_def const_sem_zero_ext)
        show ?thesis
          using eval_eq_term[OF thy'_wf ext_wf type_ok free_ok' const_ok
              inner_check inner_type wf_theory_false_term_check(1)[OF thy'_wf]
              wf_theory_false_term_check(2)[OF thy'_wf]]
            eval_eq_term[OF thy'_wf ext_wf type_ok free_ok' const_ok
              zero_c_check(1) zero_c_check(2) succ_app_check succ_app_type]
            zero_eval succ_eval HOLZF_zero_not_succ
          by simp
      qed
      show ?thesis using outer eval_body by simp
    qed
  qed

  show "valid_sequent (nat_ext_frame F) thy' (hyps si_th) (concl si_th)"
    unfolding si_hyps si_ceq valid_sequent_def
  proof (intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok (nat_ext_frame F) thy' \<rho>"
      and free_ok: "free_valuation_ok (nat_ext_frame F) \<rho> \<nu>"
    show "holds (nat_ext_frame F) \<rho> \<nu> si_concl"
    proof -
      have lhs_check: "check_term thy' (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
          (Comb nat_succ_c (FVar nat_n0 nat_aty)))"
        and lhs_type: "type_of (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
          (Comb nat_succ_c (FVar nat_n0 nat_aty))) = Some bool_ty"
        using wf_theory_eq_term_check[OF thy'_wf nat_aty_check
            succ_app_check succ_app_type succ_app_check succ_app_type]
        by simp_all
      have rhs_check: "check_term thy' (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))"
        and rhs_type: "type_of (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)) =
          Some bool_ty"
        using wf_theory_eq_term_check[OF thy'_wf nat_aty_check fvar_check fvar_type
            fvar_check fvar_type]
        by simp_all
      have imp_check: "check_term thy' (target_imp
          (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
            (Comb nat_succ_c (FVar nat_n0 nat_aty)))
          (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)))"
        and imp_type: "type_of (target_imp
          (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
            (Comb nat_succ_c (FVar nat_n0 nat_aty)))
          (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))) = Some bool_ty"
        using wf_theory_target_imp_check[OF thy'_wf lhs_check lhs_type rhs_check rhs_type]
        by simp_all
      have inner_forall_check: "check_term thy' (target_forall nat_n0 nat_aty (target_imp
          (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
            (Comb nat_succ_c (FVar nat_n0 nat_aty)))
          (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))))"
        and inner_forall_type: "type_of (target_forall nat_n0 nat_aty (target_imp
          (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
            (Comb nat_succ_c (FVar nat_n0 nat_aty)))
          (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)))) = Some bool_ty"
        using wf_theory_target_forall_check[OF thy'_wf nat_aty_check imp_check imp_type]
        by simp_all
      have m_left_check: "check_term thy' (target_abs nat_m0 nat_aty (target_forall nat_n0 nat_aty
          (target_imp (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
              (Comb nat_succ_c (FVar nat_n0 nat_aty)))
            (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)))))"
        and m_left_type: "type_of (target_abs nat_m0 nat_aty (target_forall nat_n0 nat_aty
          (target_imp (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
              (Comb nat_succ_c (FVar nat_n0 nat_aty)))
            (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))))) =
          Some (mk_fun nat_aty bool_ty)"
        using target_abs_ok[OF nat_aty_check inner_forall_check inner_forall_type] by simp_all
      have m_right_check: "check_term thy' (Abs nat_aty true_term)"
        using wf_theory_true_term_check[OF thy'_wf]
          nat_aty_check check_open_term_weaken[of thy' "[]" true_term "[nat_aty]"]
        by (simp add: check_term_def)
      have m_right_type: "type_of (Abs nat_aty true_term) = Some (mk_fun nat_aty bool_ty)"
        using wf_theory_true_term_check[OF thy'_wf] by simp
      have outer: "holds (nat_ext_frame F) \<rho> \<nu> si_concl \<longleftrightarrow>
          (\<forall>m. Elem m Nat \<longrightarrow>
            eval_term (nat_ext_frame F) \<rho> (\<nu>((nat_m0, nat_aty) := m)) []
              (target_forall nat_n0 nat_aty (target_imp
                (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
                  (Comb nat_succ_c (FVar nat_n0 nat_aty)))
                (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)))) = ztrue)"
        unfolding si_concl_def
        using holds_target_forall_iff_general[OF thy'_wf ext_wf type_ok const_ok free_ok
            inner_forall_check m_left_check m_left_type m_right_check m_right_type]
        by simp
      have m_step: "eval_term (nat_ext_frame F) \<rho> (\<nu>((nat_m0, nat_aty) := m)) []
            (target_forall nat_n0 nat_aty (target_imp
              (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
                (Comb nat_succ_c (FVar nat_n0 nat_aty)))
              (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)))) = ztrue"
        if m_in: "Elem m Nat" for m
      proof -
        let ?\<nu>m = "\<nu>((nat_m0, nat_aty) := m)"
        have free_ok_m: "free_valuation_ok (nat_ext_frame F) \<rho> ?\<nu>m"
          using free_valuation_update[OF free_ok] m_in by simp
        have n_left_check: "check_term thy' (target_abs nat_n0 nat_aty (target_imp
            (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
              (Comb nat_succ_c (FVar nat_n0 nat_aty)))
            (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))))"
          and n_left_type: "type_of (target_abs nat_n0 nat_aty (target_imp
            (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
              (Comb nat_succ_c (FVar nat_n0 nat_aty)))
            (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)))) =
            Some (mk_fun nat_aty bool_ty)"
          using target_abs_ok[OF nat_aty_check imp_check imp_type] by simp_all
        have n_right_check: "check_term thy' (Abs nat_aty true_term)"
          using wf_theory_true_term_check[OF thy'_wf]
            nat_aty_check check_open_term_weaken[of thy' "[]" true_term "[nat_aty]"]
          by (simp add: check_term_def)
        have n_right_type: "type_of (Abs nat_aty true_term) = Some (mk_fun nat_aty bool_ty)"
          using wf_theory_true_term_check[OF thy'_wf] by simp
        have inner: "holds (nat_ext_frame F) \<rho> ?\<nu>m (target_forall nat_n0 nat_aty (target_imp
              (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
                (Comb nat_succ_c (FVar nat_n0 nat_aty)))
              (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)))) \<longleftrightarrow>
            (\<forall>n. Elem n Nat \<longrightarrow>
              eval_term (nat_ext_frame F) \<rho> (?\<nu>m((nat_n0, nat_aty) := n)) [] (target_imp
                (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
                  (Comb nat_succ_c (FVar nat_n0 nat_aty)))
                (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))) = ztrue)"
          unfolding holds_def
          using holds_target_forall_iff_general[OF thy'_wf ext_wf type_ok const_ok free_ok_m
              imp_check n_left_check n_left_type n_right_check n_right_type]
          by (simp add: holds_def)
        have n_step: "eval_term (nat_ext_frame F) \<rho> (?\<nu>m((nat_n0, nat_aty) := n)) [] (target_imp
              (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
                (Comb nat_succ_c (FVar nat_n0 nat_aty)))
              (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))) = ztrue"
          if n_in: "Elem n Nat" for n
        proof -
          let ?\<nu>mn = "?\<nu>m((nat_n0, nat_aty) := n)"
          have free_ok_mn: "free_valuation_ok (nat_ext_frame F) \<rho> ?\<nu>mn"
            using free_valuation_update[OF free_ok_m] n_in by simp
          have mval: "?\<nu>mn (nat_m0, nat_aty) = m" by simp
          have succ_m_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>mn [] (Comb nat_succ_c
              (FVar nat_m0 nat_aty)) = SucNat m"
            using mval by (simp add: nat_succ_c_def const_sem_succ_ext Lambda_app m_in)
          have succ_n_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>mn [] (Comb nat_succ_c
              (FVar nat_n0 nat_aty)) = SucNat n"
            by (simp add: nat_succ_c_def const_sem_succ_ext Lambda_app n_in)
          have m_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>mn [] (FVar nat_m0 nat_aty) = m"
            using mval by simp
          have n_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>mn [] (FVar nat_n0 nat_aty) = n" by simp
          have lhs_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>mn [] (eq_term nat_aty
              (Comb nat_succ_c (FVar nat_m0 nat_aty)) (Comb nat_succ_c (FVar nat_n0 nat_aty))) =
              (if SucNat m = SucNat n then ztrue else zfalse)"
            using eval_eq_term[OF thy'_wf ext_wf type_ok free_ok_mn const_ok
                succ_app_check succ_app_type succ_app_check succ_app_type]
              succ_m_eval succ_n_eval
            by simp
          have rhs_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>mn [] (eq_term nat_aty
              (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)) = (if m = n then ztrue else zfalse)"
            using eval_eq_term[OF thy'_wf ext_wf type_ok free_ok_mn const_ok
                fvar_check fvar_type fvar_check fvar_type]
              m_eval n_eval
            by simp
          have p_fresh: "\<not> vfree_in conj_fn conj_fty (eq_term nat_aty
              (Comb nat_succ_c (FVar nat_m0 nat_aty)) (Comb nat_succ_c (FVar nat_n0 nat_aty)))"
            by (simp add: eq_term_def eq_const_def nat_succ_c_def)
          have q_fresh: "\<not> vfree_in conj_fn conj_fty (eq_term nat_aty
              (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))"
            by (simp add: eq_term_def eq_const_def)
          have imp_iff: "holds (nat_ext_frame F) \<rho> ?\<nu>mn (target_imp
                (eq_term nat_aty (Comb nat_succ_c (FVar nat_m0 nat_aty))
                  (Comb nat_succ_c (FVar nat_n0 nat_aty)))
                (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty))) \<longleftrightarrow>
              (holds (nat_ext_frame F) \<rho> ?\<nu>mn (eq_term nat_aty
                  (Comb nat_succ_c (FVar nat_m0 nat_aty)) (Comb nat_succ_c (FVar nat_n0 nat_aty))) \<longrightarrow>
               holds (nat_ext_frame F) \<rho> ?\<nu>mn
                 (eq_term nat_aty (FVar nat_m0 nat_aty) (FVar nat_n0 nat_aty)))"
            using wf_theory_target_imp_holds[OF thy'_wf ext_wf type_ok const_ok free_ok_mn
                lhs_check lhs_type rhs_check rhs_type p_fresh q_fresh] .
          show ?thesis
            using imp_iff lhs_eval rhs_eval HOLZF_succ_inj[OF m_in n_in] ztrue_neq_zfalse
            by (simp add: holds_def)
        qed
        show ?thesis using inner n_step by (simp add: holds_def)
      qed
      show ?thesis using outer m_step by (simp add: holds_def)
    qed
  qed

  show "valid_sequent (nat_ext_frame F) thy' (hyps ind_th) (concl ind_th)"
    unfolding ind_hyps ind_ceq valid_sequent_def
  proof (intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok (nat_ext_frame F) thy' \<rho>"
      and free_ok: "free_valuation_ok (nat_ext_frame F) \<rho> \<nu>"
    show "holds (nat_ext_frame F) \<rho> \<nu> ind_concl"
    proof -
      let ?Pz = "Comb (FVar nat_p0 nat_pty) nat_zero_c"
      let ?Pn = "Comb (FVar nat_p0 nat_pty) (FVar nat_n0 nat_aty)"
      let ?Psn = "Comb (FVar nat_p0 nat_pty) (Comb nat_succ_c (FVar nat_n0 nat_aty))"
      let ?stepimp = "target_imp ?Pn ?Psn"
      let ?stepforall = "target_forall nat_n0 nat_aty ?stepimp"
      let ?hypconj = "target_conj ?Pz ?stepforall"
      let ?cforall = "target_forall nat_n0 nat_aty ?Pn"
      let ?indbody = "target_imp ?hypconj ?cforall"
      have pz_check: "check_term thy' ?Pz" and pz_type: "type_of ?Pz = Some bool_ty"
        using nat_pty_check zero_c_check by (simp_all add: check_term_def nat_pty_def mk_fun_def)
      have pn_check: "check_term thy' ?Pn" and pn_type: "type_of ?Pn = Some bool_ty"
        using nat_pty_check fvar_check fvar_type
        by (simp_all add: check_term_def nat_pty_def mk_fun_def)
      have psn_check: "check_term thy' ?Psn" and psn_type: "type_of ?Psn = Some bool_ty"
        using nat_pty_check succ_app_check succ_app_type
        by (simp_all add: check_term_def nat_pty_def mk_fun_def)
      have step_imp_check: "check_term thy' ?stepimp" and step_imp_type: "type_of ?stepimp = Some bool_ty"
        using wf_theory_target_imp_check[OF thy'_wf pn_check pn_type psn_check psn_type]
        by simp_all
      have step_forall_check: "check_term thy' ?stepforall"
        and step_forall_type: "type_of ?stepforall = Some bool_ty"
        using wf_theory_target_forall_check[OF thy'_wf nat_aty_check step_imp_check step_imp_type]
        by simp_all
      have hyp_conj_check: "check_term thy' ?hypconj" and hyp_conj_type: "type_of ?hypconj = Some bool_ty"
        using wf_theory_target_conj_check[OF thy'_wf pz_check pz_type
            step_forall_check step_forall_type]
        by simp_all
      have concl_forall_check: "check_term thy' ?cforall"
        and concl_forall_type: "type_of ?cforall = Some bool_ty"
        using wf_theory_target_forall_check[OF thy'_wf nat_aty_check pn_check pn_type]
        by simp_all
      have ind_body_check: "check_term thy' ?indbody"
        and ind_body_type: "type_of ?indbody = Some bool_ty"
        using wf_theory_target_imp_check[OF thy'_wf hyp_conj_check hyp_conj_type
            concl_forall_check concl_forall_type]
        by simp_all
      have ind_left_check: "check_term thy' (target_abs nat_p0 nat_pty ?indbody)"
        and ind_left_type: "type_of (target_abs nat_p0 nat_pty ?indbody) = Some (mk_fun nat_pty bool_ty)"
        using target_abs_ok[OF nat_pty_check ind_body_check ind_body_type] by simp_all
      have ind_right_check: "check_term thy' (Abs nat_pty true_term)"
        using wf_theory_true_term_check[OF thy'_wf]
          nat_pty_check check_open_term_weaken[of thy' "[]" true_term "[nat_pty]"]
        by (simp add: check_term_def)
      have ind_right_type: "type_of (Abs nat_pty true_term) = Some (mk_fun nat_pty bool_ty)"
        using wf_theory_true_term_check[OF thy'_wf] by simp
      have outer: "holds (nat_ext_frame F) \<rho> \<nu> ind_concl \<longleftrightarrow>
          (\<forall>p. Elem p (Fun Nat zbool) \<longrightarrow>
            eval_term (nat_ext_frame F) \<rho> (\<nu>((nat_p0, nat_pty) := p)) [] ?indbody = ztrue)"
        unfolding ind_concl_def
        using holds_target_forall_iff_general[OF thy'_wf ext_wf type_ok const_ok free_ok
            ind_body_check ind_left_check ind_left_type ind_right_check ind_right_type]
        by (simp add: nat_pty_def)
      have p_step: "eval_term (nat_ext_frame F) \<rho> (\<nu>((nat_p0, nat_pty) := p)) [] ?indbody = ztrue"
        if p_in: "Elem p (Fun Nat zbool)" for p
      proof -
        let ?\<nu>p = "\<nu>((nat_p0, nat_pty) := p)"
        have free_ok_p: "free_valuation_ok (nat_ext_frame F) \<rho> ?\<nu>p"
          using free_valuation_update[OF free_ok] p_in by (simp add: nat_pty_def)
        have hyp_fresh: "\<not> vfree_in conj_fn conj_fty ?hypconj" by simp
        have cforall_fresh: "\<not> vfree_in conj_fn conj_fty ?cforall" by simp
        have imp_iff: "holds (nat_ext_frame F) \<rho> ?\<nu>p ?indbody \<longleftrightarrow>
            (holds (nat_ext_frame F) \<rho> ?\<nu>p ?hypconj \<longrightarrow> holds (nat_ext_frame F) \<rho> ?\<nu>p ?cforall)"
          using wf_theory_target_imp_holds[OF thy'_wf ext_wf type_ok const_ok free_ok_p
              hyp_conj_check hyp_conj_type concl_forall_check concl_forall_type
              hyp_fresh cforall_fresh] .
        have main: "holds (nat_ext_frame F) \<rho> ?\<nu>p ?hypconj \<longrightarrow> holds (nat_ext_frame F) \<rho> ?\<nu>p ?cforall"
        proof
          assume hyp_holds: "holds (nat_ext_frame F) \<rho> ?\<nu>p ?hypconj"
          have pz_fresh: "\<not> vfree_in conj_fn conj_fty ?Pz" by (simp add: nat_zero_c_def)
          have stepforall_fresh: "\<not> vfree_in conj_fn conj_fty ?stepforall" by simp
          have conj_iff: "holds (nat_ext_frame F) \<rho> ?\<nu>p ?hypconj \<longleftrightarrow>
              (holds (nat_ext_frame F) \<rho> ?\<nu>p ?Pz \<and> holds (nat_ext_frame F) \<rho> ?\<nu>p ?stepforall)"
            using wf_theory_target_conj_holds[OF thy'_wf ext_wf type_ok const_ok free_ok_p
                pz_check pz_type step_forall_check step_forall_type pz_fresh stepforall_fresh] .
          have pz_holds: "holds (nat_ext_frame F) \<rho> ?\<nu>p ?Pz"
            and stepforall_holds: "holds (nat_ext_frame F) \<rho> ?\<nu>p ?stepforall"
            using hyp_holds conj_iff by simp_all
          have pval0: "?\<nu>p (nat_p0, nat_pty) = p" by simp
          have pz_eval: "app p (eval_term (nat_ext_frame F) \<rho> ?\<nu>p [] nat_zero_c) = ztrue"
            using pz_holds pval0 by (simp add: holds_def)
          have zero_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>p [] nat_zero_c = Empty"
            by (simp add: nat_zero_c_def const_sem_zero_ext)
          have p_at_zero: "app p Empty = ztrue" using pz_eval zero_eval by simp
          have step_prop: "Elem n Nat \<Longrightarrow> app p n = ztrue \<Longrightarrow> app p (SucNat n) = ztrue" for n
          proof -
            assume n_in: "Elem n Nat" and pn_true: "app p n = ztrue"
            let ?\<nu>pn = "?\<nu>p((nat_n0, nat_aty) := n)"
            have free_ok_pn: "free_valuation_ok (nat_ext_frame F) \<rho> ?\<nu>pn"
              using free_valuation_update[OF free_ok_p] n_in by simp
            have n_left_check: "check_term thy' (target_abs nat_n0 nat_aty ?stepimp)"
              and n_left_type: "type_of (target_abs nat_n0 nat_aty ?stepimp) =
                Some (mk_fun nat_aty bool_ty)"
              using target_abs_ok[OF nat_aty_check step_imp_check step_imp_type] by simp_all
            have n_right_check: "check_term thy' (Abs nat_aty true_term)"
              using wf_theory_true_term_check[OF thy'_wf]
                nat_aty_check check_open_term_weaken[of thy' "[]" true_term "[nat_aty]"]
              by (simp add: check_term_def)
            have n_right_type: "type_of (Abs nat_aty true_term) = Some (mk_fun nat_aty bool_ty)"
              using wf_theory_true_term_check[OF thy'_wf] by simp
            have step_iff: "holds (nat_ext_frame F) \<rho> ?\<nu>p ?stepforall \<longleftrightarrow>
                (\<forall>n'. Elem n' Nat \<longrightarrow>
                  eval_term (nat_ext_frame F) \<rho> (?\<nu>p((nat_n0, nat_aty) := n')) [] ?stepimp = ztrue)"
              unfolding holds_def
              using holds_target_forall_iff_general[OF thy'_wf ext_wf type_ok const_ok free_ok_p
                  step_imp_check n_left_check n_left_type n_right_check n_right_type]
              by (simp add: holds_def)
            have n_holds: "eval_term (nat_ext_frame F) \<rho> ?\<nu>pn [] ?stepimp = ztrue"
              using stepforall_holds step_iff n_in by blast
            have nval: "?\<nu>pn (nat_n0, nat_aty) = n" by simp
            have pval: "?\<nu>pn (nat_p0, nat_pty) = p" using nat_vars_distinct(3) by simp
            have pn_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>pn [] ?Pn = app p n"
              using nval pval by simp
            have psn_eval: "eval_term (nat_ext_frame F) \<rho> ?\<nu>pn [] ?Psn = app p (SucNat n)"
              using nval pval by (simp add: nat_succ_c_def const_sem_succ_ext Lambda_app n_in)
            have p_fresh': "\<not> vfree_in conj_fn conj_fty ?Pn" by simp
            have q_fresh': "\<not> vfree_in conj_fn conj_fty ?Psn" by (simp add: nat_succ_c_def)
            have step_imp_iff: "holds (nat_ext_frame F) \<rho> ?\<nu>pn ?stepimp \<longleftrightarrow>
                (holds (nat_ext_frame F) \<rho> ?\<nu>pn ?Pn \<longrightarrow> holds (nat_ext_frame F) \<rho> ?\<nu>pn ?Psn)"
              using wf_theory_target_imp_holds[OF thy'_wf ext_wf type_ok const_ok free_ok_pn
                  pn_check pn_type psn_check psn_type p_fresh' q_fresh'] .
            show "app p (SucNat n) = ztrue"
              using n_holds step_imp_iff pn_eval psn_eval pn_true
              by (simp add: holds_def)
          qed
          have p_forall: "\<forall>n. Elem n Nat \<longrightarrow> app p n = ztrue"
          proof (intro allI impI)
            fix n assume n_in: "Elem n Nat"
            show "app p n = ztrue"
              using HOLZF_nat_induct[of "\<lambda>x. app p x = ztrue" n] p_at_zero step_prop n_in
              by blast
          qed
          show "holds (nat_ext_frame F) \<rho> ?\<nu>p ?cforall"
          proof -
            have cleft_check: "check_term thy' (target_abs nat_n0 nat_aty ?Pn)"
              and cleft_type: "type_of (target_abs nat_n0 nat_aty ?Pn) = Some (mk_fun nat_aty bool_ty)"
              using target_abs_ok[OF nat_aty_check pn_check pn_type] by simp_all
            have cright_check: "check_term thy' (Abs nat_aty true_term)"
              using wf_theory_true_term_check[OF thy'_wf]
                nat_aty_check check_open_term_weaken[of thy' "[]" true_term "[nat_aty]"]
              by (simp add: check_term_def)
            have cright_type: "type_of (Abs nat_aty true_term) = Some (mk_fun nat_aty bool_ty)"
              using wf_theory_true_term_check[OF thy'_wf] by simp
            have cforall_iff: "holds (nat_ext_frame F) \<rho> ?\<nu>p ?cforall \<longleftrightarrow>
                (\<forall>n. Elem n Nat \<longrightarrow>
                  eval_term (nat_ext_frame F) \<rho> (?\<nu>p((nat_n0, nat_aty) := n)) [] ?Pn = ztrue)"
              unfolding holds_def
              using holds_target_forall_iff_general[OF thy'_wf ext_wf type_ok const_ok free_ok_p
                  pn_check cleft_check cleft_type cright_check cright_type]
              by (simp add: holds_def)
            have pn_pointwise: "eval_term (nat_ext_frame F) \<rho> (?\<nu>p((nat_n0, nat_aty) := n)) [] ?Pn =
                app p n"
              if n_in: "Elem n Nat" for n
            proof -
              have nval: "(?\<nu>p((nat_n0, nat_aty) := n)) (nat_n0, nat_aty) = n" by simp
              have pval: "(?\<nu>p((nat_n0, nat_aty) := n)) (nat_p0, nat_pty) = p"
                using nat_vars_distinct(3) by simp
              show ?thesis using nval pval by simp
            qed
            show ?thesis
              using cforall_iff p_forall pn_pointwise by simp
          qed
        qed
        show ?thesis using imp_iff main by (simp add: holds_def)
      qed
      show ?thesis using outer p_step by simp
    qed
  qed
qed

end
