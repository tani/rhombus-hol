theory Rhombus_HOL_Base_Model
  imports Rhombus_HOL_Extensions
begin

section \<open>Closed target booleans\<close>

definition eq_bool_ty :: htype where
  "eq_bool_ty = mk_fun bool_ty (mk_fun bool_ty bool_ty)"

definition true_term :: hterm where
  "true_term = eq_term eq_bool_ty (eq_const bool_ty) (eq_const bool_ty)"

definition constant_true_function :: hterm where
  "constant_true_function = Abs bool_ty (Abs bool_ty true_term)"

definition false_term :: hterm where
  "false_term = eq_term eq_bool_ty (eq_const bool_ty) constant_true_function"

text \<open>Church-style connectives are definitions in the target syntax, not new
trusted constants. Bound indices follow the nearest-binder convention.\<close>

definition church_true :: hterm where
  "church_true = Abs bool_ty (Abs bool_ty (BVar 1 bool_ty))"

definition church_false :: hterm where
  "church_false = Abs bool_ty (Abs bool_ty (BVar 0 bool_ty))"

definition church_not :: hterm where
  "church_not = Abs (mk_fun bool_ty (mk_fun bool_ty bool_ty))
    (Abs bool_ty (Abs bool_ty
      (Comb (Comb (BVar 2 (mk_fun bool_ty (mk_fun bool_ty bool_ty)))
        (BVar 0 bool_ty)) (BVar 1 bool_ty))))"

section \<open>Runtime base theory terms\<close>

definition select_name :: hname where
  "select_name = NUser 0 ''select''"

definition target_abs :: "hname \<Rightarrow> htype \<Rightarrow> hterm \<Rightarrow> hterm" where
  "target_abs n ty body = Abs ty (abstract_fvar n ty body)"

definition target_forall :: "hname \<Rightarrow> htype \<Rightarrow> hterm \<Rightarrow> hterm" where
  "target_forall n ty body =
    eq_term (mk_fun ty bool_ty) (target_abs n ty body)
      (Abs ty true_term)"

definition conj_fty :: htype where
  "conj_fty = mk_fun bool_ty (mk_fun bool_ty bool_ty)"

definition conj_fn :: hname where "conj_fn = NUser 1 ''conj_f''"

definition conj_lhs :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "conj_lhs p q = target_abs conj_fn conj_fty
    (Comb (Comb (FVar conj_fn conj_fty) p) q)"

definition conj_rhs :: hterm where
  "conj_rhs = target_abs conj_fn conj_fty
    (Comb (Comb (FVar conj_fn conj_fty) true_term) true_term)"

definition target_conj :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "target_conj p q = eq_term (mk_fun conj_fty bool_ty)
    (conj_lhs p q) conj_rhs"

definition target_imp :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "target_imp p q = eq_term bool_ty (target_conj p q) p"

definition disj_rn :: hname where "disj_rn = NUser 2 ''disj_r''"
definition disj_r :: hterm where "disj_r = FVar disj_rn bool_ty"
definition disj_left :: "hterm \<Rightarrow> hterm" where
  "disj_left p = target_imp p disj_r"
definition disj_right :: "hterm \<Rightarrow> hterm" where
  "disj_right q = target_imp (target_imp q disj_r) disj_r"
definition disj_body :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "disj_body p q = target_imp (disj_left p) (disj_right q)"
definition target_disj :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "target_disj p q = target_forall disj_rn bool_ty (disj_body p q)"

definition eta_aty :: htype where "eta_aty = TyVar NAlpha"
definition eta_bty :: htype where "eta_bty = TyVar (NUser 3 ''beta'')"
definition eta_fty :: htype where "eta_fty = mk_fun eta_aty eta_bty"
definition eta_fn :: hname where "eta_fn = NUser 4 ''eta_f''"
definition eta_xn :: hname where "eta_xn = NUser 5 ''eta_x''"
definition eta_body :: hterm where
  "eta_body = eq_term eta_fty
    (target_abs eta_xn eta_aty
      (Comb (FVar eta_fn eta_fty) (FVar eta_xn eta_aty)))
    (FVar eta_fn eta_fty)"

definition eta_axiom_term :: hterm where
  "eta_axiom_term = target_forall eta_fn eta_fty eta_body"

definition select_aty :: htype where "select_aty = TyVar NAlpha"
definition select_pty :: htype where "select_pty = mk_fun select_aty bool_ty"
definition select_pn :: hname where "select_pn = NUser 6 ''select_P''"
definition select_xn :: hname where "select_xn = NUser 7 ''select_x''"
definition select_p :: hterm where "select_p = FVar select_pn select_pty"
definition select_x :: hterm where "select_x = FVar select_xn select_aty"
definition select_value :: hterm where
  "select_value = Comb (Const select_name (mk_fun select_pty select_aty)) select_p"
definition select_antecedent :: hterm where
  "select_antecedent = Comb select_p select_x"
definition select_consequent :: hterm where
  "select_consequent = Comb select_p select_value"
definition select_body :: hterm where
  "select_body = target_imp select_antecedent select_consequent"
definition select_inner :: hterm where
  "select_inner = target_forall select_xn select_aty select_body"

definition select_axiom_term :: hterm where
  "select_axiom_term = target_forall select_pn select_pty select_inner"

definition bool_cases_tn :: hname where "bool_cases_tn = NUser 8 ''bool_t''"
definition bool_cases_t :: hterm where
  "bool_cases_t = FVar bool_cases_tn bool_ty"
definition bool_cases_true :: hterm where
  "bool_cases_true = eq_term bool_ty bool_cases_t true_term"
definition bool_cases_false :: hterm where
  "bool_cases_false = eq_term bool_ty bool_cases_t false_term"
definition bool_cases_body :: hterm where
  "bool_cases_body = target_disj bool_cases_true bool_cases_false"
definition bool_cases_axiom_term :: hterm where
  "bool_cases_axiom_term =
    target_forall bool_cases_tn bool_ty bool_cases_body"

definition base_stamp :: stamp where
  "base_stamp = next_stamp 1 (thy_stamp (initial_theory 0))"

definition base_axiom_thms :: "hthm list" where
  "base_axiom_thms =
    [\<lparr>hyps = [], concl = eta_axiom_term, thm_stamp = base_stamp\<rparr>,
     \<lparr>hyps = [], concl = select_axiom_term, thm_stamp = base_stamp\<rparr>,
     \<lparr>hyps = [], concl = bool_cases_axiom_term, thm_stamp = base_stamp\<rparr>]"

definition base_theory :: htheory where
  "base_theory =
    \<lparr>tyops = tyops (initial_theory 0),
     const_tab = (const_tab (initial_theory 0))
       (select_name := Some (mk_fun (mk_fun (TyVar NAlpha) bool_ty)
         (TyVar NAlpha))),
     axiom_list = base_axiom_thms, def_tab = def_tab (initial_theory 0),
     thy_stamp = base_stamp\<rparr>"

lemma select_name_not_eq [simp]: "select_name \<noteq> NEq"
  by (simp add: select_name_def)

lemma eq_not_select_name [simp]: "NEq \<noteq> select_name"
  by (simp add: select_name_def)

lemma base_theory_wf [simp]: "wf_theory base_theory"
  by (simp add: wf_theory_def base_theory_def base_stamp_def
      initial_theory_def select_name_def mk_fun_def bool_ty_def)

lemma eta_axiom_term_wf [simp]: "check_prop base_theory eta_axiom_term"
  by eval

lemma select_axiom_term_wf [simp]: "check_prop base_theory select_axiom_term"
  by eval

lemma bool_cases_axiom_term_wf [simp]:
  "check_prop base_theory bool_cases_axiom_term"
  by eval

lemma base_stamp_descends [simp]:
  "descends base_stamp (thy_stamp base_theory)"
  by (simp add: base_theory_def base_stamp_def initial_theory_def
      fresh_stamp_def next_stamp_def descends_def)

lemma base_theory_contents_wf [simp]: "theory_contents_wf base_theory"
proof (unfold theory_contents_wf_def, intro conjI)
  have axiom_list_eq: "axiom_list base_theory = base_axiom_thms"
    by (simp add: base_theory_def)
  show "list_all (wf_thm base_theory) (axiom_list base_theory)"
    by (simp add: axiom_list_eq base_axiom_thms_def wf_thm_def)
  show "\<forall>n th. def_tab base_theory n = Some th \<longrightarrow> wf_thm base_theory th"
    by (simp add: base_theory_def initial_theory_def)
qed
section \<open>Standard HOLZF frame\<close>

definition semantic_select :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "semantic_select A P =
    (if (\<exists>x. Elem x A \<and> app P x = ztrue)
     then (SOME x. Elem x A \<and> app P x = ztrue)
     else chosen_member A)"

definition standard_frame :: frame where
  "standard_frame = \<lparr>tyop_denote = (\<lambda>_ _. zbool),
    const_scheme = (\<lambda>n. if n = NEq then
      Some (mk_fun (TyVar NAlpha) (mk_fun (TyVar NAlpha) bool_ty))
      else if n = select_name then
        Some (mk_fun (mk_fun (TyVar NAlpha) bool_ty) (TyVar NAlpha))
      else None),
    const_denote = (\<lambda>n \<rho>. if n = NEq then zeq (\<rho> NAlpha)
      else if n = select_name then
        Lambda (Fun (\<rho> NAlpha) zbool) (semantic_select (\<rho> NAlpha))
      else Empty)\<rparr>"

definition ETA_AX :: bool where
  "ETA_AX \<longleftrightarrow> (\<forall>A B f. Elem f (Fun A B) \<longrightarrow> Lambda A (app f) = f)"

definition SELECT_AX :: bool where
  "SELECT_AX \<longleftrightarrow> (\<forall>A P x. Elem x A \<longrightarrow> app P x = ztrue \<longrightarrow>
    app P (semantic_select A P) = ztrue)"

definition BOOL_CASES_AX :: bool where
  "BOOL_CASES_AX \<longleftrightarrow> (\<forall>b. Elem b zbool \<longrightarrow> b = ztrue \<or> b = zfalse)"

definition INFINITY_AX :: bool where
  "INFINITY_AX \<longleftrightarrow> Elem Empty Nat \<and> (\<forall>x. Elem x Nat \<longrightarrow> Elem (SucNat x) Nat)"

lemma eta_axiom_valid: ETA_AX
proof (unfold ETA_AX_def, intro allI impI)
  fix A B f
  assume member: "Elem f (Fun A B)"
  then obtain g where f: "f = Lambda A g" using Elem_Fun_Lambda by blast
  show "Lambda A (app f) = f"
    unfolding f by (simp add: Lambda_ext Lambda_app)
qed

lemma select_axiom_valid: SELECT_AX
proof (unfold SELECT_AX_def, intro allI impI)
  fix A P x
  assume x_in: "Elem x A" and px: "app P x = ztrue"
  have witness: "\<exists>y. Elem y A \<and> app P y = ztrue" using x_in px by blast
  have chosen: "Elem (SOME y. Elem y A \<and> app P y = ztrue) A \<and>
      app P (SOME y. Elem y A \<and> app P y = ztrue) = ztrue"
    by (rule someI_ex[OF witness])
  show "app P (semantic_select A P) = ztrue"
    using witness chosen by (simp add: semantic_select_def)
qed

lemma bool_cases_axiom_valid: BOOL_CASES_AX
  by (auto simp: BOOL_CASES_AX_def)

lemma infinity_axiom_valid: INFINITY_AX
  by (simp add: INFINITY_AX_def Elem_Empty_Nat Elem_SucNat_Nat)

theorem three_runtime_base_axioms_valid:
  "ETA_AX \<and> SELECT_AX \<and> BOOL_CASES_AX"
  using eta_axiom_valid select_axiom_valid bool_cases_axiom_valid by blast

lemma standard_frame_wf [simp]: "frame_wf standard_frame"
  by (auto simp: frame_wf_def standard_frame_def inhabited_def mk_fun_def bool_ty_def)

lemma equality_type_match_shape:
  assumes "type_match (mk_fun (TyVar NAlpha)
      (mk_fun (TyVar NAlpha) bool_ty)) ty (\<lambda>_. None) \<noteq> None"
  obtains u where "ty = mk_fun u (mk_fun u bool_ty)"
  using equality_match_shape[OF assms] that by blast

lemma standard_frame_initial_constants:
  "type_valuation_ok \<rho> \<Longrightarrow>
    const_interpretation_ok standard_frame (initial_theory fresh) \<rho>"
proof (unfold const_interpretation_ok_def, intro allI impI)
  fix n generic \<sigma>
  assume sigma_ok: "type_valuation_ok \<sigma>"
    and tab: "const_tab (initial_theory fresh) n = Some generic"
  have name: "n = NEq"
    using tab by (cases n) (simp_all add: initial_theory_def)
  have scheme: "generic = mk_fun (TyVar NAlpha)
      (mk_fun (TyVar NAlpha) bool_ty)"
    using tab name by (simp add: initial_theory_def)
  show "const_scheme standard_frame n = Some generic \<and>
      Elem (const_denote standard_frame n \<sigma>)
        (interp_type standard_frame \<sigma> generic)"
    using name scheme zeq_in_fun[of "\<sigma> NAlpha"]
    by (simp add: standard_frame_def mk_fun_def bool_ty_def)
qed
lemma standard_frame_models_initial:
  "models_theory standard_frame (initial_theory fresh)"
proof (unfold models_theory_def, intro conjI)
  show "frame_wf standard_frame" by simp
  show "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
      const_interpretation_ok standard_frame (initial_theory fresh) \<rho>"
    using standard_frame_initial_constants by blast
  show "\<forall>th\<in>set (axiom_list (initial_theory fresh)).
      valid_sequent standard_frame (initial_theory fresh) (hyps th) (concl th)"
    by (simp add: initial_theory_def)
  show "\<forall>n th. def_tab (initial_theory fresh) n = Some th \<longrightarrow>
      valid_sequent standard_frame (initial_theory fresh) (hyps th) (concl th)"
    by (simp add: initial_theory_def)
qed

lemma semantic_select_member:
  assumes "inhabited A"
  shows "Elem (semantic_select A P) A"
proof (cases "\<exists>x. Elem x A \<and> app P x = ztrue")
  case True
  have chosen: "Elem (SOME x. Elem x A \<and> app P x = ztrue) A"
    using someI_ex[OF True] by blast
  show ?thesis using True chosen by (simp add: semantic_select_def)
next
  case False
  have no_witness: "\<not> (\<exists>x. Elem x A \<and> app P x = ztrue)"
    using False by blast
  show ?thesis
    using chosen_member_in[OF assms] no_witness
    unfolding semantic_select_def by (subst if_not_P) auto
qed

lemma standard_frame_base_constants:
  assumes rho_ok: "type_valuation_ok \<rho>"
  shows "const_interpretation_ok standard_frame base_theory \<rho>"
proof (unfold const_interpretation_ok_def, intro allI impI)
  fix n generic \<sigma>
  assume sigma_ok: "type_valuation_ok \<sigma>"
    and tab: "const_tab base_theory n = Some generic"
  show "const_scheme standard_frame n = Some generic \<and>
      Elem (const_denote standard_frame n \<sigma>)
        (interp_type standard_frame \<sigma> generic)"
  proof (cases "n = select_name")
    case True
    have generic: "generic = mk_fun (mk_fun (TyVar NAlpha) bool_ty)
        (TyVar NAlpha)"
      using tab True by (simp add: base_theory_def)
    have inhabited: "inhabited (\<sigma> NAlpha)"
      using sigma_ok by (simp add: type_valuation_ok_def)
    have member: "Elem
        (Lambda (Fun (\<sigma> NAlpha) zbool) (semantic_select (\<sigma> NAlpha)))
        (Fun (Fun (\<sigma> NAlpha) zbool) (\<sigma> NAlpha))"
      using semantic_select_member[OF inhabited]
      by (simp add: Elem_Lambda_Fun)
    show ?thesis using True generic member
      by (simp add: standard_frame_def mk_fun_def bool_ty_def)
  next
    case False
    have initial_tab: "const_tab (initial_theory 0) n = Some generic"
      using tab False by (simp add: base_theory_def)
    have name: "n = NEq"
      using initial_tab by (cases n) (simp_all add: initial_theory_def)
    have generic: "generic = mk_fun (TyVar NAlpha)
        (mk_fun (TyVar NAlpha) bool_ty)"
      using initial_tab name by (simp add: initial_theory_def)
    show ?thesis using name generic zeq_in_fun[of "\<sigma> NAlpha"]
      by (simp add: standard_frame_def mk_fun_def bool_ty_def)
  qed
qed

section \<open>Evaluation of encoded base propositions\<close>

lemma eval_true_term [simp]:
  "eval_term standard_frame \<rho> \<nu> env true_term = ztrue"
  by (simp add: const_sem_def true_term_def eq_bool_ty_def eq_term_def eq_const_def
      mk_fun_def bool_ty_def zeq_apply zeq_in_fun)

lemma eval_constant_true_function [simp]:
  "eval_term standard_frame \<rho> \<nu> env constant_true_function =
    Lambda zbool (\<lambda>_. Lambda zbool (\<lambda>_. ztrue))"
  by (simp add: constant_true_function_def)

lemma equality_not_constant_true:
  "zeq zbool \<noteq> Lambda zbool (\<lambda>_. Lambda zbool (\<lambda>_. ztrue))"
proof
  assume equal: "zeq zbool = Lambda zbool (\<lambda>_. Lambda zbool (\<lambda>_. ztrue))"
  have first: "app (app (zeq zbool) zfalse) ztrue = ztrue"
    by (simp add: equal Lambda_app)
  have second: "app (app (zeq zbool) zfalse) ztrue = zfalse"
    by (simp add: zeq_apply ztrue_neq_zfalse)
  have "ztrue = zfalse" using first second by simp
  then show False using ztrue_neq_zfalse by contradiction
qed

lemma eval_false_term [simp]:
  "eval_term standard_frame \<rho> \<nu> env false_term = zfalse"
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

lemma eval_target_abs:
  assumes checked: "check_term thy body"
  shows "eval_term F \<rho> \<nu> [] (target_abs n ty body) =
    Lambda (interp_type F \<rho> ty)
      (\<lambda>z. eval_term F \<rho> (\<nu>((n, ty) := z)) [] body)"
proof -
  have pointwise: "eval_term F \<rho> \<nu> [z] (abstract_fvar n ty body) =
      eval_term F \<rho> (\<nu>((n, ty) := z)) [] body" for z
  proof -
    let ?\<nu>z = "\<nu>((n, ty) := z)"
    have invariant: "eval_term F \<rho> ?\<nu>z [z] (abstract_fvar n ty body) =
        eval_term F \<rho> \<nu> [z] (abstract_fvar n ty body)"
      using eval_not_vfree_update[OF abstract_fvar_removes_fvar,
          where F=F and \<rho>=\<rho> and \<nu>=\<nu> and z=z and env="[z]"] .
    have abstract: "eval_term F \<rho> ?\<nu>z [z] (abstract_fvar n ty body) =
        eval_term F \<rho> ?\<nu>z [] body"
      using eval_abstract_fvar[OF checked, of F \<rho> ?\<nu>z n ty] by simp
    show ?thesis using invariant abstract by simp
  qed
  show ?thesis
    unfolding target_abs_def using pointwise by (simp add: Lambda_ext)
qed

lemma holds_target_forall_iff:
  assumes type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok standard_frame base_theory \<rho>"
    and free_ok: "free_valuation_ok standard_frame \<rho> \<nu>"
    and body_check: "check_term base_theory body"
    and left_check: "check_term base_theory (target_abs n ty body)"
    and left_type: "type_of (target_abs n ty body) =
      Some (mk_fun ty bool_ty)"
    and right_check: "check_term base_theory (Abs ty true_term)"
    and right_type: "type_of (Abs ty true_term) =
      Some (mk_fun ty bool_ty)"
  shows "holds standard_frame \<rho> \<nu> (target_forall n ty body) \<longleftrightarrow>
    (\<forall>z. Elem z (interp_type standard_frame \<rho> ty) \<longrightarrow>
      eval_term standard_frame \<rho> (\<nu>((n, ty) := z)) [] body = ztrue)"
proof -
  let ?A = "interp_type standard_frame \<rho> ty"
  let ?g = "\<lambda>z. eval_term standard_frame \<rho> (\<nu>((n, ty) := z)) [] body"
  have outer: "holds standard_frame \<rho> \<nu>
      (eq_term (mk_fun ty bool_ty) (target_abs n ty body)
        (Abs ty true_term)) \<longleftrightarrow>
      eval_term standard_frame \<rho> \<nu> [] (target_abs n ty body) =
        eval_term standard_frame \<rho> \<nu> [] (Abs ty true_term)"
    using holds_eq_iff[OF base_theory_wf standard_frame_wf type_ok free_ok
        const_ok left_check left_type right_check right_type] .
  have left_eval: "eval_term standard_frame \<rho> \<nu> []
      (target_abs n ty body) = Lambda ?A ?g"
    using eval_target_abs[OF body_check] .
  have right_eval: "eval_term standard_frame \<rho> \<nu> [] (Abs ty true_term) =
      Lambda ?A (\<lambda>_. ztrue)"
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
    using outer left_eval right_eval lambda_eq
    by (simp add: target_forall_def)
qed

lemma holds_target_conj_iff:
  assumes type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok standard_frame base_theory \<rho>"
    and free_ok: "free_valuation_ok standard_frame \<rho> \<nu>"
    and p_check: "check_term base_theory p" and p_type: "type_of p = Some bool_ty"
    and q_check: "check_term base_theory q" and q_type: "type_of q = Some bool_ty"
    and p_fresh: "\<not> vfree_in conj_fn conj_fty p"
    and q_fresh: "\<not> vfree_in conj_fn conj_fty q"
    and body_check: "check_term base_theory
      (Comb (Comb (FVar conj_fn conj_fty) p) q)"
    and rhs_body_check: "check_term base_theory
      (Comb (Comb (FVar conj_fn conj_fty) true_term) true_term)"
    and lhs_check: "check_term base_theory (conj_lhs p q)"
    and lhs_type: "type_of (conj_lhs p q) = Some (mk_fun conj_fty bool_ty)"
    and rhs_check: "check_term base_theory conj_rhs"
    and rhs_type: "type_of conj_rhs = Some (mk_fun conj_fty bool_ty)"
  shows "holds standard_frame \<rho> \<nu> (target_conj p q) \<longleftrightarrow>
    (holds standard_frame \<rho> \<nu> p \<and> holds standard_frame \<rho> \<nu> q)"
proof -
  let ?P = "eval_term standard_frame \<rho> \<nu> [] p"
  let ?Q = "eval_term standard_frame \<rho> \<nu> [] q"
  let ?Funs = "Fun zbool (Fun zbool zbool)"
  have empty: "bound_valuation_ok standard_frame \<rho> [] []"
    by (simp add: bound_valuation_ok_def)
  have p_open: "check_open_term base_theory [] p"
    using p_check by (simp add: check_term_def)
  have q_open: "check_open_term base_theory [] q"
    using q_check by (simp add: check_term_def)
  have p_in: "Elem ?P zbool"
    using eval_type_sound[OF base_theory_wf standard_frame_wf type_ok free_ok
        const_ok empty p_open p_type]
    by (simp add: bool_ty_def)
  have q_in: "Elem ?Q zbool"
    using eval_type_sound[OF base_theory_wf standard_frame_wf type_ok free_ok
        const_ok empty q_open q_type]
    by (simp add: bool_ty_def)
  have left_eval: "eval_term standard_frame \<rho> \<nu> [] (conj_lhs p q) =
      Lambda ?Funs (\<lambda>f. app (app f ?P) ?Q)"
  proof -
    note abs_raw = eval_target_abs[OF body_check,
        of standard_frame \<rho> \<nu> conj_fn conj_fty]
    have pointwise: "eval_term standard_frame \<rho>
        (\<nu>((conj_fn, conj_fty) := f)) []
        (Comb (Comb (FVar conj_fn conj_fty) p) q) = app (app f ?P) ?Q" for f
    proof -
      have ep: "eval_term standard_frame \<rho>
          (\<nu>((conj_fn, conj_fty) := f)) [] p = ?P"
        using eval_not_vfree_update[OF p_fresh, of standard_frame \<rho> \<nu> f "[]"] .
      have eq: "eval_term standard_frame \<rho>
          (\<nu>((conj_fn, conj_fty) := f)) [] q = ?Q"
        using eval_not_vfree_update[OF q_fresh, of standard_frame \<rho> \<nu> f "[]"] .
      show ?thesis using ep eq by simp
    qed
    show ?thesis
      using abs_raw pointwise
      by (simp add: conj_lhs_def conj_fty_def mk_fun_def bool_ty_def
          Lambda_ext)
  qed
  have right_eval: "eval_term standard_frame \<rho> \<nu> [] conj_rhs =
      Lambda ?Funs (\<lambda>f. app (app f ztrue) ztrue)"
  proof -
    note abs_raw = eval_target_abs[OF rhs_body_check,
        of standard_frame \<rho> \<nu> conj_fn conj_fty]
    show ?thesis using abs_raw
      by (simp add: conj_rhs_def conj_fty_def mk_fun_def bool_ty_def
          Lambda_ext)
  qed
  have outer: "holds standard_frame \<rho> \<nu>
      (eq_term (mk_fun conj_fty bool_ty) (conj_lhs p q) conj_rhs) \<longleftrightarrow>
      eval_term standard_frame \<rho> \<nu> [] (conj_lhs p q) =
        eval_term standard_frame \<rho> \<nu> [] conj_rhs"
    using holds_eq_iff[OF base_theory_wf standard_frame_wf type_ok free_ok
        const_ok lhs_check lhs_type rhs_check rhs_type] .
  have function_eq: "Lambda ?Funs (\<lambda>f. app (app f ?P) ?Q) =
      Lambda ?Funs (\<lambda>f. app (app f ztrue) ztrue) \<longleftrightarrow>
      (?P = ztrue \<and> ?Q = ztrue)"
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
    have "?P = ztrue" using fst_equal fst_in p_in q_in
      by (simp add: Lambda_app)
    moreover have "?Q = ztrue" using snd_equal snd_in p_in q_in
      by (simp add: Lambda_app)
    ultimately show "?P = ztrue \<and> ?Q = ztrue" by blast
  next
    assume both: "?P = ztrue \<and> ?Q = ztrue"
    then show "Lambda ?Funs (\<lambda>f. app (app f ?P) ?Q) =
      Lambda ?Funs (\<lambda>f. app (app f ztrue) ztrue)" by simp
  qed
  show ?thesis
    using outer left_eval right_eval function_eq
    by (simp add: target_conj_def holds_def)
qed

lemma holds_target_imp_iff:
  assumes type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok standard_frame base_theory \<rho>"
    and free_ok: "free_valuation_ok standard_frame \<rho> \<nu>"
    and conj_check: "check_term base_theory (target_conj p q)"
    and conj_type: "type_of (target_conj p q) = Some bool_ty"
    and p_check: "check_term base_theory p"
    and p_type: "type_of p = Some bool_ty"
    and conj_sem: "holds standard_frame \<rho> \<nu> (target_conj p q) \<longleftrightarrow>
      (holds standard_frame \<rho> \<nu> p \<and> holds standard_frame \<rho> \<nu> q)"
  shows "holds standard_frame \<rho> \<nu> (target_imp p q) \<longleftrightarrow>
    (holds standard_frame \<rho> \<nu> p \<longrightarrow> holds standard_frame \<rho> \<nu> q)"
proof -
  let ?C = "eval_term standard_frame \<rho> \<nu> [] (target_conj p q)"
  let ?P = "eval_term standard_frame \<rho> \<nu> [] p"
  have empty: "bound_valuation_ok standard_frame \<rho> [] []"
    by (simp add: bound_valuation_ok_def)
  have conj_open: "check_open_term base_theory [] (target_conj p q)"
    using conj_check by (simp add: check_term_def)
  have p_open: "check_open_term base_theory [] p"
    using p_check by (simp add: check_term_def)
  have c_in: "Elem ?C zbool"
    using eval_type_sound[OF base_theory_wf standard_frame_wf type_ok free_ok
        const_ok empty conj_open conj_type]
    by (simp add: bool_ty_def)
  have p_in: "Elem ?P zbool"
    using eval_type_sound[OF base_theory_wf standard_frame_wf type_ok free_ok
        const_ok empty p_open p_type]
    by (simp add: bool_ty_def)
  have outer: "holds standard_frame \<rho> \<nu>
      (eq_term bool_ty (target_conj p q) p) \<longleftrightarrow> ?C = ?P"
    using holds_eq_iff[OF base_theory_wf standard_frame_wf type_ok free_ok
        const_ok conj_check conj_type p_check p_type] .
  have truth: "(?C = ?P) \<longleftrightarrow>
      (?P = ztrue \<longrightarrow> eval_term standard_frame \<rho> \<nu> [] q = ztrue)"
    using c_in p_in conj_sem ztrue_neq_zfalse
    by (auto simp: holds_def)
  show ?thesis using outer truth by (simp add: target_imp_def holds_def)
qed


lemma eta_axiom_term_valid:
  "valid_sequent standard_frame base_theory [] eta_axiom_term"
proof (unfold valid_sequent_def, intro allI impI)
  fix \<rho> \<nu>
  assume type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok standard_frame base_theory \<rho>"
    and free_ok: "free_valuation_ok standard_frame \<rho> \<nu>"
  have body_check: "check_term base_theory eta_body" by eval
  have left_check: "check_term base_theory
      (target_abs eta_fn eta_fty eta_body)" by eval
  have left_type: "type_of (target_abs eta_fn eta_fty eta_body) =
      Some (mk_fun eta_fty bool_ty)" by eval
  have right_check: "check_term base_theory (Abs eta_fty true_term)"
    by eval
  have right_type: "type_of (Abs eta_fty true_term) =
      Some (mk_fun eta_fty bool_ty)" by eval
  have outer: "holds standard_frame \<rho> \<nu>
      (target_forall eta_fn eta_fty eta_body) \<longleftrightarrow>
    (\<forall>f. Elem f (interp_type standard_frame \<rho> eta_fty) \<longrightarrow>
      eval_term standard_frame \<rho> (\<nu>((eta_fn, eta_fty) := f)) []
        eta_body = ztrue)"
    using holds_target_forall_iff[OF type_ok const_ok free_ok body_check
        left_check left_type right_check right_type] .
  have pointwise: "\<forall>f. Elem f (interp_type standard_frame \<rho> eta_fty) \<longrightarrow>
      eval_term standard_frame \<rho> (\<nu>((eta_fn, eta_fty) := f)) []
        eta_body = ztrue"
  proof (intro allI impI)
    fix f
    assume f_in: "Elem f (interp_type standard_frame \<rho> eta_fty)"
    let ?\<nu>f = "\<nu>((eta_fn, eta_fty) := f)"
    have free_f: "free_valuation_ok standard_frame \<rho> ?\<nu>f"
      using free_valuation_update[OF free_ok f_in] .
    have inner_check: "check_term base_theory
        (Comb (FVar eta_fn eta_fty) (FVar eta_xn eta_aty))" by eval
    have abs_eval: "eval_term standard_frame \<rho> ?\<nu>f []
        (target_abs eta_xn eta_aty
          (Comb (FVar eta_fn eta_fty) (FVar eta_xn eta_aty))) = f"
    proof -
      have f_fun: "Elem f (Fun (\<rho> NAlpha) (\<rho> (NUser 3 ''beta'')))"
        using f_in by (simp add: eta_fty_def eta_aty_def eta_bty_def
            mk_fun_def standard_frame_def)
      have "eval_term standard_frame \<rho> ?\<nu>f []
          (target_abs eta_xn eta_aty
            (Comb (FVar eta_fn eta_fty) (FVar eta_xn eta_aty))) =
          Lambda (\<rho> NAlpha) (app f)"
        using eval_target_abs[OF inner_check, of standard_frame \<rho> ?\<nu>f]
        by (simp add: eta_fn_def eta_xn_def eta_fty_def eta_aty_def
            eta_bty_def mk_fun_def standard_frame_def)
      then show ?thesis
        using eta_axiom_valid f_fun by (auto simp: ETA_AX_def)
    qed
    have eta_holds: "holds standard_frame \<rho> ?\<nu>f eta_body"
    proof -
      have lhs_check: "check_term base_theory
          (target_abs eta_xn eta_aty
            (Comb (FVar eta_fn eta_fty) (FVar eta_xn eta_aty)))" by eval
      have lhs_type: "type_of (target_abs eta_xn eta_aty
          (Comb (FVar eta_fn eta_fty) (FVar eta_xn eta_aty))) =
          Some eta_fty" by eval
      have rhs_check: "check_term base_theory (FVar eta_fn eta_fty)" by eval
      have rhs_type: "type_of (FVar eta_fn eta_fty) = Some eta_fty" by simp
      have "holds standard_frame \<rho> ?\<nu>f
          (eq_term eta_fty
            (target_abs eta_xn eta_aty
              (Comb (FVar eta_fn eta_fty) (FVar eta_xn eta_aty)))
            (FVar eta_fn eta_fty))"
        using holds_eq_iff[OF base_theory_wf standard_frame_wf type_ok free_f
            const_ok lhs_check lhs_type rhs_check rhs_type] abs_eval
        by simp
      then show ?thesis by (simp add: eta_body_def)
    qed
    show "eval_term standard_frame \<rho> ?\<nu>f [] eta_body = ztrue"
      using eta_holds by (simp add: holds_def)
  qed
  show "holds standard_frame \<rho> \<nu> eta_axiom_term"
    using outer pointwise by (simp add: eta_axiom_term_def)
qed

lemma select_axiom_term_valid:
  "valid_sequent standard_frame base_theory [] select_axiom_term"
proof (unfold valid_sequent_def, intro allI impI)
  fix \<rho> \<nu>
  assume type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok standard_frame base_theory \<rho>"
    and free_ok: "free_valuation_ok standard_frame \<rho> \<nu>"
  have outer_body: "check_term base_theory select_inner" by eval
  have outer_left: "check_term base_theory
      (target_abs select_pn select_pty select_inner)" by eval
  have outer_left_ty: "type_of (target_abs select_pn select_pty select_inner) =
      Some (mk_fun select_pty bool_ty)" by eval
  have outer_right: "check_term base_theory (Abs select_pty true_term)" by eval
  have outer_right_ty: "type_of (Abs select_pty true_term) =
      Some (mk_fun select_pty bool_ty)" by eval
  have outer: "holds standard_frame \<rho> \<nu>
      (target_forall select_pn select_pty select_inner) \<longleftrightarrow>
    (\<forall>P. Elem P (interp_type standard_frame \<rho> select_pty) \<longrightarrow>
      eval_term standard_frame \<rho> (\<nu>((select_pn, select_pty) := P)) []
        select_inner = ztrue)"
    using holds_target_forall_iff[OF type_ok const_ok free_ok outer_body
        outer_left outer_left_ty outer_right outer_right_ty] .
  have pointwise_P: "\<forall>P. Elem P (interp_type standard_frame \<rho> select_pty) \<longrightarrow>
      eval_term standard_frame \<rho> (\<nu>((select_pn, select_pty) := P)) []
        select_inner = ztrue"
  proof (intro allI impI)
    fix P
    assume p_in: "Elem P (interp_type standard_frame \<rho> select_pty)"
    let ?\<nu>P = "\<nu>((select_pn, select_pty) := P)"
    have free_P: "free_valuation_ok standard_frame \<rho> ?\<nu>P"
      using free_valuation_update[OF free_ok p_in] .
    have inner_body: "check_term base_theory select_body" by eval
    have inner_left: "check_term base_theory
        (target_abs select_xn select_aty select_body)" by eval
    have inner_left_ty: "type_of (target_abs select_xn select_aty select_body) =
        Some (mk_fun select_aty bool_ty)" by eval
    have inner_right: "check_term base_theory (Abs select_aty true_term)" by eval
    have inner_right_ty: "type_of (Abs select_aty true_term) =
        Some (mk_fun select_aty bool_ty)" by eval
    have inner: "holds standard_frame \<rho> ?\<nu>P
        (target_forall select_xn select_aty select_body) \<longleftrightarrow>
      (\<forall>x. Elem x (interp_type standard_frame \<rho> select_aty) \<longrightarrow>
        eval_term standard_frame \<rho>
          (?\<nu>P((select_xn, select_aty) := x)) [] select_body = ztrue)"
      using holds_target_forall_iff[OF type_ok const_ok free_P inner_body
          inner_left inner_left_ty inner_right inner_right_ty] .
    have pointwise_x: "\<forall>x. Elem x (interp_type standard_frame \<rho> select_aty) \<longrightarrow>
        eval_term standard_frame \<rho>
          (?\<nu>P((select_xn, select_aty) := x)) [] select_body = ztrue"
    proof (intro allI impI)
      fix x
      assume x_in: "Elem x (interp_type standard_frame \<rho> select_aty)"
      let ?\<nu>Px = "?\<nu>P((select_xn, select_aty) := x)"
      have free_Px: "free_valuation_ok standard_frame \<rho> ?\<nu>Px"
        using free_valuation_update[OF free_P x_in] .
      have p_check: "check_term base_theory select_antecedent" by eval
      have p_type: "type_of select_antecedent = Some bool_ty" by eval
      have q_check: "check_term base_theory select_consequent" by eval
      have q_type: "type_of select_consequent = Some bool_ty" by eval
      have p_fresh: "\<not> vfree_in conj_fn conj_fty select_antecedent" by eval
      have q_fresh: "\<not> vfree_in conj_fn conj_fty select_consequent" by eval
      have conj_body: "check_term base_theory
          (Comb (Comb (FVar conj_fn conj_fty) select_antecedent)
            select_consequent)" by eval
      have conj_rhs_body: "check_term base_theory
          (Comb (Comb (FVar conj_fn conj_fty) true_term) true_term)" by eval
      have conj_lhs_check: "check_term base_theory
          (conj_lhs select_antecedent select_consequent)" by eval
      have conj_lhs_ty: "type_of (conj_lhs select_antecedent select_consequent) =
          Some (mk_fun conj_fty bool_ty)" by eval
      have conj_rhs_check: "check_term base_theory conj_rhs" by eval
      have conj_rhs_ty: "type_of conj_rhs = Some (mk_fun conj_fty bool_ty)" by eval
      have conj_sem: "holds standard_frame \<rho> ?\<nu>Px
          (target_conj select_antecedent select_consequent) \<longleftrightarrow>
        (holds standard_frame \<rho> ?\<nu>Px select_antecedent \<and>
          holds standard_frame \<rho> ?\<nu>Px select_consequent)"
        using holds_target_conj_iff[OF type_ok const_ok free_Px p_check p_type
            q_check q_type p_fresh q_fresh conj_body conj_rhs_body
            conj_lhs_check conj_lhs_ty conj_rhs_check conj_rhs_ty] .
      have conj_check: "check_term base_theory
          (target_conj select_antecedent select_consequent)" by eval
      have conj_type: "type_of
          (target_conj select_antecedent select_consequent) = Some bool_ty" by eval
      have imp_sem: "holds standard_frame \<rho> ?\<nu>Px select_body \<longleftrightarrow>
        (holds standard_frame \<rho> ?\<nu>Px select_antecedent \<longrightarrow>
          holds standard_frame \<rho> ?\<nu>Px select_consequent)"
        unfolding select_body_def
        using holds_target_imp_iff[OF type_ok const_ok free_Px conj_check
            conj_type p_check p_type conj_sem] .
      have p_shape: "Elem P (Fun (\<rho> NAlpha) zbool)"
        using p_in by (simp add: select_pty_def select_aty_def mk_fun_def)
      have x_shape: "Elem x (\<rho> NAlpha)"
        using x_in by (simp add: select_aty_def)
      have choice: "app P x = ztrue \<longrightarrow>
          app P (semantic_select (\<rho> NAlpha) P) = ztrue"
        using select_axiom_valid p_shape x_shape by (auto simp: SELECT_AX_def)
      have implication: "holds standard_frame \<rho> ?\<nu>Px select_antecedent \<longrightarrow>
          holds standard_frame \<rho> ?\<nu>Px select_consequent"
        using choice
        by (simp add: holds_def select_antecedent_def select_consequent_def
            select_p_def select_x_def select_value_def select_pn_def
            select_xn_def select_pty_def select_aty_def select_name_def
            const_sem_def subst_valuation_def type_match_def standard_frame_def
            mk_fun_def bool_ty_def Lambda_app p_shape)
      have "holds standard_frame \<rho> ?\<nu>Px select_body"
        using imp_sem implication by blast
      then show "eval_term standard_frame \<rho> ?\<nu>Px [] select_body = ztrue"
        by (simp add: holds_def)
    qed
    have "holds standard_frame \<rho> ?\<nu>P select_inner"
      using inner pointwise_x by (simp add: select_inner_def)
    then show "eval_term standard_frame \<rho> ?\<nu>P [] select_inner = ztrue"
      by (simp add: holds_def)
  qed
  show "holds standard_frame \<rho> \<nu> select_axiom_term"
    using outer pointwise_P by (simp add: select_axiom_term_def)
qed

lemma bool_cases_axiom_term_valid:
  "valid_sequent standard_frame base_theory [] bool_cases_axiom_term"
proof (unfold valid_sequent_def, intro allI impI)
  fix \<rho> \<nu>
  assume type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok standard_frame base_theory \<rho>"
    and free_ok: "free_valuation_ok standard_frame \<rho> \<nu>"
  have outer_body: "check_term base_theory bool_cases_body" by eval
  have outer_left: "check_term base_theory
      (target_abs bool_cases_tn bool_ty bool_cases_body)" by eval
  have outer_left_ty: "type_of (target_abs bool_cases_tn bool_ty bool_cases_body) =
      Some (mk_fun bool_ty bool_ty)" by eval
  have outer_right: "check_term base_theory (Abs bool_ty true_term)" by eval
  have outer_right_ty: "type_of (Abs bool_ty true_term) =
      Some (mk_fun bool_ty bool_ty)" by eval
  have outer: "holds standard_frame \<rho> \<nu>
      (target_forall bool_cases_tn bool_ty bool_cases_body) \<longleftrightarrow>
    (\<forall>t. Elem t zbool \<longrightarrow>
      eval_term standard_frame \<rho> (\<nu>((bool_cases_tn, bool_ty) := t)) []
        bool_cases_body = ztrue)"
    using holds_target_forall_iff[OF type_ok const_ok free_ok outer_body
        outer_left outer_left_ty outer_right outer_right_ty]
    by (simp add: bool_ty_def)
  have pointwise_t: "\<forall>t. Elem t zbool \<longrightarrow>
      eval_term standard_frame \<rho> (\<nu>((bool_cases_tn, bool_ty) := t)) []
        bool_cases_body = ztrue"
  proof (intro allI impI)
    fix t
    assume t_in: "Elem t zbool"
    let ?\<nu>T = "\<nu>((bool_cases_tn, bool_ty) := t)"
    have free_T: "free_valuation_ok standard_frame \<rho> ?\<nu>T"
      using free_valuation_update[OF free_ok] t_in by (simp add: bool_ty_def)
    have true_sem: "holds standard_frame \<rho> ?\<nu>T bool_cases_true \<longleftrightarrow> t = ztrue"
    proof -
      have lcheck: "check_term base_theory bool_cases_t" by eval
      have ltype: "type_of bool_cases_t = Some bool_ty" by eval
      have rcheck: "check_term base_theory true_term" by eval
      have rtype: "type_of true_term = Some bool_ty" by eval
      note eqsem = holds_eq_iff[OF base_theory_wf standard_frame_wf type_ok
          free_T const_ok lcheck ltype rcheck rtype]
      show ?thesis using eqsem
        by (simp add: bool_cases_true_def bool_cases_t_def bool_cases_tn_def)
    qed
    have false_sem: "holds standard_frame \<rho> ?\<nu>T bool_cases_false \<longleftrightarrow> t = zfalse"
    proof -
      have lcheck: "check_term base_theory bool_cases_t" by eval
      have ltype: "type_of bool_cases_t = Some bool_ty" by eval
      have rcheck: "check_term base_theory false_term" by eval
      have rtype: "type_of false_term = Some bool_ty" by eval
      note eqsem = holds_eq_iff[OF base_theory_wf standard_frame_wf type_ok
          free_T const_ok lcheck ltype rcheck rtype]
      show ?thesis using eqsem
        by (simp add: bool_cases_false_def bool_cases_t_def bool_cases_tn_def)
    qed
    have one_case: "holds standard_frame \<rho> ?\<nu>T bool_cases_true \<or>
        holds standard_frame \<rho> ?\<nu>T bool_cases_false"
      using t_in true_sem false_sem by auto
    have disj_body_check: "check_term base_theory
        (disj_body bool_cases_true bool_cases_false)" by eval
    have disj_left_check: "check_term base_theory
        (target_abs disj_rn bool_ty
          (disj_body bool_cases_true bool_cases_false))" by eval
    have disj_left_ty: "type_of (target_abs disj_rn bool_ty
        (disj_body bool_cases_true bool_cases_false)) =
        Some (mk_fun bool_ty bool_ty)" by eval
    have disj_right_check: "check_term base_theory (Abs bool_ty true_term)" by eval
    have disj_right_ty: "type_of (Abs bool_ty true_term) =
        Some (mk_fun bool_ty bool_ty)" by eval
    have disj_sem: "holds standard_frame \<rho> ?\<nu>T
        (target_forall disj_rn bool_ty
          (disj_body bool_cases_true bool_cases_false)) \<longleftrightarrow>
      (\<forall>r. Elem r zbool \<longrightarrow> eval_term standard_frame \<rho>
        (?\<nu>T((disj_rn, bool_ty) := r)) []
        (disj_body bool_cases_true bool_cases_false) = ztrue)"
      using holds_target_forall_iff[OF type_ok const_ok free_T disj_body_check
          disj_left_check disj_left_ty disj_right_check disj_right_ty]
      by (simp add: bool_ty_def)
    have pointwise_r: "\<forall>r. Elem r zbool \<longrightarrow> eval_term standard_frame \<rho>
        (?\<nu>T((disj_rn, bool_ty) := r)) []
        (disj_body bool_cases_true bool_cases_false) = ztrue"
    proof (intro allI impI)
      fix r
      assume r_in: "Elem r zbool"
      let ?\<nu>Tr = "?\<nu>T((disj_rn, bool_ty) := r)"
      have free_Tr: "free_valuation_ok standard_frame \<rho> ?\<nu>Tr"
        using free_valuation_update[OF free_T] r_in by (simp add: bool_ty_def)
      have conj_pr: "holds standard_frame \<rho> ?\<nu>Tr
          (target_conj bool_cases_true disj_r) \<longleftrightarrow>
        (holds standard_frame \<rho> ?\<nu>Tr bool_cases_true \<and>
          holds standard_frame \<rho> ?\<nu>Tr disj_r)"
        by (rule holds_target_conj_iff[OF type_ok const_ok free_Tr]; eval)
      have pr_conj_check: "check_term base_theory
          (target_conj bool_cases_true disj_r)" by eval
      have pr_conj_type: "type_of (target_conj bool_cases_true disj_r) =
          Some bool_ty" by eval
      have pr_check: "check_term base_theory bool_cases_true" by eval
      have pr_type: "type_of bool_cases_true = Some bool_ty" by eval
      have imp_pr: "holds standard_frame \<rho> ?\<nu>Tr (disj_left bool_cases_true) \<longleftrightarrow>
        (holds standard_frame \<rho> ?\<nu>Tr bool_cases_true \<longrightarrow>
          holds standard_frame \<rho> ?\<nu>Tr disj_r)"
        unfolding disj_left_def
        using holds_target_imp_iff[OF type_ok const_ok free_Tr pr_conj_check
            pr_conj_type pr_check pr_type conj_pr] .
      have conj_qr: "holds standard_frame \<rho> ?\<nu>Tr
          (target_conj bool_cases_false disj_r) \<longleftrightarrow>
        (holds standard_frame \<rho> ?\<nu>Tr bool_cases_false \<and>
          holds standard_frame \<rho> ?\<nu>Tr disj_r)"
        by (rule holds_target_conj_iff[OF type_ok const_ok free_Tr]; eval)
      have qr_conj_check: "check_term base_theory
          (target_conj bool_cases_false disj_r)" by eval
      have qr_conj_type: "type_of (target_conj bool_cases_false disj_r) =
          Some bool_ty" by eval
      have qr_check: "check_term base_theory bool_cases_false" by eval
      have qr_type: "type_of bool_cases_false = Some bool_ty" by eval
      have imp_qr: "holds standard_frame \<rho> ?\<nu>Tr
          (target_imp bool_cases_false disj_r) \<longleftrightarrow>
        (holds standard_frame \<rho> ?\<nu>Tr bool_cases_false \<longrightarrow>
          holds standard_frame \<rho> ?\<nu>Tr disj_r)"
        using holds_target_imp_iff[OF type_ok const_ok free_Tr qr_conj_check
            qr_conj_type qr_check qr_type conj_qr] .
      have conj_right: "holds standard_frame \<rho> ?\<nu>Tr
          (target_conj (target_imp bool_cases_false disj_r) disj_r) \<longleftrightarrow>
        (holds standard_frame \<rho> ?\<nu>Tr (target_imp bool_cases_false disj_r) \<and>
          holds standard_frame \<rho> ?\<nu>Tr disj_r)"
        by (rule holds_target_conj_iff[OF type_ok const_ok free_Tr]; eval)
      have right_conj_check: "check_term base_theory
          (target_conj (target_imp bool_cases_false disj_r) disj_r)" by eval
      have right_conj_type: "type_of
          (target_conj (target_imp bool_cases_false disj_r) disj_r) =
          Some bool_ty" by eval
      have right_p_check: "check_term base_theory
          (target_imp bool_cases_false disj_r)" by eval
      have right_p_type: "type_of (target_imp bool_cases_false disj_r) =
          Some bool_ty" by eval
      have imp_right: "holds standard_frame \<rho> ?\<nu>Tr (disj_right bool_cases_false) \<longleftrightarrow>
        ((holds standard_frame \<rho> ?\<nu>Tr bool_cases_false \<longrightarrow>
            holds standard_frame \<rho> ?\<nu>Tr disj_r) \<longrightarrow>
          holds standard_frame \<rho> ?\<nu>Tr disj_r)"
        unfolding disj_right_def
        using holds_target_imp_iff[OF type_ok const_ok free_Tr right_conj_check
            right_conj_type right_p_check right_p_type conj_right] imp_qr
        by blast
      have conj_outer: "holds standard_frame \<rho> ?\<nu>Tr
          (target_conj (disj_left bool_cases_true)
            (disj_right bool_cases_false)) \<longleftrightarrow>
        (holds standard_frame \<rho> ?\<nu>Tr (disj_left bool_cases_true) \<and>
          holds standard_frame \<rho> ?\<nu>Tr (disj_right bool_cases_false))"
        by (rule holds_target_conj_iff[OF type_ok const_ok free_Tr]; eval)
      have outer_conj_check: "check_term base_theory
          (target_conj (disj_left bool_cases_true)
            (disj_right bool_cases_false))" by eval
      have outer_conj_type: "type_of
          (target_conj (disj_left bool_cases_true)
            (disj_right bool_cases_false)) = Some bool_ty" by eval
      have outer_p_check: "check_term base_theory
          (disj_left bool_cases_true)" by eval
      have outer_p_type: "type_of (disj_left bool_cases_true) = Some bool_ty"
        by eval
      have imp_outer: "holds standard_frame \<rho> ?\<nu>Tr
          (disj_body bool_cases_true bool_cases_false) \<longleftrightarrow>
        ((holds standard_frame \<rho> ?\<nu>Tr bool_cases_true \<longrightarrow>
            holds standard_frame \<rho> ?\<nu>Tr disj_r) \<longrightarrow>
          ((holds standard_frame \<rho> ?\<nu>Tr bool_cases_false \<longrightarrow>
              holds standard_frame \<rho> ?\<nu>Tr disj_r) \<longrightarrow>
            holds standard_frame \<rho> ?\<nu>Tr disj_r))"
        unfolding disj_body_def
        using holds_target_imp_iff[OF type_ok const_ok free_Tr outer_conj_check
            outer_conj_type outer_p_check outer_p_type conj_outer]
          imp_pr imp_right
        by blast
      have true_fresh: "\<not> vfree_in disj_rn bool_ty bool_cases_true" by eval
      have false_fresh: "\<not> vfree_in disj_rn bool_ty bool_cases_false" by eval
      have true_stable: "eval_term standard_frame \<rho> ?\<nu>Tr [] bool_cases_true =
          eval_term standard_frame \<rho> ?\<nu>T [] bool_cases_true"
        using eval_not_vfree_update[OF true_fresh,
            of standard_frame \<rho> ?\<nu>T r "[]"] .
      have false_stable: "eval_term standard_frame \<rho> ?\<nu>Tr [] bool_cases_false =
          eval_term standard_frame \<rho> ?\<nu>T [] bool_cases_false"
        using eval_not_vfree_update[OF false_fresh,
            of standard_frame \<rho> ?\<nu>T r "[]"] .
      have cases_stable: "holds standard_frame \<rho> ?\<nu>Tr bool_cases_true \<or>
          holds standard_frame \<rho> ?\<nu>Tr bool_cases_false"
        using one_case true_stable false_stable by (simp add: holds_def)
      have "holds standard_frame \<rho> ?\<nu>Tr
          (disj_body bool_cases_true bool_cases_false)"
        using imp_outer cases_stable by blast
      then show "eval_term standard_frame \<rho> ?\<nu>Tr []
          (disj_body bool_cases_true bool_cases_false) = ztrue"
        by (simp add: holds_def)
    qed
    have "holds standard_frame \<rho> ?\<nu>T bool_cases_body"
      using disj_sem pointwise_r
      by (simp add: bool_cases_body_def target_disj_def)
    then show "eval_term standard_frame \<rho> ?\<nu>T [] bool_cases_body = ztrue"
      by (simp add: holds_def)
  qed
  show "holds standard_frame \<rho> \<nu> bool_cases_axiom_term"
    using outer pointwise_t by (simp add: bool_cases_axiom_term_def)
qed

theorem standard_frame_models_base:
  "models_theory standard_frame base_theory"
proof (unfold models_theory_def, intro conjI)
  show "frame_wf standard_frame" by simp
  show "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
      const_interpretation_ok standard_frame base_theory \<rho>"
    using standard_frame_base_constants by blast
  show "\<forall>th\<in>set (axiom_list base_theory).
      valid_sequent standard_frame base_theory (hyps th) (concl th)"
    using eta_axiom_term_valid select_axiom_term_valid
      bool_cases_axiom_term_valid
    by (simp add: base_theory_def base_axiom_thms_def)
  show "\<forall>n th. def_tab base_theory n = Some th \<longrightarrow>
      valid_sequent standard_frame base_theory (hyps th) (concl th)"
    by (simp add: base_theory_def initial_theory_def)
qed

lemma false_term_wf:
  "check_prop base_theory false_term"
  by (simp add: base_theory_def false_term_def constant_true_function_def
      true_term_def eq_bool_ty_def eq_term_def eq_const_def check_prop_def
      check_term_def is_bool_def initial_theory_def mk_fun_def bool_ty_def
      type_match_def)

lemma inhabited_fun:
  assumes "inhabited B"
  shows "inhabited (Fun A B)"
proof -
  obtain b where "Elem b B" using assms by (auto simp: inhabited_def)
  then have "Elem (Lambda A (\<lambda>_. b)) (Fun A B)"
    by (simp add: Elem_Lambda_Fun)
  then show ?thesis by (auto simp: inhabited_def)
qed

lemma standard_interp_inhabited:
  "inhabited (interp_type standard_frame (\<lambda>_. zbool) ty)"
  using interp_type_inhabited_any[OF standard_frame_wf,
      of "\<lambda>_. zbool" ty]
  by (auto simp: type_valuation_ok_def inhabited_def)
definition chosen_free_valuation :: "(hname \<times> htype) \<Rightarrow> ZF" where
  "chosen_free_valuation x = (SOME z. Elem z
    (interp_type standard_frame (\<lambda>_. zbool) (snd x)))"

lemma chosen_free_valuation_ok:
  "free_valuation_ok standard_frame (\<lambda>_. zbool) chosen_free_valuation"
  unfolding free_valuation_ok_def chosen_free_valuation_def
  using standard_interp_inhabited
  by (auto simp: inhabited_def intro: someI_ex)

theorem base_consistent:
  assumes derived: "derives base_theory \<lparr>hyps = [], concl = false_term,
      thm_stamp = thy_stamp base_theory\<rparr>"
  shows False
proof -
  have theory_wf: "wf_theory base_theory" by simp
  have valid: "valid_sequent standard_frame base_theory [] false_term"
    using derives_valid[OF derived theory_wf standard_frame_models_base] by simp
  have type_ok: "type_valuation_ok (\<lambda>_. zbool)"
    by (auto simp: type_valuation_ok_def inhabited_def)
  have const_ok: "const_interpretation_ok standard_frame base_theory (\<lambda>_. zbool)"
    using standard_frame_models_base type_ok by (auto simp: models_theory_def)
  have "holds standard_frame (\<lambda>_. zbool) chosen_free_valuation false_term"
    using valid type_ok const_ok chosen_free_valuation_ok
    by (auto simp: valid_sequent_def)
  then show False using ztrue_neq_zfalse by (simp add: holds_def)
qed



end
