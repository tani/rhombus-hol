(* SPDX-License-Identifier: 0BSD AND BSD-2-Clause AND BSD-3-Clause *)
(* Conservatively covered by HOL Light and HOL4 notices; see THIRD_PARTY_NOTICES. *)

theory Rhombus_HOL_Extensions
  imports Rhombus_HOL_Extension_Core
begin

section \<open>Explicit frame extensions\<close>

definition add_type_frame :: "frame \<Rightarrow> hname \<Rightarrow> (ZF list \<Rightarrow> ZF) \<Rightarrow> frame" where
  "add_type_frame F n D = F\<lparr>tyop_denote := (tyop_denote F)(n := D)\<rparr>"

lemma add_type_frame_wf:
  assumes "frame_wf F" "n \<noteq> NFun" "n \<noteq> NBool"
    "\<forall>args. list_all inhabited args \<longrightarrow> inhabited (D args)"
  shows "frame_wf (add_type_frame F n D)"
  using assms by (auto simp: frame_wf_def add_type_frame_def)

lemma interp_type_add_type_unchanged:
  assumes fresh: "tyops thy n = None" and checked: "check_type thy ty"
  shows "interp_type (add_type_frame F n D) \<rho> ty = interp_type F \<rho> ty"
  using checked
proof (induction ty)
  case (TyVar x)
  then show ?case by simp
next
  case (TyApp x args)
  have x_not_n: "x \<noteq> n" using TyApp.prems fresh by auto
  have maps: "map (interp_type (add_type_frame F n D) \<rho>) args =
      map (interp_type F \<rho>) args"
    using TyApp.IH TyApp.prems by (auto simp: list_all_iff intro!: map_cong)
  show ?case
    by (simp only: interp_type.simps maps; simp add: add_type_frame_def x_not_n)
qed

lemma interp_type_add_type_avoids:
  assumes "\<not> type_operator_occurs n ty"
  shows "interp_type (add_type_frame F n D) \<rho> ty = interp_type F \<rho> ty"
  using assms
proof (induction ty)
  case (TyVar x)
  then show ?case by simp
next
  case (TyApp x args)
  have x_not_n: "x \<noteq> n" using TyApp.prems by auto
  have maps: "map (interp_type (add_type_frame F n D) \<rho>) args =
      map (interp_type F \<rho>) args"
    using TyApp by (intro map_cong) (auto simp: list_ex_iff)
  show ?case by (simp only: interp_type.simps maps; simp add: add_type_frame_def x_not_n)
qed

lemma subst_valuation_add_type_agree:
  assumes avoids: "\<not> type_operator_occurs n (type_subst \<theta> generic)"
    and occurs: "type_var_occurs v generic"
  shows "subst_valuation (add_type_frame F n D) \<rho> \<theta> v =
    subst_valuation F \<rho> \<theta> v"
proof (cases "\<theta> v")
  case None
  then show ?thesis by (simp add: subst_valuation_def)
next
  case (Some ty)
  have "\<not> type_operator_occurs n ty"
    using type_subst_component_avoids_operator[OF occurs avoids] Some by simp
  then show ?thesis using Some interp_type_add_type_avoids
    by (simp add: subst_valuation_def)
qed

lemma const_sem_add_type_unchanged:
  assumes fresh: "tyops thy n = None" and checked: "check_type thy ty"
    and frame_ok: "frame_wf F"
  shows "const_sem (add_type_frame F n D) \<rho> m ty = const_sem F \<rho> m ty"
proof (cases "m = NEq")
  case True
  show ?thesis
  proof (cases "classify_equality_type ty")
    case (Equality_Instance a)
    have shape: "ty = TyApp NFun [a, TyApp NFun [a, TyApp NBool []]]"
      using classify_equality_instance[OF Equality_Instance] .
    have a_checked: "check_type thy a" using checked unfolding shape by simp
    show ?thesis using True Equality_Instance
        interp_type_add_type_unchanged[OF fresh a_checked, of F D \<rho>]
      by (simp add: const_sem_def)
  qed (simp_all add: True const_sem_def)
next
  case False
  show ?thesis
  proof (cases "const_scheme F m")
    case None
    then show ?thesis using False by (simp add: const_sem_def add_type_frame_def)
  next
    case (Some generic)
    have scheme: "const_scheme F m = Some generic" using Some .
    show ?thesis
    proof (cases "type_match generic ty (\<lambda>_. None)")
      case None
      then show ?thesis using False scheme
        by (simp add: const_sem_def add_type_frame_def)
    next
      case (Some \<theta>)
      have match: "type_match generic ty (\<lambda>_. None) = Some \<theta>" using Some .
      have instantiated: "type_subst \<theta> generic = ty"
        using type_match_sound[OF match] .
      have avoids: "\<not> type_operator_occurs n (type_subst \<theta> generic)"
        using checked_type_avoids_fresh_operator[OF fresh checked] instantiated by simp
      have agree: "\<forall>v. type_var_occurs v generic \<longrightarrow>
          subst_valuation (add_type_frame F n D) \<rho> \<theta> v =
          subst_valuation F \<rho> \<theta> v"
        using subst_valuation_add_type_agree[OF avoids] by blast
      have extensional: "\<forall>\<rho> \<sigma>.
          (\<forall>v. type_var_occurs v generic \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow>
          const_denote F m \<rho> = const_denote F m \<sigma>"
        using frame_ok scheme by (auto simp: frame_wf_def)
      have denote: "const_denote F m
          (subst_valuation (add_type_frame F n D) \<rho> \<theta>) =
          const_denote F m (subst_valuation F \<rho> \<theta>)"
        using extensional agree by blast
      show ?thesis using False scheme match denote
        by (simp add: const_sem_def add_type_frame_def)
    qed
  qed
qed

lemma eval_add_type_unchanged:
  assumes fresh: "tyops thy n = None" and frame_ok: "frame_wf F"
    and checked: "check_open_term thy envty t"
  shows "eval_term (add_type_frame F n D) \<rho> \<nu> env t = eval_term F \<rho> \<nu> env t"
  using checked
proof (induction t arbitrary: envty env)
  case (Const m ty)
  have ty_checked: "check_type thy ty" using Const.prems by simp
  show ?case using const_sem_add_type_unchanged[OF fresh ty_checked frame_ok]
    by simp
next
  case (Abs ty body)  have ty_checked: "check_type thy ty" using Abs.prems by simp
  have carrier: "interp_type (add_type_frame F n D) \<rho> ty = interp_type F \<rho> ty"
    using interp_type_add_type_unchanged[OF fresh ty_checked] .
  show ?case using Abs.IH[of "ty # envty"] Abs.prems carrier by simp
qed auto

definition chosen_member :: "ZF \<Rightarrow> ZF" where
  "chosen_member A = (SOME z. Elem z A)"

lemma chosen_member_in:
  "inhabited A \<Longrightarrow> Elem (chosen_member A) A"
  by (auto simp: inhabited_def chosen_member_def intro: someI_ex)

definition add_constant_frame :: "frame \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> frame" where
  "add_constant_frame F n generic = F\<lparr>
    const_scheme := (const_scheme F)(n := Some generic),
    const_denote := (const_denote F)
      (n := (\<lambda>\<rho>. chosen_member (interp_type F \<rho> generic)))\<rparr>"

lemma add_constant_frame_wf:
  assumes old: "frame_wf F"
  shows "frame_wf (add_constant_frame F n generic)"
proof (unfold frame_wf_def, intro conjI)
  show "\<forall>m args. m \<noteq> NFun \<longrightarrow> m \<noteq> NBool \<longrightarrow> list_all inhabited args \<longrightarrow>
      inhabited (tyop_denote (add_constant_frame F n generic) m args)"
    using old by (simp add: frame_wf_def add_constant_frame_def)
  show "\<forall>m g \<rho> \<sigma>. const_scheme (add_constant_frame F n generic) m = Some g \<longrightarrow>
      (\<forall>v. type_var_occurs v g \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow>
      const_denote (add_constant_frame F n generic) m \<rho> =
      const_denote (add_constant_frame F n generic) m \<sigma>"
  proof (intro allI impI)
    fix m g and \<rho> \<sigma> :: "hname \<Rightarrow> ZF"
    assume scheme: "const_scheme (add_constant_frame F n generic) m = Some g"
      and agree: "\<forall>v. type_var_occurs v g \<longrightarrow> \<rho> v = \<sigma> v"
    show "const_denote (add_constant_frame F n generic) m \<rho> =
        const_denote (add_constant_frame F n generic) m \<sigma>"
    proof (cases "m = n")
      case True
      have g: "g = generic" using scheme True
        by (simp add: add_constant_frame_def)
      have carrier: "interp_type F \<rho> generic = interp_type F \<sigma> generic"
        using interp_type_cong_occurs agree g by blast
      show ?thesis using True carrier by (simp add: add_constant_frame_def)
    next
      case False
      have old_scheme: "const_scheme F m = Some g"
        using scheme False by (simp add: add_constant_frame_def)
      have old_ext: "const_denote F m \<rho> = const_denote F m \<sigma>"
        using old old_scheme agree by (auto simp: frame_wf_def)
      show ?thesis using False old_ext by (simp add: add_constant_frame_def)
    qed
  qed
qed
lemma interp_type_add_constant [simp]:
  "interp_type (add_constant_frame F n generic) \<rho> ty = interp_type F \<rho> ty"
proof (induction ty)
  case (TyVar x)
  then show ?case by simp
next
  case (TyApp x args)
  have maps: "map (interp_type (add_constant_frame F n generic) \<rho>) args =
      map (interp_type F \<rho>) args"
    using TyApp.IH by (intro map_cong) auto
  show ?case by (simp only: interp_type.simps maps; simp add: add_constant_frame_def)
qed
lemma subst_valuation_add_constant [simp]:
  "subst_valuation (add_constant_frame F n generic) \<rho> \<theta> =
    subst_valuation F \<rho> \<theta>"
  by (rule ext) (simp add: subst_valuation_def split: option.splits)

lemma const_sem_add_constant_other:
  assumes other: "m \<noteq> n"
  shows "const_sem (add_constant_frame F n generic) \<rho> m ty = const_sem F \<rho> m ty"
proof (cases "m = NEq")
  case True
  show ?thesis
  proof (cases "classify_equality_type ty")
    case (Equality_Instance a)
    have interp: "interp_type (add_constant_frame F n generic) \<rho> a =
        interp_type F \<rho> a" by (rule interp_type_add_constant)
    show ?thesis using True Equality_Instance interp by (simp add: const_sem_def)
  qed (simp_all add: True const_sem_def)
next
  case False
  have scheme: "const_scheme (add_constant_frame F n generic) m =
      const_scheme F m"
    using other by (simp add: add_constant_frame_def)
  show ?thesis
  proof (cases "const_scheme F m")
    case None
    then show ?thesis using False scheme by (simp add: const_sem_def)
  next
    case (Some g)
    have old_scheme: "const_scheme F m = Some g" using Some .
    show ?thesis
    proof (cases "type_match g ty (\<lambda>_. None)")
      case None
      then show ?thesis using False scheme old_scheme by (simp add: const_sem_def)
    next
      case (Some \<theta>)
      have match: "type_match g ty (\<lambda>_. None) = Some \<theta>" using Some .
      have valuation: "subst_valuation (add_constant_frame F n generic) \<rho> \<theta> =
          subst_valuation F \<rho> \<theta>" by (rule subst_valuation_add_constant)
      have denote: "const_denote (add_constant_frame F n generic) m =
          const_denote F m"
        using other by (simp add: add_constant_frame_def)
      have scheme_new: "const_scheme (add_constant_frame F n generic) m = Some g"
        using scheme old_scheme by simp
      have lhs: "const_sem (add_constant_frame F n generic) \<rho> m ty =
          const_denote (add_constant_frame F n generic) m
            (subst_valuation (add_constant_frame F n generic) \<rho> \<theta>)"
        using const_sem_non_equality[OF False scheme_new match] .
      have rhs: "const_sem F \<rho> m ty =
          const_denote F m (subst_valuation F \<rho> \<theta>)"
        using const_sem_non_equality[OF False old_scheme match] .
      show ?thesis using lhs rhs valuation denote by simp    qed  qed
qed
lemma eval_add_constant_unchanged:  assumes "const_tab thy n = None" "check_open_term thy envty t"
  shows "eval_term (add_constant_frame F n generic) \<rho> \<nu> env t = eval_term F \<rho> \<nu> env t"
  using assms
proof (induction t arbitrary: envty env)
  case (Const m ty)
  then have "m \<noteq> n" by auto
  then show ?case using const_sem_add_constant_other by simp
qed auto

lemma check_type_tyops_cong:
  assumes "tyops a = tyops b"
  shows "check_type a ty = check_type b ty"
  using assms by (induction ty) (auto simp: list_all_iff)

lemma const_sem_add_constant_same:
  assumes "n \<noteq> NEq" "type_match generic ty (\<lambda>_. None) = Some \<theta>"
  shows "const_sem (add_constant_frame F n generic) \<rho> n ty =
    chosen_member (interp_type F \<rho> ty)"
proof -
  have instantiated: "type_subst \<theta> generic = ty"
    using type_match_sound[OF assms(2)] .
  have carrier: "interp_type F (subst_valuation F \<rho> \<theta>) generic =
      interp_type F \<rho> ty"
    using interp_type_subst[of F \<rho> \<theta> generic] instantiated by simp
  have valuation: "subst_valuation (add_constant_frame F n generic) \<rho> \<theta> =
      subst_valuation F \<rho> \<theta>" by simp
  have denote: "const_denote (add_constant_frame F n generic) n
      (subst_valuation (add_constant_frame F n generic) \<rho> \<theta>) =
      chosen_member (interp_type F (subst_valuation F \<rho> \<theta>) generic)"
    using valuation by (simp add: add_constant_frame_def)
  show ?thesis using assms carrier denote
    by (simp add: const_sem_def add_constant_frame_def)qed

definition canonical_free_valuation ::
  "frame \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ((hname \<times> htype) \<Rightarrow> ZF)" where
  "canonical_free_valuation F \<rho> =
    (\<lambda>(_, ty). chosen_member (interp_type F \<rho> ty))"

lemma canonical_free_valuation_ok:
  assumes "frame_wf F" "type_valuation_ok \<rho>"
  shows "free_valuation_ok F \<rho> (canonical_free_valuation F \<rho>)"
  using interp_type_inhabited_any[OF assms]
  by (auto simp: free_valuation_ok_def canonical_free_valuation_def
      intro: chosen_member_in)

definition closed_term_denote ::
  "frame \<Rightarrow> hterm \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "closed_term_denote F rhs \<rho> =
    eval_term F \<rho> (canonical_free_valuation F \<rho>) [] rhs"

lemma closed_term_denote_extensional:
  assumes frame_ok: "frame_wf F"
    and closed: "free_vars rhs = []"
    and vars: "set (term_type_vars rhs) \<subseteq> set (type_vars generic)"
    and agree: "\<And>v. type_var_occurs v generic \<Longrightarrow> \<rho> v = \<sigma> v"
  shows "closed_term_denote F rhs \<rho> = closed_term_denote F rhs \<sigma>"
proof -
  have type_agree: "\<And>v. v \<in> set (term_type_vars rhs) \<Longrightarrow> \<rho> v = \<sigma> v"
    using vars agree set_type_vars by auto
  have free_change: "eval_term F \<rho> (canonical_free_valuation F \<rho>) [] rhs =
      eval_term F \<rho> (canonical_free_valuation F \<sigma>) [] rhs"
    using eval_term_closed_free_valuation[OF closed] .
  have type_change: "eval_term F \<rho> (canonical_free_valuation F \<sigma>) [] rhs =
      eval_term F \<sigma> (canonical_free_valuation F \<sigma>) [] rhs"
    using eval_term_cong_type_vars[OF frame_ok type_agree] .
  show ?thesis using free_change type_change
    by (simp add: closed_term_denote_def)
qed

lemma closed_term_denote_matched:
  assumes frame_ok: "frame_wf F"
    and closed: "free_vars rhs = []"
    and vars: "set (term_type_vars rhs) \<subseteq> set (type_vars generic)"
    and instantiated: "type_subst \<theta> generic = generic"
  shows "closed_term_denote F rhs (subst_valuation F \<rho> \<theta>) =
    closed_term_denote F rhs \<rho>"
proof (rule closed_term_denote_extensional[OF frame_ok closed vars])
  fix v
  assume occurs: "type_var_occurs v generic"
  have empty: "type_subst (\<lambda>_. None) generic = generic" by simp
  have "subst_valuation F \<rho> \<theta> v =
      subst_valuation F \<rho> (\<lambda>_. None) v"
    using type_subst_semantic_agree[where \<theta>=\<theta> and \<sigma>="\<lambda>_. None"
        and ty=generic and v=v and F=F and \<rho>=\<rho>, OF _ occurs]
      instantiated empty by simp
  then show "subst_valuation F \<rho> \<theta> v = \<rho> v"
    by (simp add: subst_valuation_def)
qed

definition add_definition_frame ::
  "frame \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> ((hname \<Rightarrow> ZF) \<Rightarrow> ZF) \<Rightarrow> frame" where
  "add_definition_frame F n generic C = F\<lparr>
    const_scheme := (const_scheme F)(n := Some generic),
    const_denote := (const_denote F)(n := C)\<rparr>"
lemma add_definition_frame_wf:
  assumes "frame_wf F"
    "\<forall>\<rho> \<sigma>. (\<forall>v. type_var_occurs v generic \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow> C \<rho> = C \<sigma>"
  shows "frame_wf (add_definition_frame F n generic C)"
  using assms by (auto simp: frame_wf_def add_definition_frame_def split: if_splits)
lemma interp_type_add_definition [simp]:
  "interp_type (add_definition_frame F n generic C) \<rho> ty =
    interp_type F \<rho> ty"
proof (induction ty)
  case (TyVar x)
  then show ?case by simp
next
  case (TyApp x args)
  have maps: "map (interp_type (add_definition_frame F n generic C) \<rho>) args =
      map (interp_type F \<rho>) args"
    using TyApp.IH by (intro map_cong) auto
  show ?case
    by (simp only: interp_type.simps maps; simp add: add_definition_frame_def)
qed

lemma const_sem_add_definition_other:
  assumes other: "m \<noteq> n"
  shows "const_sem (add_definition_frame F n generic C) \<rho> m ty =
    const_sem F \<rho> m ty"
proof (cases "m = NEq")
  case True
  show ?thesis
  proof (cases "classify_equality_type ty")
    case (Equality_Instance a)
    have interp: "interp_type (add_definition_frame F n generic C) \<rho> a =
        interp_type F \<rho> a" by (rule interp_type_add_definition)
    show ?thesis using True Equality_Instance interp by (simp add: const_sem_def)
  qed (simp_all add: True const_sem_def)
next
  case False
  show ?thesis
  proof (cases "const_scheme F m")
    case None
    then show ?thesis using False other
      by (simp add: const_sem_def add_definition_frame_def)
  next
    case (Some g)
    have old_scheme: "const_scheme F m = Some g" using Some .
    have new_scheme: "const_scheme (add_definition_frame F n generic C) m =
        Some g"
      using other old_scheme by (simp add: add_definition_frame_def)
    show ?thesis
    proof (cases "type_match g ty (\<lambda>_. None)")
      case None
      then show ?thesis using False old_scheme new_scheme
        by (simp add: const_sem_def)
    next
      case (Some \<theta>)
      have match: "type_match g ty (\<lambda>_. None) = Some \<theta>" using Some .
      have valuation: "subst_valuation (add_definition_frame F n generic C) \<rho> \<theta> =
          subst_valuation F \<rho> \<theta>"
        by (rule ext) (simp add: subst_valuation_def split: option.splits)
      have denote: "const_denote (add_definition_frame F n generic C) m =
          const_denote F m"
        using other by (simp add: add_definition_frame_def)
      have lhs: "const_sem (add_definition_frame F n generic C) \<rho> m ty =
          const_denote (add_definition_frame F n generic C) m
            (subst_valuation (add_definition_frame F n generic C) \<rho> \<theta>)"
        using const_sem_non_equality[OF False new_scheme match] .
      have rhs: "const_sem F \<rho> m ty =
          const_denote F m (subst_valuation F \<rho> \<theta>)"
        using const_sem_non_equality[OF False old_scheme match] .
      show ?thesis using lhs rhs valuation denote by simp
    qed
  qed
qed

lemma eval_add_definition_unchanged:  assumes "const_tab thy n = None" "check_open_term thy envty t"
  shows "eval_term (add_definition_frame F n generic C) \<rho> \<nu> env t =
    eval_term F \<rho> \<nu> env t"
  using assms
proof (induction t arbitrary: envty env)
  case (Const m ty)
  then have "m \<noteq> n" by auto
  then show ?case using const_sem_add_definition_other by simp
qed auto

lemma const_sem_add_definition_same:
  assumes "n \<noteq> NEq" "type_match generic ty (\<lambda>_. None) = Some \<theta>"
  shows "const_sem (add_definition_frame F n generic C) \<rho> n ty =
    C (subst_valuation F \<rho> \<theta>)"
proof -
  have new_scheme: "const_scheme (add_definition_frame F n generic C) n =
      Some generic"
    by (simp add: add_definition_frame_def)
  have valuation: "subst_valuation (add_definition_frame F n generic C) \<rho> \<theta> =
      subst_valuation F \<rho> \<theta>"
    by (rule ext) (simp add: subst_valuation_def split: option.splits)
  show ?thesis using assms new_scheme valuation
    by (simp add: const_sem_def add_definition_frame_def)
qed

lemma check_open_term_result_type:
  assumes thy_wf: "wf_theory thy"
    and checked: "check_open_term thy env t"
    and typed: "type_of t = Some ty"
  shows "check_type thy ty"
  using checked typed
proof (induction t arbitrary: env ty)
  case (FVar n aty)
  then show ?case by simp
next
  case (BVar i aty)
  then show ?case by simp
next
  case (Const n aty)
  then show ?case by simp
next
  case (Comb f x)
  then obtain dty rty where
      f_type: "type_of f = Some (TyApp NFun [dty, rty])"
    and x_type: "type_of x = Some dty" and result: "ty = rty"
    by (auto split: option.splits htype.splits hname.splits list.splits if_splits)
  have f_checked: "check_open_term thy env f" using Comb.prems by simp
  have fun_checked: "check_type thy (TyApp NFun [dty, rty])"
    using Comb.IH(1)[OF f_checked f_type] .
  show ?case using fun_checked result by simp
next
  case (Abs aty body)
  then obtain bty where body_type: "type_of body = Some bty"
    and result: "ty = mk_fun aty bty"
    by (auto split: option.splits)
  have aty_checked: "check_type thy aty"
    and body_checked: "check_open_term thy (aty # env) body"
    using Abs.prems by auto
  have bty_checked: "check_type thy bty"
    using Abs.IH[OF body_checked body_type] .
  show ?case using thy_wf aty_checked bty_checked result
    by (simp add: wf_theory_def mk_fun_def)
qed

lemma distinct_type_vars_acc:
  assumes "distinct acc"
  shows "distinct (type_vars_acc ty acc)"
  using assms
proof (induction ty arbitrary: acc)
  case (TyVar n)
  then show ?case by simp
next
  case (TyApp n args)
  then show ?case by (induction args arbitrary: acc) auto
qed

lemma distinct_term_type_vars_acc:
  assumes "distinct acc"
  shows "distinct (term_type_vars_acc t acc)"
  using assms
  by (induction t arbitrary: acc)
     (auto intro: distinct_type_vars_acc)

lemma distinct_term_type_vars [simp]: "distinct (term_type_vars t)"
  by (simp add: term_type_vars_def distinct_term_type_vars_acc)

definition list_type_valuation ::
  "hname list \<Rightarrow> ZF list \<Rightarrow> hname \<Rightarrow> ZF" where
  "list_type_valuation vs args v =
    (case map_of (zip vs args) v of Some A \<Rightarrow> A | None \<Rightarrow> zbool)"

lemma list_type_valuation_map:
  assumes "distinct vs" "v \<in> set vs"
  shows "list_type_valuation vs (map \<rho> vs) v = \<rho> v"
  using assms
  by (induction vs) (auto simp: list_type_valuation_def)

lemma list_type_valuation_ok:
  assumes args_ok: "list_all inhabited args"
  shows "type_valuation_ok (list_type_valuation vs args)"
  unfolding type_valuation_ok_def
proof
  fix v
  show "inhabited (list_type_valuation vs args v)"
  proof (cases "map_of (zip vs args) v")
    case None
    have "inhabited zbool"
      unfolding inhabited_def using zfalse_in_zbool by blast
    then show ?thesis using None by (simp add: list_type_valuation_def)
  next
    case (Some A)
    have pair: "(v, A) \<in> set (zip vs args)"
      using map_of_SomeD[OF Some] .
    have member: "A \<in> set args"
      using pair
    proof (induction vs arbitrary: args)
      case Nil
      then show ?case by simp
    next
      case (Cons x xs)
      then show ?case by (cases args) auto
    qed
    have "inhabited A"
      using args_ok member by (simp add: list_all_iff)
    then show ?thesis using Some by (simp add: list_type_valuation_def)
  qed
qed
definition add_type_definition_frame ::
  "frame \<Rightarrow> hname \<Rightarrow> (ZF list \<Rightarrow> ZF) \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> ((hname \<Rightarrow> ZF) \<Rightarrow> ZF) \<Rightarrow>
    hname \<Rightarrow> htype \<Rightarrow> ((hname \<Rightarrow> ZF) \<Rightarrow> ZF) \<Rightarrow> frame" where
  "add_type_definition_frame F tn D an ag A rn rg R = F\<lparr>
    tyop_denote := (tyop_denote F)(tn := D),
    const_scheme := (const_scheme F)(an := Some ag, rn := Some rg),
    const_denote := (const_denote F)(an := A, rn := R)\<rparr>"

lemma add_type_definition_frame_factor:
  assumes "an \<noteq> rn"
  shows "add_type_definition_frame F tn D an ag A rn rg R =
    add_definition_frame
      (add_definition_frame (add_type_frame F tn D) an ag A) rn rg R"
  using assms
  by (cases F)
     (auto simp: add_type_definition_frame_def add_definition_frame_def
       add_type_frame_def fun_eq_iff)

lemma interp_type_tyop_denote_cong:
  assumes denotations: "tyop_denote F = tyop_denote G"
  shows "interp_type F \<rho> ty = interp_type G \<rho> ty"
proof (induction ty)
  case (TyVar v)
  then show ?case by simp
next
  case (TyApp n args)
  have maps: "map (interp_type F \<rho>) args = map (interp_type G \<rho>) args"
  proof (rule map_cong)
    show "args = args" by simp
  next
    fix ty
    assume "ty \<in> set args"
    then show "interp_type F \<rho> ty = interp_type G \<rho> ty"
      using TyApp.IH by blast
  qed
  show ?case
  proof (cases "n = NFun")
    case True
    have case_eq: "(case map (interp_type F \<rho>) args of
          [] \<Rightarrow> zbool | [A] \<Rightarrow> zbool | [A, B] \<Rightarrow> Fun A B | _ \<Rightarrow> zbool) =
        (case map (interp_type G \<rho>) args of
          [] \<Rightarrow> zbool | [A] \<Rightarrow> zbool | [A, B] \<Rightarrow> Fun A B | _ \<Rightarrow> zbool)"
      using arg_cong[where f="\<lambda>xs. case xs of
          [] \<Rightarrow> zbool | [A] \<Rightarrow> zbool | [A, B] \<Rightarrow> Fun A B | _ \<Rightarrow> zbool", OF maps] .
    show ?thesis using True case_eq by simp
  next
    case not_fun: False
    show ?thesis
    proof (cases "n = NBool")
      case True
      then show ?thesis using not_fun by simp
    next
      case not_bool: False
      have operator: "tyop_denote F n = tyop_denote G n"
        using fun_cong[OF denotations, of n] .
      have argument: "tyop_denote G n (map (interp_type F \<rho>) args) =
          tyop_denote G n (map (interp_type G \<rho>) args)"
        using arg_cong[where f="tyop_denote G n", OF maps] .
      show ?thesis using not_fun not_bool operator argument by simp
    qed
  qed
qed

lemma interp_type_add_type_definition_new [simp]:
  assumes "tn \<noteq> NFun" "tn \<noteq> NBool"
  shows "interp_type (add_type_definition_frame F tn D an ag A rn rg R) \<rho>
      (TyApp tn (map TyVar tvs)) = D (map \<rho> tvs)"
  using assms
  by (simp add: add_type_definition_frame_def comp_def)

lemma interp_type_add_type_definition_old:
  assumes fresh: "tyops thy tn = None" and checked: "check_type thy ty"
  shows "interp_type (add_type_definition_frame F tn D an ag A rn rg R) \<rho> ty =
    interp_type F \<rho> ty"
proof -
  have same: "interp_type
      (add_type_definition_frame F tn D an ag A rn rg R) \<rho> ty =
      interp_type (add_type_frame F tn D) \<rho> ty"
  proof (rule interp_type_tyop_denote_cong)
    show "tyop_denote (add_type_definition_frame F tn D an ag A rn rg R) =
        tyop_denote (add_type_frame F tn D)"
      by (simp add: add_type_definition_frame_def add_type_frame_def)
  qed
  show ?thesis using same interp_type_add_type_unchanged[OF fresh checked] by simp
qed

lemma eval_add_type_definition_unchanged:
  assumes type_fresh: "tyops thy tn = None"
    and abs_fresh: "const_tab thy an = None"
    and rep_fresh: "const_tab thy rn = None"
    and names: "an \<noteq> rn" and frame_ok: "frame_wf F"
    and checked: "check_open_term thy envty t"
  shows "eval_term (add_type_definition_frame F tn D an ag A rn rg R)
      \<rho> \<nu> env t = eval_term F \<rho> \<nu> env t"
proof -
  let ?F1 = "add_type_frame F tn D"
  let ?F2 = "add_definition_frame ?F1 an ag A"
  have rep_step: "eval_term (add_definition_frame ?F2 rn rg R) \<rho> \<nu> env t =
      eval_term ?F2 \<rho> \<nu> env t"
    by (rule eval_add_definition_unchanged[OF rep_fresh checked])
  have abs_step: "eval_term ?F2 \<rho> \<nu> env t = eval_term ?F1 \<rho> \<nu> env t"
    by (rule eval_add_definition_unchanged[OF abs_fresh checked])
  have type_step: "eval_term ?F1 \<rho> \<nu> env t = eval_term F \<rho> \<nu> env t"
    by (rule eval_add_type_unchanged[OF type_fresh frame_ok checked])
  show ?thesis
    using rep_step abs_step type_step add_type_definition_frame_factor[OF names]
    by simp
qed

lemma add_type_definition_frame_wf:
  assumes "frame_wf F" "tn \<noteq> NFun" "tn \<noteq> NBool"
    "\<forall>args. list_all inhabited args \<longrightarrow> inhabited (D args)"
    "an \<noteq> rn"
    "\<forall>\<rho> \<sigma>. (\<forall>v. type_var_occurs v ag \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow> A \<rho> = A \<sigma>"
    "\<forall>\<rho> \<sigma>. (\<forall>v. type_var_occurs v rg \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow> R \<rho> = R \<sigma>"
  shows "frame_wf (add_type_definition_frame F tn D an ag A rn rg R)"
  using assms
  by (auto simp: frame_wf_def add_type_definition_frame_def split: if_splits)
definition subtype_carrier :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "subtype_carrier A P = Sep A (\<lambda>x. app P x = ztrue)"

definition subtype_abs :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "subtype_abs R A = Lambda R (\<lambda>x. if Elem x A then x else chosen_member A)"

definition subtype_rep :: "ZF \<Rightarrow> ZF" where
  "subtype_rep A = Lambda A id"

definition type_definition_carrier ::
  "frame \<Rightarrow> hterm \<Rightarrow> htype \<Rightarrow> hname list \<Rightarrow> ZF list \<Rightarrow> ZF" where
  "type_definition_carrier F pred rty tvs args =
    (let \<rho> = list_type_valuation tvs args
     in subtype_carrier (interp_type F \<rho> rty)
       (eval_term F \<rho> (canonical_free_valuation F \<rho>) [] pred))"

definition type_definition_abs ::
  "frame \<Rightarrow> hterm \<Rightarrow> htype \<Rightarrow> hname list \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "type_definition_abs F pred rty tvs \<rho> =
    subtype_abs (interp_type F \<rho> rty)
      (type_definition_carrier F pred rty tvs (map \<rho> tvs))"

definition type_definition_rep ::
  "frame \<Rightarrow> hterm \<Rightarrow> htype \<Rightarrow> hname list \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "type_definition_rep F pred rty tvs \<rho> =
    subtype_rep (type_definition_carrier F pred rty tvs (map \<rho> tvs))"

lemma type_definition_carrier_map:
  assumes frame_ok: "frame_wf F" and distinct: "distinct tvs"
    and pred_vars: "set (term_type_vars pred) \<subseteq> set tvs"
    and rty_vars: "set (type_vars rty) \<subseteq> set tvs"
    and closed: "free_vars pred = []"
  shows "type_definition_carrier F pred rty tvs (map \<rho> tvs) =
    subtype_carrier (interp_type F \<rho> rty) (eval_term F \<rho> \<nu> [] pred)"
proof -
  let ?\<sigma> = "list_type_valuation tvs (map \<rho> tvs)"
  have agree: "\<And>v. v \<in> set tvs \<Longrightarrow> ?\<sigma> v = \<rho> v"
    using list_type_valuation_map[OF distinct] .
  have type_eq: "interp_type F ?\<sigma> rty = interp_type F \<rho> rty"
    using interp_type_cong_type_vars rty_vars agree by blast
  have pred_type: "eval_term F ?\<sigma> (canonical_free_valuation F ?\<sigma>) [] pred =
      eval_term F \<rho> (canonical_free_valuation F ?\<sigma>) [] pred"
    using eval_term_cong_type_vars[OF frame_ok] pred_vars agree by blast
  have pred_free: "eval_term F \<rho> (canonical_free_valuation F ?\<sigma>) [] pred =
      eval_term F \<rho> \<nu> [] pred"
    using eval_term_closed_free_valuation[OF closed] .
  show ?thesis
    using type_eq pred_type pred_free
    by (simp add: type_definition_carrier_def Let_def)
qed

lemma type_definition_abs_extensional:
  assumes aty: "aty = TyApp tn (map TyVar tvs)"
    and rty_vars: "set (type_vars rty) \<subseteq> set tvs"
    and agree: "\<And>v. type_var_occurs v (mk_fun rty aty) \<Longrightarrow> \<rho> v = \<sigma> v"
  shows "type_definition_abs F pred rty tvs \<rho> =
    type_definition_abs F pred rty tvs \<sigma>"
proof -
  have tv_agree: "\<And>v. v \<in> set tvs \<Longrightarrow> \<rho> v = \<sigma> v"
    using agree aty by (auto simp: mk_fun_def list_ex_iff)
  have maps: "map \<rho> tvs = map \<sigma> tvs"
  proof (rule map_cong)
    show "tvs = tvs" by simp
  next
    fix v
    assume "v \<in> set tvs"
    then show "\<rho> v = \<sigma> v" by (rule tv_agree)
  qed
  have types: "interp_type F \<rho> rty = interp_type F \<sigma> rty"
    using interp_type_cong_type_vars rty_vars tv_agree by blast
  show ?thesis
    unfolding type_definition_abs_def
    by (subst maps, subst types, rule refl)
qed

lemma type_definition_rep_extensional:
  assumes aty: "aty = TyApp tn (map TyVar tvs)"
    and agree: "\<And>v. type_var_occurs v (mk_fun aty rty) \<Longrightarrow> \<rho> v = \<sigma> v"
  shows "type_definition_rep F pred rty tvs \<rho> =
    type_definition_rep F pred rty tvs \<sigma>"
proof -
  have tv_agree: "\<And>v. v \<in> set tvs \<Longrightarrow> \<rho> v = \<sigma> v"
    using agree aty by (auto simp: mk_fun_def list_ex_iff)
  have maps: "map \<rho> tvs = map \<sigma> tvs"
  proof (rule map_cong)
    show "tvs = tvs" by simp
  next
    fix v
    assume "v \<in> set tvs"
    then show "\<rho> v = \<sigma> v" by (rule tv_agree)
  qed
  show ?thesis
    unfolding type_definition_rep_def
    by (subst maps, rule refl)
qed

lemma subtype_carrier_member [simp]:
  "Elem x (subtype_carrier R P) \<longleftrightarrow> Elem x R \<and> app P x = ztrue"
  by (simp add: subtype_carrier_def Sep)

lemma subtype_abs_rep_identity:
  assumes inhabited: "inhabited A" and member: "Elem x A"
    and contained: "\<And>y. Elem y A \<Longrightarrow> Elem y R"
  shows "app (subtype_abs R A) (app (subtype_rep A) x) = x"
proof -
  have xR: "Elem x R" using contained member .
  have rep: "app (subtype_rep A) x = x"
    using member by (simp add: subtype_rep_def Lambda_app)
  show ?thesis using xR member rep
    by (simp add: subtype_abs_def Lambda_app)
qed

lemma subtype_characteristic:
  assumes inhabited: "inhabited A" and xR: "Elem x R"
    and contained: "\<And>y. Elem y A \<Longrightarrow> Elem y R"
    and characteristic: "Elem x A \<longleftrightarrow> app P x = ztrue"
    and bool: "Elem (app P x) zbool"
  shows "app P x =
    app (app (zeq R)
      (app (subtype_rep A) (app (subtype_abs R A) x))) x"
proof (cases "Elem x A")
  case True
  have rep: "app (subtype_rep A) x = x"
    using True by (simp add: subtype_rep_def Lambda_app)
  have abs: "app (subtype_abs R A) x = x"
    using xR True by (simp add: subtype_abs_def Lambda_app)
  show ?thesis using True characteristic xR rep abs
    by (simp add: zeq_apply)
next
  case False
  have chosenA: "Elem (chosen_member A) A"
    using chosen_member_in[OF inhabited] .
  have chosenR: "Elem (chosen_member A) R"
    using contained[OF chosenA] .
  have abs: "app (subtype_abs R A) x = chosen_member A"
    using xR False by (simp add: subtype_abs_def Lambda_app)
  have rep: "app (subtype_rep A) (chosen_member A) = chosen_member A"
    using chosenA by (simp add: subtype_rep_def Lambda_app)
  have neq: "chosen_member A \<noteq> x" using chosenA False by blast
  have pred_false: "app P x = zfalse"
    using bool False characteristic by auto
  show ?thesis using abs rep neq xR chosenR pred_false
    by (simp add: zeq_apply)
qed

lemma subtype_carrier_inhabited:
  assumes "Elem witness A" "app P witness = ztrue"
  shows "inhabited (subtype_carrier A P)"
  using assms by (auto simp: inhabited_def subtype_carrier_def Sep)

lemma type_definition_carrier_inhabited:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and wit_wf: "wf_thm thy wit" and wit_hyps: "hyps wit = []"
    and wit_concl: "concl wit = Comb pred witness"
    and witness_type: "type_of witness = Some rty"
    and witness_valid: "valid_sequent F thy [] (Comb pred witness)"
    and args_ok: "list_all inhabited args"
  shows "inhabited (type_definition_carrier F pred rty tvs args)"
proof -
  let ?\<rho> = "list_type_valuation tvs args"
  let ?\<nu> = "canonical_free_valuation F ?\<rho>"
  have frame_ok: "frame_wf F" and constants:
      "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    using model by (auto simp: models_theory_def)
  have type_ok: "type_valuation_ok ?\<rho>"
    using list_type_valuation_ok[OF args_ok] .
  have free_ok: "free_valuation_ok F ?\<rho> ?\<nu>"
    using canonical_free_valuation_ok[OF frame_ok type_ok] .
  have witness_checked: "check_term thy witness"
    using wit_wf wit_concl
    by (auto simp: wf_thm_def check_prop_def check_term_def)
  have empty_ok: "bound_valuation_ok F ?\<rho> [] []"
    by (simp add: bound_valuation_ok_def)
  have member: "Elem (eval_term F ?\<rho> ?\<nu> [] witness)
      (interp_type F ?\<rho> rty)"
    using eval_type_sound[OF thy_wf frame_ok type_ok free_ok
        constants[rule_format, OF type_ok] empty_ok]
      witness_checked witness_type unfolding check_term_def by blast
  have truth: "app (eval_term F ?\<rho> ?\<nu> [] pred)
      (eval_term F ?\<rho> ?\<nu> [] witness) = ztrue"
    using witness_valid type_ok constants[rule_format, OF type_ok] free_ok
    by (auto simp: valid_sequent_def holds_def)
  show ?thesis
    using subtype_carrier_inhabited[OF member truth]
    by (simp add: type_definition_carrier_def Let_def)
qed

lemma subtype_rep_in_fun:
  "Elem (subtype_rep A) (Fun A A)"
  by (simp add: subtype_rep_def Elem_Lambda_Fun)

lemma subtype_abs_in_fun:
  assumes "inhabited A"
  shows "Elem (subtype_abs R A) (Fun R A)"
  using chosen_member_in[OF assms]
  by (auto simp: subtype_abs_def Elem_Lambda_Fun)

lemma subtype_rep_in_fun_contained:
  assumes "\<And>x. Elem x A \<Longrightarrow> Elem x R"
  shows "Elem (subtype_rep A) (Fun A R)"
  using assms by (auto simp: subtype_rep_def Elem_Lambda_Fun)

definition theory_contents_wf :: "htheory \<Rightarrow> bool" where
  "theory_contents_wf thy \<longleftrightarrow>
    list_all (wf_thm thy) (axiom_list thy) \<and>
    (\<forall>n th. def_tab thy n = Some th \<longrightarrow> wf_thm thy th)"

lemma holds_add_constant_unchanged:
  assumes "const_tab thy n = None" "check_term thy t"
  shows "holds (add_constant_frame F n generic) \<rho> \<nu> t \<longleftrightarrow> holds F \<rho> \<nu> t"
  using eval_add_constant_unchanged[OF assms(1), of "[]" t F generic \<rho> \<nu> "[]"] assms(2)
  by (simp add: check_term_def holds_def)

lemma valid_sequent_add_constant_unchanged:
  assumes fresh: "const_tab thy n = None"
    and contents: "list_all (check_prop thy) hs" "check_prop thy c"
    and constants: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    and valid: "valid_sequent F thy hs c"
  shows "valid_sequent (add_constant_frame F n generic) thy' hs c"
proof (unfold valid_sequent_def, intro allI impI)
  fix \<rho> \<nu>
  assume type_ok: "type_valuation_ok \<rho>"
    and new_const_ok: "const_interpretation_ok (add_constant_frame F n generic) thy' \<rho>"
    and free_ok: "free_valuation_ok (add_constant_frame F n generic) \<rho> \<nu>"
    and hyps_ok: "\<forall>h\<in>set hs. holds (add_constant_frame F n generic) \<rho> \<nu> h"
  have old_free: "free_valuation_ok F \<rho> \<nu>"
    using free_ok by (simp add: free_valuation_ok_def)
  have old_hyps: "\<forall>h\<in>set hs. holds F \<rho> \<nu> h"
    using contents(1) hyps_ok fresh
    by (auto simp: list_all_iff check_prop_def
        dest: holds_add_constant_unchanged[THEN iffD1])
  have old_concl: "holds F \<rho> \<nu> c"
    using valid type_ok constants[rule_format, OF type_ok] old_free old_hyps
    by (auto simp: valid_sequent_def)
  show "holds (add_constant_frame F n generic) \<rho> \<nu> c"
    using contents(2) fresh old_concl
    by (auto simp: check_prop_def
        dest: holds_add_constant_unchanged[THEN iffD2])
qed
definition old_free_valuation ::
  "frame \<Rightarrow> htheory \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ((hname \<times> htype) \<Rightarrow> ZF) \<Rightarrow>
    ((hname \<times> htype) \<Rightarrow> ZF)" where
  "old_free_valuation F thy \<rho> \<nu> =
    (\<lambda>(n, ty). if check_type thy ty then \<nu> (n, ty)
      else chosen_member (interp_type F \<rho> ty))"

lemma old_free_valuation_agrees:
  "check_type thy ty \<Longrightarrow> old_free_valuation F thy \<rho> \<nu> (n, ty) = \<nu> (n, ty)"
  by (simp add: old_free_valuation_def)

lemma old_free_valuation_ok:
  assumes frame_ok: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>"
    and new_free: "free_valuation_ok (add_type_frame F tn D) \<rho> \<nu>"
    and fresh: "tyops thy tn = None"
  shows "free_valuation_ok F \<rho> (old_free_valuation F thy \<rho> \<nu>)"
proof (unfold free_valuation_ok_def, intro allI)
  fix n ty
  show "Elem (old_free_valuation F thy \<rho> \<nu> (n, ty))
      (interp_type F \<rho> ty)"
  proof (cases "check_type thy ty")
    case True
    have carrier: "interp_type (add_type_frame F tn D) \<rho> ty =
        interp_type F \<rho> ty"
      using interp_type_add_type_unchanged[OF fresh True] .
    have member: "Elem (\<nu> (n, ty))
        (interp_type (add_type_frame F tn D) \<rho> ty)"
      using new_free by (auto simp: free_valuation_ok_def)
    show ?thesis using True carrier member
      by (simp add: old_free_valuation_def)
  next
    case False
    have inhabited: "inhabited (interp_type F \<rho> ty)"
      using interp_type_inhabited_any[OF frame_ok type_ok] .
    show ?thesis using False chosen_member_in[OF inhabited]
      by (simp add: old_free_valuation_def)
  qed
qed

lemma old_free_valuation_ok_cong:
  assumes frame_ok: "frame_wf F" and type_ok: "type_valuation_ok \<rho>"
    and new_free: "free_valuation_ok G \<rho> \<nu>"
    and carriers: "\<And>ty. check_type thy ty \<Longrightarrow>
      interp_type G \<rho> ty = interp_type F \<rho> ty"
  shows "free_valuation_ok F \<rho> (old_free_valuation F thy \<rho> \<nu>)"
proof (unfold free_valuation_ok_def, intro allI)
  fix n ty
  show "Elem (old_free_valuation F thy \<rho> \<nu> (n, ty))
      (interp_type F \<rho> ty)"
  proof (cases "check_type thy ty")
    case True
    have member: "Elem (\<nu> (n, ty)) (interp_type G \<rho> ty)"
      using new_free by (auto simp: free_valuation_ok_def)
    show ?thesis using True carriers[OF True] member
      by (simp add: old_free_valuation_def)
  next
    case False
    have inhabited: "inhabited (interp_type F \<rho> ty)"
      using interp_type_inhabited_any[OF frame_ok type_ok] .
    show ?thesis using False chosen_member_in[OF inhabited]
      by (simp add: old_free_valuation_def)
  qed
qed

lemma eval_old_free_valuation_unchanged:
  assumes checked: "check_open_term thy envty t"
  shows "eval_term F \<rho> (old_free_valuation F thy \<rho> \<nu>) env t =
    eval_term F \<rho> \<nu> env t"
  using checked
  by (induction t arbitrary: envty env)
    (auto simp: old_free_valuation_agrees)

lemma holds_add_type_unchanged:
  assumes fresh: "tyops thy tn = None" and frame_ok: "frame_wf F"
    and checked: "check_term thy t"
  shows "holds (add_type_frame F tn D) \<rho> \<nu> t \<longleftrightarrow>
    holds F \<rho> (old_free_valuation F thy \<rho> \<nu>) t"
proof -
  have checked_open: "check_open_term thy [] t"
    using checked by (simp add: check_term_def)
  have frame_eval: "eval_term (add_type_frame F tn D) \<rho> \<nu> [] t =
      eval_term F \<rho> \<nu> [] t"
    using eval_add_type_unchanged[OF fresh frame_ok checked_open] .
  have free_eval: "eval_term F \<rho> (old_free_valuation F thy \<rho> \<nu>) [] t =
      eval_term F \<rho> \<nu> [] t"
    using eval_old_free_valuation_unchanged[OF checked_open] .
  show ?thesis using frame_eval free_eval by (simp add: holds_def)qed

lemma valid_sequent_add_type_unchanged:
  assumes fresh: "tyops thy tn = None" and frame_ok: "frame_wf F"
    and contents: "list_all (check_prop thy) hs" "check_prop thy c"
    and constants: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    and valid: "valid_sequent F thy hs c"
  shows "valid_sequent (add_type_frame F tn D) thy' hs c"
proof (unfold valid_sequent_def, intro allI impI)
  fix \<rho> \<nu>
  assume type_ok: "type_valuation_ok \<rho>"
    and new_const_ok: "const_interpretation_ok (add_type_frame F tn D) thy' \<rho>"
    and new_free: "free_valuation_ok (add_type_frame F tn D) \<rho> \<nu>"
    and new_hyps: "\<forall>h\<in>set hs. holds (add_type_frame F tn D) \<rho> \<nu> h"
  let ?\<nu>old = "old_free_valuation F thy \<rho> \<nu>"
  have old_free: "free_valuation_ok F \<rho> ?\<nu>old"
    using old_free_valuation_ok[OF frame_ok type_ok new_free fresh] .
  have old_hyps: "\<forall>h\<in>set hs. holds F \<rho> ?\<nu>old h"
    using contents(1) new_hyps
    by (auto simp: list_all_iff check_prop_def
        dest: holds_add_type_unchanged[OF fresh frame_ok, THEN iffD1])
  have old_concl: "holds F \<rho> ?\<nu>old c"
    using valid type_ok constants[rule_format, OF type_ok] old_free old_hyps
    by (auto simp: valid_sequent_def)
  show "holds (add_type_frame F tn D) \<rho> \<nu> c"
    using contents(2) old_concl
    by (auto simp: check_prop_def
        dest: holds_add_type_unchanged[OF fresh frame_ok, THEN iffD2])
qed

lemma holds_add_type_definition_unchanged:
  assumes type_fresh: "tyops thy tn = None"
    and abs_fresh: "const_tab thy an = None"
    and rep_fresh: "const_tab thy rn = None"
    and names: "an \<noteq> rn" and frame_ok: "frame_wf F"
    and checked: "check_term thy t"
  shows "holds (add_type_definition_frame F tn D an ag A rn rg R) \<rho> \<nu> t \<longleftrightarrow>
    holds F \<rho> (old_free_valuation F thy \<rho> \<nu>) t"
proof -
  have checked_open: "check_open_term thy [] t"
    using checked by (simp add: check_term_def)
  have frame_eval: "eval_term
      (add_type_definition_frame F tn D an ag A rn rg R) \<rho> \<nu> [] t =
      eval_term F \<rho> \<nu> [] t"
    using eval_add_type_definition_unchanged[OF type_fresh abs_fresh rep_fresh
        names frame_ok checked_open] .
  have free_eval: "eval_term F \<rho> (old_free_valuation F thy \<rho> \<nu>) [] t =
      eval_term F \<rho> \<nu> [] t"
    using eval_old_free_valuation_unchanged[OF checked_open] .
  show ?thesis using frame_eval free_eval by (simp add: holds_def)
qed

lemma valid_sequent_add_type_definition_unchanged:
  assumes type_fresh: "tyops thy tn = None"
    and abs_fresh: "const_tab thy an = None"
    and rep_fresh: "const_tab thy rn = None"
    and names: "an \<noteq> rn" and frame_ok: "frame_wf F"
    and contents: "list_all (check_prop thy) hs" "check_prop thy c"
    and constants: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    and valid: "valid_sequent F thy hs c"
  shows "valid_sequent
    (add_type_definition_frame F tn D an ag A rn rg R) thy' hs c"
proof (unfold valid_sequent_def, intro allI impI)
  fix \<rho> \<nu>
  assume type_ok: "type_valuation_ok \<rho>"
    and new_const_ok: "const_interpretation_ok
      (add_type_definition_frame F tn D an ag A rn rg R) thy' \<rho>"
    and new_free: "free_valuation_ok
      (add_type_definition_frame F tn D an ag A rn rg R) \<rho> \<nu>"
    and new_hyps: "\<forall>h\<in>set hs. holds
      (add_type_definition_frame F tn D an ag A rn rg R) \<rho> \<nu> h"
  let ?\<nu>old = "old_free_valuation F thy \<rho> \<nu>"
  have old_free: "free_valuation_ok F \<rho> ?\<nu>old"
  proof (rule old_free_valuation_ok_cong[OF frame_ok type_ok new_free])
    fix ty
    assume "check_type thy ty"
    then show "interp_type
        (add_type_definition_frame F tn D an ag A rn rg R) \<rho> ty =
        interp_type F \<rho> ty"
      by (rule interp_type_add_type_definition_old[OF type_fresh])
  qed
  have old_hyps: "\<forall>h\<in>set hs. holds F \<rho> ?\<nu>old h"
    using contents(1) new_hyps
    by (auto simp: list_all_iff check_prop_def
        dest: holds_add_type_definition_unchanged[OF type_fresh abs_fresh
          rep_fresh names frame_ok, THEN iffD1])
  have old_concl: "holds F \<rho> ?\<nu>old c"
    using valid type_ok constants[rule_format, OF type_ok] old_free old_hyps
    by (auto simp: valid_sequent_def)
  show "holds (add_type_definition_frame F tn D an ag A rn rg R) \<rho> \<nu> c"
    using contents(2) old_concl
    by (auto simp: check_prop_def
        dest: holds_add_type_definition_unchanged[OF type_fresh abs_fresh
          rep_fresh names frame_ok, THEN iffD2])
qed

lemma holds_add_definition_unchanged:
  assumes "const_tab thy n = None" "check_term thy t"
  shows "holds (add_definition_frame F n generic C) \<rho> \<nu> t \<longleftrightarrow>
    holds F \<rho> \<nu> t"
  using eval_add_definition_unchanged[OF assms(1), of "[]" t F generic C \<rho> \<nu> "[]"]
    assms(2)
  by (simp add: check_term_def holds_def)

lemma valid_sequent_add_definition_unchanged:
  assumes fresh: "const_tab thy n = None"
    and contents: "list_all (check_prop thy) hs" "check_prop thy c"
    and constants: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    and valid: "valid_sequent F thy hs c"
  shows "valid_sequent (add_definition_frame F n generic C) thy' hs c"
proof (unfold valid_sequent_def, intro allI impI)
  fix \<rho> \<nu>
  assume type_ok: "type_valuation_ok \<rho>"
    and new_const_ok: "const_interpretation_ok
      (add_definition_frame F n generic C) thy' \<rho>"
    and free_ok: "free_valuation_ok (add_definition_frame F n generic C) \<rho> \<nu>"
    and hyps_ok: "\<forall>h\<in>set hs.
      holds (add_definition_frame F n generic C) \<rho> \<nu> h"
  have old_free: "free_valuation_ok F \<rho> \<nu>"
    using free_ok by (simp add: free_valuation_ok_def)
  have old_hyps: "\<forall>h\<in>set hs. holds F \<rho> \<nu> h"
    using contents(1) hyps_ok fresh
    by (auto simp: list_all_iff check_prop_def
        dest: holds_add_definition_unchanged[THEN iffD1])
  have old_concl: "holds F \<rho> \<nu> c"
    using valid type_ok constants[rule_format, OF type_ok] old_free old_hyps
    by (auto simp: valid_sequent_def)
  show "holds (add_definition_frame F n generic C) \<rho> \<nu> c"
    using contents(2) fresh old_concl
    by (auto simp: check_prop_def
        dest: holds_add_definition_unchanged[THEN iffD2])
qed

section \<open>Model extension theorems\<close>theorem new_type_conservative_from_obligations:
  assumes run: "new_type fresh thy n arity = Some thy'"
    and obligations: "preserves_old_model_obligations F thy thy'"
  shows "models_theory F thy'"
proof -
  from new_type_extract[OF run] have tables:
    "axiom_list thy' = axiom_list thy" "def_tab thy' = def_tab thy"
    by (auto simp: extend_theory_def)
  show ?thesis using obligations tables
    by (auto simp: preserves_old_model_obligations_def models_theory_def)
qed

theorem new_constant_conservative_from_obligations:
  assumes run: "new_constant fresh thy n ty = Some thy'"
    and obligations: "preserves_old_model_obligations F thy thy'"
  shows "models_theory F thy'"
proof -
  from new_constant_extract[OF run] have tables:
    "axiom_list thy' = axiom_list thy" "def_tab thy' = def_tab thy"
    by (auto simp: extend_theory_def)
  show ?thesis using obligations tables
    by (auto simp: preserves_old_model_obligations_def models_theory_def)
qed

theorem new_axiom_model_extension_from_obligations:
  assumes run: "new_axiom fresh thy p = Some (thy', th)"
    and obligations: "preserves_old_model_obligations F thy thy'"
    and axiom_valid: "valid_sequent F thy' [] p"
  shows "models_theory F thy'"
proof -
  from new_axiom_extract[OF run] have shape:
    "axiom_list thy' = th # axiom_list thy" "hyps th = []" "concl th = p"
    "def_tab thy' = def_tab thy" by auto
  show ?thesis using obligations axiom_valid shape
    by (auto simp: preserves_old_model_obligations_def models_theory_def)
qed

theorem new_basic_definition_conservative_from_obligations:
  assumes run: "new_basic_definition fresh thy tm = Some (thy', dth)"
    and obligations: "preserves_old_model_obligations F thy thy'"
    and definition_valid: "valid_sequent F thy' (hyps dth) (concl dth)"
  shows "models_theory F thy'"
proof -
  have "\<exists>n. axiom_list thy' = axiom_list thy \<and>
      def_tab thy' = (def_tab thy)(n := Some dth)"
    using run by (auto simp: new_basic_definition_def Let_def
        split: option.splits prod.splits hterm.splits if_splits)
  then obtain n where shape:
    "axiom_list thy' = axiom_list thy"
    "def_tab thy' = (def_tab thy)(n := Some dth)" by blast
  show ?thesis using obligations definition_valid shape
    by (auto simp: preserves_old_model_obligations_def models_theory_def
        split: if_splits)
qed

theorem new_basic_type_definition_conservative_from_obligations:
  assumes run: "new_basic_type_definition fresh thy tn an rn wit =
      Some (thy', th1, th2)"
    and obligations: "preserves_old_model_obligations F thy thy'"
  shows "models_theory F thy'"
proof -
  from new_basic_type_definition_extract[OF run] have tables:
    "axiom_list thy' = axiom_list thy" "def_tab thy' = def_tab thy" by auto
  show ?thesis using obligations tables
    by (auto simp: preserves_old_model_obligations_def models_theory_def)
qed
theorem new_type_conservative:
  assumes run: "new_type fresh thy n arity = Some thy'"
    and thy_wf: "wf_theory thy"
    and contents_wf: "theory_contents_wf thy"
    and model: "models_theory F thy"
  shows "models_theory (add_type_frame F n (\<lambda>_. zbool)) thy'"
proof -
  from new_type_extract[OF run] have fresh_name: "tyops thy n = None"
    and shape: "thy' = extend_theory fresh thy
      ((tyops thy)(n := Some arity)) (const_tab thy)
      (axiom_list thy) (def_tab thy)"
    by blast+
  have n_not_fun: "n \<noteq> NFun" and n_not_bool: "n \<noteq> NBool"
    using fresh_name thy_wf by (auto simp: wf_theory_def)
  have old_frame: "frame_wf F"
    using model by (simp add: models_theory_def)
  have frame_ok: "frame_wf (add_type_frame F n (\<lambda>_. zbool))"
    using add_type_frame_wf[OF old_frame n_not_fun n_not_bool,
        where D="\<lambda>_. zbool"] zfalse_in_zbool
    by (auto simp: inhabited_def)  have old_constants:
    "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    using model by (auto simp: models_theory_def)
  have new_constants:
    "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
      const_interpretation_ok (add_type_frame F n (\<lambda>_. zbool)) thy' \<rho>"
  proof (intro allI impI)
    fix \<rho>
    assume rho_ok: "type_valuation_ok \<rho>"
    show "const_interpretation_ok (add_type_frame F n (\<lambda>_. zbool)) thy' \<rho>"
      unfolding const_interpretation_ok_def
    proof (intro allI impI)
      fix m generic \<sigma>
      assume sigma_ok: "type_valuation_ok \<sigma>"
        and tab': "const_tab thy' m = Some generic"
      have old_tab: "const_tab thy m = Some generic"
        using tab' shape by (simp add: extend_theory_def)
      have checked: "check_type thy generic"
        using thy_wf old_tab by (auto simp: wf_theory_def)
      have old_ok: "const_interpretation_ok F thy \<sigma>"
        using old_constants sigma_ok by blast
      have old_entry: "const_scheme F m = Some generic \<and>
          Elem (const_denote F m \<sigma>) (interp_type F \<sigma> generic)"
        using old_ok sigma_ok old_tab
        by (auto simp: const_interpretation_ok_def)
      have carrier: "interp_type (add_type_frame F n (\<lambda>_. zbool)) \<sigma> generic =
          interp_type F \<sigma> generic"
        using interp_type_add_type_unchanged[OF fresh_name checked] .
      show "const_scheme (add_type_frame F n (\<lambda>_. zbool)) m = Some generic \<and>
          Elem (const_denote (add_type_frame F n (\<lambda>_. zbool)) m \<sigma>)
            (interp_type (add_type_frame F n (\<lambda>_. zbool)) \<sigma> generic)"
        using old_entry carrier by (simp add: add_type_frame_def)
    qed
  qed
  have axiom_checks: "\<forall>th\<in>set (axiom_list thy).
      list_all (check_prop thy) (hyps th) \<and> check_prop thy (concl th)"
    using contents_wf
    by (auto simp: theory_contents_wf_def wf_thm_def list_all_iff)
  have definition_checks: "\<forall>m th. def_tab thy m = Some th \<longrightarrow>
      list_all (check_prop thy) (hyps th) \<and> check_prop thy (concl th)"
    using contents_wf by (auto simp: theory_contents_wf_def wf_thm_def)
  show ?thesis
    unfolding models_theory_def
  proof (intro conjI)
    show "frame_wf (add_type_frame F n (\<lambda>_. zbool))" using frame_ok .
    show "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
        const_interpretation_ok (add_type_frame F n (\<lambda>_. zbool)) thy' \<rho>"
      using new_constants .
    show "\<forall>th\<in>set (axiom_list thy').
        valid_sequent (add_type_frame F n (\<lambda>_. zbool)) thy'
          (hyps th) (concl th)"
      using model axiom_checks shape old_constants old_frame
      by (auto simp: models_theory_def extend_theory_def
          intro!: valid_sequent_add_type_unchanged[OF fresh_name old_frame])
    show "\<forall>m th. def_tab thy' m = Some th \<longrightarrow>
        valid_sequent (add_type_frame F n (\<lambda>_. zbool)) thy'
          (hyps th) (concl th)"
      using model definition_checks shape old_constants old_frame
      by (auto simp: models_theory_def extend_theory_def
          intro!: valid_sequent_add_type_unchanged[OF fresh_name old_frame])
  qed
qed

theorem new_constant_conservative:  assumes run: "new_constant fresh thy n ty = Some thy'"
    and thy_wf: "wf_theory thy"
    and contents_wf: "theory_contents_wf thy"
    and model: "models_theory F thy"
  shows "models_theory (add_constant_frame F n ty) thy'"
proof -
  from new_constant_extract[OF run] have fresh_name: "const_tab thy n = None"
    and type_checked: "check_type thy ty"
    and shape: "thy' = extend_theory fresh thy (tyops thy)
      ((const_tab thy)(n := Some ty)) (axiom_list thy) (def_tab thy)"
    by blast+
  have n_not_eq: "n \<noteq> NEq"
    using fresh_name thy_wf by (auto simp: wf_theory_def)
  have old_frame: "frame_wf F" using model by (simp add: models_theory_def)
  have frame_ok: "frame_wf (add_constant_frame F n ty)"
    using add_constant_frame_wf[OF old_frame] .
  have old_constants:
    "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    using model by (auto simp: models_theory_def)
  have new_constants:
    "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
      const_interpretation_ok (add_constant_frame F n ty) thy' \<rho>"
  proof (intro allI impI)
    fix \<rho>
    assume rho_ok: "type_valuation_ok \<rho>"
    show "const_interpretation_ok (add_constant_frame F n ty) thy' \<rho>"
      unfolding const_interpretation_ok_def
    proof (intro allI impI)
      fix m generic \<sigma>
      assume sigma_ok: "type_valuation_ok \<sigma>"
        and tab': "const_tab thy' m = Some generic"
      have carrier: "interp_type (add_constant_frame F n ty) \<sigma> generic =
          interp_type F \<sigma> generic"
        by (rule interp_type_add_constant)
      show "const_scheme (add_constant_frame F n ty) m = Some generic \<and>
          Elem (const_denote (add_constant_frame F n ty) m \<sigma>)
            (interp_type (add_constant_frame F n ty) \<sigma> generic)"
      proof (cases "m = n")
        case True
        have generic_ty: "generic = ty"
          using tab' True shape by (simp add: extend_theory_def)
        have inhabited: "inhabited (interp_type F \<sigma> ty)"
          using interp_type_inhabited_any[OF old_frame sigma_ok] .
        show ?thesis
          using True generic_ty carrier chosen_member_in[OF inhabited]
          by (simp add: add_constant_frame_def)
      next
        case False
        have old_tab: "const_tab thy m = Some generic"
          using tab' False shape by (simp add: extend_theory_def)
        have old_ok: "const_interpretation_ok F thy \<sigma>"
          using old_constants sigma_ok by blast
        have old_entry: "const_scheme F m = Some generic \<and>
            Elem (const_denote F m \<sigma>) (interp_type F \<sigma> generic)"
          using old_ok sigma_ok old_tab
          by (auto simp: const_interpretation_ok_def)
        show ?thesis using False carrier old_entry
          by (simp add: add_constant_frame_def)
      qed
    qed
  qed
  have axiom_checks: "\<forall>th\<in>set (axiom_list thy).      list_all (check_prop thy) (hyps th) \<and> check_prop thy (concl th)"
    using contents_wf by (auto simp: theory_contents_wf_def wf_thm_def list_all_iff)
  have definition_checks: "\<forall>m th. def_tab thy m = Some th \<longrightarrow>
      list_all (check_prop thy) (hyps th) \<and> check_prop thy (concl th)"
    using contents_wf by (auto simp: theory_contents_wf_def wf_thm_def)
  show ?thesis
    unfolding models_theory_def
  proof (intro conjI)
    show "frame_wf (add_constant_frame F n ty)" using frame_ok .
    show "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
        const_interpretation_ok (add_constant_frame F n ty) thy' \<rho>"
      using new_constants .
    show "\<forall>th\<in>set (axiom_list thy').
        valid_sequent (add_constant_frame F n ty) thy' (hyps th) (concl th)"
      using model axiom_checks fresh_name old_constants shape
      by (auto simp: models_theory_def extend_theory_def
          intro!: valid_sequent_add_constant_unchanged)
    show "\<forall>m th. def_tab thy' m = Some th \<longrightarrow>
        valid_sequent (add_constant_frame F n ty) thy' (hyps th) (concl th)"
      using model definition_checks fresh_name old_constants shape
      by (auto simp: models_theory_def extend_theory_def
          intro!: valid_sequent_add_constant_unchanged)
  qed
qed
theorem new_axiom_model_extension:
  assumes run: "new_axiom fresh thy p = Some (thy', th)"
    and model: "models_theory F thy"
    and axiom_valid: "valid_sequent F thy' [] p"
  shows "models_theory F thy'"
proof -
  from new_axiom_extract[OF run] have shape:
    "const_tab thy' = const_tab thy"
    "axiom_list thy' = th # axiom_list thy"
    "def_tab thy' = def_tab thy"
    "hyps th = []" "concl th = p"
    by auto
  have const_equiv: "const_interpretation_ok F thy' \<rho> \<longleftrightarrow>
      const_interpretation_ok F thy \<rho>" for \<rho>
    using shape(1) by (simp add: const_interpretation_ok_def)
  have old_valid: "valid_sequent F thy hs c \<Longrightarrow>
      valid_sequent F thy' hs c" for hs c
    using const_equiv by (auto simp: valid_sequent_def)
  have new_constants: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
      const_interpretation_ok F thy' \<rho>"
    using model const_equiv by (auto simp: models_theory_def)
  show ?thesis using model axiom_valid shape old_valid new_constants
    by (auto simp: models_theory_def)
qed

theorem new_basic_definition_conservative:  assumes run: "new_basic_definition fresh thy tm = Some (thy', dth)"
    and thy_wf: "wf_theory thy"
    and contents_wf: "theory_contents_wf thy"
    and model: "models_theory F thy"
  obtains n ty rhs where
    "dest_eq tm = Some (FVar n ty, rhs)"
    "dth = \<lparr>hyps = [], concl = eq_term ty (Const n ty) rhs,
      thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    "models_theory
      (add_definition_frame F n ty (closed_term_denote F rhs)) thy'"
    "valid_sequent
      (add_definition_frame F n ty (closed_term_denote F rhs))
      thy' [] (concl dth)"
proof -
  obtain n ty rhs where dest: "dest_eq tm = Some (FVar n ty, rhs)"
    and fresh_name: "const_tab thy n = None"
    and rhs_checked: "check_term thy rhs"
    and rhs_closed: "free_vars rhs = []"
    and rhs_type: "type_of rhs = Some ty"
    and rhs_vars: "set (term_type_vars rhs) \<subseteq> set (type_vars ty)"
    and dth: "dth = \<lparr>hyps = [], concl = eq_term ty (Const n ty) rhs,
      thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    and shape: "thy' = \<lparr>tyops = tyops thy,
      const_tab = (const_tab thy)(n := Some ty),
      axiom_list = axiom_list thy,
      def_tab = (def_tab thy)(n := Some dth),
      thy_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    and dth_wf: "wf_thm thy' dth"
    using new_basic_definition_extract[OF run] by blast
  let ?C = "closed_term_denote F rhs"
  let ?F' = "add_definition_frame F n ty ?C"
  have n_not_eq: "n \<noteq> NEq"
    using fresh_name thy_wf by (auto simp: wf_theory_def)
  have old_frame: "frame_wf F"
    using model by (simp add: models_theory_def)
  have C_extensional: "\<forall>\<rho> \<sigma>.
      (\<forall>v. type_var_occurs v ty \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow> ?C \<rho> = ?C \<sigma>"
    using closed_term_denote_extensional[OF old_frame rhs_closed rhs_vars]
    by blast
  have frame_ok: "frame_wf ?F'"
    using add_definition_frame_wf[OF old_frame C_extensional] .
  have old_constants:
    "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    using model by (auto simp: models_theory_def)
  have new_constants:
    "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok ?F' thy' \<rho>"
  proof (intro allI impI)
    fix \<rho>
    assume rho_ok: "type_valuation_ok \<rho>"
    show "const_interpretation_ok ?F' thy' \<rho>"
      unfolding const_interpretation_ok_def
    proof (intro allI impI)
      fix m generic \<sigma>
      assume sigma_ok: "type_valuation_ok \<sigma>"
        and tab': "const_tab thy' m = Some generic"
      have carrier: "interp_type ?F' \<sigma> generic = interp_type F \<sigma> generic"
        by (rule interp_type_add_definition)
      show "const_scheme ?F' m = Some generic \<and>
          Elem (const_denote ?F' m \<sigma>) (interp_type ?F' \<sigma> generic)"      proof (cases "m = n")
        case True
        have generic_ty: "generic = ty"
          using tab' True shape by simp
        have old_const_ok: "const_interpretation_ok F thy \<sigma>"
          using old_constants sigma_ok by blast
        have canonical_ok: "free_valuation_ok F \<sigma>
            (canonical_free_valuation F \<sigma>)"
          using canonical_free_valuation_ok[OF old_frame sigma_ok] .
        have empty_ok: "bound_valuation_ok F \<sigma> [] []"
          by (simp add: bound_valuation_ok_def)
        have member: "Elem (?C \<sigma>) (interp_type F \<sigma> ty)"
          unfolding closed_term_denote_def
          using eval_type_sound[OF thy_wf old_frame sigma_ok canonical_ok
              old_const_ok empty_ok]
            rhs_checked rhs_type unfolding check_term_def by blast
        show ?thesis using True generic_ty member carrier
          by (simp add: add_definition_frame_def)
      next
        case False
        have old_tab: "const_tab thy m = Some generic"
          using tab' False shape by simp
        have old_ok: "const_interpretation_ok F thy \<sigma>"
          using old_constants sigma_ok by blast
        have old_entry: "const_scheme F m = Some generic \<and>
            Elem (const_denote F m \<sigma>) (interp_type F \<sigma> generic)"
          using old_ok sigma_ok old_tab
          by (auto simp: const_interpretation_ok_def)
        show ?thesis using False old_entry carrier
          by (simp add: add_definition_frame_def)      qed
    qed
  qed
  have equation_checked: "check_term thy'
      (eq_term ty (Const n ty) rhs)"
    using dth_wf dth by (simp add: wf_thm_def check_prop_def)
  have const_checked: "check_term thy' (Const n ty)"
    using equation_checked unfolding check_term_def eq_term_def by auto
  have rhs_checked': "check_term thy' rhs"
    using equation_checked unfolding check_term_def eq_term_def by auto
  have ty_checked': "check_type thy' ty"
    using const_checked by (auto simp: check_term_def split: option.splits)
  have same_tyops: "tyops thy' = tyops thy" using shape by simp
  have all_types_checked: "\<forall>m generic. const_tab thy' m = Some generic \<longrightarrow>
      check_type thy' generic"
  proof (intro allI impI)
    fix m generic
    assume tab': "const_tab thy' m = Some generic"
    show "check_type thy' generic"
    proof (cases "m = n")
      case True
      then show ?thesis using tab' shape ty_checked' by simp
    next
      case False
      have old_tab: "const_tab thy m = Some generic"
        using tab' shape False by simp
      have old_checked: "check_type thy generic"
        using thy_wf old_tab by (auto simp: wf_theory_def)
      show ?thesis
        using check_type_tyops_cong[OF same_tyops, of generic] old_checked by simp
    qed
  qed
  have thy'_wf: "wf_theory thy'"
    using thy_wf n_not_eq shape all_types_checked
    by (auto simp: wf_theory_def)
  have definition_valid: "valid_sequent ?F' thy' [] (concl dth)"
  proof (unfold valid_sequent_def, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok ?F' thy' \<rho>"
      and free_ok: "free_valuation_ok ?F' \<rho> \<nu>"
    have new_tab: "const_tab thy' n = Some ty" using shape by simp
    obtain \<theta> where match: "type_match ty ty (\<lambda>_. None) = Some \<theta>"
      using const_checked new_tab
      by (auto simp: check_term_def split: option.splits)
    have instantiated: "type_subst \<theta> ty = ty"
      using type_match_sound[OF match] .
    have const_value: "eval_term ?F' \<rho> \<nu> [] (Const n ty) = ?C \<rho>"
      using const_sem_add_definition_same[OF n_not_eq match]
        closed_term_denote_matched[OF old_frame rhs_closed rhs_vars instantiated]
      by simp
    have rhs_open: "check_open_term thy [] rhs"
      using rhs_checked unfolding check_term_def .
    have rhs_frame: "eval_term ?F' \<rho> \<nu> [] rhs = eval_term F \<rho> \<nu> [] rhs"
      using eval_add_definition_unchanged[where thy=thy and n=n and envty="[]"
          and t=rhs and F=F and generic=ty and C="closed_term_denote F rhs"
          and \<rho>=\<rho> and \<nu>=\<nu> and env="[]", OF fresh_name rhs_open] .    have rhs_free: "eval_term F \<rho> \<nu> [] rhs = ?C \<rho>"
      using eval_term_closed_free_valuation[where F=F and \<rho>=\<rho> and \<nu>=\<nu>
          and \<mu>="canonical_free_valuation F \<rho>" and env="[]" and t=rhs,
          OF rhs_closed]
      by (simp add: closed_term_denote_def)
    have equality: "eval_term ?F' \<rho> \<nu> [] (Const n ty) =
        eval_term ?F' \<rho> \<nu> [] rhs"
      using const_value rhs_frame rhs_free by simp
    show "holds ?F' \<rho> \<nu> (concl dth)"
      using holds_eq_iff[OF thy'_wf frame_ok type_ok free_ok const_ok
          const_checked _ rhs_checked' _]
        equality dth rhs_type
      by simp  qed
  have axiom_checks: "\<forall>th\<in>set (axiom_list thy).
      list_all (check_prop thy) (hyps th) \<and> check_prop thy (concl th)"
    using contents_wf
    by (auto simp: theory_contents_wf_def wf_thm_def list_all_iff)
  have definition_checks: "\<forall>m th. def_tab thy m = Some th \<longrightarrow>
      list_all (check_prop thy) (hyps th) \<and> check_prop thy (concl th)"
    using contents_wf by (auto simp: theory_contents_wf_def wf_thm_def)
  have final_model: "models_theory ?F' thy'"
    unfolding models_theory_def
  proof (intro conjI)
    show "frame_wf ?F'" using frame_ok .
    show "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok ?F' thy' \<rho>"
      using new_constants .
    show "\<forall>th\<in>set (axiom_list thy').
        valid_sequent ?F' thy' (hyps th) (concl th)"
      using model axiom_checks shape old_constants
      by (auto simp: models_theory_def
          intro!: valid_sequent_add_definition_unchanged[OF fresh_name])
    show "\<forall>m th. def_tab thy' m = Some th \<longrightarrow>
        valid_sequent ?F' thy' (hyps th) (concl th)"
      using model definition_checks shape old_constants definition_valid dth
      by (auto simp: models_theory_def split: if_splits
          intro!: valid_sequent_add_definition_unchanged[OF fresh_name])
  qed
  show thesis using that[OF dest dth final_model definition_valid] .
qed

lemma subst_valuation_fixed_type:
  assumes fixed: "type_subst \<theta> ty = ty"
    and occurs: "type_var_occurs v ty"
  shows "subst_valuation F \<rho> \<theta> v = \<rho> v"
  using fixed occurs
proof (induction ty)
  case (TyVar n)
  then show ?case
    by (cases "\<theta> n") (auto simp: subst_valuation_def)
next
  case (TyApp n args)
  then obtain arg where arg: "arg \<in> set args"
    and in_arg: "type_var_occurs v arg"
    by (auto simp: list_ex_iff)
  have fixed_args: "map (type_subst \<theta>) args = args"
    using TyApp.prems(1) by simp
  have fixed_arg: "type_subst \<theta> arg = arg"
    using fixed_args arg
    by (metis in_set_conv_nth nth_map)
  show ?case using TyApp.IH[OF arg fixed_arg in_arg] .
qed

lemma const_sem_add_type_definition_abs_same:
  assumes an_not_eq: "an \<noteq> NEq" and names: "an \<noteq> rn"
    and match: "type_match ag ag (\<lambda>_. None) = Some \<theta>"
    and extensional: "\<forall>\<rho> \<sigma>.
      (\<forall>v. type_var_occurs v ag \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow> A \<rho> = A \<sigma>"
  shows "const_sem (add_type_definition_frame F tn D an ag A rn rg R)
      \<rho> an ag = A \<rho>"
proof -
  let ?F' = "add_type_definition_frame F tn D an ag A rn rg R"
  have scheme: "const_scheme ?F' an = Some ag"
    using names by (simp add: add_type_definition_frame_def)
  have raw: "const_sem ?F' \<rho> an ag =
      const_denote ?F' an (subst_valuation ?F' \<rho> \<theta>)"
    using const_sem_non_equality[OF an_not_eq scheme match] .
  have fixed: "type_subst \<theta> ag = ag" using type_match_sound[OF match] .
  have agree: "\<forall>v. type_var_occurs v ag \<longrightarrow>
      subst_valuation ?F' \<rho> \<theta> v = \<rho> v"
    using subst_valuation_fixed_type[OF fixed] by blast
  have denotation: "A (subst_valuation ?F' \<rho> \<theta>) = A \<rho>"
    using extensional agree by blast
  show ?thesis using raw denotation names
    by (simp add: add_type_definition_frame_def)
qed

lemma const_sem_add_type_definition_rep_same:
  assumes rn_not_eq: "rn \<noteq> NEq" and names: "an \<noteq> rn"
    and match: "type_match rg rg (\<lambda>_. None) = Some \<theta>"
    and extensional: "\<forall>\<rho> \<sigma>.
      (\<forall>v. type_var_occurs v rg \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow> R \<rho> = R \<sigma>"
  shows "const_sem (add_type_definition_frame F tn D an ag A rn rg R)
      \<rho> rn rg = R \<rho>"
proof -
  let ?F' = "add_type_definition_frame F tn D an ag A rn rg R"
  have scheme: "const_scheme ?F' rn = Some rg"
    using names by (simp add: add_type_definition_frame_def)
  have raw: "const_sem ?F' \<rho> rn rg =
      const_denote ?F' rn (subst_valuation ?F' \<rho> \<theta>)"
    using const_sem_non_equality[OF rn_not_eq scheme match] .
  have fixed: "type_subst \<theta> rg = rg" using type_match_sound[OF match] .
  have agree: "\<forall>v. type_var_occurs v rg \<longrightarrow>
      subst_valuation ?F' \<rho> \<theta> v = \<rho> v"
    using subst_valuation_fixed_type[OF fixed] by blast
  have denotation: "R (subst_valuation ?F' \<rho> \<theta>) = R \<rho>"
    using extensional agree by blast
  show ?thesis using raw denotation names
    by (simp add: add_type_definition_frame_def)
qed

theorem new_basic_type_definition_conservative:
  assumes run: "new_basic_type_definition fresh thy tn an rn wit =
      Some (thy', th1, th2)"
    and thy_wf: "wf_theory thy"
    and contents_wf: "theory_contents_wf thy"
    and model: "models_theory F thy"
    and witness_valid: "valid_sequent F thy (hyps wit) (concl wit)"
  obtains pred witness rty tvs aty where
    "concl wit = Comb pred witness"
    "models_theory
      (add_type_definition_frame F tn
        (type_definition_carrier F pred rty tvs) an (mk_fun rty aty)
        (type_definition_abs F pred rty tvs) rn (mk_fun aty rty)
        (type_definition_rep F pred rty tvs)) thy'"
    "valid_sequent
      (add_type_definition_frame F tn
        (type_definition_carrier F pred rty tvs) an (mk_fun rty aty)
        (type_definition_abs F pred rty tvs) rn (mk_fun aty rty)
        (type_definition_rep F pred rty tvs)) thy' [] (concl th1)"
    "valid_sequent
      (add_type_definition_frame F tn
        (type_definition_carrier F pred rty tvs) an (mk_fun rty aty)
        (type_definition_abs F pred rty tvs) rn (mk_fun aty rty)
        (type_definition_rep F pred rty tvs)) thy' [] (concl th2)"
proof -
  obtain pred witness rty tvs aty where
      wit_wf: "wf_thm thy wit" and wit_hyps: "hyps wit = []"
    and type_fresh: "tyops thy tn = None"
    and abs_fresh: "const_tab thy an = None"
    and rep_fresh: "const_tab thy rn = None" and names: "an \<noteq> rn"
    and wit_concl: "concl wit = Comb pred witness"
    and witness_type: "type_of witness = Some rty"
    and pred_closed: "free_vars pred = []"
    and rty_vars: "set (type_vars rty) \<subseteq> set (term_type_vars pred)"
    and tvs: "tvs = term_type_vars pred"
    and aty: "aty = TyApp tn (map TyVar tvs)"
    and th1_shape: "th1 = \<lparr>hyps = [],
      concl = eq_term aty
        (Comb (Const an (mk_fun rty aty))
          (Comb (Const rn (mk_fun aty rty)) (FVar NAlpha aty)))
        (FVar NAlpha aty),
      thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    and th2_shape: "th2 = \<lparr>hyps = [],
      concl = eq_term bool_ty (Comb pred (FVar NRepVar rty))
        (eq_term rty
          (Comb (Const rn (mk_fun aty rty))
            (Comb (Const an (mk_fun rty aty)) (FVar NRepVar rty)))
          (FVar NRepVar rty)),
      thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    and shape: "thy' = \<lparr>tyops = (tyops thy)(tn := Some (length tvs)),
      const_tab = (const_tab thy)
        (an := Some (mk_fun rty aty), rn := Some (mk_fun aty rty)),
      axiom_list = axiom_list thy, def_tab = def_tab thy,
      thy_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    and th1_wf: "wf_thm thy' th1" and th2_wf: "wf_thm thy' th2"
    using new_basic_type_definition_obtain[OF run] by blast
  let ?D = "type_definition_carrier F pred rty tvs"
  let ?A = "type_definition_abs F pred rty tvs"
  let ?R = "type_definition_rep F pred rty tvs"
  let ?ag = "mk_fun rty aty"
  let ?rg = "mk_fun aty rty"
  let ?F' = "add_type_definition_frame F tn ?D an ?ag ?A rn ?rg ?R"
  have old_frame: "frame_wf F" and old_constants:
      "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>"
    using model by (auto simp: models_theory_def)
  have tn_not_fun: "tn \<noteq> NFun" and tn_not_bool: "tn \<noteq> NBool"
    using type_fresh thy_wf by (auto simp: wf_theory_def)
  have an_not_eq: "an \<noteq> NEq" and rn_not_eq: "rn \<noteq> NEq"
    using abs_fresh rep_fresh thy_wf by (auto simp: wf_theory_def)
  have pred_vars: "set (term_type_vars pred) \<subseteq> set tvs"
    using tvs by simp
  have rty_vars_tvs: "set (type_vars rty) \<subseteq> set tvs"
    using rty_vars tvs by simp
  have distinct_tvs: "distinct tvs" using tvs by simp
  have witness_valid': "valid_sequent F thy [] (Comb pred witness)"
    using witness_valid wit_hyps wit_concl by simp
  have D_inhabited: "\<forall>args. list_all inhabited args \<longrightarrow> inhabited (?D args)"
    using type_definition_carrier_inhabited[OF thy_wf model wit_wf wit_hyps
        wit_concl witness_type witness_valid'] by blast
  have A_extensional: "\<forall>\<rho> \<sigma>.
      (\<forall>v. type_var_occurs v ?ag \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow> ?A \<rho> = ?A \<sigma>"
    using type_definition_abs_extensional[OF aty rty_vars_tvs] by blast
  have R_extensional: "\<forall>\<rho> \<sigma>.
      (\<forall>v. type_var_occurs v ?rg \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow> ?R \<rho> = ?R \<sigma>"
    using type_definition_rep_extensional[OF aty] by blast
  have frame_ok: "frame_wf ?F'"
    using add_type_definition_frame_wf[OF old_frame tn_not_fun tn_not_bool
        D_inhabited names A_extensional R_extensional] .
  have witness_checked: "check_term thy witness"
    using wit_wf wit_concl
    by (auto simp: wf_thm_def check_prop_def check_term_def)
  have rty_checked: "check_type thy rty"
    using check_open_term_result_type[OF thy_wf]
      witness_checked witness_type unfolding check_term_def by blast
  have new_constants: "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow>
      const_interpretation_ok ?F' thy' \<rho>"
  proof (intro allI impI)
    fix \<rho>
    assume rho_ok: "type_valuation_ok \<rho>"
    show "const_interpretation_ok ?F' thy' \<rho>"
      unfolding const_interpretation_ok_def
    proof (intro allI impI)
      fix m generic \<sigma>
      assume sigma_ok: "type_valuation_ok \<sigma>"
        and tab': "const_tab thy' m = Some generic"
      show "const_scheme ?F' m = Some generic \<and>
        Elem (const_denote ?F' m \<sigma>) (interp_type ?F' \<sigma> generic)"
      proof (cases "m = an")
        case True
        have generic_ag: "generic = ?ag"
          using tab' shape True names by simp
        have args_ok: "list_all inhabited (map \<sigma> tvs)"
          using sigma_ok by (auto simp: type_valuation_ok_def list_all_iff)
        have carrier_inh: "inhabited (?D (map \<sigma> tvs))"
          using D_inhabited args_ok by blast
        have abs_member: "Elem (?A \<sigma>)
            (Fun (interp_type F \<sigma> rty) (?D (map \<sigma> tvs)))"
          using subtype_abs_in_fun[OF carrier_inh]
          by (simp add: type_definition_abs_def)
        have old_rty: "interp_type ?F' \<sigma> rty = interp_type F \<sigma> rty"
          using interp_type_add_type_definition_old[OF type_fresh rty_checked] .
        have new_aty: "interp_type ?F' \<sigma> aty = ?D (map \<sigma> tvs)"
          unfolding aty
          by (rule interp_type_add_type_definition_new[OF tn_not_fun tn_not_bool])
        have generic_interp: "interp_type ?F' \<sigma> ?ag =
            Fun (interp_type F \<sigma> rty) (?D (map \<sigma> tvs))"
          using old_rty new_aty by (simp add: mk_fun_def)
        show ?thesis using True generic_ag abs_member generic_interp names
          by (simp add: add_type_definition_frame_def)
      next
        case not_abs: False
        show ?thesis
        proof (cases "m = rn")
          case True
          have generic_rg: "generic = ?rg"
            using tab' shape True not_abs by simp
          have normalized: "?D (map \<sigma> tvs) =
              subtype_carrier (interp_type F \<sigma> rty)
                (eval_term F \<sigma> (canonical_free_valuation F \<sigma>) [] pred)"
            using type_definition_carrier_map[OF old_frame distinct_tvs
                pred_vars rty_vars_tvs pred_closed] .
          have contained: "\<And>x. Elem x (?D (map \<sigma> tvs)) \<Longrightarrow>
              Elem x (interp_type F \<sigma> rty)"
            using normalized by simp
          have rep_member: "Elem (?R \<sigma>)
              (Fun (?D (map \<sigma> tvs)) (interp_type F \<sigma> rty))"
            using subtype_rep_in_fun_contained[OF contained]
            by (simp add: type_definition_rep_def)
          have old_rty: "interp_type ?F' \<sigma> rty = interp_type F \<sigma> rty"
            using interp_type_add_type_definition_old[OF type_fresh rty_checked] .
          have new_aty: "interp_type ?F' \<sigma> aty = ?D (map \<sigma> tvs)"
            unfolding aty
            by (rule interp_type_add_type_definition_new[OF tn_not_fun tn_not_bool])
          have generic_interp: "interp_type ?F' \<sigma> ?rg =
              Fun (?D (map \<sigma> tvs)) (interp_type F \<sigma> rty)"
            using old_rty new_aty by (simp add: mk_fun_def)
          show ?thesis using True generic_rg rep_member generic_interp names
            by (simp add: add_type_definition_frame_def)
        next
          case not_rep: False
          have old_tab: "const_tab thy m = Some generic"
            using tab' shape not_abs not_rep by simp
          have old_entry: "const_scheme F m = Some generic \<and>
              Elem (const_denote F m \<sigma>) (interp_type F \<sigma> generic)"
            using old_constants sigma_ok old_tab
            by (auto simp: const_interpretation_ok_def)
          have generic_checked: "check_type thy generic"
            using thy_wf old_tab by (auto simp: wf_theory_def)
          have carrier: "interp_type ?F' \<sigma> generic = interp_type F \<sigma> generic"
            using interp_type_add_type_definition_old[OF type_fresh generic_checked] .
          show ?thesis using not_abs not_rep old_entry carrier
            by (simp add: add_type_definition_frame_def)
        qed
      qed
    qed
  qed
  have axiom_checks: "\<forall>th\<in>set (axiom_list thy).
      list_all (check_prop thy) (hyps th) \<and> check_prop thy (concl th)"
    using contents_wf
    by (auto simp: theory_contents_wf_def wf_thm_def list_all_iff)
  have definition_checks: "\<forall>m th. def_tab thy m = Some th \<longrightarrow>
      list_all (check_prop thy) (hyps th) \<and> check_prop thy (concl th)"
    using contents_wf by (auto simp: theory_contents_wf_def wf_thm_def)
  have old_type_checked: "\<And>ty. check_type thy ty \<Longrightarrow> check_type thy' ty"
  proof -
    fix ty
    assume "check_type thy ty"
    then show "check_type thy' ty"
      using shape type_fresh
      by (induction ty) (auto simp: list_all_iff)
  qed
  have thy'_wf: "wf_theory thy'"
    using thy_wf type_fresh abs_fresh rep_fresh names rty_checked aty
      old_type_checked
    by (auto simp: shape wf_theory_def mk_fun_def list_all_iff)
  have final_model: "models_theory ?F' thy'"
    unfolding models_theory_def
  proof (intro conjI)
    show "frame_wf ?F'" using frame_ok .
    show "\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok ?F' thy' \<rho>"
      using new_constants .
    show "\<forall>th\<in>set (axiom_list thy').
        valid_sequent ?F' thy' (hyps th) (concl th)"
      using model axiom_checks shape old_constants
      by (auto simp: models_theory_def
          intro!: valid_sequent_add_type_definition_unchanged
            [OF type_fresh abs_fresh rep_fresh names old_frame])
    show "\<forall>m th. def_tab thy' m = Some th \<longrightarrow>
        valid_sequent ?F' thy' (hyps th) (concl th)"
      using model definition_checks shape old_constants
      by (auto simp: models_theory_def
          intro!: valid_sequent_add_type_definition_unchanged
            [OF type_fresh abs_fresh rep_fresh names old_frame])
  qed
  obtain \<theta>a where abs_match:
      "type_match ?ag ?ag (\<lambda>_. None) = Some \<theta>a"
    using th1_wf shape names
    by (auto simp: th1_shape wf_thm_def check_prop_def check_term_def
        eq_term_def eq_const_def mk_fun_def split: option.splits)
  obtain \<theta>r where rep_match:
      "type_match ?rg ?rg (\<lambda>_. None) = Some \<theta>r"
    using th1_wf shape names
    by (auto simp: th1_shape wf_thm_def check_prop_def check_term_def
        eq_term_def eq_const_def mk_fun_def split: option.splits)
  have th1_valid: "valid_sequent ?F' thy' [] (concl th1)"
  proof (unfold valid_sequent_def, intro allI impI)
    fix \<rho> \<nu>
    assume rho_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok ?F' thy' \<rho>"
      and free_ok: "free_valuation_ok ?F' \<rho> \<nu>"
    let ?x = "\<nu> (NAlpha, aty)"
    let ?left = "Comb (Const an ?ag)
      (Comb (Const rn ?rg) (FVar NAlpha aty))"
    have left_check: "check_term thy' ?left"
      and right_check: "check_term thy' (FVar NAlpha aty)"
      using th1_wf
      by (auto simp: th1_shape wf_thm_def check_prop_def check_term_def
          eq_term_def eq_const_def mk_fun_def split: option.splits)
    have left_type: "type_of ?left = Some aty"
      and right_type: "type_of (FVar NAlpha aty) = Some aty"
      by (simp_all add: mk_fun_def)
    have new_aty: "interp_type ?F' \<rho> aty = ?D (map \<rho> tvs)"
      unfolding aty
      by (rule interp_type_add_type_definition_new[OF tn_not_fun tn_not_bool])
    have x_typed: "Elem ?x (interp_type ?F' \<rho> aty)"
      using free_ok by (auto simp: free_valuation_ok_def)
    have x_member: "Elem ?x (?D (map \<rho> tvs))"
      using x_typed new_aty by simp
    have args_ok: "list_all inhabited (map \<rho> tvs)"
      using rho_ok by (auto simp: type_valuation_ok_def list_all_iff)
    have carrier_inhabited: "inhabited (?D (map \<rho> tvs))"
      using D_inhabited args_ok by blast
    have normalized: "?D (map \<rho> tvs) =
        subtype_carrier (interp_type F \<rho> rty)
          (eval_term F \<rho> (canonical_free_valuation F \<rho>) [] pred)"
      using type_definition_carrier_map[OF old_frame distinct_tvs
          pred_vars rty_vars_tvs pred_closed] .
    have contained: "\<And>x. Elem x (?D (map \<rho> tvs)) \<Longrightarrow>
        Elem x (interp_type F \<rho> rty)"
      using normalized by simp
    have identity: "app (?A \<rho>) (app (?R \<rho>) ?x) = ?x"
      unfolding type_definition_abs_def type_definition_rep_def
      using subtype_abs_rep_identity[OF carrier_inhabited x_member contained] .
    have abs_sem: "const_sem ?F' \<rho> an ?ag = ?A \<rho>"
      using const_sem_add_type_definition_abs_same[OF an_not_eq names
          abs_match A_extensional] .
    have rep_sem: "const_sem ?F' \<rho> rn ?rg = ?R \<rho>"
      using const_sem_add_type_definition_rep_same[OF rn_not_eq names
          rep_match R_extensional] .
    have evaluated: "eval_term ?F' \<rho> \<nu> [] ?left =
        eval_term ?F' \<rho> \<nu> [] (FVar NAlpha aty)"
      using identity abs_sem rep_sem by simp
    note eq_iff = holds_eq_iff[OF thy'_wf frame_ok rho_ok free_ok const_ok
        left_check left_type right_check right_type]
    show "holds ?F' \<rho> \<nu> (concl th1)"
      using eq_iff evaluated by (simp add: th1_shape)
  qed
  have pred_check: "check_term thy pred"
    using wit_wf wit_concl
    by (auto simp: wf_thm_def check_prop_def check_term_def)
  have pred_type: "type_of pred = Some (mk_fun rty bool_ty)"
    using wit_wf wit_concl witness_type
    by (auto simp: wf_thm_def check_prop_def check_term_def is_bool_def
        mk_fun_def split: option.splits htype.splits hname.splits list.splits
          if_splits)
  have th2_valid: "valid_sequent ?F' thy' [] (concl th2)"
  proof (unfold valid_sequent_def, intro allI impI)
    fix \<rho> \<nu>
    assume rho_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok ?F' thy' \<rho>"
      and free_ok: "free_valuation_ok ?F' \<rho> \<nu>"
    let ?x = "\<nu> (NRepVar, rty)"
    let ?P = "eval_term F \<rho> (canonical_free_valuation F \<rho>) [] pred"
    let ?rebuilt = "Comb (Const rn ?rg)
      (Comb (Const an ?ag) (FVar NRepVar rty))"
    let ?left = "Comb pred (FVar NRepVar rty)"
    let ?right = "eq_term rty ?rebuilt (FVar NRepVar rty)"
    have left_check: "check_term thy' ?left"
      and right_check: "check_term thy' ?right"
      using th2_wf
      by (auto simp: th2_shape wf_thm_def check_prop_def check_term_def
          eq_term_def eq_const_def mk_fun_def split: option.splits)
    have left_type: "type_of ?left = Some bool_ty"
      and right_type: "type_of ?right = Some bool_ty"
      using pred_type by (simp_all add: mk_fun_def eq_term_def eq_const_def)
    have old_rty: "interp_type ?F' \<rho> rty = interp_type F \<rho> rty"
      using interp_type_add_type_definition_old[OF type_fresh rty_checked] .
    have x_typed: "Elem ?x (interp_type ?F' \<rho> rty)"
      using free_ok by (auto simp: free_valuation_ok_def)
    have x_member: "Elem ?x (interp_type F \<rho> rty)"
      using x_typed old_rty by simp
    have args_ok: "list_all inhabited (map \<rho> tvs)"
      using rho_ok by (auto simp: type_valuation_ok_def list_all_iff)
    have carrier_inhabited: "inhabited (?D (map \<rho> tvs))"
      using D_inhabited args_ok by blast
    have normalized: "?D (map \<rho> tvs) =
        subtype_carrier (interp_type F \<rho> rty) ?P"
      using type_definition_carrier_map[OF old_frame distinct_tvs
          pred_vars rty_vars_tvs pred_closed] .
    have contained: "\<And>y. Elem y (?D (map \<rho> tvs)) \<Longrightarrow>
        Elem y (interp_type F \<rho> rty)"
      using normalized by simp
    have characteristic: "Elem ?x (?D (map \<rho> tvs)) \<longleftrightarrow> app ?P ?x = ztrue"
      using normalized x_member by simp
    have canonical_ok: "free_valuation_ok F \<rho>
        (canonical_free_valuation F \<rho>)"
      using canonical_free_valuation_ok[OF old_frame rho_ok] .
    have empty_ok: "bound_valuation_ok F \<rho> [] []"
      by (simp add: bound_valuation_ok_def)
    have pred_member: "Elem ?P
        (interp_type F \<rho> (mk_fun rty bool_ty))"
      using eval_type_sound[OF thy_wf old_frame rho_ok canonical_ok
          old_constants[rule_format, OF rho_ok] empty_ok]
        pred_check pred_type unfolding check_term_def by blast
    have pred_fun: "Elem ?P (Fun (interp_type F \<rho> rty) zbool)"
      using pred_member by (simp add: mk_fun_def bool_ty_def)
    have bool_member: "Elem (app ?P ?x) zbool"
      using app_in_fun[OF pred_fun x_member] .
    have law: "app ?P ?x =
        app (app (zeq (interp_type F \<rho> rty))
          (app (?R \<rho>) (app (?A \<rho>) ?x))) ?x"
      unfolding type_definition_abs_def type_definition_rep_def
      using subtype_characteristic[OF carrier_inhabited x_member contained
          characteristic bool_member] .
    have abs_sem: "const_sem ?F' \<rho> an ?ag = ?A \<rho>"
      using const_sem_add_type_definition_abs_same[OF an_not_eq names
          abs_match A_extensional] .
    have rep_sem: "const_sem ?F' \<rho> rn ?rg = ?R \<rho>"
      using const_sem_add_type_definition_rep_same[OF rn_not_eq names
          rep_match R_extensional] .
    have pred_frame: "eval_term ?F' \<rho> \<nu> [] pred = eval_term F \<rho> \<nu> [] pred"
      using eval_add_type_definition_unchanged[OF type_fresh abs_fresh
          rep_fresh names old_frame, where envty="[]" and env="[]"]
        pred_check unfolding check_term_def by blast
    have pred_free: "eval_term F \<rho> \<nu> [] pred = ?P"
      using eval_term_closed_free_valuation[OF pred_closed] .
    have evaluated: "eval_term ?F' \<rho> \<nu> [] ?left =
        eval_term ?F' \<rho> \<nu> [] ?right"
      using law abs_sem rep_sem pred_frame pred_free old_rty
      by (simp add: eq_term_def eq_const_def const_sem_def mk_fun_def
          bool_ty_def)
    note eq_iff = holds_eq_iff[OF thy'_wf frame_ok rho_ok free_ok const_ok
        left_check left_type right_check right_type]
    show "holds ?F' \<rho> \<nu> (concl th2)"
      using eq_iff evaluated by (simp add: th2_shape)
  qed
  show thesis using that[OF wit_concl final_model th1_valid th2_valid] .
qed

end
