(* SPDX-License-Identifier: 0BSD AND BSD-2-Clause AND BSD-3-Clause *)
(* Conservatively covered by HOL Light and HOL4 notices; see THIRD_PARTY_NOTICES. *)

theory Rhombus_HOL_Semantics
  imports Rhombus_HOL_Kernel
begin

section \<open>Set-theoretic frames\<close>

text \<open>The semantic frame uses carrier arguments rather than syntax- or valuation-dependent interpretation fields.\<close>

record frame =
  tyop_denote :: "hname \<Rightarrow> ZF list \<Rightarrow> ZF"
  const_scheme :: "hname \<Rightarrow> htype option"
  const_denote :: "hname \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ZF"

definition zfalse :: ZF where "zfalse = Empty"
definition ztrue :: ZF where "ztrue = Singleton Empty"
definition zbool :: ZF where "zbool = Upair zfalse ztrue"

definition zeq :: "ZF \<Rightarrow> ZF" where
  "zeq A = Lambda A (\<lambda>x. Lambda A (\<lambda>y. if x = y then ztrue else zfalse))"

definition inhabited :: "ZF \<Rightarrow> bool" where
  "inhabited A \<longleftrightarrow> (\<exists>x. Elem x A)"

definition frame_wf :: "frame \<Rightarrow> bool" where
  "frame_wf F \<longleftrightarrow>
    (\<forall>n args. n \<noteq> NFun \<longrightarrow> n \<noteq> NBool \<longrightarrow> list_all inhabited args \<longrightarrow>
      inhabited (tyop_denote F n args)) \<and>
    (\<forall>n generic \<rho> \<sigma>. const_scheme F n = Some generic \<longrightarrow>
      (\<forall>v. type_var_occurs v generic \<longrightarrow> \<rho> v = \<sigma> v) \<longrightarrow>
      const_denote F n \<rho> = const_denote F n \<sigma>)"

lemma ztrue_neq_zfalse: "ztrue \<noteq> zfalse"
  by (auto simp: ztrue_def zfalse_def Singleton_def Upair_nonEmpty)

lemma zfalse_in_zbool [simp]: "Elem zfalse zbool"
  by (simp add: zbool_def Upair)

lemma ztrue_in_zbool [simp]: "Elem ztrue zbool"
  by (simp add: zbool_def Upair)

lemma elem_zbool_iff [simp]:
  "Elem z zbool \<longleftrightarrow> z = zfalse \<or> z = ztrue"
  by (simp add: zbool_def Upair)

section \<open>Type interpretation\<close>

fun interp_type :: "frame \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> htype \<Rightarrow> ZF" where
  "interp_type F \<rho> (TyVar n) = \<rho> n"
| "interp_type F \<rho> (TyApp n args) =
    (if n = NFun then
       (case map (interp_type F \<rho>) args of [A, B] \<Rightarrow> Fun A B | _ \<Rightarrow> zbool)
     else if n = NBool then zbool
     else tyop_denote F n (map (interp_type F \<rho>) args))"

lemma interp_type_bool_ty [simp]:
  "interp_type F \<rho> bool_ty = zbool"
  by (simp add: bool_ty_def)

definition subst_valuation ::
  "frame \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow> hname \<Rightarrow> ZF" where
  "subst_valuation F \<rho> \<theta> n =
    (case \<theta> n of None \<Rightarrow> \<rho> n | Some ty \<Rightarrow> interp_type F \<rho> ty)"

lemma interp_type_subst:
  "interp_type F \<rho> (type_subst \<theta> ty) =
    interp_type F (subst_valuation F \<rho> \<theta>) ty"
proof (induction ty)
  case (TyVar n)
  then show ?case by (simp add: subst_valuation_def split: option.splits)
next
  case (TyApp n args)
  have maps: "map (\<lambda>x. interp_type F \<rho> (type_subst \<theta> x)) args =
      map (interp_type F (subst_valuation F \<rho> \<theta>)) args"
    using TyApp.IH by (intro map_cong) auto
  show ?case
    by (simp only: type_subst.simps interp_type.simps map_map o_def maps; simp)
qed

lemma interp_type_cong_occurs:
  assumes "\<forall>v. type_var_occurs v ty \<longrightarrow> \<rho> v = \<sigma> v"
  shows "interp_type F \<rho> ty = interp_type F \<sigma> ty"
  using assms
proof (induction ty)
  case (TyVar n)
  then show ?case by simp
next
  case (TyApp n args)
  have maps: "map (interp_type F \<rho>) args = map (interp_type F \<sigma>) args"
    using TyApp by (intro map_cong) (auto simp: list_ex_iff)
  show ?case by (simp only: interp_type.simps maps)
qed

definition compose_type_subst ::
  "(hname \<Rightarrow> htype option) \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow> hname \<Rightarrow> htype option" where
  "compose_type_subst outer inner v =
    (case inner v of None \<Rightarrow> outer v | Some ty \<Rightarrow> Some (type_subst outer ty))"

lemma type_subst_compose:
  "type_subst (compose_type_subst outer inner) ty =
    type_subst outer (type_subst inner ty)"
  by (induction ty)
    (auto simp: compose_type_subst_def split: option.splits)

lemma subst_valuation_compose:
  "subst_valuation F \<rho> (compose_type_subst outer inner) v =
    subst_valuation F (subst_valuation F \<rho> outer) inner v"
  by (auto simp: compose_type_subst_def subst_valuation_def interp_type_subst
      split: option.splits)

lemma type_subst_semantic_agree:
  assumes equal: "type_subst \<theta> ty = type_subst \<sigma> ty"
    and occurs: "type_var_occurs v ty"
  shows "subst_valuation F \<rho> \<theta> v = subst_valuation F \<rho> \<sigma> v"
  using equal occurs
proof (induction ty)
  case (TyVar n)
  then show ?case
    by (cases "\<theta> n"; cases "\<sigma> n")
      (auto simp: subst_valuation_def)
next
  case (TyApp n args)
  then obtain arg where arg: "arg \<in> set args" "type_var_occurs v arg"
    by (auto simp: list_ex_iff)
  have arg_equal: "type_subst \<theta> arg = type_subst \<sigma> arg"
    using TyApp.prems(1) arg(1) by simp
  show ?case using TyApp.IH[OF arg(1) arg_equal arg(2)] .
qed

section \<open>Term interpretation\<close>

definition type_valuation_ok :: "(hname \<Rightarrow> ZF) \<Rightarrow> bool" where
  "type_valuation_ok \<rho> \<longleftrightarrow> (\<forall>n. inhabited (\<rho> n))"

datatype equality_instance =
    Equality_Instance htype
  | Ill_Typed_Equality
  | Other_Constant_Type

fun classify_equality_type :: "htype \<Rightarrow> equality_instance" where
  "classify_equality_type
      (TyApp NFun [a, TyApp NFun [b, TyApp NBool []]]) =
     (if a = b then Equality_Instance a else Ill_Typed_Equality)"
| "classify_equality_type _ = Other_Constant_Type"

lemma classify_equality_instance:
  "classify_equality_type ty = Equality_Instance a \<Longrightarrow>
    ty = TyApp NFun [a, TyApp NFun [a, TyApp NBool []]]"
  by (induction ty rule: classify_equality_type.induct)
    (auto split: if_splits)

definition const_sem ::
  "frame \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> ZF" where
  "const_sem F \<rho> n ty =
    (if n = NEq then
       (case classify_equality_type ty of
          Equality_Instance a \<Rightarrow> zeq (interp_type F \<rho> a)
        | Ill_Typed_Equality \<Rightarrow> Empty
        | Other_Constant_Type \<Rightarrow> Empty)
     else case const_scheme F n of
       None \<Rightarrow> Empty
     | Some generic \<Rightarrow>
         (case type_match generic ty (\<lambda>_. None) of
            None \<Rightarrow> Empty
          | Some \<theta> \<Rightarrow> const_denote F n (subst_valuation F \<rho> \<theta>)))"

lemma const_sem_non_equality:
  assumes "n \<noteq> NEq" "const_scheme F n = Some generic"
    "type_match generic ty (\<lambda>_. None) = Some \<theta>"
  shows "const_sem F \<rho> n ty = const_denote F n (subst_valuation F \<rho> \<theta>)"
  using assms by (simp add: const_sem_def)

lemma equality_match_shape_early:
  assumes "type_match (mk_fun (TyVar NAlpha)
      (mk_fun (TyVar NAlpha) bool_ty)) ty (\<lambda>_. None) \<noteq> None"
  shows "\<exists>a. ty = mk_fun a (mk_fun a bool_ty)"
proof (cases ty)
  case (TyVar n)
  then show ?thesis using assms
    by (simp add: type_match_def mk_fun_def bool_ty_def)
next
  case (TyApp n args)
  have ty_def: "ty = TyApp n args" using TyApp .
  have len: "n = NFun \<and> length args = 2"
    using assms TyApp
    by (auto simp: type_match_def mk_fun_def bool_ty_def split: if_splits)
  obtain a rest where first: "args = a # rest"
    using len by (cases args) auto
  obtain b where args: "args = [a, b]"
    using len first by (cases rest) auto
  have match: "type_match (mk_fun (TyVar NAlpha)
      (mk_fun (TyVar NAlpha) bool_ty)) (TyApp NFun [a, b])
      (\<lambda>_. None) \<noteq> None"
    using assms TyApp len args by simp
  show ?thesis
  proof (cases b)
    case (TyVar bn)
    then show ?thesis using match TyApp len args
      by (auto simp: type_match_def mk_fun_def bool_ty_def
          split: option.splits if_splits)
  next
    case (TyApp m inner)
    have inner_len: "m = NFun \<and> length inner = 2"
      using match TyApp
      by (auto simp: type_match_def mk_fun_def bool_ty_def split: if_splits)
    obtain c rest' where first': "inner = c # rest'"
      using inner_len by (cases inner) auto
    obtain d where inner: "inner = [c, d]"
      using inner_len first' by (cases rest') auto
    show ?thesis using match ty_def len args TyApp inner_len inner
      by (cases d)
         (auto simp: type_match_def mk_fun_def bool_ty_def
           split: htype.splits hname.splits list.splits option.splits if_splits)
  qed
qed

fun eval_term ::
  "frame \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ((hname \<times> htype) \<Rightarrow> ZF) \<Rightarrow> ZF list \<Rightarrow> hterm \<Rightarrow> ZF" where
  "eval_term F \<rho> \<nu> env (FVar n ty) = \<nu> (n, ty)"
| "eval_term F \<rho> \<nu> env (BVar i ty) = (if i < length env then env ! i else Empty)"
| "eval_term F \<rho> \<nu> env (Const n ty) = const_sem F \<rho> n ty"
| "eval_term F \<rho> \<nu> env (Comb f x) =
     app (eval_term F \<rho> \<nu> env f) (eval_term F \<rho> \<nu> env x)"
| "eval_term F \<rho> \<nu> env (Abs aty body) =
     Lambda (interp_type F \<rho> aty) (\<lambda>x. eval_term F \<rho> \<nu> (x # env) body)"

definition free_valuation_ok ::
  "frame \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ((hname \<times> htype) \<Rightarrow> ZF) \<Rightarrow> bool" where
  "free_valuation_ok F \<rho> \<nu> \<longleftrightarrow>
    (\<forall>n ty. Elem (\<nu> (n, ty)) (interp_type F \<rho> ty))"

definition bound_valuation_ok ::
  "frame \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> htype list \<Rightarrow> ZF list \<Rightarrow> bool" where
  "bound_valuation_ok F \<rho> tys env \<longleftrightarrow>
    length tys = length env \<and>
    (\<forall>i < length tys. Elem (env ! i) (interp_type F \<rho> (tys ! i)))"

definition const_interpretation_ok ::
  "frame \<Rightarrow> htheory \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> bool" where
  "const_interpretation_ok F thy \<rho> \<longleftrightarrow>
    (\<forall>n generic \<sigma>. type_valuation_ok \<sigma> \<longrightarrow>
      const_tab thy n = Some generic \<longrightarrow>
      const_scheme F n = Some generic \<and>
      Elem (const_denote F n \<sigma>) (interp_type F \<sigma> generic))"lemma zeq_apply:
  assumes "Elem x A" "Elem y A"
  shows "app (app (zeq A) x) y = (if x = y then ztrue else zfalse)"
  using assms by (simp add: zeq_def Lambda_app)

lemma zeq_in_fun: "Elem (zeq A) (Fun A (Fun A zbool))"
  by (simp add: zeq_def Elem_Lambda_Fun)

lemma app_in_fun:
  assumes "Elem f (Fun A B)" "Elem x A"
  shows "Elem (app f x) B"
proof -
  have pf: "isFun f" using assms(1)
    by (auto simp: Fun_def Sep PFun_def)
  have dom: "Domain f = A" using assms(1)
    by (simp add: Fun_def Sep)
  have "Elem (app f x) (Range f)"
    using assms(2) pf dom fun_value_in_range by simp
  then show ?thesis using Fun_Range[OF assms(1)]
    by (auto simp: subset_def)
qed

lemma interp_type_inhabited_any:
  assumes frame_ok: "frame_wf F" and type_ok: "type_valuation_ok \<rho>"
  shows "inhabited (interp_type F \<rho> ty)"
proof (induction ty)
  case (TyVar n)
  then show ?case using type_ok by (simp add: type_valuation_ok_def)
next
  case (TyApp n args)
  let ?vals = "map (interp_type F \<rho>) args"
  have vals_inh: "list_all inhabited ?vals"
    using TyApp.IH by (auto simp: list_all_iff)
  have bool_inh: "inhabited zbool"
    unfolding inhabited_def using zfalse_in_zbool by blast
  show ?case
  proof (cases "n = NFun")
    case True
    show ?thesis
    proof (cases ?vals)
      case Nil
      then show ?thesis using True bool_inh by simp
    next
      case (Cons A rest)
      have vals1: "?vals = A # rest" using Cons .
      show ?thesis
      proof (cases rest)
        case Nil
        then show ?thesis using True vals1 bool_inh by simp
      next
        case (Cons B tail)
        have rest1: "rest = B # tail" using Cons .
        show ?thesis
        proof (cases tail)
          case Nil
          obtain y where y: "Elem y B"
            using vals_inh vals1 rest1 Nil
            by (auto simp: inhabited_def list_all_iff)
          have fun_member: "Elem (Lambda A (\<lambda>_. y)) (Fun A B)"
            using y by (simp add: Elem_Lambda_Fun)
          show ?thesis using True vals1 rest1 Nil fun_member
            by (auto simp: inhabited_def)
        next
          case (Cons C more)
          then show ?thesis using True vals1 rest1 bool_inh by simp
        qed
      qed
    qed  next
    case False
    have not_fun: "n \<noteq> NFun" using False .
    show ?thesis
    proof (cases "n = NBool")
      case True
      then show ?thesis using not_fun bool_inh by simp
    next
      case False
      then show ?thesis using not_fun frame_ok vals_inh
        by (auto simp: frame_wf_def)
    qed
  qed
qed

lemma subst_valuation_ok:
  assumes frame_ok: "frame_wf F" and type_ok: "type_valuation_ok \<rho>"
  shows "type_valuation_ok (subst_valuation F \<rho> \<theta>)"
proof (unfold type_valuation_ok_def, intro allI)
  fix n
  show "inhabited (subst_valuation F \<rho> \<theta> n)"
  proof (cases "\<theta> n")
    case None
    then show ?thesis using type_ok
      by (simp add: subst_valuation_def type_valuation_ok_def)
  next
    case (Some ty)
    then show ?thesis using interp_type_inhabited_any[OF frame_ok type_ok, of ty]
      by (simp add: subst_valuation_def)
  qed
qed

lemma interp_type_inhabited:
  assumes "wf_theory thy" "frame_wf F" "type_valuation_ok \<rho>"
    "check_type thy ty"
  shows "inhabited (interp_type F \<rho> ty)"
  using assms
proof (induction ty)
  case (TyVar n)
  then show ?case by (simp add: type_valuation_ok_def)
next
  case (TyApp n args)
  have arg_inh: "list_all inhabited (map (interp_type F \<rho>) args)"
    using TyApp.IH TyApp.prems by (auto simp: list_all_iff)
  show ?case
  proof (cases "n = NFun")
    case True
    have len: "length args = 2"
      using True TyApp.prems by (simp add: wf_theory_def)
    obtain a rest where args1: "args = a # rest"
      using len by (cases args) auto
    obtain b where args: "args = [a, b]"
      using len args1 by (cases rest) auto
    obtain y where y: "Elem y (interp_type F \<rho> b)"
      using arg_inh unfolding args inhabited_def by auto
    have "Elem (Lambda (interp_type F \<rho> a) (\<lambda>_. y))
        (Fun (interp_type F \<rho> a) (interp_type F \<rho> b))"
      using y by (simp add: Elem_Lambda_Fun)
    then show ?thesis using True args by (auto simp: inhabited_def)
  next
    case not_fun: False
    show ?thesis
    proof (cases "n = NBool")
      case True
      have "length args = 0"
        using True TyApp.prems by (simp add: wf_theory_def)
      then have args: "args = []" by simp
      have zb: "inhabited zbool"
        unfolding inhabited_def using zfalse_in_zbool by blast
      show ?thesis using True not_fun zb by (simp add: args)
    next
      case False
      then show ?thesis using TyApp.prems not_fun arg_inh
        by (auto simp: frame_wf_def)
    qed
  qed
qed

lemma bound_valuation_cons:
  assumes "bound_valuation_ok F \<rho> tys env"
    "Elem x (interp_type F \<rho> ty)"
  shows "bound_valuation_ok F \<rho> (ty # tys) (x # env)"
  using assms by (auto simp: bound_valuation_ok_def nth_Cons split: nat.splits)

lemma type_of_comb_Some:
  assumes "type_of (Comb f x) = Some r"
  shows "\<exists>d. type_of f = Some (mk_fun d r) \<and> type_of x = Some d"
  using assms
  by (auto simp: mk_fun_def
      split: htype.splits hname.splits option.splits list.splits if_splits)

lemma eval_type_sound:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and bound_ok: "bound_valuation_ok F \<rho> tys env"
    and checked: "check_open_term thy tys t"
    and typeof: "type_of t = Some ty"
  shows "Elem (eval_term F \<rho> \<nu> env t) (interp_type F \<rho> ty)"
  using bound_ok checked typeof
proof (induction t arbitrary: tys env ty)
  case (FVar n u)
  then show ?case using free_ok by (auto simp: free_valuation_ok_def)
next
  case (BVar i u)
  then show ?case by (auto simp: bound_valuation_ok_def)
next
  case (Const n u)
  have result_ty: "u = ty" using Const.prems(3) by simp
  show ?case
  proof (cases "n = NEq")
    case True
    have match: "type_match (mk_fun (TyVar NAlpha)
        (mk_fun (TyVar NAlpha) bool_ty)) u (\<lambda>_. None) \<noteq> None"
      using Const.prems(2) thy_wf True by (simp add: wf_theory_def)
    obtain a where shape: "u = mk_fun a (mk_fun a bool_ty)"
      using equality_match_shape_early[OF match] by blast
    have classified: "classify_equality_type ty = Equality_Instance a"
      using shape result_ty by (simp add: mk_fun_def bool_ty_def)
    have carrier: "interp_type F \<rho> ty =
        Fun (interp_type F \<rho> a) (Fun (interp_type F \<rho> a) zbool)"
      using shape result_ty by (simp add: mk_fun_def bool_ty_def)
    show ?thesis using True result_ty classified carrier
        zeq_in_fun[of "interp_type F \<rho> a"]
      by (simp add: const_sem_def)
  next
    case False
    obtain generic where tab: "const_tab thy n = Some generic"
      using Const.prems(2) by (auto split: option.splits)
    obtain \<theta> where match: "type_match generic u (\<lambda>_. None) = Some \<theta>"
      using Const.prems(2) tab by (auto split: option.splits)
    have sigma_ok: "type_valuation_ok (subst_valuation F \<rho> \<theta>)"
      using subst_valuation_ok[OF frame_ok type_ok] .
    have scheme: "const_scheme F n = Some generic"
      and member: "Elem (const_denote F n (subst_valuation F \<rho> \<theta>))
        (interp_type F (subst_valuation F \<rho> \<theta>) generic)"
      using const_ok sigma_ok tab by (auto simp: const_interpretation_ok_def)    have instantiated: "type_subst \<theta> generic = u"
      using type_match_sound[OF match] .
    have carrier: "interp_type F (subst_valuation F \<rho> \<theta>) generic =
        interp_type F \<rho> u"
    proof -
      have "interp_type F (subst_valuation F \<rho> \<theta>) generic =
          interp_type F \<rho> (type_subst \<theta> generic)"
        using interp_type_subst[of F \<rho> \<theta> generic] by simp
      then show ?thesis using instantiated by simp
    qed
    show ?thesis using False result_ty scheme match member carrier
      by (simp add: const_sem_def)
  qed
next
  case (Comb f x)
  obtain d where parts:
      "type_of f = Some (mk_fun d ty)" "type_of x = Some d"
    using type_of_comb_Some[OF Comb.prems(3)] by blast
  have f_checked: "check_open_term thy tys f" and
       x_checked: "check_open_term thy tys x"
    using Comb.prems(2) by auto
  have f_in: "Elem (eval_term F \<rho> \<nu> env f)
      (Fun (interp_type F \<rho> d) (interp_type F \<rho> ty))"
    using Comb.IH(1)[OF Comb.prems(1) f_checked parts(1)]
    by (simp add: mk_fun_def)
  have x_in: "Elem (eval_term F \<rho> \<nu> env x) (interp_type F \<rho> d)"
    using Comb.IH(2)[OF Comb.prems(1) x_checked parts(2)] .
  show ?case using app_in_fun[OF f_in x_in] by simp
next
  case (Abs aty body)
  then obtain bty where body_ty: "type_of body = Some bty"
      and result: "ty = mk_fun aty bty"
    by (auto split: option.splits)
  have body_checked: "check_open_term thy (aty # tys) body"
    using Abs.prems by simp
  have body_sem: "\<forall>x. Elem x (interp_type F \<rho> aty) \<longrightarrow>
      Elem (eval_term F \<rho> \<nu> (x # env) body) (interp_type F \<rho> bty)"
  proof (intro allI impI)
    fix x
    assume x: "Elem x (interp_type F \<rho> aty)"
    have extended: "bound_valuation_ok F \<rho> (aty # tys) (x # env)"
      using bound_valuation_cons[OF Abs.prems(1) x] .
    show "Elem (eval_term F \<rho> \<nu> (x # env) body) (interp_type F \<rho> bty)"
      using Abs.IH[OF extended body_checked body_ty] .
  qed
  show ?case using body_sem result
    by (simp add: mk_fun_def Elem_Lambda_Fun)
qed

section \<open>Semantic substitution\<close>

definition env_agree :: "htype list \<Rightarrow> ZF list \<Rightarrow> ZF list \<Rightarrow> bool" where
  "env_agree tys xs ys \<longleftrightarrow>
    length tys \<le> length xs \<and> length tys \<le> length ys \<and>
    (\<forall>i < length tys. xs ! i = ys ! i)"

lemma env_agree_cons:
  assumes "env_agree tys xs ys"
  shows "env_agree (ty # tys) (x # xs) (x # ys)"
  using assms by (auto simp: env_agree_def nth_Cons split: nat.splits)

lemma eval_env_cong:
  assumes "check_open_term thy tys t" "env_agree tys xs ys"
  shows "eval_term F \<rho> \<nu> xs t = eval_term F \<rho> \<nu> ys t"
  using assms
proof (induction t arbitrary: tys xs ys)
  case (BVar i ty)
  then show ?case by (auto simp: env_agree_def)
next
  case (Comb f x)
  have f: "eval_term F \<rho> \<nu> xs f = eval_term F \<rho> \<nu> ys f"
    using Comb.IH(1) Comb.prems by auto
  have x: "eval_term F \<rho> \<nu> xs x = eval_term F \<rho> \<nu> ys x"
    using Comb.IH(2) Comb.prems by auto
  show ?case using f x by simp
next
  case (Abs aty body)
  have pointwise: "eval_term F \<rho> \<nu> (z # xs) body =
      eval_term F \<rho> \<nu> (z # ys) body" for z
    using Abs.IH env_agree_cons Abs.prems by auto
  show ?case using pointwise by (simp add: Lambda_ext)
qed auto

lemma eval_closed_env:
  assumes "check_term thy t"
  shows "eval_term F \<rho> \<nu> env t = eval_term F \<rho> \<nu> [] t"
  using eval_env_cong[of thy "[]" t env "[]" F \<rho> \<nu>] assms
  by (simp add: check_term_def env_agree_def)

lemma eval_beta_subst_general:
  assumes body: "check_open_term thy (prefix @ [aty]) t"
    and prefix: "length prefix = j" "length vals = j"
    and arg: "check_term thy s"
  shows "eval_term F \<rho> \<nu> vals (shift (-1) j (subst_at j s t)) =
    eval_term F \<rho> \<nu> (vals @ [eval_term F \<rho> \<nu> [] s]) t"
  using body prefix
proof (induction t arbitrary: prefix vals j)
  case (FVar n ty)
  then show ?case by simp
next
  case (BVar i ty)
  have inserted_shift: "shift (int j) 0 s = s"
    using shift_closed[OF arg] .
  have removed_shift: "shift (-1) j s = s"
    using shift_closed[OF arg] .
  show ?case using BVar.prems eval_closed_env[OF arg, of F \<rho> \<nu> vals]
    by (auto simp: inserted_shift removed_shift nth_append split: if_splits)
next
  case (Const n ty)
  then show ?case by simp
next
  case (Comb f x)
  have checks: "check_open_term thy (prefix @ [aty]) f"
      "check_open_term thy (prefix @ [aty]) x"
    using Comb.prems(1) by auto
  have f: "eval_term F \<rho> \<nu> vals (shift (-1) j (subst_at j s f)) =
      eval_term F \<rho> \<nu> (vals @ [eval_term F \<rho> \<nu> [] s]) f"
    using Comb.IH(1)[OF checks(1) Comb.prems(2) Comb.prems(3)] .
  have x: "eval_term F \<rho> \<nu> vals (shift (-1) j (subst_at j s x)) =
      eval_term F \<rho> \<nu> (vals @ [eval_term F \<rho> \<nu> [] s]) x"
    using Comb.IH(2)[OF checks(2) Comb.prems(2) Comb.prems(3)] .
  show ?case using f x by simp
next
  case (Abs bty body)
  have checked: "check_open_term thy ((bty # prefix) @ [aty]) body"
    using Abs.prems by simp
  have lengths: "length (bty # prefix) = Suc j" "length (z # vals) = Suc j" for z
    using Abs.prems by simp_all
  have pointwise: "eval_term F \<rho> \<nu> (z # vals)
      (shift (-1) (Suc j) (subst_at (Suc j) s body)) =
      eval_term F \<rho> \<nu> ((z # vals) @ [eval_term F \<rho> \<nu> [] s]) body" for z
    using Abs.IH[OF checked lengths] .
  show ?case using pointwise by (simp add: Lambda_ext)
qed

lemma eval_subst_bvar:
  assumes "check_open_term thy [aty] body" "check_term thy arg"
  shows "eval_term F \<rho> \<nu> [] (subst_bvar arg body) =
    eval_term F \<rho> \<nu> [eval_term F \<rho> \<nu> [] arg] body"
  using eval_beta_subst_general[of thy "[]" aty body 0 "[]" arg F \<rho> \<nu>]
    assms by (simp add: subst_bvar_def)

lemma eval_abstract_at:
  assumes "j < length env" "env ! j = \<nu> (n, ty)"
  shows "eval_term F \<rho> \<nu> env (abstract_at j n ty t) =
    eval_term F \<rho> \<nu> env t"
  using assms
proof (induction t arbitrary: j env)
  case (FVar m u)
  then show ?case by auto
next
  case (BVar i u)
  then show ?case by simp
next
  case (Const m u)
  then show ?case by simp
next
  case (Comb f x)
  then show ?case by simp
next
  case (Abs aty body)
  have rec: "eval_term F \<rho> \<nu> (z # env)
      (abstract_at (Suc j) n ty body) =
      eval_term F \<rho> \<nu> (z # env) body" for z
    using Abs.IH[of "Suc j" "z # env"] Abs.prems
    by (simp add: nth_Cons)
  show ?case using rec by (simp add: Lambda_ext)
qed

lemma eval_abstract_fvar:
  assumes "check_term thy t"
  shows "eval_term F \<rho> \<nu> [\<nu> (n, ty)] (abstract_fvar n ty t) =
    eval_term F \<rho> \<nu> [] t"
proof -
  have abstract: "eval_term F \<rho> \<nu> [\<nu> (n, ty)] (abstract_at 0 n ty t) =
      eval_term F \<rho> \<nu> [\<nu> (n, ty)] t"
    using eval_abstract_at[of 0 "[\<nu> (n, ty)]" \<nu> n ty F \<rho> t] by simp
  have closed: "eval_term F \<rho> \<nu> [\<nu> (n, ty)] t = eval_term F \<rho> \<nu> [] t"
    using eval_closed_env[OF assms, of F \<rho> \<nu> "[\<nu> (n, ty)]"] .
  show ?thesis using abstract closed by (simp add: abstract_fvar_def)
qed

definition semantic_fvar_subst ::
  "frame \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ((hname \<times> htype) \<Rightarrow> ZF) \<Rightarrow>
    (hterm \<times> (hname \<times> htype)) list \<Rightarrow> (hname \<times> htype) \<Rightarrow> ZF" where
  "semantic_fvar_subst F \<rho> \<nu> \<theta> key =
    (case lookup_fvar \<theta> (fst key) (snd key) of
       None \<Rightarrow> \<nu> key
     | Some rep \<Rightarrow> eval_term F \<rho> \<nu> [] rep)"

lemma eval_inst_fvar_at:
  assumes "wf_term_subst thy \<theta>"
  shows "eval_term F \<rho> \<nu> env (inst_fvar_at \<theta> depth t) =
    eval_term F \<rho> (semantic_fvar_subst F \<rho> \<nu> \<theta>) env t"
  using assms
proof (induction t arbitrary: depth env)
  case (FVar n ty)
  show ?case
  proof (cases "lookup_fvar \<theta> n ty")
    case None
    then show ?thesis by (simp add: semantic_fvar_subst_def)
  next
    case (Some rep)
    have checked: "check_term thy rep"
      using lookup_fvar_wf[OF FVar.prems Some] by blast
    have "shift (int depth) 0 rep = rep" using shift_closed[OF checked] .
    then show ?thesis using eval_closed_env[OF checked, of F \<rho> \<nu> env] Some
      by (simp add: semantic_fvar_subst_def)
  qed
next
  case (Abs aty body)
  have rec: "eval_term F \<rho> \<nu> (z # env)
      (inst_fvar_at \<theta> (Suc depth) body) =
      eval_term F \<rho> (semantic_fvar_subst F \<rho> \<nu> \<theta>) (z # env) body" for z
    using Abs.IH Abs.prems by blast
  show ?case using rec by (simp add: Lambda_ext)
qed auto

lemma eval_inst_fvar:
  assumes "wf_term_subst thy \<theta>"
  shows "eval_term F \<rho> \<nu> [] (inst_fvar \<theta> t) =
    eval_term F \<rho> (semantic_fvar_subst F \<rho> \<nu> \<theta>) [] t"
  using eval_inst_fvar_at[OF assms, where F=F and \<rho>=\<rho> and \<nu>=\<nu>
      and env="[]" and depth=0 and t=t]
  by (simp add: inst_fvar_def)

section \<open>Semantic type instantiation\<close>

lemma equality_match_shape:
  assumes "type_match (mk_fun (TyVar NAlpha)
      (mk_fun (TyVar NAlpha) bool_ty)) ty (\<lambda>_. None) \<noteq> None"
  shows "\<exists>a. ty = mk_fun a (mk_fun a bool_ty)"
proof (cases ty)
  case (TyVar n)
  then show ?thesis using assms
    by (simp add: type_match_def mk_fun_def bool_ty_def)
next
  case (TyApp n args)
  have ty_def: "ty = TyApp n args" using TyApp .
  have len: "n = NFun \<and> length args = 2"
    using assms TyApp
    by (auto simp: type_match_def mk_fun_def bool_ty_def split: if_splits)
  obtain a rest where first: "args = a # rest"
    using len by (cases args) auto
  obtain b where args: "args = [a, b]"
    using len first by (cases rest) auto
  have match: "type_match (mk_fun (TyVar NAlpha)
      (mk_fun (TyVar NAlpha) bool_ty)) (TyApp NFun [a, b])
      (\<lambda>_. None) \<noteq> None"
    using assms TyApp len args by simp
  show ?thesis
  proof (cases b)
    case (TyVar bn)
    then show ?thesis using match TyApp len args
      by (auto simp: type_match_def mk_fun_def bool_ty_def
          split: option.splits if_splits)
  next
    case (TyApp m inner)
    have inner_len: "m = NFun \<and> length inner = 2"
      using match TyApp
      by (auto simp: type_match_def mk_fun_def bool_ty_def split: if_splits)
    obtain c rest' where first': "inner = c # rest'"
      using inner_len by (cases inner) auto
    obtain d where inner: "inner = [c, d]"
      using inner_len first' by (cases rest') auto
    show ?thesis using match ty_def len args TyApp inner_len inner
      by (cases d)
         (auto simp: type_match_def mk_fun_def bool_ty_def
           split: htype.splits hname.splits list.splits option.splits if_splits)
  qed
qed

definition semantic_type_fvars ::
  "(hname \<Rightarrow> htype option) \<Rightarrow> ((hname \<times> htype) \<Rightarrow> ZF) \<Rightarrow>
    (hname \<times> htype) \<Rightarrow> ZF" where
  "semantic_type_fvars \<theta> \<nu> key = \<nu> (fst key, type_subst \<theta> (snd key))"

lemma const_sem_type_subst:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and subst_ok: "type_subst_ok thy outer"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and checked: "check_open_term thy [] (Const n ty)"
  shows "const_sem F \<rho> n (type_subst outer ty) =
    const_sem F (subst_valuation F \<rho> outer) n ty"
proof (cases "n = NEq")
  case True
  have match: "type_match (mk_fun (TyVar NAlpha)
      (mk_fun (TyVar NAlpha) bool_ty)) ty (\<lambda>_. None) \<noteq> None"
    using checked thy_wf True by (simp add: wf_theory_def)
  obtain a where shape: "ty = mk_fun a (mk_fun a bool_ty)"
    using equality_match_shape[OF match] by blast
  show ?thesis using True shape
    by (simp add: const_sem_def mk_fun_def bool_ty_def interp_type_subst)
next
  case False
  obtain generic where tab: "const_tab thy n = Some generic"
    using checked by (auto split: option.splits)
  obtain inner where inner_match:
      "type_match generic ty (\<lambda>_. None) = Some inner"
    using checked tab by (auto split: option.splits)
  have inst_checked: "check_open_term thy []
      (Const n (type_subst outer ty))"
    using subst_ok checked by (auto simp: type_subst_ok_def)
  obtain combined where combined_match:
      "type_match generic (type_subst outer ty) (\<lambda>_. None) = Some combined"
    using inst_checked tab by (auto split: option.splits)
  have trivial_ok: "type_valuation_ok (\<lambda>_. zbool)"
    by (auto simp: type_valuation_ok_def inhabited_def)
  have scheme: "const_scheme F n = Some generic"
    using const_ok trivial_ok tab by (auto simp: const_interpretation_ok_def)  have inner_eq: "type_subst inner generic = ty"
    using type_match_sound[OF inner_match] .
  have combined_eq: "type_subst combined generic = type_subst outer ty"
    using type_match_sound[OF combined_match] .
  have composed_eq: "type_subst (compose_type_subst outer inner) generic =
      type_subst outer ty"
    using inner_eq by (simp add: type_subst_compose)
  have valuations_agree: "\<forall>v. type_var_occurs v generic \<longrightarrow>
      subst_valuation F \<rho> combined v =
      subst_valuation F \<rho> (compose_type_subst outer inner) v"
    using type_subst_semantic_agree[OF trans[OF combined_eq sym[OF composed_eq]]]
    by blast
  have denotation_eq: "const_denote F n (subst_valuation F \<rho> combined) =
      const_denote F n (subst_valuation F \<rho> (compose_type_subst outer inner))"
    using frame_ok scheme valuations_agree by (auto simp: frame_wf_def)
  have compose_val: "subst_valuation F \<rho> (compose_type_subst outer inner) =
      subst_valuation F (subst_valuation F \<rho> outer) inner"
    by (rule ext, rule subst_valuation_compose)
  show ?thesis using False scheme inner_match combined_match denotation_eq compose_val
    by (simp add: const_sem_def)
qed

lemma eval_inst_type:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and subst_ok: "type_subst_ok thy \<theta>"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and checked: "check_open_term thy envty t"
  shows "eval_term F \<rho> \<nu> env (inst_type \<theta> t) =
    eval_term F (subst_valuation F \<rho> \<theta>) (semantic_type_fvars \<theta> \<nu>) env t"
  using checked
proof (induction t arbitrary: envty env)
  case (FVar n ty)
  then show ?case by (simp add: semantic_type_fvars_def)
next
  case (BVar i ty)
  then show ?case by simp
next
  case (Const n ty)
  have closed: "check_open_term thy [] (Const n ty)"
    using Const.prems by simp
  show ?case using const_sem_type_subst[OF thy_wf frame_ok subst_ok const_ok closed]
    by simp
next
  case (Comb f x)
  have checks: "check_open_term thy envty f" "check_open_term thy envty x"
    using Comb.prems by auto
  have f: "eval_term F \<rho> \<nu> env (inst_type \<theta> f) =
      eval_term F (subst_valuation F \<rho> \<theta>) (semantic_type_fvars \<theta> \<nu>) env f"
    using Comb.IH(1)[OF checks(1)] .
  have x: "eval_term F \<rho> \<nu> env (inst_type \<theta> x) =
      eval_term F (subst_valuation F \<rho> \<theta>) (semantic_type_fvars \<theta> \<nu>) env x"
    using Comb.IH(2)[OF checks(2)] .
  show ?case using f x by simp
next
  case (Abs aty body)
  have body_checked: "check_open_term thy (aty # envty) body"
    using Abs.prems by simp
  have pointwise: "eval_term F \<rho> \<nu> (z # env) (inst_type \<theta> body) =
      eval_term F (subst_valuation F \<rho> \<theta>) (semantic_type_fvars \<theta> \<nu>)
        (z # env) body" for z
    using Abs.IH[OF body_checked] .
  show ?case using pointwise interp_type_subst[of F \<rho> \<theta> aty]
    by (simp add: Lambda_ext)
qed

section \<open>Valuation transport\<close>

lemma free_valuation_update:
  assumes "free_valuation_ok F \<rho> \<nu>" "Elem z (interp_type F \<rho> ty)"
  shows "free_valuation_ok F \<rho> (\<nu>((n, ty) := z))"
  using assms
  by (auto simp: free_valuation_ok_def)

lemma eval_not_vfree_update:
  assumes "\<not> vfree_in n ty t"
  shows "eval_term F \<rho> (\<nu>((n, ty) := z)) env t = eval_term F \<rho> \<nu> env t"
  using assms
proof (induction t arbitrary: env)
  case (FVar m u)
  then show ?case by (cases "m = n"; cases "u = ty"; simp)
next
  case (BVar i u)
  then show ?case by simp
next
  case (Const m u)
  then show ?case by simp
next
  case (Comb f x)
  then show ?case by simp
next
  case (Abs aty body)
  have body_free: "\<not> vfree_in n ty body" using Abs.prems by simp
  have pointwise: "eval_term F \<rho> (\<nu>((n, ty) := z)) (x # env) body =
      eval_term F \<rho> \<nu> (x # env) body" for x
    using Abs.IH[OF body_free, of "x # env"] .
  show ?case
  proof (simp only: eval_term.simps Lambda_ext, intro conjI allI impI)
    show "interp_type F \<rho> aty = interp_type F \<rho> aty" by simp
  next
    fix x
    assume "Elem x (interp_type F \<rho> aty)"
    show "eval_term F \<rho> (\<nu>((n, ty) := z)) (x # env) body =
      eval_term F \<rho> \<nu> (x # env) body" using pointwise .
  qed
qed

lemma semantic_fvar_subst_ok:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and subst_ok: "wf_term_subst thy \<theta>"
  shows "free_valuation_ok F \<rho> (semantic_fvar_subst F \<rho> \<nu> \<theta>)"
proof (unfold free_valuation_ok_def, intro allI)
  fix n ty
  show "Elem (semantic_fvar_subst F \<rho> \<nu> \<theta> (n, ty)) (interp_type F \<rho> ty)"
  proof (cases "lookup_fvar \<theta> n ty")
    case None
    then show ?thesis using free_ok
      by (simp add: semantic_fvar_subst_def free_valuation_ok_def)
  next
    case (Some rep)
    have rep: "check_term thy rep \<and> type_of rep = Some ty"
      using lookup_fvar_wf[OF subst_ok Some] .
    have empty: "bound_valuation_ok F \<rho> [] []"
      by (simp add: bound_valuation_ok_def)
    have "Elem (eval_term F \<rho> \<nu> [] rep) (interp_type F \<rho> ty)"
      using eval_type_sound[OF thy_wf frame_ok type_ok free_ok const_ok empty]
        rep unfolding check_term_def by blast
    then show ?thesis using Some by (simp add: semantic_fvar_subst_def)
  qed
qed

lemma semantic_type_fvars_ok:
  assumes "free_valuation_ok F \<rho> \<nu>"
  shows "free_valuation_ok F (subst_valuation F \<rho> \<theta>)
    (semantic_type_fvars \<theta> \<nu>)"
  using assms
  by (auto simp: free_valuation_ok_def semantic_type_fvars_def
      interp_type_subst[symmetric])

section \<open>Sequents and models\<close>

definition holds ::
  "frame \<Rightarrow> (hname \<Rightarrow> ZF) \<Rightarrow> ((hname \<times> htype) \<Rightarrow> ZF) \<Rightarrow> hterm \<Rightarrow> bool" where
  "holds F \<rho> \<nu> p \<longleftrightarrow> eval_term F \<rho> \<nu> [] p = ztrue"

definition valid_sequent :: "frame \<Rightarrow> htheory \<Rightarrow> hterm list \<Rightarrow> hterm \<Rightarrow> bool" where
  "valid_sequent F thy hs c \<longleftrightarrow>
    (\<forall>\<rho> \<nu>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho> \<longrightarrow>
      free_valuation_ok F \<rho> \<nu> \<longrightarrow>
      (\<forall>h\<in>set hs. holds F \<rho> \<nu> h) \<longrightarrow> holds F \<rho> \<nu> c)"

definition models_theory :: "frame \<Rightarrow> htheory \<Rightarrow> bool" where
  "models_theory F thy \<longleftrightarrow>
    frame_wf F \<and>
    (\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F thy \<rho>) \<and>
    (\<forall>th\<in>set (axiom_list thy). valid_sequent F thy (hyps th) (concl th)) \<and>
    (\<forall>n th. def_tab thy n = Some th \<longrightarrow>
      valid_sequent F thy (hyps th) (concl th))"

definition semantically_valid :: "htheory \<Rightarrow> hthm \<Rightarrow> bool" where
  "semantically_valid thy th \<longleftrightarrow>
    wf_thm thy th \<and>
    (\<forall>F. models_theory F thy \<longrightarrow> valid_sequent F thy (hyps th) (concl th))"

lemma set_hyp_insert [simp]: "set (hyp_insert h hs) = insert h (set hs)"
  by (auto simp: hyp_insert_def)

lemma set_hyp_union [simp]:
  "set (hyp_union a b) = set a \<union> set b"
  unfolding hyp_union_def
  by (induction b arbitrary: a) auto

lemma set_hyp_remove [simp]:
  "set (hyp_remove h hs) = set hs - {h}"
  by (auto simp: hyp_remove_def)

lemma set_rehash_hyps [simp]: "set (rehash_hyps hs) = set hs"
  unfolding rehash_hyps_def
  by (induction hs rule: rev_induct) auto

lemma eval_eq_term:
  assumes thy_wf: "wf_theory thy" and frame_ok: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and left: "check_term thy l" "type_of l = Some ty"
    and right: "check_term thy r" "type_of r = Some ty"
  shows "eval_term F \<rho> \<nu> [] (eq_term ty l r) =
    (if eval_term F \<rho> \<nu> [] l = eval_term F \<rho> \<nu> [] r then ztrue else zfalse)"
proof -
  have empty: "bound_valuation_ok F \<rho> [] []"
    by (simp add: bound_valuation_ok_def)
  have l_in: "Elem (eval_term F \<rho> \<nu> [] l) (interp_type F \<rho> ty)"
    using eval_type_sound[OF thy_wf frame_ok type_ok free_ok const_ok empty]
      left unfolding check_term_def by blast
  have r_in: "Elem (eval_term F \<rho> \<nu> [] r) (interp_type F \<rho> ty)"
    using eval_type_sound[OF thy_wf frame_ok type_ok free_ok const_ok empty]
      right unfolding check_term_def by blast
  show ?thesis using zeq_apply[OF l_in r_in]
    by (simp add: const_sem_def eq_term_def eq_const_def mk_fun_def bool_ty_def)
qed

lemma holds_eq_iff:
  assumes "wf_theory thy" "frame_wf F" "type_valuation_ok \<rho>"
    "free_valuation_ok F \<rho> \<nu>" "const_interpretation_ok F thy \<rho>"
    "check_term thy l" "type_of l = Some ty"
    "check_term thy r" "type_of r = Some ty"
  shows "holds F \<rho> \<nu> (eq_term ty l r) \<longleftrightarrow>
    eval_term F \<rho> \<nu> [] l = eval_term F \<rho> \<nu> [] r"
  using eval_eq_term[OF assms] ztrue_neq_zfalse
  by (auto simp: holds_def)

lemma subst_valuation_cong_on_instance:
  assumes instantiated: "type_subst \<theta> generic = ty"
    and agree: "\<And>w. type_var_occurs w ty \<Longrightarrow> \<rho> w = \<sigma> w"
    and source: "type_var_occurs v generic"
  shows "subst_valuation F \<rho> \<theta> v = subst_valuation F \<sigma> \<theta> v"
proof (cases "\<theta> v")
  case None
  have occurrence: "type_var_occurs v ty"
    using type_subst_component_occurs[OF source, where \<theta>=\<theta> and w=v]
      None instantiated by simp
  show ?thesis using None agree[OF occurrence]
    by (simp add: subst_valuation_def)
next
  case (Some component)
  have component_agree: "\<And>w. type_var_occurs w component \<Longrightarrow> \<rho> w = \<sigma> w"
  proof -
    fix w
    assume in_component: "type_var_occurs w component"
    have "type_var_occurs w ty"
      using type_subst_component_occurs[OF source, where \<theta>=\<theta> and w=w]
        Some in_component instantiated by simp    then show "\<rho> w = \<sigma> w" by (rule agree)
  qed
  have interp: "interp_type F \<rho> component = interp_type F \<sigma> component"
    using interp_type_cong_occurs component_agree by blast
  show ?thesis using Some interp by (simp add: subst_valuation_def)
qed
lemma const_sem_cong_type_vars:
  assumes frame_ok: "frame_wf F"
    and agree: "\<And>v. v \<in> set (type_vars ty) \<Longrightarrow> \<rho> v = \<sigma> v"
  shows "const_sem F \<rho> n ty = const_sem F \<sigma> n ty"
proof (cases "n = NEq")
  case True
  show ?thesis
  proof (cases "classify_equality_type ty")
    case (Equality_Instance a)
    have shape: "ty = mk_fun a (mk_fun a bool_ty)"
      using classify_equality_instance[OF Equality_Instance]
      by (simp add: mk_fun_def bool_ty_def)
    have a_agree: "\<And>v. type_var_occurs v a \<Longrightarrow> \<rho> v = \<sigma> v"
      using agree shape set_type_vars by (auto simp: mk_fun_def bool_ty_def)
    have carrier: "interp_type F \<rho> a = interp_type F \<sigma> a"
      using interp_type_cong_occurs a_agree by blast
    show ?thesis using True Equality_Instance carrier
      by (simp add: const_sem_def)
  qed (simp_all add: True const_sem_def)
next
  case False
  show ?thesis
  proof (cases "const_scheme F n")
    case None
    then show ?thesis using False by (simp add: const_sem_def)
  next
    case (Some generic)
    have scheme: "const_scheme F n = Some generic" using Some .
    show ?thesis
    proof (cases "type_match generic ty (\<lambda>_. None)")
      case None
      then show ?thesis using False scheme by (simp add: const_sem_def)
    next
      case (Some \<theta>)
      have match: "type_match generic ty (\<lambda>_. None) = Some \<theta>" using Some .
      have instantiated: "type_subst \<theta> generic = ty"
        using type_match_sound[OF match] .
      have target_agree: "\<And>v. type_var_occurs v ty \<Longrightarrow> \<rho> v = \<sigma> v"
        using agree set_type_vars by auto
      have valuation_agree: "\<And>v. type_var_occurs v generic \<Longrightarrow>
          subst_valuation F \<rho> \<theta> v = subst_valuation F \<sigma> \<theta> v"
      proof -
        fix v
        assume source: "type_var_occurs v generic"
        show "subst_valuation F \<rho> \<theta> v = subst_valuation F \<sigma> \<theta> v"
          using subst_valuation_cong_on_instance[where F=F and \<rho>=\<rho> and \<sigma>=\<sigma>
              and \<theta>=\<theta> and generic=generic and ty=ty and v=v,
              OF instantiated target_agree source] .
      qed
      have extensional: "\<forall>r s. (\<forall>v. type_var_occurs v generic \<longrightarrow> r v = s v) \<longrightarrow>
          const_denote F n r = const_denote F n s"
        using frame_ok scheme by (auto simp: frame_wf_def)
      have denote: "const_denote F n (subst_valuation F \<rho> \<theta>) =
          const_denote F n (subst_valuation F \<sigma> \<theta>)"
        using extensional valuation_agree by blast
      have lhs: "const_sem F \<rho> n ty =
          const_denote F n (subst_valuation F \<rho> \<theta>)"
        using const_sem_non_equality[OF False scheme match] .
      have rhs: "const_sem F \<sigma> n ty =
          const_denote F n (subst_valuation F \<sigma> \<theta>)"
        using const_sem_non_equality[OF False scheme match] .
      show ?thesis using lhs rhs denote by simp
    qed  qed
qed

lemma interp_type_cong_type_vars:
  assumes "\<And>v. v \<in> set (type_vars ty) \<Longrightarrow> \<rho> v = \<sigma> v"
  shows "interp_type F \<rho> ty = interp_type F \<sigma> ty"
  using assms interp_type_cong_occurs set_type_vars by auto

lemma eval_term_cong_type_vars:
  assumes frame_ok: "frame_wf F"
    and agree: "\<And>v. v \<in> set (term_type_vars t) \<Longrightarrow> \<rho> v = \<sigma> v"
  shows "eval_term F \<rho> \<nu> env t = eval_term F \<sigma> \<nu> env t"
  using agree
proof (induction t arbitrary: env)
  case (FVar n ty)
  then show ?case by simp
next
  case (BVar i ty)
  then show ?case by simp
next
  case (Const n ty)
  have type_agree: "\<And>v. v \<in> set (type_vars ty) \<Longrightarrow> \<rho> v = \<sigma> v"
    using Const.prems by simp
  show ?case using const_sem_cong_type_vars[OF frame_ok type_agree] by simp
next
  case (Comb f x)
  have f: "eval_term F \<rho> \<nu> env f = eval_term F \<sigma> \<nu> env f"
    using Comb.IH(1) Comb.prems by auto
  have x: "eval_term F \<rho> \<nu> env x = eval_term F \<sigma> \<nu> env x"
    using Comb.IH(2) Comb.prems by auto
  show ?case using f x by simp
next
  case (Abs ty body)
  have type_agree: "\<And>v. v \<in> set (type_vars ty) \<Longrightarrow> \<rho> v = \<sigma> v"
    using Abs.prems by auto
  have carrier: "interp_type F \<rho> ty = interp_type F \<sigma> ty"
    using interp_type_cong_type_vars[OF type_agree] .
  have body: "\<And>z. eval_term F \<rho> \<nu> (z # env) body =
      eval_term F \<sigma> \<nu> (z # env) body"
    using Abs.IH Abs.prems by auto
  show ?case using carrier body by simp
qed

lemma eval_term_cong_free_vars:
  assumes agree: "\<And>key. key \<in> set (free_vars t) \<Longrightarrow> \<nu> key = \<mu> key"
  shows "eval_term F \<rho> \<nu> env t = eval_term F \<rho> \<mu> env t"
  using agree
proof (induction t arbitrary: env)
  case (FVar n ty)
  then show ?case by simp
next
  case (BVar i ty)
  then show ?case by simp
next
  case (Const n ty)
  then show ?case by simp
next
  case (Comb f x)
  then show ?case by auto
next
  case (Abs ty body)
  have body: "\<And>z. eval_term F \<rho> \<nu> (z # env) body =
      eval_term F \<rho> \<mu> (z # env) body"
    using Abs.IH Abs.prems by auto
  show ?case using body by simp
qed

lemma eval_term_closed_free_valuation:
  assumes closed: "free_vars t = []"
  shows "eval_term F \<rho> \<nu> env t = eval_term F \<rho> \<mu> env t"
proof (rule eval_term_cong_free_vars)
  fix key
  assume "key \<in> set (free_vars t)"
  then show "\<nu> key = \<mu> key" using closed by simp
qed

end