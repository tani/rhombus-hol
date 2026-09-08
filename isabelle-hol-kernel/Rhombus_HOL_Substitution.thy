theory Rhombus_HOL_Substitution
  imports Rhombus_HOL_Syntax
begin

section \<open>Locally nameless operations\<close>

text \<open>Rocq correspondence: Kernel.v and term.rhm shift, substAt, substBVar, abstractAt, abstractFVar, instFVar, and instType.\<close>

fun shift :: "int \<Rightarrow> nat \<Rightarrow> hterm \<Rightarrow> hterm" where
  "shift d cutoff (BVar i ty) =
     (if i < cutoff then BVar i ty else BVar (nat (int i + d)) ty)"
| "shift d cutoff (Comb f x) = Comb (shift d cutoff f) (shift d cutoff x)"
| "shift d cutoff (Abs aty b) = Abs aty (shift d (Suc cutoff) b)"
| "shift _ _ t = t"

fun subst_at :: "nat \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "subst_at j s (BVar i ty) = (if i = j then shift (int j) 0 s else BVar i ty)"
| "subst_at j s (Comb f x) = Comb (subst_at j s f) (subst_at j s x)"
| "subst_at j s (Abs aty b) = Abs aty (subst_at (Suc j) s b)"
| "subst_at _ _ t = t"

definition subst_bvar :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "subst_bvar s body = shift (-1) 0 (subst_at 0 s body)"

fun abstract_at :: "nat \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> hterm \<Rightarrow> hterm" where
  "abstract_at j n ty (FVar m u) =
     (if n = m \<and> ty = u then BVar j ty else FVar m u)"
| "abstract_at j n ty (Comb f x) =
     Comb (abstract_at j n ty f) (abstract_at j n ty x)"
| "abstract_at j n ty (Abs aty b) = Abs aty (abstract_at (Suc j) n ty b)"
| "abstract_at _ _ _ t = t"

definition abstract_fvar :: "hname \<Rightarrow> htype \<Rightarrow> hterm \<Rightarrow> hterm" where
  "abstract_fvar n ty body = abstract_at 0 n ty body"

fun lookup_fvar :: "(hterm \<times> (hname \<times> htype)) list \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> hterm option" where
  "lookup_fvar [] _ _ = None"
| "lookup_fvar ((rep, (n, ty)) # rest) m u =
     (if n = m \<and> ty = u then Some rep else lookup_fvar rest m u)"

fun inst_fvar_at :: "(hterm \<times> (hname \<times> htype)) list \<Rightarrow> nat \<Rightarrow> hterm \<Rightarrow> hterm" where
  "inst_fvar_at \<theta> depth (FVar n ty) =
     (case lookup_fvar \<theta> n ty of None \<Rightarrow> FVar n ty | Some rep \<Rightarrow> shift (int depth) 0 rep)"
| "inst_fvar_at \<theta> depth (Comb f x) =
     Comb (inst_fvar_at \<theta> depth f) (inst_fvar_at \<theta> depth x)"
| "inst_fvar_at \<theta> depth (Abs aty b) = Abs aty (inst_fvar_at \<theta> (Suc depth) b)"
| "inst_fvar_at _ _ t = t"

definition inst_fvar :: "(hterm \<times> (hname \<times> htype)) list \<Rightarrow> hterm \<Rightarrow> hterm" where
  "inst_fvar \<theta> t = inst_fvar_at \<theta> 0 t"

fun inst_type :: "(hname \<Rightarrow> htype option) \<Rightarrow> hterm \<Rightarrow> hterm" where
  "inst_type \<theta> (FVar n ty) = FVar n (type_subst \<theta> ty)"
| "inst_type \<theta> (BVar i ty) = BVar i (type_subst \<theta> ty)"
| "inst_type \<theta> (Const n ty) = Const n (type_subst \<theta> ty)"
| "inst_type \<theta> (Comb f x) = Comb (inst_type \<theta> f) (inst_type \<theta> x)"
| "inst_type \<theta> (Abs aty b) = Abs (type_subst \<theta> aty) (inst_type \<theta> b)"

section \<open>Type preservation\<close>

lemma shift_type_of [simp]: "type_of (shift d cutoff t) = type_of t"
  by (induction t arbitrary: cutoff)
     (auto split: htype.splits option.splits prod.splits)

lemma abstract_at_type_of [simp]:
  "type_of (abstract_at j n ty t) = type_of t"
  by (induction t arbitrary: j)
     (auto split: htype.splits option.splits prod.splits)

lemma inst_type_type_of:
  "type_of t = Some ty \<Longrightarrow> type_of (inst_type \<theta> t) = Some (type_subst \<theta> ty)"
proof (induction t arbitrary: ty)
  case (Comb f x)
  then obtain dty rty where parts:
    "type_of f = Some (TyApp NFun [dty, rty])"
    "type_of x = Some dty" "ty = rty"
    by (auto split: htype.splits hname.splits option.splits list.splits if_splits)
  then show ?case using Comb.IH by simp
qed (auto simp: mk_fun_def split: option.splits)

lemma check_open_term_weaken:
  "check_open_term thy env t \<Longrightarrow> check_open_term thy (env @ extra) t"
proof (induction t arbitrary: env)
  case (Abs aty body)
  have body0: "check_open_term thy (aty # env) body"
    using Abs.prems by simp
  have body': "check_open_term thy ((aty # env) @ extra) body"
    using Abs.IH[OF body0] .
  show ?case using Abs.prems body' by simp
qed (auto simp: nth_append split: option.splits if_splits)

lemma abstract_at_check:
  assumes "check_open_term thy env t" "j < length env" "env ! j = ty"
  shows "check_open_term thy env (abstract_at j n ty t)"
  using assms
  by (induction t arbitrary: env j)
     (auto simp: nth_Cons split: htype.splits option.splits prod.splits if_splits)

lemma abstract_at_removes_fvar:
  "\<not> vfree_in n ty (abstract_at depth n ty t)"
  by (induction t arbitrary: depth) auto

lemma abstract_fvar_removes_fvar:
  "\<not> vfree_in n ty (abstract_fvar n ty t)"
  by (simp add: abstract_fvar_def abstract_at_removes_fvar)

lemma abstract_fvar_preserves_check:
  assumes "check_open_term thy [] (FVar n ty)" "check_open_term thy [] body"
  shows "check_term thy (Abs ty (abstract_fvar n ty body))"
proof -
  have body': "check_open_term thy [ty] body"
    using assms(2) check_open_term_weaken[of thy "[]" body "[ty]"] by simp
  have "check_open_term thy [ty] (abstract_at 0 n ty body)"
    using abstract_at_check[OF body', of 0 ty n] by simp
  then show ?thesis using assms(1)
    by (simp add: check_term_def abstract_fvar_def)
qed

lemma shift_checked_above:
  assumes "check_open_term thy env t" "length env \<le> cutoff"
  shows "shift d cutoff t = t"
  using assms
  by (induction t arbitrary: env cutoff)
     (auto split: option.splits if_splits)

lemma shift_closed [simp]:
  "check_term thy t \<Longrightarrow> shift d cutoff t = t"
  using shift_checked_above[of thy "[]" t cutoff d]
  by (simp add: check_term_def)

lemma subst_at_type_of:
  assumes "check_open_term thy (prefix @ [aty]) t"
    "length prefix = j" "type_of s = Some aty"
  shows "type_of (subst_at j s t) = type_of t"
  using assms
proof (induction t arbitrary: prefix j aty)
  case (Comb f x)
  have f_eq: "type_of (subst_at j s f) = type_of f"
    using Comb.IH(1)[of prefix aty j] Comb.prems by simp
  have x_eq: "type_of (subst_at j s x) = type_of x"
    using Comb.IH(2)[of prefix aty j] Comb.prems by simp
  show ?case by (simp add: f_eq x_eq)
next
  case (Abs bty body)
  have body_eq: "type_of (subst_at (Suc j) s body) = type_of body"
    using Abs.IH[of "bty # prefix" aty "Suc j"] Abs.prems by simp
  then show ?case by simp
qed (auto simp: nth_append split: if_splits)

lemma subst_at_check:
  assumes body: "check_open_term thy (prefix @ [aty]) t"
    and depth: "length prefix = j"
    and replacement: "check_term thy s" "type_of s = Some aty"
  shows "check_open_term thy prefix
    (shift (-1) (length prefix) (subst_at j s t))"
  using body depth replacement
proof (induction t arbitrary: prefix j aty)
  case (BVar i ty)
  then show ?case using check_open_term_weaken[of thy "[]" s prefix]
    by (auto simp: nth_append check_term_def shift_checked_above split: if_splits)
next
  case (Comb f x)
  have f_checked: "check_open_term thy (prefix @ [aty]) f"
    and x_checked: "check_open_term thy (prefix @ [aty]) x"
    and app_typed: "type_of (Comb f x) \<noteq> None"
    using Comb.prems by auto
  have f_rec: "check_open_term thy prefix
      (shift (-1) (length prefix) (subst_at j s f))"
    using Comb.IH(1)[OF f_checked] Comb.prems by simp
  have x_rec: "check_open_term thy prefix
      (shift (-1) (length prefix) (subst_at j s x))"
    using Comb.IH(2)[OF x_checked] Comb.prems by simp
  have f_type: "type_of (subst_at j s f) = type_of f"
    by (rule subst_at_type_of[OF f_checked Comb.prems(2) Comb.prems(4)])
  have x_type: "type_of (subst_at j s x) = type_of x"
    by (rule subst_at_type_of[OF x_checked Comb.prems(2) Comb.prems(4)])
  show ?case using f_rec x_rec app_typed f_type x_type Comb.prems by simp
next
  case (Abs bty body)
  have checked: "check_open_term thy ((bty # prefix) @ [aty]) body"
    using Abs.prems by simp
  have rec: "check_open_term thy (bty # prefix)
      (shift (-1) (length (bty # prefix))
        (subst_at (Suc j) s body))"
    using Abs.IH[OF checked] Abs.prems by simp
  then show ?case using Abs.prems by simp
qed auto

lemma subst_bvar_type_preservation:
  assumes "check_open_term thy [aty] body"
    "check_term thy arg" "type_of arg = Some aty"
  shows "type_of (subst_bvar arg body) = type_of body"
  using subst_at_type_of[of thy "[]" aty body 0 arg] assms
  by (simp add: subst_bvar_def)

lemma beta_subject_reduction:
  assumes redex: "check_term thy (Comb (Abs aty body) arg)"
  shows "check_term thy (subst_bvar arg body) \<and>
    type_of (subst_bvar arg body) = type_of (Comb (Abs aty body) arg)"
proof -
  from redex have body: "check_open_term thy [aty] body"
    and arg: "check_term thy arg" and aty: "type_of arg = Some aty"
    by (auto simp: check_term_def mk_fun_def
        split: htype.splits option.splits prod.splits if_splits)
  have checked: "check_term thy (subst_bvar arg body)"
    using subst_at_check[of thy "[]" aty body 0 arg] body arg aty
    by (simp add: check_term_def subst_bvar_def)
  moreover have "type_of (subst_bvar arg body) = type_of body"
    using subst_bvar_type_preservation[OF body arg aty] .
  moreover from redex have "type_of (Comb (Abs aty body) arg) = type_of body"
    by (auto simp: check_term_def mk_fun_def
        split: htype.splits option.splits prod.splits if_splits)
  ultimately show ?thesis by simp
qed

section \<open>Instantiation preservation\<close>

definition wf_term_subst :: "htheory \<Rightarrow> (hterm \<times> (hname \<times> htype)) list \<Rightarrow> bool" where
  "wf_term_subst thy \<theta> \<longleftrightarrow>
    list_all (\<lambda>(rep, (_, ty)). check_term thy rep \<and> type_of rep = Some ty) \<theta>"

lemma lookup_fvar_wf:
  assumes "wf_term_subst thy \<theta>" "lookup_fvar \<theta> n ty = Some rep"
  shows "check_term thy rep \<and> type_of rep = Some ty"
  using assms
  by (induction \<theta>) (auto simp: wf_term_subst_def split: if_splits prod.splits)

lemma inst_fvar_at_type_of:
  assumes "wf_term_subst thy \<theta>" "check_open_term thy env t"
  shows "type_of (inst_fvar_at \<theta> depth t) = type_of t"
  using assms
proof (induction t arbitrary: env depth)
  case (FVar n ty)
  then show ?case using lookup_fvar_wf[of thy \<theta> n ty]
    by (auto split: option.splits)
next
  case (Comb f x)
  have f_checked: "check_open_term thy env f"
    and x_checked: "check_open_term thy env x" using Comb.prems by auto
  have f_eq: "type_of (inst_fvar_at \<theta> depth f) = type_of f"
    using Comb.IH(1)[OF Comb.prems(1) f_checked] .
  have x_eq: "type_of (inst_fvar_at \<theta> depth x) = type_of x"
    using Comb.IH(2)[OF Comb.prems(1) x_checked] .
  show ?case by (simp add: f_eq x_eq)
qed (auto split: option.splits)

lemma inst_fvar_at_preserves_check:
  assumes "wf_term_subst thy \<theta>" "check_open_term thy env t"
    "length env = depth"
  shows "check_open_term thy env (inst_fvar_at \<theta> depth t)"
  using assms
proof (induction t arbitrary: env depth)
  case (FVar n ty)
  then show ?case
    using lookup_fvar_wf[of thy \<theta> n ty]
      check_open_term_weaken[of thy "[]" _ env]
    by (auto simp: check_term_def split: option.splits)
next
  case (Comb f x)
  have f_checked: "check_open_term thy env f"
    and x_checked: "check_open_term thy env x"
    and app_typed: "type_of (Comb f x) \<noteq> None" using Comb.prems by auto
  have f_rec: "check_open_term thy env (inst_fvar_at \<theta> depth f)"
    using Comb.IH(1)[OF Comb.prems(1) f_checked Comb.prems(3)] .
  have x_rec: "check_open_term thy env (inst_fvar_at \<theta> depth x)"
    using Comb.IH(2)[OF Comb.prems(1) x_checked Comb.prems(3)] .
  have f_type: "type_of (inst_fvar_at \<theta> depth f) = type_of f"
    using inst_fvar_at_type_of[OF Comb.prems(1) f_checked] .
  have x_type: "type_of (inst_fvar_at \<theta> depth x) = type_of x"
    using inst_fvar_at_type_of[OF Comb.prems(1) x_checked] .
  show ?case using f_rec x_rec app_typed f_type x_type by simp
next
  case (Abs aty body)
  then show ?case by simp
qed auto

lemma inst_fvar_preserves_check:
  assumes "wf_term_subst thy \<theta>" "check_term thy t"
  shows "check_term thy (inst_fvar \<theta> t)"
  using inst_fvar_at_preserves_check[of thy \<theta> "[]" t 0] assms
  by (simp add: check_term_def inst_fvar_def)

definition type_subst_ok :: "htheory \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow> bool" where
  "type_subst_ok thy \<theta> \<longleftrightarrow>
    (\<forall>n ty. \<theta> n = Some ty \<longrightarrow> check_type thy ty) \<and>
    (\<forall>ty. check_type thy ty \<longrightarrow> check_type thy (type_subst \<theta> ty)) \<and>
    (\<forall>n ty. check_open_term thy [] (Const n ty) \<longrightarrow>
      check_open_term thy [] (Const n (type_subst \<theta> ty)))"

lemma inst_type_preserves_check_open:
  assumes "type_subst_ok thy \<theta>" "check_open_term thy env t"
  shows "check_open_term thy (map (type_subst \<theta>) env) (inst_type \<theta> t)"
  using assms
proof (induction t arbitrary: env)
  case (Comb f x)
  have f_checked: "check_open_term thy env f"
    and x_checked: "check_open_term thy env x"
    and app_typed: "type_of (Comb f x) \<noteq> None" using Comb.prems by auto
  obtain dty rty where types:
    "type_of f = Some (TyApp NFun [dty, rty])" "type_of x = Some dty"
    using app_typed
    by (auto split: htype.splits hname.splits option.splits list.splits if_splits)
  have f_rec: "check_open_term thy (map (type_subst \<theta>) env) (inst_type \<theta> f)"
    using Comb.IH(1)[OF Comb.prems(1) f_checked] .
  have x_rec: "check_open_term thy (map (type_subst \<theta>) env) (inst_type \<theta> x)"
    using Comb.IH(2)[OF Comb.prems(1) x_checked] .
  have f_type: "type_of (inst_type \<theta> f) =
      Some (TyApp NFun [type_subst \<theta> dty, type_subst \<theta> rty])"
    using inst_type_type_of[OF types(1)] by simp
  have x_type: "type_of (inst_type \<theta> x) = Some (type_subst \<theta> dty)"
    using inst_type_type_of[OF types(2)] .
  show ?case using f_rec x_rec f_type x_type by simp
next
  case (Abs aty body)
  have body_rec: "check_open_term thy
      (type_subst \<theta> aty # map (type_subst \<theta>) env) (inst_type \<theta> body)"
    using Abs.IH[of "aty # env"] Abs.prems by simp
  then show ?case using Abs.prems by (auto simp: type_subst_ok_def)
qed (auto simp: type_subst_ok_def split: option.splits if_splits)

lemma inst_type_preserves_check:
  assumes "type_subst_ok thy \<theta>" "check_term thy t"
  shows "check_term thy (inst_type \<theta> t)"
  using inst_type_preserves_check_open[of thy \<theta> "[]" t] assms
  by (simp add: check_term_def)

end
