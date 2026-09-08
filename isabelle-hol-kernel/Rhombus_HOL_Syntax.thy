theory Rhombus_HOL_Syntax
  imports "HOL-ZF.MainZF"
begin

text \<open>Trust boundary: Isabelle/HOL, HOLZF's axiomatized ZFC universe, and the three target-logic base axioms ETA_AX, SELECT_AX, and BOOL_CASES_AX. INFINITY_AX is a proved fact of the HOLZF model, not a target-theory axiom. New axioms are only conditionally model-preserving.\<close>

section \<open>Deep syntax and provenance\<close>

text \<open>Rhombus correspondence: kernel.rhm's names, types, terms, stamps, theorems, and theories. The final name constructor records both generative identity and display text.\<close>

datatype hname = NFun | NBool | NEq | NAlpha | NRepVar | NUser nat string

datatype htype = TyVar hname | TyApp hname "htype list"

datatype hterm =
    FVar hname htype
  | BVar nat htype
  | Const hname htype
  | Comb hterm hterm
  | Abs htype hterm

record stamp =
  sid :: nat
  gen :: nat
  ancestors :: "nat set"

record hthm =
  hyps :: "hterm list"
  concl :: hterm
  thm_stamp :: stamp

record htheory =
  tyops :: "hname \<Rightarrow> nat option"
  const_tab :: "hname \<Rightarrow> htype option"
  axiom_list :: "hthm list"
  def_tab :: "hname \<Rightarrow> hthm option"
  thy_stamp :: stamp

section \<open>Names and types\<close>

definition bool_ty :: htype where
  "bool_ty = TyApp NBool []"

definition mk_fun :: "htype \<Rightarrow> htype \<Rightarrow> htype" where
  "mk_fun a b = TyApp NFun [a, b]"

fun dest_fun :: "htype \<Rightarrow> (htype \<times> htype) option" where
  "dest_fun (TyApp NFun [a, b]) = Some (a, b)"
| "dest_fun _ = None"

fun insert_once :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_once x xs = (if x \<in> set xs then xs else xs @ [x])"

fun type_vars_acc :: "htype \<Rightarrow> hname list \<Rightarrow> hname list" where
  "type_vars_acc (TyVar n) acc = insert_once n acc"
| "type_vars_acc (TyApp _ args) acc = fold type_vars_acc args acc"

definition type_vars :: "htype \<Rightarrow> hname list" where
  "type_vars ty = type_vars_acc ty []"

fun type_var_occurs :: "hname \<Rightarrow> htype \<Rightarrow> bool" where
  "type_var_occurs v (TyVar n) = (v = n)"
| "type_var_occurs v (TyApp _ args) = list_ex (type_var_occurs v) args"

fun type_operator_occurs :: "hname \<Rightarrow> htype \<Rightarrow> bool" where
  "type_operator_occurs op (TyVar _) = False"
| "type_operator_occurs op (TyApp n args) =
    (op = n \<or> list_ex (type_operator_occurs op) args)"

fun type_subst :: "(hname \<Rightarrow> htype option) \<Rightarrow> htype \<Rightarrow> htype" where
  "type_subst \<theta> (TyVar n) = (case \<theta> n of None \<Rightarrow> TyVar n | Some ty \<Rightarrow> ty)"
| "type_subst \<theta> (TyApp n args) = TyApp n (map (type_subst \<theta>) args)"

lemma type_subst_component_avoids_operator:
  assumes occurs: "type_var_occurs v generic"
    and avoids: "\<not> type_operator_occurs op (type_subst \<theta> generic)"
  shows "case \<theta> v of None \<Rightarrow> True | Some ty \<Rightarrow> \<not> type_operator_occurs op ty"
  using occurs avoids
proof (induction generic)
  case (TyVar n)
  then show ?case by (cases "\<theta> n") auto
next
  case (TyApp n args)
  then obtain arg where arg: "arg \<in> set args" "type_var_occurs v arg"
    by (auto simp: list_ex_iff)
  have "\<not> type_operator_occurs op (type_subst \<theta> arg)"
    using TyApp.prems(2) arg(1) by (auto simp: list_ex_iff)
  then show ?case using TyApp.IH[OF arg(1) arg(2)] by blast
qed

fun type_match_fuel :: "nat \<Rightarrow> htype \<Rightarrow> htype \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow> (hname \<Rightarrow> htype option) option" where
  "type_match_fuel 0 _ _ _ = None"
| "type_match_fuel (Suc k) (TyVar n) ty acc =
     (case acc n of None \<Rightarrow> Some (acc(n := Some ty))
      | Some old \<Rightarrow> if old = ty then Some acc else None)"
| "type_match_fuel (Suc k) (TyApp n ps) (TyApp m ts) acc =
     (if n = m \<and> length ps = length ts then
        fold (\<lambda>(p, t) r. case r of None \<Rightarrow> None | Some a \<Rightarrow> type_match_fuel k p t a)
          (zip ps ts) (Some acc)
      else None)"
| "type_match_fuel (Suc k) (TyApp _ _) (TyVar _) _ = None"

definition type_match :: "htype \<Rightarrow> htype \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow> (hname \<Rightarrow> htype option) option" where
  "type_match pat ty acc =
    (case type_match_fuel (size pat + 1) pat ty acc of
       None \<Rightarrow> None
     | Some \<theta> \<Rightarrow> if type_subst \<theta> pat = ty then Some \<theta> else None)"

lemma type_match_sound:
  "type_match pat ty acc = Some \<theta> \<Longrightarrow> type_subst \<theta> pat = ty"
  by (auto simp: type_match_def split: option.splits if_splits)

section \<open>Executable term inspection\<close>

text \<open>Rhombus correspondence: typeOf, freeVars, and termTypeVars; failures that raise source exceptions are represented by option or bool.\<close>

fun type_of :: "hterm \<Rightarrow> htype option" where
  "type_of (FVar _ ty) = Some ty"
| "type_of (BVar _ ty) = Some ty"
| "type_of (Const _ ty) = Some ty"
| "type_of (Abs aty body) = map_option (mk_fun aty) (type_of body)"
| "type_of (Comb f x) =
    (case (type_of f, type_of x) of
       (Some (TyApp NFun [dty, rty]), Some aty) \<Rightarrow> if dty = aty then Some rty else None
     | _ \<Rightarrow> None)"

fun free_vars_acc :: "hterm \<Rightarrow> (hname \<times> htype) list \<Rightarrow> (hname \<times> htype) list" where
  "free_vars_acc (FVar n ty) acc = insert_once (n, ty) acc"
| "free_vars_acc (Comb f x) acc = free_vars_acc x (free_vars_acc f acc)"
| "free_vars_acc (Abs _ b) acc = free_vars_acc b acc"
| "free_vars_acc _ acc = acc"

definition free_vars :: "hterm \<Rightarrow> (hname \<times> htype) list" where
  "free_vars t = free_vars_acc t []"

fun term_type_vars_acc :: "hterm \<Rightarrow> hname list \<Rightarrow> hname list" where
  "term_type_vars_acc (FVar _ ty) acc = type_vars_acc ty acc"
| "term_type_vars_acc (BVar _ ty) acc = type_vars_acc ty acc"
| "term_type_vars_acc (Const _ ty) acc = type_vars_acc ty acc"
| "term_type_vars_acc (Comb f x) acc = term_type_vars_acc x (term_type_vars_acc f acc)"
| "term_type_vars_acc (Abs aty b) acc = term_type_vars_acc b (type_vars_acc aty acc)"

definition term_type_vars :: "hterm \<Rightarrow> hname list" where
  "term_type_vars t = term_type_vars_acc t []"

fun vfree_in :: "hname \<Rightarrow> htype \<Rightarrow> hterm \<Rightarrow> bool" where
  "vfree_in n ty (FVar m u) = (n = m \<and> ty = u)"
| "vfree_in n ty (Comb f x) = (vfree_in n ty f \<or> vfree_in n ty x)"
| "vfree_in n ty (Abs _ b) = vfree_in n ty b"
| "vfree_in _ _ _ = False"

section \<open>Theory provenance\<close>

text \<open>Rhombus correspondence: freshStamp, nextStamp, descends, combineStamps, and initialTheory. Callers provide fresh natural identities; generation is diagnostic only.\<close>

definition wf_stamp :: "stamp \<Rightarrow> bool" where
  "wf_stamp st \<longleftrightarrow> sid st \<in> ancestors st"

definition fresh_stamp :: "nat \<Rightarrow> stamp" where
  "fresh_stamp fresh = \<lparr>sid = fresh, gen = 0, ancestors = {fresh}\<rparr>"

definition next_stamp :: "nat \<Rightarrow> stamp \<Rightarrow> stamp" where
  "next_stamp fresh prev =
    \<lparr>sid = fresh, gen = Suc (gen prev), ancestors = insert fresh (ancestors prev)\<rparr>"

definition descends :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" where
  "descends old new \<longleftrightarrow> sid old \<in> ancestors new"

definition combine_stamps :: "stamp \<Rightarrow> stamp \<Rightarrow> stamp option" where
  "combine_stamps a b =
    (if descends a b then Some b else if descends b a then Some a else None)"

definition initial_theory :: "nat \<Rightarrow> htheory" where
  "initial_theory fresh =
    \<lparr>tyops = (\<lambda>_. None)(NFun := Some 2, NBool := Some 0),
     const_tab = (\<lambda>_. None)(NEq := Some (mk_fun (TyVar NAlpha)
       (mk_fun (TyVar NAlpha) bool_ty))),
     axiom_list = [], def_tab = (\<lambda>_. None), thy_stamp = fresh_stamp fresh\<rparr>"

lemma fresh_stamp_wf [simp]: "wf_stamp (fresh_stamp fresh)"
  by (simp add: wf_stamp_def fresh_stamp_def)

lemma next_stamp_wf [simp]: "wf_stamp (next_stamp fresh st)"
  by (simp add: wf_stamp_def next_stamp_def)

lemma next_stamp_descends: "wf_stamp st \<Longrightarrow> descends st (next_stamp fresh st)"
  by (simp add: wf_stamp_def descends_def next_stamp_def)

lemma combine_stamps_later:
  "combine_stamps a b = Some st \<Longrightarrow> st = a \<or> st = b"
  by (auto simp: combine_stamps_def split: if_splits)

lemma combine_stamps_siblings:
  "\<not> descends a b \<Longrightarrow> \<not> descends b a \<Longrightarrow> combine_stamps a b = None"
  by (simp add: combine_stamps_def)

section \<open>Executable checks and sequents\<close>

text \<open>Rhombus correspondence: checkType, checkOpenTerm, checkTerm, isBool, mkEq, destEq, and duplicate-free hypothesis operations.\<close>

fun check_type :: "htheory \<Rightarrow> htype \<Rightarrow> bool" where
  "check_type thy (TyVar _) = True"
| "check_type thy (TyApp n args) =
    (tyops thy n = Some (length args) \<and> list_all (check_type thy) args)"

lemma checked_type_avoids_fresh_operator:
  assumes "tyops thy op = None" "check_type thy ty"
  shows "\<not> type_operator_occurs op ty"
  using assms by (induction ty) (auto simp: list_all_iff list_ex_iff)

fun check_open_term :: "htheory \<Rightarrow> htype list \<Rightarrow> hterm \<Rightarrow> bool" where
  "check_open_term thy env (FVar _ ty) = check_type thy ty"
| "check_open_term thy env (BVar i ty) =
    (i < length env \<and> env ! i = ty \<and> check_type thy ty)"
| "check_open_term thy env (Const n ty) =
    (check_type thy ty \<and>
      (case const_tab thy n of None \<Rightarrow> False
       | Some generic \<Rightarrow> type_match generic ty (\<lambda>_. None) \<noteq> None))"
| "check_open_term thy env (Comb f x) =
    (check_open_term thy env f \<and> check_open_term thy env x \<and> type_of (Comb f x) \<noteq> None)"
| "check_open_term thy env (Abs aty body) =
    (check_type thy aty \<and> check_open_term thy (aty # env) body)"

definition check_term :: "htheory \<Rightarrow> hterm \<Rightarrow> bool" where
  "check_term thy t \<longleftrightarrow> check_open_term thy [] t"

definition is_bool :: "hterm \<Rightarrow> bool" where
  "is_bool t \<longleftrightarrow> type_of t = Some bool_ty"

definition check_prop :: "htheory \<Rightarrow> hterm \<Rightarrow> bool" where
  "check_prop thy p \<longleftrightarrow> check_term thy p \<and> is_bool p"

definition eq_const :: "htype \<Rightarrow> hterm" where
  "eq_const ty = Const NEq (mk_fun ty (mk_fun ty bool_ty))"

definition eq_term :: "htype \<Rightarrow> hterm \<Rightarrow> hterm \<Rightarrow> hterm" where
  "eq_term ty l r = Comb (Comb (eq_const ty) l) r"

definition mk_eq :: "hterm \<Rightarrow> hterm \<Rightarrow> hterm option" where
  "mk_eq l r =
    (case (type_of l, type_of r) of
       (Some lty, Some rty) \<Rightarrow> if lty = rty then Some (eq_term lty l r) else None
     | _ \<Rightarrow> None)"

fun dest_eq :: "hterm \<Rightarrow> (hterm \<times> hterm) option" where
  "dest_eq (Comb (Comb (Const NEq _) l) r) = Some (l, r)"
| "dest_eq _ = None"

definition hyp_insert :: "hterm \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "hyp_insert t hs = insert_once t hs"

definition hyp_union :: "hterm list \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "hyp_union a b = fold hyp_insert b a"

definition hyp_remove :: "hterm \<Rightarrow> hterm list \<Rightarrow> hterm list" where
  "hyp_remove t hs = filter (\<lambda>h. h \<noteq> t) hs"

definition rehash_hyps :: "hterm list \<Rightarrow> hterm list" where
  "rehash_hyps hs = fold hyp_insert hs []"

definition wf_theory :: "htheory \<Rightarrow> bool" where
  "wf_theory thy \<longleftrightarrow>
    wf_stamp (thy_stamp thy) \<and>
    tyops thy NFun = Some 2 \<and> tyops thy NBool = Some 0 \<and>
    const_tab thy NEq = Some (mk_fun (TyVar NAlpha) (mk_fun (TyVar NAlpha) bool_ty)) \<and>
    (\<forall>n ty. const_tab thy n = Some ty \<longrightarrow> check_type thy ty)"

definition wf_thm :: "htheory \<Rightarrow> hthm \<Rightarrow> bool" where
  "wf_thm thy th \<longleftrightarrow>
    distinct (hyps th) \<and> check_prop thy (concl th) \<and>
    list_all (check_prop thy) (hyps th) \<and> descends (thm_stamp th) (thy_stamp thy)"

lemma hyp_insert_distinct:
  "distinct hs \<Longrightarrow> distinct (hyp_insert t hs)"
  by (simp add: hyp_insert_def)

lemma hyp_union_distinct:
  "distinct a \<Longrightarrow> distinct b \<Longrightarrow> distinct (hyp_union a b)"
  by (induction b arbitrary: a) (auto simp: hyp_union_def hyp_insert_def)

lemma fold_hyp_insert_distinct:
  "distinct acc \<Longrightarrow> distinct (fold hyp_insert xs acc)"
  by (induction xs arbitrary: acc) (auto simp: hyp_insert_def)

lemma rehash_hyps_distinct [simp]: "distinct (rehash_hyps hs)"
  by (simp add: rehash_hyps_def fold_hyp_insert_distinct)

lemma same_printing_symbols_remain_distinct:
  "length (hyp_insert (FVar (NUser 1 ''x'') bool_ty)
     (hyp_insert (FVar (NUser 0 ''x'') bool_ty) [])) = 2"
  by (simp add: hyp_insert_def bool_ty_def)

lemma initial_theory_wf [simp]: "wf_theory (initial_theory fresh)"
  by (auto simp: wf_theory_def initial_theory_def mk_fun_def bool_ty_def
      type_match_def split: hname.splits option.splits)

lemma set_fold_acc_union:
  assumes step: "\<And>x acc. x \<in> set xs \<Longrightarrow> set (F x acc) = G x \<union> set acc"
  shows "set (fold F xs acc) = (\<Union>x\<in>set xs. G x) \<union> set acc"
  using step
proof (induction xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have head: "set (F x acc) = G x \<union> set acc"
    using Cons.prems by auto
  have tail_step: "\<And>y rest. y \<in> set xs \<Longrightarrow>
      set (F y rest) = G y \<union> set rest"
    using Cons.prems by auto
  have tail: "set (fold F xs (F x acc)) =
      (\<Union>y\<in>set xs. G y) \<union> set (F x acc)"
    using Cons.IH[OF tail_step] .
  show ?case using head tail by auto
qed

lemma set_type_vars_acc:
  "set (type_vars_acc ty acc) = {v. type_var_occurs v ty} \<union> set acc"
proof (induction ty arbitrary: acc)
  case (TyVar n)
  then show ?case by auto
next
  case (TyApp n args)
  have step: "\<And>ty rest. ty \<in> set args \<Longrightarrow>
      set (type_vars_acc ty rest) =
        {v. type_var_occurs v ty} \<union> set rest"
    using TyApp.IH .
  have fold: "set (fold type_vars_acc args acc) =
      (\<Union>ty\<in>set args. {v. type_var_occurs v ty}) \<union> set acc"
    using set_fold_acc_union[OF step] .
  show ?case using fold by (auto simp: list_ex_iff)
qed

lemma set_type_vars:
  "set (type_vars ty) = {v. type_var_occurs v ty}"
  by (simp add: type_vars_def set_type_vars_acc)

lemma set_term_type_vars_acc:
  "set (term_type_vars_acc t acc) =
    set (term_type_vars t) \<union> set acc"
proof (induction t arbitrary: acc)
  case (FVar n ty)
  then show ?case by (simp add: term_type_vars_def set_type_vars_acc)
next
  case (BVar i ty)
  then show ?case by (simp add: term_type_vars_def set_type_vars_acc)
next
  case (Const n ty)
  then show ?case by (simp add: term_type_vars_def set_type_vars_acc)
next
  case (Comb f x)
  have first: "set (term_type_vars_acc f acc) =
      set (term_type_vars f) \<union> set acc"
    using Comb.IH(1) .
  have second: "set (term_type_vars_acc x (term_type_vars_acc f acc)) =
      set (term_type_vars x) \<union> set (term_type_vars_acc f acc)"
    using Comb.IH(2) .
  have empty: "set (term_type_vars_acc x (term_type_vars_acc f [])) =
      set (term_type_vars x) \<union> set (term_type_vars f)"
    using Comb.IH by auto
  show ?case using first second empty by (simp add: term_type_vars_def) auto
next
  case (Abs ty body)
  have body: "set (term_type_vars_acc body (type_vars_acc ty acc)) =
      set (term_type_vars body) \<union> set (type_vars_acc ty acc)"
    using Abs.IH .
  have empty: "set (term_type_vars_acc body (type_vars_acc ty [])) =
      set (term_type_vars body) \<union> set (type_vars ty)"
    using Abs.IH by (simp add: type_vars_def)
  have ty_set: "set (type_vars ty) = {v. type_var_occurs v ty}"
    by (rule set_type_vars)
  show ?case using body empty ty_set
    by (simp add: term_type_vars_def set_type_vars_acc) auto
qed
lemma set_term_type_vars_FVar [simp]:
  "set (term_type_vars (FVar n ty)) = set (type_vars ty)"
  by (simp add: term_type_vars_def type_vars_def)

lemma set_term_type_vars_BVar [simp]:
  "set (term_type_vars (BVar i ty)) = set (type_vars ty)"
  by (simp add: term_type_vars_def type_vars_def)

lemma set_term_type_vars_Const [simp]:
  "set (term_type_vars (Const n ty)) = set (type_vars ty)"
  by (simp add: term_type_vars_def type_vars_def)

lemma set_term_type_vars_Comb [simp]:
  "set (term_type_vars (Comb f x)) =
    set (term_type_vars f) \<union> set (term_type_vars x)"
  using set_term_type_vars_acc[of x "term_type_vars_acc f []"]
  by (auto simp: term_type_vars_def)
lemma set_term_type_vars_Abs [simp]:
  "set (term_type_vars (Abs ty body)) =
    set (type_vars ty) \<union> set (term_type_vars body)"
  using set_term_type_vars_acc[of body "type_vars_acc ty []"]
  by (auto simp: term_type_vars_def type_vars_def)

lemma type_subst_component_occurs:
  assumes source: "type_var_occurs v generic"
    and component: "case \<theta> v of None \<Rightarrow> w = v
      | Some ty \<Rightarrow> type_var_occurs w ty"
  shows "type_var_occurs w (type_subst \<theta> generic)"
  using source component
proof (induction generic)
  case (TyVar n)
  then show ?case by (cases "\<theta> n") auto
next
  case (TyApp n args)
  then obtain arg where member: "arg \<in> set args"
    and occurs: "type_var_occurs v arg"
    by (auto simp: list_ex_iff)
  have "type_var_occurs w (type_subst \<theta> arg)"
    using TyApp.IH[OF member occurs TyApp.prems(2)] .
  then show ?case using member by (auto simp: list_ex_iff)
qed

lemma set_free_vars_acc:
  "set (free_vars_acc t acc) = set (free_vars t) \<union> set acc"
proof (induction t arbitrary: acc)
  case (FVar n ty)
  then show ?case by (auto simp: free_vars_def)
next
  case (BVar i ty)
  then show ?case by (simp add: free_vars_def)
next
  case (Const n ty)
  then show ?case by (simp add: free_vars_def)
next
  case (Comb f x)
  have first: "set (free_vars_acc f acc) =
      set (free_vars f) \<union> set acc" using Comb.IH(1) .
  have second: "set (free_vars_acc x (free_vars_acc f acc)) =
      set (free_vars x) \<union> set (free_vars_acc f acc)"
    using Comb.IH(2) .
  have empty: "set (free_vars_acc x (free_vars_acc f [])) =
      set (free_vars x) \<union> set (free_vars f)"
    using Comb.IH by auto
  show ?case using first second empty by (auto simp: free_vars_def)
next
  case (Abs ty body)
  have collected: "set (free_vars_acc body acc) =
      set (free_vars body) \<union> set acc"
    using Abs.IH .
  have same: "free_vars (Abs ty body) = free_vars body"
    unfolding free_vars_def by simp
  show ?case using collected same by simp
qed

lemma set_free_vars_FVar [simp]:
  "set (free_vars (FVar n ty)) = {(n, ty)}"
  by (auto simp: free_vars_def)

lemma set_free_vars_BVar [simp]: "set (free_vars (BVar i ty)) = {}"
  by (simp add: free_vars_def)

lemma set_free_vars_Const [simp]: "set (free_vars (Const n ty)) = {}"
  by (simp add: free_vars_def)

lemma set_free_vars_Comb [simp]:
  "set (free_vars (Comb f x)) = set (free_vars f) \<union> set (free_vars x)"
  using set_free_vars_acc[of x "free_vars_acc f []"]
  by (auto simp: free_vars_def)

lemma set_free_vars_Abs [simp]:
  "set (free_vars (Abs ty body)) = set (free_vars body)"
  by (simp add: free_vars_def)

end