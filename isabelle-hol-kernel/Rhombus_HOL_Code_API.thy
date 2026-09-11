(* SPDX-License-Identifier: 0BSD AND BSD-2-Clause AND BSD-3-Clause *)
(* Conservatively covered by HOL Light and HOL4 notices; see THIRD_PARTY_NOTICES. *)

theory Rhombus_HOL_Code_API
  imports Rhombus_HOL_Audit
begin

section \<open>Finite code-generation façade\<close>

type_synonym type_subst_entries = "(hname \<times> htype) list"

definition entries_subst :: "type_subst_entries \<Rightarrow> hname \<Rightarrow> htype option" where
  "entries_subst entries = map_of entries"

definition valid_type_subst_entries ::
  "htheory \<Rightarrow> type_subst_entries \<Rightarrow> bool" where
  "valid_type_subst_entries thy entries \<longleftrightarrow>
    distinct (map fst entries) \<and> list_all (check_type thy \<circ> snd) entries"

lemma valid_type_subst_entries_lookup:
  assumes "valid_type_subst_entries thy entries"
    "entries_subst entries n = Some ty"
  shows "check_type thy ty"
  using assms map_of_SomeD
  by (auto simp: valid_type_subst_entries_def entries_subst_def list_all_iff)

lemma valid_type_subst_entries_preserve_type:
  assumes valid: "valid_type_subst_entries thy entries"
    and checked: "check_type thy ty"
  shows "check_type thy (type_subst (entries_subst entries) ty)"
  using checked
proof (induction ty)
  case (TyVar n)
  then show ?case
    using valid valid_type_subst_entries_lookup
    by (auto split: option.splits)
next
  case (TyApp n args)
  then show ?case by (auto simp: list_all_iff)
qed

definition subst_option_map ::
  "(hname \<Rightarrow> htype option) \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow> hname \<Rightarrow> htype option" where
  "subst_option_map \<sigma> \<theta> n = map_option (type_subst \<sigma>) (\<theta> n)"

lemma type_subst_option_map:
  assumes "\<forall>n. type_var_occurs n ty \<longrightarrow> \<theta> n \<noteq> None"
  shows "type_subst (subst_option_map \<sigma> \<theta>) ty = type_subst \<sigma> (type_subst \<theta> ty)"
  using assms
proof (induction ty)
  case (TyVar n)
  then show ?case by (cases "\<theta> n") (auto simp: subst_option_map_def)
next
  case (TyApp n args)
  have each: "\<And>arg. arg \<in> set args \<Longrightarrow>
      \<forall>v. type_var_occurs v arg \<longrightarrow> \<theta> v \<noteq> None"
    using TyApp.prems by (auto simp: list_ex_iff)
  have args_eq: "map (type_subst (subst_option_map \<sigma> \<theta>)) args =
      map (type_subst \<sigma> \<circ> type_subst \<theta>) args"
  proof (rule map_cong)
    fix arg
    assume arg: "arg \<in> set args"
    show "type_subst (subst_option_map \<sigma> \<theta>) arg =
      (type_subst \<sigma> \<circ> type_subst \<theta>) arg"
      using TyApp.IH[OF arg each[OF arg]] by simp
  qed simp
  then show ?case by (simp only: type_subst.simps map_map o_apply)
qed

lemma fold_type_match_fuel_none [simp]:
  "fold (\<lambda>(p, t) result.
      case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
    pairs None = None"
  by (induction pairs) auto

lemma fold_type_match_fuel_subst:
  assumes step: "\<And>p t acc out. (p, t) \<in> set pairs \<Longrightarrow>
      type_match_fuel k p t acc = Some out \<Longrightarrow>
      type_match_fuel k p (type_subst \<sigma> t) (subst_option_map \<sigma> acc) =
        Some (subst_option_map \<sigma> out)"
    and run: "fold (\<lambda>(p, t) result.
      case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
      pairs (Some acc) = Some out"
  shows "fold (\<lambda>(p, t) result.
      case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
      (map (\<lambda>(p, t). (p, type_subst \<sigma> t)) pairs)
      (Some (subst_option_map \<sigma> acc)) = Some (subst_option_map \<sigma> out)"
  using run step
proof (induction pairs arbitrary: acc out)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  obtain p t where pair: "pair = (p, t)" by (cases pair)
  show ?case
  proof (cases "type_match_fuel k p t acc")
    case None
    then show ?thesis using Cons.prems pair by simp
  next
    case (Some mid)
    have first: "type_match_fuel k p (type_subst \<sigma> t)
        (subst_option_map \<sigma> acc) = Some (subst_option_map \<sigma> mid)"
      using Cons.prems(2)[of p t acc mid] Some pair by simp
    have rest: "fold (\<lambda>(p, t) result.
        case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
        pairs (Some mid) = Some out"
      using Cons.prems(1) Some pair by simp
    have rest_step: "\<And>p t acc out. (p, t) \<in> set pairs \<Longrightarrow>
        type_match_fuel k p t acc = Some out \<Longrightarrow>
        type_match_fuel k p (type_subst \<sigma> t) (subst_option_map \<sigma> acc) =
          Some (subst_option_map \<sigma> out)"
      using Cons.prems(2) pair by auto
    show ?thesis using Cons.IH[OF rest rest_step] first pair by simp
  qed
qed

lemma type_match_fuel_subst:
  assumes "type_match_fuel k pat ty acc = Some out"
  shows "type_match_fuel k pat (type_subst \<sigma> ty) (subst_option_map \<sigma> acc) =
    Some (subst_option_map \<sigma> out)"
  using assms
proof (induction k pat ty acc arbitrary: out rule: type_match_fuel.induct)
  case (3 k n ps m ts acc)
  show ?case
  proof (cases "n = m \<and> length ps = length ts")
    case False
    have False using 3 False by (auto split: if_splits)
    then show ?thesis by blast
  next
    case True
    have run: "fold (\<lambda>(p, t) result.
        case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
        (zip ps ts) (Some acc) = Some out"
      using 3 True by (auto split: if_splits)
    have step: "\<And>p t acc out. (p, t) \<in> set (zip ps ts) \<Longrightarrow>
        type_match_fuel k p t acc = Some out \<Longrightarrow>
        type_match_fuel k p (type_subst \<sigma> t) (subst_option_map \<sigma> acc) =
          Some (subst_option_map \<sigma> out)"
    proof -
      fix p t acc' out'
      assume mem: "(p, t) \<in> set (zip ps ts)"
        and subrun: "type_match_fuel k p t acc' = Some out'"
      show "type_match_fuel k p (type_subst \<sigma> t) (subst_option_map \<sigma> acc') =
        Some (subst_option_map \<sigma> out')"
        using 3(1)[OF True mem refl subrun] .
    qed
    have transformed: "fold (\<lambda>(p, t) result.
        case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
        (map (\<lambda>(p, t). (p, type_subst \<sigma> t)) (zip ps ts))
        (Some (subst_option_map \<sigma> acc)) = Some (subst_option_map \<sigma> out)"
      using fold_type_match_fuel_subst[OF step run] .
    show ?thesis using transformed True
      by (simp add: zip_map2)
  qed
qed (auto simp: subst_option_map_def split: htype.splits option.splits if_splits)


lemma fold_type_match_fuel_invariant:
  fixes pairs :: "(htype \<times> htype) list"
  assumes step_preserves: "\<And>p t acc out. (p, t) \<in> set pairs \<Longrightarrow>
      type_match_fuel k p t acc = Some out \<Longrightarrow> acc v \<noteq> None \<Longrightarrow> out v = acc v"
    and step_covers: "\<And>p t acc out. (p, t) \<in> set pairs \<Longrightarrow>
      type_match_fuel k p t acc = Some out \<Longrightarrow> type_var_occurs v p \<Longrightarrow> out v \<noteq> None"
    and run: "fold (\<lambda>(p, t) result.
      case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
      pairs (Some acc) = Some out"
  shows "(acc v \<noteq> None \<longrightarrow> out v = acc v) \<and>
    (list_ex (\<lambda>(p, t). type_var_occurs v p) pairs \<longrightarrow> out v \<noteq> None)"
  using step_preserves step_covers run
proof (induction pairs arbitrary: acc out)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  obtain p t where pair: "pair = (p, t)" by (cases pair)
  obtain mid where first: "type_match_fuel k p t acc = Some mid"
    and rest: "fold (\<lambda>(p, t) result.
      case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
      pairs (Some mid) = Some out"
    using Cons.prems(3) unfolding pair
    by (cases "type_match_fuel k p t acc") auto
  have head_mem: "(p, t) \<in> set (pair # pairs)" unfolding pair by simp
  have head_preserves: "acc v \<noteq> None \<Longrightarrow> mid v = acc v"
    using Cons.prems(1)[OF head_mem first] .
  have head_covers: "type_var_occurs v p \<Longrightarrow> mid v \<noteq> None"
    using Cons.prems(2)[OF head_mem first] .
  have tail_preserves: "\<And>p t acc out. (p, t) \<in> set pairs \<Longrightarrow>
      type_match_fuel k p t acc = Some out \<Longrightarrow> acc v \<noteq> None \<Longrightarrow> out v = acc v"
  proof -
    fix p t acc' out'
    assume mem: "(p, t) \<in> set pairs"
      and subrun: "type_match_fuel k p t acc' = Some out'"
      and present: "acc' v \<noteq> None"
    have "(p, t) \<in> set (pair # pairs)" using mem by simp
    then show "out' v = acc' v"
      using Cons.prems(1) subrun present by blast
  qed
  have tail_covers: "\<And>p t acc out. (p, t) \<in> set pairs \<Longrightarrow>
      type_match_fuel k p t acc = Some out \<Longrightarrow> type_var_occurs v p \<Longrightarrow> out v \<noteq> None"
  proof -
    fix p t acc' out'
    assume mem: "(p, t) \<in> set pairs"
      and subrun: "type_match_fuel k p t acc' = Some out'"
      and occurs: "type_var_occurs v p"
    have "(p, t) \<in> set (pair # pairs)" using mem by simp
    then show "out' v \<noteq> None"
      using Cons.prems(2) subrun occurs by blast
  qed
  have tail: "(mid v \<noteq> None \<longrightarrow> out v = mid v) \<and>
      (list_ex (\<lambda>(p, t). type_var_occurs v p) pairs \<longrightarrow> out v \<noteq> None)"
  proof (rule Cons.IH)
    show "\<And>p t acc out. (p, t) \<in> set pairs \<Longrightarrow>
      type_match_fuel k p t acc = Some out \<Longrightarrow> acc v \<noteq> None \<Longrightarrow> out v = acc v"
      by (rule tail_preserves)
    show "\<And>p t acc out. (p, t) \<in> set pairs \<Longrightarrow>
      type_match_fuel k p t acc = Some out \<Longrightarrow> type_var_occurs v p \<Longrightarrow> out v \<noteq> None"
      by (rule tail_covers)
    show "fold (\<lambda>(p, t) result.
      case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
      pairs (Some mid) = Some out" by (rule rest)
  qed
  show ?case using head_preserves head_covers tail unfolding pair by auto
qed

lemma type_match_fuel_invariant:
  assumes "type_match_fuel k pat ty acc = Some out"
  shows "(acc v \<noteq> None \<longrightarrow> out v = acc v) \<and>
    (type_var_occurs v pat \<longrightarrow> out v \<noteq> None)"
  using assms
proof (induction k pat ty acc arbitrary: out rule: type_match_fuel.induct)
  case (3 k n ps m ts acc)
  show ?case
  proof (cases "n = m \<and> length ps = length ts")
    case False
    have False using 3 False by (auto split: if_splits)
    then show ?thesis by blast
  next
    case True
    have run: "fold (\<lambda>(p, t) result.
        case result of None \<Rightarrow> None | Some acc \<Rightarrow> type_match_fuel k p t acc)
        (zip ps ts) (Some acc) = Some out"
      using 3 True by (auto split: if_splits)
    have step_preserves: "\<And>p t acc out. (p, t) \<in> set (zip ps ts) \<Longrightarrow>
        type_match_fuel k p t acc = Some out \<Longrightarrow> acc v \<noteq> None \<Longrightarrow> out v = acc v"
      using 3(1)[OF True] by blast
    have step_covers: "\<And>p t acc out. (p, t) \<in> set (zip ps ts) \<Longrightarrow>
        type_match_fuel k p t acc = Some out \<Longrightarrow> type_var_occurs v p \<Longrightarrow> out v \<noteq> None"
      using 3(1)[OF True] by blast
    have folded: "(acc v \<noteq> None \<longrightarrow> out v = acc v) \<and>
        (list_ex (\<lambda>(p, t). type_var_occurs v p) (zip ps ts) \<longrightarrow> out v \<noteq> None)"
      using fold_type_match_fuel_invariant[OF step_preserves step_covers run] .
    have zipped: "list_ex (type_var_occurs v) ps \<Longrightarrow>
        list_ex (\<lambda>(p, t). type_var_occurs v p) (zip ps ts)"
      using True
    proof (induction ps arbitrary: ts)
      case Nil
      then show ?case by simp
    next
      case (Cons p ps)
      then obtain t ts' where ts: "ts = t # ts'" by (cases ts) auto
      show ?case
      proof (cases "type_var_occurs v p")
        case True
        then show ?thesis unfolding ts by simp
      next
        case False
        have tail_occurs: "list_ex (type_var_occurs v) ps"
          using Cons.prems(1) False by simp
        have tail_length: "n = m \<and> length ps = length ts'"
          using Cons.prems(2) ts by simp
        have tail_zipped: "list_ex (\<lambda>(p, t). type_var_occurs v p) (zip ps ts')"
          using Cons.IH[OF tail_occurs tail_length] .
        then show ?thesis unfolding ts by simp
      qed
    qed
    show ?thesis using folded zipped by auto
  qed
qed (auto simp: subst_option_map_def split: htype.splits option.splits if_splits)


lemma type_match_subst:
  assumes match: "type_match pat ty (\<lambda>_. None) = Some out"
  shows "type_match pat (type_subst \<sigma> ty) (\<lambda>_. None) =
    Some (subst_option_map \<sigma> out)"
proof -
  have run: "type_match_fuel (size pat + 1) pat ty (\<lambda>_. None) = Some out"
    using match by (auto simp: type_match_def split: option.splits if_splits)
  have covers: "\<forall>v. type_var_occurs v pat \<longrightarrow> out v \<noteq> None"
    using type_match_fuel_invariant[OF run] by blast
  have composed: "type_subst (subst_option_map \<sigma> out) pat = type_subst \<sigma> ty"
    using type_subst_option_map[OF covers] type_match_sound[OF match] by simp
  have empty_map: "subst_option_map \<sigma> (\<lambda>_. None) = (\<lambda>_. None)"
    by (rule ext) (simp add: subst_option_map_def)
  have transformed: "type_match_fuel (size pat + 1) pat (type_subst \<sigma> ty)
      (\<lambda>_. None) = Some (subst_option_map \<sigma> out)"
    using type_match_fuel_subst[where \<sigma> = \<sigma>, OF run] empty_map by simp
  show ?thesis unfolding type_match_def using transformed composed by simp
qed


lemma valid_type_subst_entries_type_subst_ok:
  assumes valid: "valid_type_subst_entries thy entries"
  shows "type_subst_ok thy (entries_subst entries)"
  unfolding type_subst_ok_def
proof (intro conjI)
  show "\<forall>n ty. entries_subst entries n = Some ty \<longrightarrow> check_type thy ty"
    using valid valid_type_subst_entries_lookup by blast
  show "\<forall>ty. check_type thy ty \<longrightarrow> check_type thy (type_subst (entries_subst entries) ty)"
    using valid valid_type_subst_entries_preserve_type by blast
  show "\<forall>n ty. check_open_term thy [] (Const n ty) \<longrightarrow>
      check_open_term thy [] (Const n (type_subst (entries_subst entries) ty))"
  proof (intro allI impI)
    fix n ty
    assume checked: "check_open_term thy [] (Const n ty)"
    have checked_type: "check_type thy (type_subst (entries_subst entries) ty)"
      using checked valid valid_type_subst_entries_preserve_type by simp
    obtain generic where generic: "const_tab thy n = Some generic"
      using checked by (cases "const_tab thy n") auto
    obtain out where matched: "type_match generic ty (\<lambda>_. None) = Some out"
      using checked generic by (cases "type_match generic ty (\<lambda>_. None)") auto
    have substituted: "type_match generic (type_subst (entries_subst entries) ty) (\<lambda>_. None) =
        Some (subst_option_map (entries_subst entries) out)"
      using type_match_subst[OF matched] .
    show "check_open_term thy [] (Const n (type_subst (entries_subst entries) ty))"
      using checked_type generic substituted by simp
  qed
qed

definition inst_type_entries ::
  "htheory \<Rightarrow> type_subst_entries \<Rightarrow> hthm \<Rightarrow> hthm option" where
  "inst_type_entries thy entries th =
    (if valid_type_subst_entries thy entries \<and>
        descends (thm_stamp th) (thy_stamp thy) then
       checked_thm thy
         (rehash_hyps (map (inst_type (entries_subst entries)) (hyps th)))
         (inst_type (entries_subst entries) (concl th)) (thy_stamp thy)
     else None)"

lemma inst_type_entries_agrees:
  assumes valid: "valid_type_subst_entries thy entries"
  shows "inst_type_entries thy entries th =
    inst_type_rule thy (entries_subst entries) th"
  using valid valid_type_subst_entries_type_subst_ok[OF valid]
  by (simp add: inst_type_entries_def inst_type_rule_def)


section \<open>Direct code-generation rule façade\<close>

datatype code_failure =
    CodeUndeclaredType hname
  | CodeTypeArity hname nat nat
  | CodeInvalidType htype
  | CodeUnboundIndex nat nat
  | CodeBinderTypeMismatch nat htype htype
  | CodeUndeclaredConstant hname
  | CodeConstantTypeMismatch hname htype htype
  | CodeOperatorNotFunction hterm
  | CodeIllTypedApplication hterm
  | CodeNotProposition hterm
  | CodeNotEquation hterm
  | CodeMiddleTermsDiffer hterm hterm
  | CodeCombinationTypeMismatch
  | CodeVariableFreeInHypotheses hname
  | CodeNotBetaRedex hterm
  | CodeAntecedentMismatch hterm hterm
  | CodeInvalidInstantiationTarget hterm
  | CodeInstantiationTypeMismatch hterm hterm
  | CodeInvalidTypeSubstitution
  | CodeDuplicateType hname
  | CodeDuplicateConstant hname
  | CodeDefinitionNotEquation
  | CodeDefinitionLeftNotVariable
  | CodeDefinitionOpen hterm
  | CodeDefinitionTypeMismatch
  | CodeDefinitionExtraTypeVariables
  | CodeTypeDefinitionSameConstants
  | CodeTypeDefinitionHasHypotheses
  | CodeTypeDefinitionOpenPredicate
  | CodeTypeDefinitionExtraTypeVariables htype
  | CodeTypeDefinitionBadWitness
  | CodeRuleRejected
  | CodeExtensionRejected

datatype 'a code_result =
    CodeSuccess 'a
  | CodeFailure code_failure

fun erase_code_result :: "'a code_result \<Rightarrow> 'a option" where
  "erase_code_result (CodeSuccess value) = Some value"
| "erase_code_result (CodeFailure _) = None"

fun result_of_option :: "code_failure \<Rightarrow> 'a option \<Rightarrow> 'a code_result" where
  "result_of_option _ (Some value) = CodeSuccess value"
| "result_of_option failure None = CodeFailure failure"

lemma erase_result_of_option [simp]:
  "erase_code_result (result_of_option failure result) = result"
  by (cases result) simp_all

lemma result_of_option_success_iff [simp]:
  "result_of_option failure result = CodeSuccess value \<longleftrightarrow> result = Some value"
  by (cases result) simp_all

lemma result_of_option_failure_iff [simp]:
  "result_of_option failure result = CodeFailure failure \<longleftrightarrow> result = None"
  by (cases result) simp_all

lemma erase_code_result_option_case [simp]:
  "erase_code_result
      (case result of Some value \<Rightarrow> CodeSuccess value | None \<Rightarrow> CodeFailure failure) =
    result"
  by (cases result) simp_all

fun diagnose_type_failure :: "htheory \<Rightarrow> htype \<Rightarrow> code_failure option" where
  "diagnose_type_failure thy (TyVar _) = None"
| "diagnose_type_failure thy (TyApp n args) =
    (case tyops thy n of
       None \<Rightarrow> Some (CodeUndeclaredType n)
     | Some arity \<Rightarrow>
         if arity \<noteq> length args then Some (CodeTypeArity n arity (length args))
         else if list_all (check_type thy) args then None
         else Some (CodeInvalidType (TyApp n args)))"

fun diagnose_open_term_failure ::
  "htheory \<Rightarrow> htype list \<Rightarrow> hterm \<Rightarrow> code_failure option" where
  "diagnose_open_term_failure thy env (FVar _ ty) = diagnose_type_failure thy ty"
| "diagnose_open_term_failure thy env (BVar i ty) =
    (if i \<ge> length env then Some (CodeUnboundIndex i (length env))
     else if env ! i \<noteq> ty then Some (CodeBinderTypeMismatch i (env ! i) ty)
     else diagnose_type_failure thy ty)"
| "diagnose_open_term_failure thy env (Const n ty) =
    (case diagnose_type_failure thy ty of
       Some failure \<Rightarrow> Some failure
     | None \<Rightarrow> (case const_tab thy n of
         None \<Rightarrow> Some (CodeUndeclaredConstant n)
       | Some generic \<Rightarrow> if type_match generic ty (\<lambda>_. None) = None
           then Some (CodeConstantTypeMismatch n generic ty) else None))"
| "diagnose_open_term_failure thy env (Comb f x) =
    (case diagnose_open_term_failure thy env f of
       Some failure \<Rightarrow> Some failure
     | None \<Rightarrow> (case diagnose_open_term_failure thy env x of
         Some failure \<Rightarrow> Some failure
       | None \<Rightarrow> (case type_of f of
           Some (TyApp NFun [arg_ty, result_ty]) \<Rightarrow>
             if type_of x = Some arg_ty then None
             else Some (CodeIllTypedApplication (Comb f x))
         | _ \<Rightarrow> Some (CodeOperatorNotFunction (Comb f x)))))"
| "diagnose_open_term_failure thy env (Abs aty body) =
    (case diagnose_type_failure thy aty of
       Some failure \<Rightarrow> Some failure
     | None \<Rightarrow> diagnose_open_term_failure thy (aty # env) body)"

definition diagnose_term_failure :: "htheory \<Rightarrow> hterm \<Rightarrow> code_failure" where
  "diagnose_term_failure thy t =
    (case diagnose_open_term_failure thy [] t of
       Some failure \<Rightarrow> failure
     | None \<Rightarrow> CodeRuleRejected)"

definition diagnose_prop_failure :: "htheory \<Rightarrow> hterm \<Rightarrow> code_failure" where
  "diagnose_prop_failure thy p =
    (case diagnose_open_term_failure thy [] p of
       Some failure \<Rightarrow> failure
     | None \<Rightarrow> CodeNotProposition p)"

definition diagnose_trans_failure :: "hthm \<Rightarrow> hthm \<Rightarrow> code_failure" where
  "diagnose_trans_failure a b =
    (case dest_eq (concl a) of
       None \<Rightarrow> CodeNotEquation (concl a)
     | Some (_, middle) \<Rightarrow> (case dest_eq (concl b) of
         None \<Rightarrow> CodeNotEquation (concl b)
       | Some (middle', _) \<Rightarrow> if middle = middle' then CodeRuleRejected
           else CodeMiddleTermsDiffer middle middle'))"

definition diagnose_mk_comb_failure :: "hthm \<Rightarrow> hthm \<Rightarrow> code_failure" where
  "diagnose_mk_comb_failure fth xth =
    (case dest_eq (concl fth) of
       None \<Rightarrow> CodeNotEquation (concl fth)
     | Some (f, _) \<Rightarrow> (case dest_eq (concl xth) of
         None \<Rightarrow> CodeNotEquation (concl xth)
       | Some (x, _) \<Rightarrow> (case type_of f of
           Some (TyApp NFun [arg_ty, result_ty]) \<Rightarrow>
             if type_of x = Some arg_ty then CodeRuleRejected
             else CodeCombinationTypeMismatch
         | _ \<Rightarrow> CodeOperatorNotFunction f)))"

definition diagnose_abs_failure ::
  "htheory \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> hthm \<Rightarrow> code_failure" where
  "diagnose_abs_failure thy n ty th =
    (case diagnose_open_term_failure thy [] (FVar n ty) of
       Some failure \<Rightarrow> failure
     | None \<Rightarrow> if list_ex (vfree_in n ty) (hyps th)
         then CodeVariableFreeInHypotheses n
         else if dest_eq (concl th) = None then CodeNotEquation (concl th)
         else CodeRuleRejected)"

definition diagnose_beta_failure :: "htheory \<Rightarrow> hterm \<Rightarrow> code_failure" where
  "diagnose_beta_failure thy t =
    (case diagnose_open_term_failure thy [] t of
       Some failure \<Rightarrow> failure
     | None \<Rightarrow> CodeNotBetaRedex t)"

definition diagnose_eq_mp_failure :: "hthm \<Rightarrow> hthm \<Rightarrow> code_failure" where
  "diagnose_eq_mp_failure eqth th =
    (case dest_eq (concl eqth) of
       None \<Rightarrow> CodeNotEquation (concl eqth)
     | Some (expected, _) \<Rightarrow> if expected = concl th then CodeRuleRejected
         else CodeAntecedentMismatch expected (concl th))"

fun diagnose_inst_entries ::
  "htheory \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> code_failure option" where
  "diagnose_inst_entries thy [] = None"
| "diagnose_inst_entries thy ((replacement, target) # rest) =
    (case target of
       FVar _ ty \<Rightarrow> (case diagnose_open_term_failure thy [] replacement of
         Some failure \<Rightarrow> Some failure
       | None \<Rightarrow> if type_of replacement \<noteq> Some ty
           then Some (CodeInstantiationTypeMismatch target replacement)
           else diagnose_inst_entries thy rest)
     | _ \<Rightarrow> Some (CodeInvalidInstantiationTarget target))"

definition diagnose_inst_failure ::
  "htheory \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> code_failure" where
  "diagnose_inst_failure thy entries =
    (case diagnose_inst_entries thy entries of
       Some failure \<Rightarrow> failure
     | None \<Rightarrow> CodeRuleRejected)"

fun diagnose_type_entries ::
  "htheory \<Rightarrow> type_subst_entries \<Rightarrow> code_failure option" where
  "diagnose_type_entries thy [] = None"
| "diagnose_type_entries thy ((_, ty) # rest) =
    (case diagnose_type_failure thy ty of
       Some failure \<Rightarrow> Some failure
     | None \<Rightarrow> diagnose_type_entries thy rest)"

definition code_check_type :: "htheory \<Rightarrow> htype \<Rightarrow> unit code_result" where
  "code_check_type thy ty =
    (if check_type thy ty then CodeSuccess ()
     else case diagnose_type_failure thy ty of
       Some failure \<Rightarrow> CodeFailure failure
     | None \<Rightarrow> CodeFailure CodeRuleRejected)"

definition code_check_term :: "htheory \<Rightarrow> hterm \<Rightarrow> unit code_result" where
  "code_check_term thy t =
    (if check_term thy t then CodeSuccess ()
     else case diagnose_open_term_failure thy [] t of
       Some failure \<Rightarrow> CodeFailure failure
     | None \<Rightarrow> CodeFailure CodeRuleRejected)"
definition code_refl :: "htheory \<Rightarrow> hterm \<Rightarrow> hthm code_result" where
  "code_refl thy t =
    (case refl thy t of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_term_failure thy t))"

definition code_trans :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_trans thy a b =
    (case trans thy a b of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_trans_failure a b))"

definition code_mk_comb :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_mk_comb thy fth xth =
    (case mk_comb_rule thy fth xth of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_mk_comb_failure fth xth))"

definition code_abs ::
  "htheory \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_abs thy n ty th =
    (case abs_rule thy n ty th of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_abs_failure thy n ty th))"

definition code_beta :: "htheory \<Rightarrow> hterm \<Rightarrow> hthm code_result" where
  "code_beta thy t =
    (case beta thy t of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_beta_failure thy t))"

definition code_assume :: "htheory \<Rightarrow> hterm \<Rightarrow> hthm code_result" where
  "code_assume thy p =
    (case assume_rule thy p of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_prop_failure thy p))"

definition code_eq_mp :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_eq_mp thy eqth th =
    (case eq_mp thy eqth th of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_eq_mp_failure eqth th))"

definition code_deduct_antisym ::
  "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_deduct_antisym thy a b =
    result_of_option CodeRuleRejected (deduct_antisym_rule thy a b)"

definition code_inst ::
  "htheory \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_inst thy entries th =
    (case inst thy entries th of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_inst_failure thy entries))"

definition code_inst_type ::
  "htheory \<Rightarrow> type_subst_entries \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_inst_type thy entries th =
    (if valid_type_subst_entries thy entries then
       result_of_option CodeRuleRejected (inst_type_entries thy entries th)
     else (case diagnose_type_entries thy entries of
       Some failure \<Rightarrow> CodeFailure failure
     | None \<Rightarrow> CodeFailure CodeInvalidTypeSubstitution))"
lemma code_refl_erasure [simp]:
  "erase_code_result (code_refl thy t) = refl thy t"
  by (simp add: code_refl_def)

lemma code_trans_erasure [simp]:
  "erase_code_result (code_trans thy a b) = trans thy a b"
  by (simp add: code_trans_def)

lemma code_mk_comb_erasure [simp]:
  "erase_code_result (code_mk_comb thy fth xth) = mk_comb_rule thy fth xth"
  by (simp add: code_mk_comb_def)

lemma code_abs_erasure [simp]:
  "erase_code_result (code_abs thy n ty th) = abs_rule thy n ty th"
  by (simp add: code_abs_def)

lemma code_beta_erasure [simp]:
  "erase_code_result (code_beta thy t) = beta thy t"
  by (simp add: code_beta_def)

lemma code_assume_erasure [simp]:
  "erase_code_result (code_assume thy p) = assume_rule thy p"
  by (simp add: code_assume_def)

lemma code_eq_mp_erasure [simp]:
  "erase_code_result (code_eq_mp thy eqth th) = eq_mp thy eqth th"
  by (simp add: code_eq_mp_def)

lemma code_deduct_antisym_erasure [simp]:
  "erase_code_result (code_deduct_antisym thy a b) = deduct_antisym_rule thy a b"
  by (simp add: code_deduct_antisym_def)

lemma code_inst_erasure [simp]:
  "erase_code_result (code_inst thy entries th) = inst thy entries th"
  by (simp add: code_inst_def)

lemma code_inst_type_erasure [simp]:
  "erase_code_result (code_inst_type thy entries th) = inst_type_entries thy entries th"
  by (cases "valid_type_subst_entries thy entries";
      cases "diagnose_type_entries thy entries")
     (simp_all add: code_inst_type_def inst_type_entries_def)

lemma code_result_success_iff [simp]:
  "result = CodeSuccess value \<longleftrightarrow> erase_code_result result = Some value"
  by (cases result) simp_all

lemma code_result_failure_iff [simp]:
  "(\<exists>failure. result = CodeFailure failure) \<longleftrightarrow> erase_code_result result = None"
  by (cases result) auto

lemma code_refl_success_iff:
  "code_refl thy t = CodeSuccess result \<longleftrightarrow> refl thy t = Some result"
  by simp

lemma code_refl_failure_iff:
  "(\<exists>failure. code_refl thy t = CodeFailure failure) \<longleftrightarrow> refl thy t = None"
  by simp

lemma code_refl_sound:
  assumes "code_refl thy t = CodeSuccess result"
  shows "rule_spec (IRefl thy t) result"
  using run_rule_sound[of "IRefl thy t" result] assms by simp

lemma code_refl_preserves_wf:
  assumes "code_refl thy t = CodeSuccess result"
    and "wf_inputs (IRefl thy t)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IRefl thy t" result] assms by simp

lemma code_trans_success_iff:
  "code_trans thy a b = CodeSuccess result \<longleftrightarrow> trans thy a b = Some result"
  by simp

lemma code_trans_failure_iff:
  "(\<exists>failure. code_trans thy a b = CodeFailure failure) \<longleftrightarrow> trans thy a b = None"
  by simp

lemma code_trans_sound:
  assumes "code_trans thy a b = CodeSuccess result"
  shows "rule_spec (ITrans thy a b) result"
  using run_rule_sound[of "ITrans thy a b" result] assms by simp

lemma code_trans_preserves_wf:
  assumes "code_trans thy a b = CodeSuccess result"
    and "wf_inputs (ITrans thy a b)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "ITrans thy a b" result] assms by simp

lemma code_mk_comb_success_iff:
  "code_mk_comb thy fth xth = CodeSuccess result \<longleftrightarrow> mk_comb_rule thy fth xth = Some result"
  by simp

lemma code_mk_comb_failure_iff:
  "(\<exists>failure. code_mk_comb thy fth xth = CodeFailure failure) \<longleftrightarrow> mk_comb_rule thy fth xth = None"
  by simp

lemma code_mk_comb_sound:
  assumes "code_mk_comb thy fth xth = CodeSuccess result"
  shows "rule_spec (IMkComb thy fth xth) result"
  using run_rule_sound[of "IMkComb thy fth xth" result] assms by simp

lemma code_mk_comb_preserves_wf:
  assumes "code_mk_comb thy fth xth = CodeSuccess result"
    and "wf_inputs (IMkComb thy fth xth)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IMkComb thy fth xth" result] assms by simp

lemma code_abs_success_iff:
  "code_abs thy n ty input = CodeSuccess result \<longleftrightarrow> abs_rule thy n ty input = Some result"
  by simp

lemma code_abs_failure_iff:
  "(\<exists>failure. code_abs thy n ty input = CodeFailure failure) \<longleftrightarrow> abs_rule thy n ty input = None"
  by simp

lemma code_abs_sound:
  assumes "code_abs thy n ty input = CodeSuccess result"
  shows "rule_spec (IAbs thy n ty input) result"
  using run_rule_sound[of "IAbs thy n ty input" result] assms by simp

lemma code_abs_preserves_wf:
  assumes "code_abs thy n ty input = CodeSuccess result"
    and "wf_inputs (IAbs thy n ty input)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IAbs thy n ty input" result] assms by simp

lemma code_beta_success_iff:
  "code_beta thy t = CodeSuccess result \<longleftrightarrow> beta thy t = Some result"
  by simp

lemma code_beta_failure_iff:
  "(\<exists>failure. code_beta thy t = CodeFailure failure) \<longleftrightarrow> beta thy t = None"
  by simp

lemma code_beta_sound:
  assumes "code_beta thy t = CodeSuccess result"
  shows "rule_spec (IBeta thy t) result"
  using run_rule_sound[of "IBeta thy t" result] assms by simp

lemma code_beta_preserves_wf:
  assumes "code_beta thy t = CodeSuccess result"
    and "wf_inputs (IBeta thy t)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IBeta thy t" result] assms by simp

lemma code_assume_success_iff:
  "code_assume thy p = CodeSuccess result \<longleftrightarrow> assume_rule thy p = Some result"
  by simp

lemma code_assume_failure_iff:
  "(\<exists>failure. code_assume thy p = CodeFailure failure) \<longleftrightarrow> assume_rule thy p = None"
  by simp

lemma code_assume_sound:
  assumes "code_assume thy p = CodeSuccess result"
  shows "rule_spec (IAssume thy p) result"
  using run_rule_sound[of "IAssume thy p" result] assms by simp

lemma code_assume_preserves_wf:
  assumes "code_assume thy p = CodeSuccess result"
    and "wf_inputs (IAssume thy p)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IAssume thy p" result] assms by simp

lemma code_eq_mp_success_iff:
  "code_eq_mp thy eqth input = CodeSuccess result \<longleftrightarrow> eq_mp thy eqth input = Some result"
  by simp

lemma code_eq_mp_failure_iff:
  "(\<exists>failure. code_eq_mp thy eqth input = CodeFailure failure) \<longleftrightarrow> eq_mp thy eqth input = None"
  by simp

lemma code_eq_mp_sound:
  assumes "code_eq_mp thy eqth input = CodeSuccess result"
  shows "rule_spec (IEqMp thy eqth input) result"
  using run_rule_sound[of "IEqMp thy eqth input" result] assms by simp

lemma code_eq_mp_preserves_wf:
  assumes "code_eq_mp thy eqth input = CodeSuccess result"
    and "wf_inputs (IEqMp thy eqth input)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IEqMp thy eqth input" result] assms by simp

lemma code_deduct_antisym_success_iff:
  "code_deduct_antisym thy a b = CodeSuccess result \<longleftrightarrow> deduct_antisym_rule thy a b = Some result"
  by simp

lemma code_deduct_antisym_failure_iff:
  "(\<exists>failure. code_deduct_antisym thy a b = CodeFailure failure) \<longleftrightarrow> deduct_antisym_rule thy a b = None"
  by simp

lemma code_deduct_antisym_sound:
  assumes "code_deduct_antisym thy a b = CodeSuccess result"
  shows "rule_spec (IDeductAntisym thy a b) result"
  using run_rule_sound[of "IDeductAntisym thy a b" result] assms by simp

lemma code_deduct_antisym_preserves_wf:
  assumes "code_deduct_antisym thy a b = CodeSuccess result"
    and "wf_inputs (IDeductAntisym thy a b)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IDeductAntisym thy a b" result] assms by simp

lemma code_inst_success_iff:
  "code_inst thy entries input = CodeSuccess result \<longleftrightarrow> inst thy entries input = Some result"
  by simp

lemma code_inst_failure_iff:
  "(\<exists>failure. code_inst thy entries input = CodeFailure failure) \<longleftrightarrow> inst thy entries input = None"
  by simp

lemma code_inst_sound:
  assumes "code_inst thy entries input = CodeSuccess result"
  shows "rule_spec (IInst thy entries input) result"
  using run_rule_sound[of "IInst thy entries input" result] assms by simp

lemma code_inst_preserves_wf:
  assumes "code_inst thy entries input = CodeSuccess result"
    and "wf_inputs (IInst thy entries input)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IInst thy entries input" result] assms by simp

lemma code_inst_type_success_iff:
  "code_inst_type thy entries input = CodeSuccess result \<longleftrightarrow>
    inst_type_entries thy entries input = Some result"
  using code_result_success_iff[of "code_inst_type thy entries input" result]
  by simp

lemma code_inst_type_failure_iff:
  "(\<exists>failure. code_inst_type thy entries input = CodeFailure failure) \<longleftrightarrow>
    inst_type_entries thy entries input = None"
  using code_result_failure_iff[of "code_inst_type thy entries input"]
  by simp

lemma code_inst_type_sound:
  assumes "code_inst_type thy entries input = CodeSuccess result"
  shows "rule_spec (IInstType thy (entries_subst entries) input) result"
  using run_rule_sound[of "IInstType thy (entries_subst entries) input" result]
    assms valid_type_subst_entries_type_subst_ok
  by (auto simp: code_inst_type_def inst_type_entries_agrees split: if_splits option.splits)

lemma code_inst_type_preserves_wf:
  assumes "code_inst_type thy entries input = CodeSuccess result"
    and "wf_inputs (IInstType thy (entries_subst entries) input)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IInstType thy (entries_subst entries) input" result]
    assms valid_type_subst_entries_type_subst_ok
  by (auto simp: code_inst_type_def inst_type_entries_agrees split: if_splits option.splits)

section \<open>Direct code-generation extension façade\<close>

datatype extension_delta =
    DeltaType hname nat
  | DeltaConstant hname htype
  | DeltaAxiom hthm
  | DeltaDefinition hname htype hthm
  | DeltaTypeDefinition hname nat hname htype hname htype hthm hthm

definition diagnose_new_type_failure :: "htheory \<Rightarrow> hname \<Rightarrow> code_failure" where
  "diagnose_new_type_failure thy n =
    (if tyops thy n = None then CodeExtensionRejected else CodeDuplicateType n)"

definition diagnose_new_constant_failure ::
  "htheory \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> code_failure" where
  "diagnose_new_constant_failure thy n ty =
    (if const_tab thy n \<noteq> None then CodeDuplicateConstant n
     else case diagnose_type_failure thy ty of
       Some failure \<Rightarrow> failure
     | None \<Rightarrow> CodeExtensionRejected)"

definition diagnose_definition_failure ::
  "htheory \<Rightarrow> hterm \<Rightarrow> code_failure" where
  "diagnose_definition_failure thy tm =
    (case dest_eq tm of
       None \<Rightarrow> CodeDefinitionNotEquation
     | Some (lhs, rhs) \<Rightarrow> (case lhs of
         FVar n ty \<Rightarrow>
           if const_tab thy n \<noteq> None then CodeDuplicateConstant n
           else (case diagnose_open_term_failure thy [] rhs of
             Some failure \<Rightarrow> failure
           | None \<Rightarrow> (case free_vars rhs of
               free # _ \<Rightarrow> CodeDefinitionOpen (case free of (v, vty) \<Rightarrow> FVar v vty)
             | [] \<Rightarrow> if type_of rhs \<noteq> Some ty then CodeDefinitionTypeMismatch
                 else if \<not> set (term_type_vars rhs) \<subseteq> set (type_vars ty)
                   then CodeDefinitionExtraTypeVariables
                 else CodeExtensionRejected))
       | _ \<Rightarrow> CodeDefinitionLeftNotVariable))"

definition diagnose_type_definition_failure ::
  "htheory \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hthm \<Rightarrow> code_failure" where
  "diagnose_type_definition_failure thy tyname absname repname wit =
    (if \<not> wf_thm thy wit then CodeTypeDefinitionBadWitness
     else if hyps wit \<noteq> [] then CodeTypeDefinitionHasHypotheses
     else if tyops thy tyname \<noteq> None then CodeDuplicateType tyname
     else if const_tab thy absname \<noteq> None then CodeDuplicateConstant absname
     else if const_tab thy repname \<noteq> None then CodeDuplicateConstant repname
     else if absname = repname then CodeTypeDefinitionSameConstants
     else case concl wit of
       Comb pred witness \<Rightarrow> (case type_of witness of
         None \<Rightarrow> CodeTypeDefinitionBadWitness
       | Some rty \<Rightarrow> if free_vars pred \<noteq> [] then CodeTypeDefinitionOpenPredicate
           else if \<not> set (type_vars rty) \<subseteq> set (term_type_vars pred)
             then CodeTypeDefinitionExtraTypeVariables rty
           else CodeExtensionRejected)
     | _ \<Rightarrow> CodeTypeDefinitionBadWitness)"

fun definition_delta_of :: "hterm \<Rightarrow> hthm \<Rightarrow> extension_delta" where
  "definition_delta_of (Comb (Comb (Const _ _) (FVar n ty)) rhs) th =
    DeltaDefinition n ty th"
| "definition_delta_of _ th = DeltaAxiom th"

definition type_definition_delta_of ::
  "hname \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> extension_delta" where
  "type_definition_delta_of tyname absname repname wit th1 th2 =
    (case concl wit of
       Comb pred witness \<Rightarrow> (case type_of witness of
         Some rty \<Rightarrow> let tvs = term_type_vars pred;
             aty = TyApp tyname (map TyVar tvs)
           in DeltaTypeDefinition tyname (length tvs)
             absname (mk_fun rty aty) repname (mk_fun aty rty) th1 th2
       | None \<Rightarrow> DeltaAxiom th1)
     | _ \<Rightarrow> DeltaAxiom th1)"
definition code_new_type ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> nat \<Rightarrow> htheory code_result" where
  "code_new_type fresh thy n arity =
    (case new_type fresh thy n arity of
       Some thy' \<Rightarrow> CodeSuccess thy'
     | None \<Rightarrow> CodeFailure (diagnose_new_type_failure thy n))"

definition code_new_constant ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> htheory code_result" where
  "code_new_constant fresh thy n ty =
    (case new_constant fresh thy n ty of
       Some thy' \<Rightarrow> CodeSuccess thy'
     | None \<Rightarrow> CodeFailure (diagnose_new_constant_failure thy n ty))"

definition code_new_axiom ::
  "nat \<Rightarrow> htheory \<Rightarrow> hterm \<Rightarrow> (htheory \<times> hthm) code_result" where
  "code_new_axiom fresh thy p =
    (case new_axiom fresh thy p of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_prop_failure thy p))"

definition code_new_basic_definition ::
  "nat \<Rightarrow> htheory \<Rightarrow> hterm \<Rightarrow> (htheory \<times> hthm) code_result" where
  "code_new_basic_definition fresh thy tm =
    (case new_basic_definition fresh thy tm of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure (diagnose_definition_failure thy tm))"

definition code_new_basic_type_definition ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hthm \<Rightarrow>
    (htheory \<times> hthm \<times> hthm) code_result" where
  "code_new_basic_type_definition fresh thy tyname absname repname witness =
    (case new_basic_type_definition fresh thy tyname absname repname witness of
       Some result \<Rightarrow> CodeSuccess result
     | None \<Rightarrow> CodeFailure
         (diagnose_type_definition_failure thy tyname absname repname witness))"

definition code_new_type_with_delta ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> nat \<Rightarrow> (htheory \<times> extension_delta) code_result" where
  "code_new_type_with_delta fresh thy n arity =
    (case code_new_type fresh thy n arity of
       CodeFailure failure \<Rightarrow> CodeFailure failure
     | CodeSuccess thy' \<Rightarrow> CodeSuccess (thy', DeltaType n arity))"

definition code_new_constant_with_delta ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> (htheory \<times> extension_delta) code_result" where
  "code_new_constant_with_delta fresh thy n ty =
    (case code_new_constant fresh thy n ty of
       CodeFailure failure \<Rightarrow> CodeFailure failure
     | CodeSuccess thy' \<Rightarrow> CodeSuccess (thy', DeltaConstant n ty))"

definition code_new_axiom_with_delta ::
  "nat \<Rightarrow> htheory \<Rightarrow> hterm \<Rightarrow> (htheory \<times> extension_delta) code_result" where
  "code_new_axiom_with_delta fresh thy p =
    (case code_new_axiom fresh thy p of
       CodeFailure failure \<Rightarrow> CodeFailure failure
     | CodeSuccess (thy', th) \<Rightarrow> CodeSuccess (thy', DeltaAxiom th))"

definition code_new_basic_definition_with_delta ::
  "nat \<Rightarrow> htheory \<Rightarrow> hterm \<Rightarrow> (htheory \<times> extension_delta) code_result" where
  "code_new_basic_definition_with_delta fresh thy tm =
    (case code_new_basic_definition fresh thy tm of
       CodeFailure failure \<Rightarrow> CodeFailure failure
     | CodeSuccess (thy', th) \<Rightarrow>
         CodeSuccess (thy', definition_delta_of tm th))"

definition code_new_basic_type_definition_with_delta ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hthm \<Rightarrow>
    (htheory \<times> extension_delta) code_result" where
  "code_new_basic_type_definition_with_delta fresh thy tn an rn witness =
    (case code_new_basic_type_definition fresh thy tn an rn witness of
       CodeFailure failure \<Rightarrow> CodeFailure failure
     | CodeSuccess (thy', th1, th2) \<Rightarrow>
         CodeSuccess (thy', type_definition_delta_of tn an rn witness th1 th2))"
lemma code_new_type_erasure [simp]:
  "erase_code_result (code_new_type fresh thy n arity) =
    new_type fresh thy n arity"
  by (simp add: code_new_type_def)

lemma code_new_constant_erasure [simp]:
  "erase_code_result (code_new_constant fresh thy n ty) =
    new_constant fresh thy n ty"
  by (simp add: code_new_constant_def)

lemma code_new_axiom_erasure [simp]:
  "erase_code_result (code_new_axiom fresh thy p) = new_axiom fresh thy p"
  by (simp add: code_new_axiom_def)

lemma code_new_basic_definition_erasure [simp]:
  "erase_code_result (code_new_basic_definition fresh thy tm) =
    new_basic_definition fresh thy tm"
  by (simp add: code_new_basic_definition_def)

lemma code_new_basic_type_definition_erasure [simp]:
  "erase_code_result
      (code_new_basic_type_definition fresh thy tn an rn witness) =
    new_basic_type_definition fresh thy tn an rn witness"
  by (simp add: code_new_basic_type_definition_def)

lemma code_new_type_one_generation:
  "code_new_type fresh thy n arity = CodeSuccess thy' \<Longrightarrow>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
  using new_type_one_generation by simp

lemma code_new_constant_one_generation:
  "code_new_constant fresh thy n ty = CodeSuccess thy' \<Longrightarrow>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
  using new_constant_one_generation by simp

lemma code_new_axiom_result:
  assumes "code_new_axiom fresh thy p = CodeSuccess (thy', th)"
  shows "hyps th = [] \<and> concl th = p \<and> thm_stamp th = thy_stamp thy' \<and>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
  using new_axiom_extract[of fresh thy p thy' th]
    new_axiom_one_generation[of fresh thy p thy' th] assms
  by simp

lemma code_new_basic_definition_result:
  assumes "code_new_basic_definition fresh thy tm = CodeSuccess (thy', th)"
  shows "wf_thm thy' th \<and> thm_stamp th = thy_stamp thy' \<and>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
proof -
  have run: "new_basic_definition fresh thy tm = Some (thy', th)"
    using assms by simp
  have result: "wf_thm thy' th \<and> thm_stamp th = thy_stamp thy'"
    using run by (elim new_basic_definition_extract) simp
  show ?thesis
    using result new_basic_definition_one_generation[OF run] by blast
qed

lemma code_new_basic_type_definition_result:
  assumes "code_new_basic_type_definition fresh thy tn an rn witness =
    CodeSuccess (thy', th1, th2)"
  shows "wf_thm thy' th1 \<and> wf_thm thy' th2 \<and>
    thm_stamp th1 = thy_stamp thy' \<and> thm_stamp th2 = thy_stamp thy' \<and>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
proof -
  have run: "new_basic_type_definition fresh thy tn an rn witness =
      Some (thy', th1, th2)"
    using assms by simp
  have stamps: "thm_stamp th1 = thy_stamp thy' \<and>
      thm_stamp th2 = thy_stamp thy'"
    using run by (elim new_basic_type_definition_obtain) simp
  show ?thesis
    using stamps new_basic_type_definition_extract[OF run] by blast
qed

end
