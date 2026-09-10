(* SPDX-License-Identifier: 0BSD AND BSD-2-Clause AND BSD-3-Clause *)
(* Conservatively covered by HOL Light and HOL4 notices; see THIRD_PARTY_NOTICES. *)

theory Rhombus_HOL_Code
  imports Rhombus_HOL_Audit "HOL-Library.Code_Target_Numeral"
begin

ML_file "Rhombus_Code_Target.ML"

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
    CodeRuleRejected
  | CodeInvalidTypeSubstitution
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

definition code_refl :: "htheory \<Rightarrow> hterm \<Rightarrow> hthm code_result" where
  "code_refl thy t = result_of_option CodeRuleRejected (refl thy t)"

definition code_trans :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_trans thy a b = result_of_option CodeRuleRejected (trans thy a b)"

definition code_mk_comb :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_mk_comb thy fth xth =
    result_of_option CodeRuleRejected (mk_comb_rule thy fth xth)"

definition code_abs ::
  "htheory \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_abs thy n ty th = result_of_option CodeRuleRejected (abs_rule thy n ty th)"

definition code_beta :: "htheory \<Rightarrow> hterm \<Rightarrow> hthm code_result" where
  "code_beta thy t = result_of_option CodeRuleRejected (beta thy t)"

definition code_assume :: "htheory \<Rightarrow> hterm \<Rightarrow> hthm code_result" where
  "code_assume thy p = result_of_option CodeRuleRejected (assume_rule thy p)"

definition code_eq_mp :: "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_eq_mp thy eqth th = result_of_option CodeRuleRejected (eq_mp thy eqth th)"

definition code_deduct_antisym ::
  "htheory \<Rightarrow> hthm \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_deduct_antisym thy a b =
    result_of_option CodeRuleRejected (deduct_antisym_rule thy a b)"

definition code_inst ::
  "htheory \<Rightarrow> (hterm \<times> hterm) list \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_inst thy entries th = result_of_option CodeRuleRejected (inst thy entries th)"

definition code_inst_type ::
  "htheory \<Rightarrow> type_subst_entries \<Rightarrow> hthm \<Rightarrow> hthm code_result" where
  "code_inst_type thy entries th =
    (if valid_type_subst_entries thy entries then
       result_of_option CodeRuleRejected (inst_type_entries thy entries th)
     else CodeFailure CodeInvalidTypeSubstitution)"

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
  by (cases "valid_type_subst_entries thy entries")
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
  by (auto simp: code_inst_type_def inst_type_entries_agrees split: if_splits)

lemma code_inst_type_preserves_wf:
  assumes "code_inst_type thy entries input = CodeSuccess result"
    and "wf_inputs (IInstType thy (entries_subst entries) input)"
  shows "wf_thm thy result"
  using run_rule_preserves_wf[of "IInstType thy (entries_subst entries) input" result]
    assms valid_type_subst_entries_type_subst_ok
  by (auto simp: code_inst_type_def inst_type_entries_agrees split: if_splits)

section \<open>Direct code-generation extension façade\<close>

definition code_new_type ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> nat \<Rightarrow> htheory code_result" where
  "code_new_type fresh thy n arity =
    result_of_option CodeExtensionRejected (new_type fresh thy n arity)"

definition code_new_constant ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> htheory code_result" where
  "code_new_constant fresh thy n ty =
    result_of_option CodeExtensionRejected (new_constant fresh thy n ty)"

definition code_new_axiom ::
  "nat \<Rightarrow> htheory \<Rightarrow> hterm \<Rightarrow> (htheory \<times> hthm) code_result" where
  "code_new_axiom fresh thy p =
    result_of_option CodeExtensionRejected (new_axiom fresh thy p)"

definition code_new_basic_definition ::
  "nat \<Rightarrow> htheory \<Rightarrow> hterm \<Rightarrow> (htheory \<times> hthm) code_result" where
  "code_new_basic_definition fresh thy tm =
    result_of_option CodeExtensionRejected (new_basic_definition fresh thy tm)"

definition code_new_basic_type_definition ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hthm \<Rightarrow>
    (htheory \<times> hthm \<times> hthm) code_result" where
  "code_new_basic_type_definition fresh thy tyname absname repname witness =
    result_of_option CodeExtensionRejected
      (new_basic_type_definition fresh thy tyname absname repname witness)"

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
section \<open>Executable natural-fuel matcher\<close>

definition empty_type_subst :: "hname \<Rightarrow> htype option" where
  "empty_type_subst _ = None"

lemma empty_type_subst_eq [simp]: "empty_type_subst = (\<lambda>_. None)"
  by (rule ext) (simp add: empty_type_subst_def)

definition check_open_term_uncached :: "htheory \<Rightarrow> hterm \<Rightarrow> htype list \<Rightarrow> bool" where
  "check_open_term_uncached thy t env \<longleftrightarrow>
    (case t of
       FVar _ ty \<Rightarrow> check_type thy ty
     | BVar i ty \<Rightarrow> i < length env \<and> env ! i = ty \<and> check_type thy ty
     | Const n ty \<Rightarrow> check_type thy ty \<and>
         (case const_tab thy n of None \<Rightarrow> False
          | Some generic \<Rightarrow> type_match generic ty empty_type_subst \<noteq> None)
     | Comb f x \<Rightarrow> check_open_term thy env f \<and> check_open_term thy env x \<and>
         type_of (Comb f x) \<noteq> None
     | Abs aty body \<Rightarrow> check_type thy aty \<and> check_open_term thy (aty # env) body)"

lemma check_open_term_uncached_eq:
  "check_open_term_uncached thy t env \<longleftrightarrow> check_open_term thy env t"
  unfolding check_open_term_uncached_def empty_type_subst_eq
  by (cases t) simp_all

definition type_match_uncached ::
  "htype \<Rightarrow> htype \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow> (hname \<Rightarrow> htype option) option" where
  "type_match_uncached pat ty acc =
    (case type_match_fuel (size pat + 1) pat ty acc of
       None \<Rightarrow> None
     | Some \<theta> \<Rightarrow> if type_subst \<theta> pat = ty then Some \<theta> else None)"

lemma type_match_uncached_eq: "type_match_uncached = type_match"
  by (simp add: fun_eq_iff type_match_uncached_def type_match_def)

definition check_term_uncached :: "htheory \<Rightarrow> hterm \<Rightarrow> bool" where
  "check_term_uncached thy t \<longleftrightarrow> check_open_term thy [] t"

lemma check_term_uncached_eq: "check_term_uncached = check_term"
  by (simp add: fun_eq_iff check_term_uncached_def check_term_def)

definition memoize_binary :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" where
  "memoize_binary f a b = f a b"

definition memoize_ternary ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" where
  "memoize_ternary f a b c = f a b c"

declare [[code drop: check_open_term]]
declare [[code drop: type_match]]
declare [[code drop: check_term]]

lemma check_open_term_memo_code [code]:
  "check_open_term thy env t =
    memoize_ternary check_open_term_uncached thy t env"
  by (simp add: memoize_ternary_def check_open_term_uncached_eq)

lemma type_match_memo_code [code]:
  "type_match pat ty acc =
    memoize_ternary type_match_uncached pat ty acc"
  by (simp add: memoize_ternary_def type_match_uncached_def type_match_def)

lemma check_term_memo_code [code]:
  "check_term thy t = memoize_binary check_term_uncached thy t"
  by (simp add: memoize_binary_def check_term_uncached_def check_term_def)

declare [[code drop: type_match_fuel]]

lemma type_match_fuel_code [code]:
  "type_match_fuel fuel pat ty acc =
    (if fuel = 0 then None
     else case pat of
       TyVar n \<Rightarrow>
         (case acc n of None \<Rightarrow> Some (acc(n := Some ty))
          | Some old \<Rightarrow> if old = ty then Some acc else None)
     | TyApp n ps \<Rightarrow>
         (case ty of TyVar _ \<Rightarrow> None
          | TyApp m ts \<Rightarrow>
              if n = m \<and> length ps = length ts then
                fold (\<lambda>(p, t) result.
                  case result of None \<Rightarrow> None
                  | Some current \<Rightarrow> type_match_fuel (fuel - 1) p t current)
                  (zip ps ts) (Some acc)
              else None))"
  by (cases fuel; cases pat; cases ty) auto

definition nat_value :: "integer \<Rightarrow> nat" where
  "nat_value k = nat_of_integer k"

definition integer_value :: "nat \<Rightarrow> integer" where
  "integer_value n = integer_of_nat n"
section \<open>Rhombus integer primitives\<close>

code_printing
  type_constructor integer \<rightharpoonup> (Rhombus) "Int"
| constant "0 :: integer" \<rightharpoonup> (Rhombus) "0"
| constant "plus :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup> (Rhombus) infixl 6 "+"
| constant "uminus :: integer \<Rightarrow> integer" \<rightharpoonup> (Rhombus) "(- _)"
| constant "minus :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup> (Rhombus) infixl 6 "-"
| constant "times :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup> (Rhombus) infixl 7 "*"
| constant "HOL.equal :: integer \<Rightarrow> integer \<Rightarrow> bool" \<rightharpoonup> (Rhombus) infix 4 "=="
| constant "less_eq :: integer \<Rightarrow> integer \<Rightarrow> bool" \<rightharpoonup> (Rhombus) infix 4 "<="
| constant "less :: integer \<Rightarrow> integer \<Rightarrow> bool" \<rightharpoonup> (Rhombus) infix 4 "<"
| constant "abs :: integer \<Rightarrow> integer" \<rightharpoonup> (Rhombus) "abs(_)"

setup \<open>
  Numeral.add_code @{const_name Code_Numeral.Pos} I
    Code_Printer.literal_numeral "Rhombus"
  #> Numeral.add_code @{const_name Code_Numeral.Neg} (~)
    Code_Printer.literal_numeral "Rhombus"
\<close>

section \<open>Native mapped equality\<close>

code_printing
  constant "HOL.equal :: hname \<Rightarrow> hname \<Rightarrow> bool" \<rightharpoonup> (Rhombus) "abi.structural'_equal"
| constant "HOL.equal :: htype \<Rightarrow> htype \<Rightarrow> bool" \<rightharpoonup> (Rhombus) "abi.structural'_equal"
| constant "HOL.equal :: hterm \<Rightarrow> hterm \<Rightarrow> bool" \<rightharpoonup> (Rhombus) "abi.structural'_equal"
| constant "HOL.equal :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (Rhombus) "abi.structural'_equal"

section \<open>Persistent Rhombus function tables\<close>

text \<open>The extracted program uses function update only for immutable generated
  names. Rhombus maps use the same structural equality for those values. Retaining
  the base function and a persistent map flattens update chains without changing the
  observable lookup result of @{const fun_upd}.\<close>

code_printing
  code_module Rhombus_Function_Update \<rightharpoonup> (Rhombus) \<open>
class RhombusFunUpdateValue(value)
class RhombusFunUpdateState(entries, fallback)

def rhombus_fun_update_states = WeakMutableMap.by(===)()

fun rhombus_fun_upd(base):
  fun (key):
    fun (value):
      let state = rhombus_fun_update_states.maybe[base]
                    || RhombusFunUpdateState({}, base)
      let entries = state.entries ++ {key: RhombusFunUpdateValue(value)}
      fun updated(query):
        match entries.get(query, #false)
        | #false: state.fallback(query)
        | RhombusFunUpdateValue(found): found
      rhombus_fun_update_states[updated] := RhombusFunUpdateState(entries, state.fallback)
      updated
\<close> for constant fun_upd
| constant fun_upd \<rightharpoonup> (Rhombus) "rhombus'_fun'_upd"

text \<open>The theorem checker revisits immutable terms and type instances across
  inference results. Weak identity tables partition caches by computation and live
  syntax roots; structural innermost keys share equivalent small environments. A
  cache hit is observationally equal to recomputation.\<close>

code_printing
  code_module Rhombus_Memo \<rightharpoonup> (Rhombus) \<open>
class RhombusMemoValue(value)

def rhombus_binary_memos = WeakMutableMap.by(===)()
def rhombus_ternary_memos = WeakMutableMap.by(===)()

fun rhombus_memoized_binary(run):
  fun (first):
    fun (second):
      let firsts:
        match rhombus_binary_memos.maybe[run]
        | #false:
            let table = WeakMutableMap.by(===)()
            rhombus_binary_memos[run] := table
            table
        | table: table
      let seconds:
        match firsts.maybe[first]
        | #false:
            let table = WeakMutableMap.by(===)()
            firsts[first] := table
            table
        | table: table
      match seconds.maybe[second]
      | #false:
          let result = ((run)(first))(second)
          seconds[second] := RhombusMemoValue(result)
          result
      | RhombusMemoValue(result): result

fun rhombus_memoized_ternary(run):
  fun (first):
    fun (second):
      fun (third):
        let firsts:
          match rhombus_ternary_memos.maybe[run]
          | #false:
              let table = WeakMutableMap.by(===)()
              rhombus_ternary_memos[run] := table
              table
          | table: table
        let seconds:
          match firsts.maybe[first]
          | #false:
              let table = WeakMutableMap.by(===)()
              firsts[first] := table
              table
          | table: table
        let thirds:
          match seconds.maybe[second]
          | #false:
              let table = MutableMap()
              seconds[second] := table
              table
          | table: table
        match thirds.maybe[third]
        | #false:
            let result = (((run)(first))(second))(third)
            thirds[third] := RhombusMemoValue(result)
            result
        | RhombusMemoValue(result): result
\<close> for constant memoize_binary memoize_ternary
| constant memoize_binary \<rightharpoonup> (Rhombus) "rhombus'_memoized'_binary"
| constant memoize_ternary \<rightharpoonup> (Rhombus) "rhombus'_memoized'_ternary"

section \<open>Stable Rhombus API names\<close>

code_identifier
  type_constructor stamp_ext \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Stamp"
| type_constructor hthm_ext \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.HThm"
| type_constructor htheory_ext \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.HTheory"
| type_constructor code_failure \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.FailureCode"
| type_constructor code_result \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Result"
| constant check_open_term_uncached \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.check_open_term_uncached"
| constant type_match_uncached \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.type_match_uncached"
| constant check_term_uncached \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.check_term_uncached"
| constant CodeRuleRejected \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.RuleRejected"
| constant CodeInvalidTypeSubstitution \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.InvalidTypeSubstitution"
| constant CodeExtensionRejected \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.ExtensionRejected"
| constant CodeSuccess \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Success"
| constant CodeFailure \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Failure"
| constant code_refl \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.REFL"
| constant code_trans \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TRANS"
| constant code_mk_comb \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.MK_COMB"
| constant code_abs \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.ABS"
| constant code_beta \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.BETA"
| constant code_assume \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.ASSUME"
| constant code_eq_mp \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.EQ_MP"
| constant code_deduct_antisym \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.DEDUCT_ANTISYM_RULE"
| constant code_inst \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.INST"
| constant code_inst_type \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.INST_TYPE"
| constant code_new_type \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_type_result"
| constant code_new_constant \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_constant_result"
| constant code_new_axiom \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_axiom_result"
| constant code_new_basic_definition \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_basic_definition_result"
| constant code_new_basic_type_definition \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_basic_type_definition_result"
| constant Pair \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.PairValue"

section \<open>Generated Rhombus module\<close>

export_code CodeRuleRejected CodeInvalidTypeSubstitution CodeExtensionRejected
  CodeSuccess CodeFailure Pair
  code_refl code_trans code_mk_comb code_abs code_beta code_assume code_eq_mp
  code_deduct_antisym code_inst code_inst_type
  code_new_type code_new_constant code_new_axiom code_new_basic_definition
  code_new_basic_type_definition
  initial_theory check_type check_open_term check_term is_bool mk_eq dest_eq
  sid gen ancestors hyps concl thm_stamp tyops const_tab axiom_list def_tab thy_stamp
  in Rhombus module_name Rhombus_HOL_Generated file_prefix rhombus_hol_kernel

export_code CodeRuleRejected CodeInvalidTypeSubstitution CodeExtensionRejected
  CodeSuccess CodeFailure Pair
  code_refl code_trans code_mk_comb code_abs code_beta code_assume code_eq_mp
  code_deduct_antisym code_inst code_inst_type
  code_new_type code_new_constant code_new_axiom code_new_basic_definition
  code_new_basic_type_definition
  initial_theory check_type check_open_term check_term is_bool mk_eq dest_eq
  sid gen ancestors hyps concl thm_stamp tyops const_tab axiom_list def_tab thy_stamp
  checking Rhombus
end