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


section \<open>Code-generation rule requests\<close>

datatype code_rule_request =
    CodeRefl htheory hterm
  | CodeTrans htheory hthm hthm
  | CodeMkComb htheory hthm hthm
  | CodeAbs htheory hname htype hthm
  | CodeBeta htheory hterm
  | CodeAssume htheory hterm
  | CodeEqMp htheory hthm hthm
  | CodeDeductAntisym htheory hthm hthm
  | CodeInst htheory "(hterm \<times> hterm) list" hthm
  | CodeInstType htheory type_subst_entries hthm

fun valid_code_rule_request :: "code_rule_request \<Rightarrow> bool" where
  "valid_code_rule_request (CodeRefl _ _) = True"
| "valid_code_rule_request (CodeTrans _ _ _) = True"
| "valid_code_rule_request (CodeMkComb _ _ _) = True"
| "valid_code_rule_request (CodeAbs _ _ _ _) = True"
| "valid_code_rule_request (CodeBeta _ _) = True"
| "valid_code_rule_request (CodeAssume _ _) = True"
| "valid_code_rule_request (CodeEqMp _ _ _) = True"
| "valid_code_rule_request (CodeDeductAntisym _ _ _) = True"
| "valid_code_rule_request (CodeInst _ _ _) = True"
| "valid_code_rule_request (CodeInstType thy entries _) =
    valid_type_subst_entries thy entries"

fun inference_of_code_rule :: "code_rule_request \<Rightarrow> inference" where
  "inference_of_code_rule (CodeRefl thy t) = IRefl thy t"
| "inference_of_code_rule (CodeTrans thy a b) = ITrans thy a b"
| "inference_of_code_rule (CodeMkComb thy a b) = IMkComb thy a b"
| "inference_of_code_rule (CodeAbs thy n ty th) = IAbs thy n ty th"
| "inference_of_code_rule (CodeBeta thy t) = IBeta thy t"
| "inference_of_code_rule (CodeAssume thy p) = IAssume thy p"
| "inference_of_code_rule (CodeEqMp thy a b) = IEqMp thy a b"
| "inference_of_code_rule (CodeDeductAntisym thy a b) = IDeductAntisym thy a b"
| "inference_of_code_rule (CodeInst thy entries th) = IInst thy entries th"
| "inference_of_code_rule (CodeInstType thy entries th) =
    IInstType thy (entries_subst entries) th"

fun run_code_rule :: "code_rule_request \<Rightarrow> hthm option" where
  "run_code_rule (CodeRefl thy t) = refl thy t"
| "run_code_rule (CodeTrans thy a b) = trans thy a b"
| "run_code_rule (CodeMkComb thy a b) = mk_comb_rule thy a b"
| "run_code_rule (CodeAbs thy n ty th) = abs_rule thy n ty th"
| "run_code_rule (CodeBeta thy t) = beta thy t"
| "run_code_rule (CodeAssume thy p) = assume_rule thy p"
| "run_code_rule (CodeEqMp thy a b) = eq_mp thy a b"
| "run_code_rule (CodeDeductAntisym thy a b) = deduct_antisym_rule thy a b"
| "run_code_rule (CodeInst thy entries th) = inst thy entries th"
| "run_code_rule (CodeInstType thy entries th) = inst_type_entries thy entries th"

lemma run_code_rule_correspondence:
  assumes "valid_code_rule_request request"
  shows "run_code_rule request = run_rule (inference_of_code_rule request)"
  using assms by (cases request) (simp_all add: inst_type_entries_agrees)

lemma run_code_rule_sound:
  assumes valid: "valid_code_rule_request request"
    and run: "run_code_rule request = Some th"
  shows "rule_spec (inference_of_code_rule request) th"
  using run_rule_sound run run_code_rule_correspondence[OF valid] by metis

lemma run_code_rule_preserves_wf:
  assumes valid: "valid_code_rule_request request"
    and run: "run_code_rule request = Some th"
    and inputs: "wf_inputs (inference_of_code_rule request)"
  shows "wf_thm (ambient_theory (inference_of_code_rule request)) th"
  using run_rule_preserves_wf run inputs run_code_rule_correspondence[OF valid] by metis



section \<open>Executable natural-fuel matcher\<close>

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

section \<open>Stable Rhombus API names\<close>

code_identifier
  type_constructor hname \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.HName"
| type_constructor htype \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.HType"
| type_constructor hterm \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.HTerm"
| type_constructor stamp_ext \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Stamp"
| type_constructor hthm_ext \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.HThm"
| type_constructor htheory_ext \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.HTheory"
| type_constructor code_rule_request \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeRuleRequest"
| constant NFun \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.NFun"
| constant NBool \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.NBool"
| constant NEq \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.NEq"
| constant NAlpha \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.NAlpha"
| constant NRepVar \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.NRepVar"
| constant NUser \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.NUser"
| constant TyVar \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TyVar"
| constant TyApp \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TyApp"
| constant FVar \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.FVar"
| constant BVar \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.BVar"
| constant Const \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Const"
| constant Comb \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Comb"
| constant Rhombus_HOL_Syntax.Abs \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Abs"
| constant CodeRefl \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeRefl"
| constant CodeTrans \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeTrans"
| constant CodeMkComb \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeMkComb"
| constant CodeAbs \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeAbs"
| constant CodeBeta \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeBeta"
| constant CodeAssume \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeAssume"
| constant CodeEqMp \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeEqMp"
| constant CodeDeductAntisym \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeDeductAntisym"
| constant CodeInst \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeInst"
| constant CodeInstType \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CodeInstType"
| constant Nil \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Nil"
| constant Cons \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Cons"
| constant None \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.None"
| constant Some \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Some"
| constant Pair \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.PairValue"


section \<open>Generated Rhombus module\<close>

export_code NFun NBool NEq NAlpha NRepVar NUser
  nat_value Nil Cons None Some Pair
  TyVar TyApp FVar BVar Const Comb Rhombus_HOL_Syntax.Abs
  CodeRefl CodeTrans CodeMkComb CodeAbs CodeBeta CodeAssume CodeEqMp
  CodeDeductAntisym CodeInst CodeInstType
  bool_ty mk_fun dest_fun type_vars type_var_occurs type_operator_occurs
  type_of free_vars term_type_vars vfree_in
  wf_stamp fresh_stamp next_stamp descends combine_stamps initial_theory
  check_type check_open_term check_term is_bool check_prop
  eq_const eq_term mk_eq dest_eq
  sid gen ancestors hyps concl thm_stamp tyops const_tab axiom_list def_tab thy_stamp
  wf_thm valid_code_rule_request run_code_rule
  extend_theory new_type new_constant new_axiom new_basic_definition
  new_basic_type_definition
  in Rhombus module_name Rhombus_HOL_Generated file_prefix rhombus_hol_kernel

export_code NFun NBool NEq NAlpha NRepVar NUser
  nat_value Nil Cons None Some Pair
  TyVar TyApp FVar BVar Const Comb Rhombus_HOL_Syntax.Abs
  CodeRefl CodeTrans CodeMkComb CodeAbs CodeBeta CodeAssume CodeEqMp
  CodeDeductAntisym CodeInst CodeInstType
  bool_ty mk_fun dest_fun type_vars type_var_occurs type_operator_occurs
  type_of free_vars term_type_vars vfree_in
  wf_stamp fresh_stamp next_stamp descends combine_stamps initial_theory
  check_type check_open_term check_term is_bool check_prop
  eq_const eq_term mk_eq dest_eq
  sid gen ancestors hyps concl thm_stamp tyops const_tab axiom_list def_tab thy_stamp
  wf_thm valid_code_rule_request run_code_rule
  extend_theory new_type new_constant new_axiom new_basic_definition
  new_basic_type_definition checking Rhombus

end