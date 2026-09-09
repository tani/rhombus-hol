(* SPDX-License-Identifier: 0BSD AND BSD-2-Clause AND BSD-3-Clause *)
(* Conservatively covered by HOL Light and HOL4 notices; see THIRD_PARTY_NOTICES. *)

theory Rhombus_HOL_Countermodels
  imports "HOL.Nitpick"
begin

text \<open>These finite abstractions remove HOLZF's axiomatized universe from the
Nitpick search problem. Each datatype retains exactly the guard-relevant state.\<close>

datatype ctype = CNum | CBool | CFun ctype ctype
datatype cterm =
    CFree nat ctype
  | CBound nat ctype
  | CConstant nat ctype
  | CApp cterm cterm
  | CLam ctype cterm

fun ctype_of :: "cterm \<Rightarrow> ctype option" where
  "ctype_of (CFree _ ty) = Some ty"
| "ctype_of (CBound _ ty) = Some ty"
| "ctype_of (CConstant _ ty) = Some ty"
| "ctype_of (CLam ty body) = map_option (CFun ty) (ctype_of body)"
| "ctype_of (CApp f x) =
    (case (ctype_of f, ctype_of x) of
       (Some (CFun dty cod), Some aty) \<Rightarrow> if dty = aty then Some cod else None
     | _ \<Rightarrow> None)"

fun guarded_check :: "ctype list \<Rightarrow> cterm \<Rightarrow> bool" where
  "guarded_check _ (CFree _ _) = True"
| "guarded_check env (CBound i ty) =
    (i < length env \<and> env ! i = ty)"
| "guarded_check _ (CConstant _ _) = True"
| "guarded_check env (CApp f x) =
    (guarded_check env f \<and> guarded_check env x \<and>
      (case (ctype_of f, ctype_of x) of
         (Some (CFun dty _), Some aty) \<Rightarrow> dty = aty
       | _ \<Rightarrow> False))"
| "guarded_check env (CLam ty body) = guarded_check (ty # env) body"

fun weakened_check :: "ctype list \<Rightarrow> cterm \<Rightarrow> bool" where
  "weakened_check _ (CFree _ _) = True"
| "weakened_check env (CBound i _) = (i < length env)"
| "weakened_check _ (CConstant _ _) = True"
| "weakened_check env (CApp f x) =
    (weakened_check env f \<and> weakened_check env x \<and>
      (case (ctype_of f, ctype_of x) of
         (Some (CFun dty _), Some aty) \<Rightarrow> dty = aty
       | _ \<Rightarrow> False))"
| "weakened_check env (CLam ty body) = weakened_check (ty # env) body"

fun subst_zero :: "cterm \<Rightarrow> cterm \<Rightarrow> cterm" where
  "subst_zero arg (CBound 0 _) = arg"
| "subst_zero _ (CBound (Suc i) ty) = CBound i ty"
| "subst_zero _ (CFree n ty) = CFree n ty"
| "subst_zero _ (CConstant n ty) = CConstant n ty"
| "subst_zero arg (CApp f x) = CApp (subst_zero arg f) (subst_zero arg x)"
| "subst_zero arg (CLam ty body) = CLam ty (subst_zero arg body)"

lemma binder_type_guard_countermodel:
  "\<exists>aty body arg rty.
    weakened_check [] (CApp (CLam aty body) arg) \<and>
    ctype_of (CApp (CLam aty body) arg) = Some rty \<and>
    ctype_of (subst_zero arg body) \<noteq> Some rty"
  nitpick [card = 1-5, satisfy, expect = genuine, timeout = 30]
  by (rule exI[of _ CNum], rule exI[of _ "CBound 0 CBool"],
      rule exI[of _ "CConstant 0 CNum"], rule exI[of _ CBool]) simp

record cstamp =
  csid :: nat
  cgen :: nat
  cancestors :: "nat set"

definition comparable :: "cstamp \<Rightarrow> cstamp \<Rightarrow> bool" where
  "comparable a b \<longleftrightarrow> csid a \<in> cancestors b \<or> csid b \<in> cancestors a"

record cbranch =
  branch_stamp :: cstamp
  zero_meaning :: bool

definition safe_merge :: "cbranch \<Rightarrow> cbranch \<Rightarrow> cbranch option" where
  "safe_merge a b = (if comparable (branch_stamp a) (branch_stamp b)
    then Some b else None)"

definition generation_only_merge :: "cbranch \<Rightarrow> cbranch \<Rightarrow> cbranch option" where
  "generation_only_merge a b = (if cgen (branch_stamp a) = cgen (branch_stamp b)
    then Some b else None)"

definition conflicting_zero :: "cbranch \<Rightarrow> cbranch \<Rightarrow> bool" where
  "conflicting_zero a b \<longleftrightarrow> zero_meaning a \<noteq> zero_meaning b"

lemma lineage_sibling_countermodel:
  "\<exists>a b. generation_only_merge a b = Some b \<and> safe_merge a b = None \<and>
    conflicting_zero a b"
  nitpick [card = 1-5, satisfy, expect = genuine, timeout = 30]
  by (rule exI[of _
        "\<lparr>branch_stamp = \<lparr>csid = 1, cgen = 1, cancestors = {0, 1}\<rparr>,
           zero_meaning = False\<rparr>"],
      rule exI[of _
        "\<lparr>branch_stamp = \<lparr>csid = 2, cgen = 1, cancestors = {0, 2}\<rparr>,
           zero_meaning = True\<rparr>"])
    (simp add: generation_only_merge_def safe_merge_def comparable_def
      conflicting_zero_def)

datatype csymbol = CSymbol0 | CSymbol1

record csnapshot =
  snapshot_stamp :: cstamp
  declared_symbols :: "csymbol set"

record cproof =
  proof_stamp :: cstamp
  used_symbols :: "csymbol set"
definition proof_wf :: "csnapshot \<Rightarrow> cproof \<Rightarrow> bool" where
  "proof_wf thy th \<longleftrightarrow>
    csid (proof_stamp th) \<in> cancestors (snapshot_stamp thy) \<and>
    used_symbols th \<subseteq> declared_symbols thy"

definition stale_result :: "csnapshot \<Rightarrow> csymbol \<Rightarrow> cproof" where
  "stale_result old late =
    \<lparr>proof_stamp = snapshot_stamp old, used_symbols = {late}\<rparr>"

lemma stale_stamp_countermodel:
  "\<exists>old current late.
    late \<notin> declared_symbols old \<and> late \<in> declared_symbols current \<and>
    proof_wf current (stale_result old late) \<and>
    \<not> proof_wf old (stale_result old late)"
  nitpick [card = 1-5, satisfy, expect = genuine, timeout = 30]
  by (rule exI[of _
        "\<lparr>snapshot_stamp = \<lparr>csid = 0, cgen = 0, cancestors = {0}\<rparr>,
           declared_symbols = {}\<rparr>"],
      rule exI[of _
        "\<lparr>snapshot_stamp = \<lparr>csid = 1, cgen = 1, cancestors = {0, 1}\<rparr>,
           declared_symbols = {CSymbol1}\<rparr>"],
      rule exI[of _ CSymbol1])
    (simp add: proof_wf_def stale_result_def)

datatype cinst_target = CInstVariable nat | CInstArbitrary cterm

fun replace_free :: "nat \<Rightarrow> cterm \<Rightarrow> cterm \<Rightarrow> cterm" where
  "replace_free n replacement (CFree m ty) =
    (if n = m then replacement else CFree m ty)"
| "replace_free _ _ (CBound i ty) = CBound i ty"
| "replace_free _ _ (CConstant n ty) = CConstant n ty"
| "replace_free n replacement (CApp f x) =
    CApp (replace_free n replacement f) (replace_free n replacement x)"
| "replace_free n replacement (CLam ty body) =
    CLam ty (replace_free n replacement body)"

fun guarded_inst :: "cinst_target \<Rightarrow> cterm \<Rightarrow> cterm \<Rightarrow> cterm option" where
  "guarded_inst (CInstVariable n) replacement source =
    Some (replace_free n replacement source)"
| "guarded_inst (CInstArbitrary _) _ _ = None"

fun weakened_inst :: "cinst_target \<Rightarrow> cterm \<Rightarrow> cterm \<Rightarrow> cterm option" where
  "weakened_inst (CInstVariable n) replacement source =
    Some (replace_free n replacement source)"
| "weakened_inst (CInstArbitrary _) _ source = Some source"

lemma inst_target_guard_countermodel:
  "\<exists>target replacement source.
    weakened_inst target replacement source = Some source \<and>
    guarded_inst target replacement source = None"
  nitpick [card = 1-5, satisfy, expect = genuine, timeout = 30]
  by (rule exI[of _ "CInstArbitrary (CConstant 0 CBool)"],
      rule exI[of _ "CConstant 1 CBool"],
      rule exI[of _ "CConstant 2 CBool"]) simp

definition definition_model_exists :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "definition_model_exists closed scoped \<longleftrightarrow>
    (\<exists>constant_value. \<forall>free_value type_instance.
      constant_value =
        (if closed then if scoped then False else type_instance else free_value))"

definition weakened_definition_guard :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "weakened_definition_guard closed scoped \<longleftrightarrow> closed \<or> scoped"

lemma definition_closedness_guard_countermodel:
  "\<exists>closed scoped. weakened_definition_guard closed scoped \<and>
    \<not> definition_model_exists closed scoped"
  nitpick [card = 1-5, satisfy, expect = genuine, timeout = 30]
  by (rule exI[of _ False], rule exI[of _ True])
    (auto simp: weakened_definition_guard_def definition_model_exists_def)

lemma definition_scope_guard_countermodel:
  "\<exists>closed scoped. weakened_definition_guard closed scoped \<and>
    \<not> definition_model_exists closed scoped"
  nitpick [card = 1-5, satisfy, expect = genuine, timeout = 30]
  by (rule exI[of _ True], rule exI[of _ False])
    (auto simp: weakened_definition_guard_def definition_model_exists_def)

definition type_extension_constructible ::
  "(bool \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "type_extension_constructible pred fresh distinct_names \<longleftrightarrow>
    (\<exists>witness. pred witness) \<and> fresh \<and> distinct_names"

definition weakened_type_definition_guard ::
  "(bool \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "weakened_type_definition_guard pred fresh distinct_names \<longleftrightarrow>
    fresh \<and> distinct_names"

lemma type_definition_guard_countermodel:
  "\<exists>pred fresh distinct_names.
    weakened_type_definition_guard pred fresh distinct_names \<and>
    \<not> type_extension_constructible pred fresh distinct_names"
  nitpick [card = 1-5, satisfy, expect = genuine, timeout = 30]
  by (rule exI[of _ "\<lambda>_. False"], rule exI[of _ True],
      rule exI[of _ True])
    (simp add: weakened_type_definition_guard_def
      type_extension_constructible_def)

record cname =
  identity :: nat
  display_name :: bool

definition same_display :: "cname \<Rightarrow> cname \<Rightarrow> bool" where
  "same_display a b \<longleftrightarrow> display_name a = display_name b"

definition identity_insert :: "cname \<Rightarrow> cname list \<Rightarrow> cname list" where
  "identity_insert x xs = (if x \<in> set xs then xs else xs @ [x])"

definition display_insert :: "cname \<Rightarrow> cname list \<Rightarrow> cname list" where
  "display_insert x xs =
    (if \<exists>y\<in>set xs. same_display x y then xs else xs @ [x])"

lemma same_printing_symbol_countermodel:
  "\<exists>a b. a \<noteq> b \<and> same_display a b \<and>
    length (display_insert b (display_insert a [])) = 1 \<and>
    length (identity_insert b (identity_insert a [])) = 2"
  nitpick [card = 1-5, satisfy, expect = genuine, timeout = 30]
  by (rule exI[of _ "\<lparr>identity = 0, display_name = False\<rparr>"],
      rule exI[of _ "\<lparr>identity = 1, display_name = False\<rparr>"])
    (simp add: same_display_def display_insert_def identity_insert_def)

end
