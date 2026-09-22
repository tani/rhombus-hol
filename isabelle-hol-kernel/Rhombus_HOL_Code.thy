(* SPDX-License-Identifier: 0BSD *)
(* Original code-export equations and Rhombus target configuration. *)

theory Rhombus_HOL_Code
  imports Rhombus_HOL_Code_API "HOL-Library.Code_Target_Numeral"
begin

ML_file "Rhombus_Code_Target.ML"

section \<open>Executable natural-fuel matcher\<close>

definition empty_type_subst :: "hname \<Rightarrow> htype option" where
  "empty_type_subst _ = None"

lemma empty_type_subst_eq [simp]: "empty_type_subst = (\<lambda>_. None)"
  by (rule ext) (simp add: empty_type_subst_def)

section \<open>Single-pass checking with type computation\<close>

text \<open>The specification checks both children of every application and then traverses
  the same subtree again through @{const type_of}. Fuse validation and type
  computation for executable code while leaving the trusted specification unchanged.\<close>

fun check_term_type :: "htheory \<Rightarrow> htype list \<Rightarrow> hterm \<Rightarrow> htype option" where
  "check_term_type thy env (FVar _ ty) =
     (if check_type thy ty then Some ty else None)"
| "check_term_type thy env (BVar i ty) =
     (if i < length env \<and> env ! i = ty \<and> check_type thy ty then Some ty else None)"
| "check_term_type thy env (Const n ty) =
     (if check_type thy ty \<and>
         (case const_tab thy n of None \<Rightarrow> False
          | Some generic \<Rightarrow> type_match generic ty empty_type_subst \<noteq> None)
      then Some ty else None)"
| "check_term_type thy env (NatLit _) =
     (if check_type thy nat_aty \<and> check_type thy nat_sty \<and>
         const_tab thy nat_zero_name = Some nat_aty \<and>
         const_tab thy nat_succ_name = Some nat_sty
      then Some nat_aty else None)"
| "check_term_type thy env (Comb f x) =
     (case (check_term_type thy env f, check_term_type thy env x) of
        (Some (TyApp NFun [dty, rty]), Some aty) \<Rightarrow>
          (if dty = aty then Some rty else None)
      | _ \<Rightarrow> None)"
| "check_term_type thy env (Abs aty body) =
     (if check_type thy aty
      then map_option (mk_fun aty) (check_term_type thy (aty # env) body)
      else None)"

lemma check_open_term_type_of:
  "check_open_term thy env t \<Longrightarrow> type_of t \<noteq> None"
  by (induction t arbitrary: env) auto

lemma check_term_type_eq:
  "check_term_type thy env t = (if check_open_term thy env t then type_of t else None)"
proof (induction t arbitrary: env)
  case (Comb f x)
  show ?case
    using Comb.IH(1)[of env] Comb.IH(2)[of env] check_open_term_type_of
    by (auto split: option.splits htype.splits list.splits hname.splits)
next
  case (Abs aty body)
  show ?case
    using Abs.IH[of "aty # env"] by auto
next
  case (Const n ty)
  show ?case
    by (simp add: empty_type_subst_def split: option.splits)
qed simp_all

definition type_match_uncached ::
  "htype \<Rightarrow> htype \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow> (hname \<Rightarrow> htype option) option" where
  "type_match_uncached pat ty acc =
    (case type_match_fuel (size pat + 1) pat ty acc of
       None \<Rightarrow> None
     | Some \<theta> \<Rightarrow> if type_subst \<theta> pat = ty then Some \<theta> else None)"

lemma type_match_uncached_eq: "type_match_uncached = type_match"
  by (simp add: fun_eq_iff type_match_uncached_def type_match_def)

declare [[code drop: check_open_term]]
declare [[code drop: type_match]]
declare [[code drop: check_term]]
declare [[code drop: check_prop]]

lemma check_open_term_code [code]:
  "check_open_term thy env t \<longleftrightarrow> check_term_type thy env t \<noteq> None"
  by (auto simp: check_term_type_eq dest: check_open_term_type_of)

lemma type_match_code [code]:
  "type_match pat ty acc = type_match_uncached pat ty acc"
  by (simp add: type_match_uncached_eq)

lemma check_term_code [code]:
  "check_term thy t \<longleftrightarrow> check_term_type thy [] t \<noteq> None"
  by (auto simp: check_term_def check_term_type_eq dest: check_open_term_type_of)

lemma check_prop_code [code]:
  "check_prop thy p \<longleftrightarrow> check_term_type thy [] p = Some bool_ty"
  by (auto simp: check_prop_def check_term_def is_bool_def check_term_type_eq)

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

section \<open>Stable Rhombus API names\<close>

code_identifier
  type_constructor stamp_ext \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Stamp"
| type_constructor hthm_ext \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.HThm"
| type_constructor htheory_ext \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.HTheory"
| type_constructor code_failure \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.FailureCode"
| type_constructor code_result \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Result"
| constant type_match_uncached \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.type_match_uncached"
| constant CodeUndeclaredType \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.UndeclaredType"
| constant CodeTypeArity \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TypeArity"
| constant CodeInvalidType \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.InvalidType"
| constant CodeUnboundIndex \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.UnboundIndex"
| constant CodeBinderTypeMismatch \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.BinderTypeMismatch"
| constant CodeUndeclaredConstant \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.UndeclaredConstant"
| constant CodeConstantTypeMismatch \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.ConstantTypeMismatch"
| constant CodeOperatorNotFunction \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.OperatorNotFunction"
| constant CodeIllTypedApplication \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.IllTypedApplication"
| constant CodeNotProposition \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.NotProposition"
| constant CodeNotEquation \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.NotEquation"
| constant CodeMiddleTermsDiffer \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.MiddleTermsDiffer"
| constant CodeCombinationTypeMismatch \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.CombinationTypeMismatch"
| constant CodeVariableFreeInHypotheses \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.VariableFreeInHypotheses"
| constant CodeNotBetaRedex \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.NotBetaRedex"
| constant CodeAntecedentMismatch \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.AntecedentMismatch"
| constant CodeInvalidInstantiationTarget \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.InvalidInstantiationTarget"
| constant CodeInstantiationTypeMismatch \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.InstantiationTypeMismatch"
| constant CodeInvalidTypeSubstitution \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.InvalidTypeSubstitution"
| constant CodeDuplicateType \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.DuplicateType"
| constant CodeDuplicateConstant \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.DuplicateConstant"
| constant CodeDefinitionNotEquation \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.DefinitionNotEquation"
| constant CodeDefinitionLeftNotVariable \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.DefinitionLeftNotVariable"
| constant CodeDefinitionOpen \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.DefinitionOpen"
| constant CodeDefinitionTypeMismatch \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.DefinitionTypeMismatch"
| constant CodeDefinitionExtraTypeVariables \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.DefinitionExtraTypeVariables"
| constant CodeTypeDefinitionSameConstants \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TypeDefinitionSameConstants"
| constant CodeTypeDefinitionHasHypotheses \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TypeDefinitionHasHypotheses"
| constant CodeTypeDefinitionOpenPredicate \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TypeDefinitionOpenPredicate"
| constant CodeTypeDefinitionExtraTypeVariables \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TypeDefinitionExtraTypeVariables"
| constant CodeTypeDefinitionBadWitness \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TypeDefinitionBadWitness"
| constant CodeRuleRejected \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.RuleRejected"
| constant CodeExtensionRejected \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.ExtensionRejected"
| constant CodeSuccess \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Success"
| constant CodeFailure \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.Failure"
| constant code_check_type \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.check_type_result"
| constant code_check_term \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.check_term_result"
| constant code_refl \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.refl"
| constant code_trans \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.trans"
| constant code_mk_comb \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.mk_comb"
| constant code_abs \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.abs"
| constant code_beta \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.beta"
| constant code_assume \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.assume"
| constant code_eq_mp \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.eq_mp"
| constant code_deduct_antisym \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.deduct_antisym"
| constant code_inst \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.inst"
| constant code_inst_type \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.inst_type"
| constant code_nat_lit_conv \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.nat_lit_conv"
| constant code_nat_lit_eq_conv \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.nat_lit_eq_conv"
| constant code_nat_lit_add_conv \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.nat_lit_add_conv"
| constant code_nat_lit_mul_conv \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.nat_lit_mul_conv"
| constant code_nat_lit_le_conv \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.nat_lit_le_conv"
| constant code_nat_lit_sub_conv \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.nat_lit_sub_conv"
| constant code_nat_lit_pow_conv \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.nat_lit_pow_conv"
| constant code_new_type \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_type"
| constant code_new_nat_type \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_nat_type"
| constant code_new_constant \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_constant"
| constant code_new_axiom \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_axiom"
| constant code_new_basic_definition \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_basic_definition"
| constant code_new_basic_type_definition \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_basic_type_definition"
| constant Pair \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.PairValue"
section \<open>Generated Rhombus module\<close>

export_code CodeUndeclaredType CodeTypeArity CodeInvalidType CodeUnboundIndex
  CodeBinderTypeMismatch CodeUndeclaredConstant CodeConstantTypeMismatch
  CodeOperatorNotFunction CodeIllTypedApplication CodeNotProposition CodeNotEquation
  CodeMiddleTermsDiffer CodeCombinationTypeMismatch CodeVariableFreeInHypotheses
  CodeNotBetaRedex CodeAntecedentMismatch CodeInvalidInstantiationTarget
  CodeInstantiationTypeMismatch CodeInvalidTypeSubstitution CodeDuplicateType
  CodeDuplicateConstant CodeDefinitionNotEquation CodeDefinitionLeftNotVariable
  CodeDefinitionOpen CodeDefinitionTypeMismatch CodeDefinitionExtraTypeVariables
  CodeTypeDefinitionSameConstants CodeTypeDefinitionHasHypotheses
  CodeTypeDefinitionOpenPredicate CodeTypeDefinitionExtraTypeVariables
  CodeTypeDefinitionBadWitness CodeRuleRejected CodeExtensionRejected
  CodeSuccess CodeFailure Pair None Some
  code_check_type code_check_term
  code_refl code_trans code_mk_comb code_abs code_beta code_assume code_eq_mp
  code_deduct_antisym code_inst code_inst_type
  code_nat_lit_conv code_nat_lit_eq_conv code_nat_lit_add_conv code_nat_lit_mul_conv
  code_nat_lit_le_conv code_nat_lit_sub_conv code_nat_lit_pow_conv code_new_nat_type code_new_type code_new_constant code_new_axiom
  code_new_basic_definition code_new_basic_type_definition
  initial_theory check_type check_open_term check_term is_bool mk_eq dest_eq
  sid gen ancestors hyps concl thm_stamp tyops const_tab axiom_list def_tab thy_stamp
  in Rhombus module_name Rhombus_HOL_Generated file_prefix rhombus_hol_kernel

export_code CodeUndeclaredType CodeTypeArity CodeInvalidType CodeUnboundIndex
  CodeBinderTypeMismatch CodeUndeclaredConstant CodeConstantTypeMismatch
  CodeOperatorNotFunction CodeIllTypedApplication CodeNotProposition CodeNotEquation
  CodeMiddleTermsDiffer CodeCombinationTypeMismatch CodeVariableFreeInHypotheses
  CodeNotBetaRedex CodeAntecedentMismatch CodeInvalidInstantiationTarget
  CodeInstantiationTypeMismatch CodeInvalidTypeSubstitution CodeDuplicateType
  CodeDuplicateConstant CodeDefinitionNotEquation CodeDefinitionLeftNotVariable
  CodeDefinitionOpen CodeDefinitionTypeMismatch CodeDefinitionExtraTypeVariables
  CodeTypeDefinitionSameConstants CodeTypeDefinitionHasHypotheses
  CodeTypeDefinitionOpenPredicate CodeTypeDefinitionExtraTypeVariables
  CodeTypeDefinitionBadWitness CodeRuleRejected CodeExtensionRejected
  CodeSuccess CodeFailure Pair None Some
  code_check_type code_check_term
  code_refl code_trans code_mk_comb code_abs code_beta code_assume code_eq_mp
  code_nat_lit_conv code_nat_lit_eq_conv code_nat_lit_add_conv code_nat_lit_mul_conv
  code_nat_lit_le_conv code_nat_lit_sub_conv code_nat_lit_pow_conv code_new_nat_type code_new_type code_new_constant code_new_axiom
  code_new_basic_definition code_new_basic_type_definition
  initial_theory check_type check_open_term check_term is_bool mk_eq dest_eq
  sid gen ancestors hyps concl thm_stamp tyops const_tab axiom_list def_tab thy_stamp
  checking Rhombus

end
