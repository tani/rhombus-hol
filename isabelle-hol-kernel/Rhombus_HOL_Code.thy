(* SPDX-License-Identifier: 0BSD AND BSD-2-Clause AND BSD-3-Clause *)
(* Conservatively covered by HOL Light and HOL4 notices; see THIRD_PARTY_NOTICES. *)

theory Rhombus_HOL_Code
  imports Rhombus_HOL_Code_API "HOL-Library.Code_Target_Numeral"
begin

ML_file "Rhombus_Code_Target.ML"

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
| type_constructor extension_delta \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.ExtensionDelta"
| constant check_open_term_uncached \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.check_open_term_uncached"
| constant type_match_uncached \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.type_match_uncached"
| constant check_term_uncached \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.check_term_uncached"
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
| constant DeltaType \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TypeDelta"
| constant DeltaConstant \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.ConstantDelta"
| constant DeltaAxiom \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.AxiomDelta"
| constant DeltaDefinition \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.DefinitionDelta"
| constant DeltaTypeDefinition \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.TypeDefinitionDelta"
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
| constant code_new_type_with_delta \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_type"
| constant code_new_constant_with_delta \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_constant"
| constant code_new_axiom_with_delta \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_axiom"
| constant code_new_basic_definition_with_delta \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_basic_definition"
| constant code_new_basic_type_definition_with_delta \<rightharpoonup> (Rhombus) "Rhombus_HOL_Generated.new_basic_type_definition"
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
  CodeSuccess CodeFailure DeltaType DeltaConstant DeltaAxiom DeltaDefinition
  DeltaTypeDefinition Pair
  code_check_type code_check_term
  code_refl code_trans code_mk_comb code_abs code_beta code_assume code_eq_mp
  code_deduct_antisym code_inst code_inst_type
  code_new_type_with_delta code_new_constant_with_delta code_new_axiom_with_delta
  code_new_basic_definition_with_delta code_new_basic_type_definition_with_delta
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
  CodeSuccess CodeFailure DeltaType DeltaConstant DeltaAxiom DeltaDefinition
  DeltaTypeDefinition Pair
  code_check_type code_check_term
  code_refl code_trans code_mk_comb code_abs code_beta code_assume code_eq_mp
  code_deduct_antisym code_inst code_inst_type
  code_new_type_with_delta code_new_constant_with_delta code_new_axiom_with_delta
  code_new_basic_definition_with_delta code_new_basic_type_definition_with_delta
  initial_theory check_type check_open_term check_term is_bool mk_eq dest_eq
  sid gen ancestors hyps concl thm_stamp tyops const_tab axiom_list def_tab thy_stamp
  checking Rhombus

end
