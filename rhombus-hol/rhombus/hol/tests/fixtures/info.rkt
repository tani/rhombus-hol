#lang info

(define module-suffixes '(#"rhm"))
;; These are inputs to tests, not tests: some of them are *meant* not to
;; compile, so `raco test` must not try to run them.
(define test-omit-paths 'all)
;; The fixtures have two contracts. Positive modules are compiled by `raco
;; setup`, while this exact set is instantiated by negative tests and must
;; remain uncompiled so its diagnostic is observed by the test harness.
(define compile-omit-paths
  '("bad_expect.rhm"
    "clausal_arity.rhm"
    "cond_missing_else.rhm"
    "conditional_stuck.rhm"
    "fun_inexhaustive.rhm"
    "fun_nonterminating.rhm"
    "function_bad_body.rhm"
    "function_no_result_type.rhm"
    "function_unsupported.rhm"
    "let_missing.rhm"
    "let_recursive_bad.rhm"
    "lexicographic_partial.rhm"
    "lexicographic_rematch_same.rhm"
    "measure_constant.rhm"
    "measure_missing.rhm"
    "measure_nonrecursive.rhm"
    "measure_not_datatype.rhm"
    "name_alias_bad.rhm"
    "nested_match_partial.rhm"
    "notation_empty_bad.rhm"
    "notation_logic_function_bad.rhm"
    "notation_logic_runtime_bad.rhm"
    "notation_runtime_logic_bad.rhm"
    "operator_bad.rhm"
    "ordered_partial.rhm"
    "ordered_unreachable.rhm"
    "qc_variable_type.rhm"
    "search_steps_starved.rhm"
    "theorem_do_not_bad_name.rhm"
    "theorem_do_not_stuck.rhm"
    "theorem_in_theory_stuck.rhm"
    "theorem_orphan_proof.rhm"
    "theorem_stuck.rhm"
    "theory_after_decl.rhm"
    "theory_forged_user.rhm"
    "theory_meta_import.rhm"
    "theory_out_of_order.rhm"
    "type_empty.rhm"
    "type_negative.rhm"))
