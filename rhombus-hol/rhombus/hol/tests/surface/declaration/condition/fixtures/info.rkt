#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "apply_branch_mismatch_bad.rhm"
    "apply_overapplied_bad.rhm"
    "bool_op_branch_mismatch_bad.rhm"
    "cond_missing_else.rhm"
    "conditional_stuck.rhm"
    "eq_branch_mismatch_bad.rhm"
    "list_expr_branch_mismatch_bad.rhm"
    "pair_branch_mismatch_bad.rhm"
    "set_expr_branch_mismatch_bad.rhm"
    "set_expr_fn_element_bad.rhm"
    "string_expr_branch_mismatch_bad.rhm"
    "typed_branch_mismatch_bad.rhm"
    ))
