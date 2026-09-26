#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "fun_inexhaustive.rhm"
    "fun_nonterminating.rhm"
    "function_bad_body.rhm"
    "function_no_result_type.rhm"
    "let_local_forward_bad.rhm"
    "let_local_self_bad.rhm"
    "let_recursive_bad.rhm"
    "mutual_datatype_empty_bad.rhm"
    "mutual_function_nonterminating_bad.rhm"
    "mutual_measure_types_bad.rhm"
    ))
