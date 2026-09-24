#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "anon_calls_enclosing_bad.rhm"
    "bool_pattern_partial_bad.rhm"
    "exists1_in_function_bad.rhm"
    "exists1_multi_bad.rhm"
    "extensionality_non_function_bad.rhm"
    "let_refutable_pattern_bad.rhm"
    "local_calls_enclosing_bad.rhm"
    "local_mutual_recursion_bad.rhm"
    "nested_match_partial.rhm"
    "select_in_function_bad.rhm"
    "select_multi_bad.rhm"
    "theorem_binder_pattern_bad.rhm"
    ))
