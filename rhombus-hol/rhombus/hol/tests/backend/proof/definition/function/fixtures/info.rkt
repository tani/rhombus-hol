#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "deep_recursive_call_bad.rhm"
    "function_unsupported.rhm"
    "lexicographic_partial.rhm"
    "lexicographic_rematch_same.rhm"
    "measure_constant.rhm"
    "measure_missing.rhm"
    "measure_nonrecursive.rhm"
    "measure_not_datatype.rhm"
    "ordered_partial.rhm"
    "ordered_unreachable.rhm"
    ))
