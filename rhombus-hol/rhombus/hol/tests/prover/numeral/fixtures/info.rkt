#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "numeral_ambiguous_bad.rhm"
    "numeral_concrete_mismatch_bad.rhm"
    "numeral_disable_arithmetic_bad.rhm"
    "numeral_disable_exposure_bad.rhm"
    "numeral_pattern_integer_bad.rhm"
    "numeral_pattern_partial.rhm"
    ))
