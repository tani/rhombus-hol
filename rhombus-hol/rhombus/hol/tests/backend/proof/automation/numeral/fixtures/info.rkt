#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "numeral_disable_arithmetic_bad.rhm"
    "numeral_disable_exposure_bad.rhm"
    "numeral_int_as_nat_bad.rhm"
    "numeral_nat_as_integer_bad.rhm"
    "numeral_nat_to_integer_bad.rhm"
    "numeral_negative_pattern_bad.rhm"
    "numeral_pattern_partial.rhm"
    "numeral_positive_pattern_bad.rhm"
    ))
