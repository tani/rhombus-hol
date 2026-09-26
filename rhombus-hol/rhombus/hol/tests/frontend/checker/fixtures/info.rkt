#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "coverage_duplicate_bad.rhm"
    "coverage_family_bad.rhm"
    "coverage_inexhaustive_bad.rhm"
    "coverage_literal_bad.rhm"
    "coverage_reserved_bad.rhm"
    "coverage_unreachable_bad.rhm"
    ))
