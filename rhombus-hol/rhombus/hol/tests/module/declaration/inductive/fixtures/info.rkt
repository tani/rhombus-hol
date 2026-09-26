#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "inductive_conclusion_bad.rhm"
    "inductive_negative_bad.rhm"
    "inductive_unapplied_bad.rhm"
    ))
