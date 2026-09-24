#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "theorem_do_not_bad_name.rhm"
    "theorem_do_not_stuck.rhm"
    "theorem_in_theory_stuck.rhm"
    "theorem_not_automatic.rhm"
    "theorem_stuck.rhm"
    ))
