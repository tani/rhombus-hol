#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "theory_after_decl.rhm"
    "theory_forged_user.rhm"
    "theory_meta_import.rhm"
    "theory_out_of_order.rhm"
    ))
