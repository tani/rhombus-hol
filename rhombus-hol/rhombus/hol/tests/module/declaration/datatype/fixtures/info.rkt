#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "type_bare_constructor.rhm"
    "type_empty.rhm"
    "type_negative.rhm"
    "type_old_application.rhm"
    "type_old_function.rhm"
    ))
