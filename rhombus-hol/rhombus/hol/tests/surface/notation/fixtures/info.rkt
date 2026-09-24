#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "name_alias_bad.rhm"
    "notation_associativity_bad.rhm"
    "notation_empty_bad.rhm"
    "notation_implementation_bad.rhm"
    "notation_runtime_bad.rhm"
    "operator_bad.rhm"
    "operator_comparison_chain_bad.rhm"
    "operator_equality_chain_bad.rhm"
    "operator_plain_logic_bad.rhm"
    ))
