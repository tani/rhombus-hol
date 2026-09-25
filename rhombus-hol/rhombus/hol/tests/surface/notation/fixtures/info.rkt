#lang info

(define module-suffixes '(#"rhm"))

;; Fixtures are inputs to their owning feature tests, never test modules.
(define test-omit-paths 'all)

;; Negative fixtures must remain uncompiled so their diagnostics reach the harness.
(define compile-omit-paths
  '(
    "name_alias_bad.rhm"
    "notation_associativity_bad.rhm"
    "notation_duplicate_operand_bad.rhm"
    "notation_empty_bad.rhm"
    "notation_implementation_bad.rhm"
    "notation_infix_postfix_bad.rhm"
    "notation_late_case_option_bad.rhm"
    "notation_pattern_partial_bad.rhm"
    "notation_pattern_unreachable_bad.rhm"
    "notation_result_type_bad.rhm"
    "notation_static_result_bad.rhm"
    "notation_unsafe_bad.rhm"
    "notation_runtime_bad.rhm"
    "operator_bad.rhm"
    "operator_comparison_chain_bad.rhm"
    "operator_equality_chain_bad.rhm"
    "operator_plain_logic_bad.rhm"
    ))
