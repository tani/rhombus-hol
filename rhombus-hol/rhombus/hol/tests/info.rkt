#lang info

(define module-suffixes '(#"rhm"))

;; Run these pure unit modules through unit_batch.rkt. Every other test keeps
;; its own process, notably modules that instantiate fixtures expected to fail.
(define test-omit-paths
  '("fixture_load.rhm"
    "htype.rhm"
    "term.rhm"
    "tyunify.rhm"
    "order.rhm"
    "conv.rhm"
    "drule.rhm"
    "ruledb.rhm"
    "terminate.rhm"))

