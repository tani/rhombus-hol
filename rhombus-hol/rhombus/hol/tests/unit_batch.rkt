#lang racket/base

(require racket/runtime-path)

(define-runtime-path tests-dir ".")

;; These modules are pure unit tests: none instantiates negative fixtures or
;; depends on state left by another test module. Loading them together shares
;; the expensive HOL dependencies while preserving separate processes for the
;; fixture and integration tests in this collection.
(for ([name (in-list '("kernel/type.rhm"
                       "kernel/term.rhm"
                       "logic/tyunify.rhm"
                       "logic/order.rhm"
                       "logic/conv.rhm"
                       "logic/drule.rhm"
                       "prover/rules/ruledb.rhm"
                       "definition/function/terminate.rhm"))])
  (dynamic-require `(file ,(path->string (build-path tests-dir name))) #f))
