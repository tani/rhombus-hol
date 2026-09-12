#lang racket/base

(require racket/runtime-path)

(define-runtime-path tests-dir ".")

;; These modules are pure unit tests: none instantiates negative fixtures or
;; depends on state left by another test module. Loading them together shares
;; the expensive HOL dependencies while preserving separate processes for the
;; fixture and integration tests in this collection.
(for ([name (in-list '("htype.rhm"
                       "term.rhm"
                       "tyunify.rhm"
                       "order.rhm"
                       "conv.rhm"
                       "drule.rhm"
                       "ruledb.rhm"
                       "terminate.rhm"))])
  (dynamic-require `(file ,(path->string (build-path tests-dir name))) #f))
