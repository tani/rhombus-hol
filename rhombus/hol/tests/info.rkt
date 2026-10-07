#lang info

(define module-suffixes '(#"rhm"))

;; Runners are invoked explicitly; support modules are not standalone suites.
;; The standard theories and examples belong to the separate `theories` job.
(define test-omit-paths '("golden" "upstream" "support" "all.rhm" "fast.rhm" "axioms.rhm"))
