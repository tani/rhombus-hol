#lang info

(define module-suffixes '(#"rhm"))
;; These are inputs to tests, not tests: some of them are *meant* not to
;; compile, so `raco test` must not try to run them.
(define test-omit-paths 'all)
