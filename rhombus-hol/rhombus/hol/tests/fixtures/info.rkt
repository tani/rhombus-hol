#lang info

(define module-suffixes '(#"rhm"))
;; These are inputs to tests, not tests: some of them are *meant* not to
;; compile, so `raco test` must not try to run them.
(define test-omit-paths 'all)
;; ... and `raco setup` must not try to build them either, for the same
;; reason: a fixture that is supposed to be refused would otherwise report
;; its refusal as a package build error.  The tests that use the positive
;; fixtures `import` them, so those still get compiled -- on demand, by the
;; test that needs them.
(define compile-omit-paths 'all)
