#lang racket/base
;; Forces real HOL verification of a #lang rhombus/hol file: instantiates its
;; `hol_theory` submodule, where the waterfall proof / kernel axiom admission
;; actually runs. `raco make` alone only type-checks a theorem's statement
;; and options (`frontend/checker`); it never instantiates the submodule, so
;; it silently accepts a theorem whose waterfall proof would fail -- see
;; rhombus-hol/rhombus/hol/tests/fixture_load.rhm's own comment on this exact
;; gotcha.
(require racket/cmdline)

(define path (command-line #:args (p) p))
(define full (path->complete-path path))

(with-handlers ([exn:fail?
                 (lambda (e)
                   (eprintf "THEORY-CHECK-FAILED: ~a\n~a\n"
                            full (exn-message e))
                   (exit 1))])
  (dynamic-require full #f)
  (dynamic-require (list 'submod full 'hol_theory) #f)
  (printf "THEORY-CHECK-OK: ~a\n" full))
