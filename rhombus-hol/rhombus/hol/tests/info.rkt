#lang info

(define module-suffixes '(#"rhm"))

;; `idris_kernel_gen.rkt` is byte-for-byte what `idris2 --cg racket` emits,
;; checked in so `raco make` need not run `idris2`.  It is data for
;; `idris_kernel.rkt`, which reads and transforms it at expansion time -- not
;; a test.  Running it directly would execute the Idris smoke test's `main`,
;; which is what the generated file does on load.
(define test-omit-paths '("idris_kernel_gen.rkt"))
