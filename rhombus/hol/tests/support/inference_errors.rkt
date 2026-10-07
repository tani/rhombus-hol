#lang racket/base
;; Expansion-only contracts: rejection must happen before any quoted term
;; or proof is run. One fresh namespace isolates the suite while sharing
;; the macro frontend across cases; every quotation has its own inference state.
(require racket/port)
(provide rejects-invalid-quotations?)
(define cases
  (list (cons "hol: fun (x): x(x)" #rx"infinite type")
        (cons "hol: var p :: bool; p((1 :: num))" #rx"incompatible types")
        (cons "hol: var x :: A; x == #true" #rx"incompatible types")
        (cons "hol: fun (x): x + x" #rx"ambiguous")
        (cons "hol: 1" #rx"numeral needs a type")))
(define (rejects-invalid-quotations?)
  (parameterize ([current-namespace (make-base-namespace)]
                 [read-accept-reader #t])
    (for/and ([case (in-list cases)])
      (define source
        (string-append "#lang rhombus\nimport: lib(\"rhombus/hol/private/hol_quote.rhm\") open\n"
                       (car case) "\n"))
      (with-handlers ([exn:fail:syntax?
                       (lambda (exn) (and (regexp-match? (cdr case) (exn-message exn)) #t))])
        (expand (read-syntax 'inference-rejection (open-input-string source)))
        #f))))
