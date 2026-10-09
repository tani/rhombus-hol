#lang racket/base
;; racket tools/ml2rhm/coverage.rkt HOL-LIGHT-DIR
;; Parses every .ml file of a HOL Light checkout and reports the failures.
(require racket/path racket/list "grammar.rkt")
(define dir (vector-ref (current-command-line-arguments) 0))
(define files
  (sort (for/list ([f (in-directory dir)]
                   #:when (regexp-match? #rx"[.]ml$" (path->string f))
                   ;; camlp5's own sources, in revised syntax, not HOL Light code
                   #:unless (regexp-match? #rx"/pa_j/" (path->string f)))
          f)
        string<? #:key path->string))
(define failures
  (for/fold ([bad '()]) ([f files])
    (with-handlers ([exn:fail? (lambda (e) (cons (cons f (exn-message e)) bad))])
      (parse-ml-file f)
      bad)))
(for ([b (reverse failures)])
  (printf "~a: ~a\n" (find-relative-path (simple-form-path dir) (simple-form-path (car b)))
          (let ([m (cdr b)]) (substring m 0 (min 160 (string-length m))))))
(printf "parsed ~a of ~a files\n" (- (length files) (length failures)) (length files))
