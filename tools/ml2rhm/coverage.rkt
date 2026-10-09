#lang racket/base
;; racket tools/ml2rhm/coverage.rkt HOL-LIGHT-DIR [EXPECTED]
;; Parses every .ml file of a HOL Light checkout and reports the failures;
;; exits non-zero when fewer than EXPECTED files parse.
(require racket/path racket/list "grammar.rkt")
(define args (current-command-line-arguments))
(define dir (vector-ref args 0))
(define expected (and (> (vector-length args) 1) (string->number (vector-ref args 1))))
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
(when (and expected (< (- (length files) (length failures)) expected))
  (exit 1))
