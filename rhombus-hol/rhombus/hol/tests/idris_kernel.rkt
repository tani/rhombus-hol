#lang racket/base
;; Turn idris2's Racket-backend output into a `require`-able library, at
;; expansion time, without editing the generated file.
;;
;; `idris_kernel_gen.rkt` is exactly what `idris2 --cg racket` emits -- byte
;; for byte, no post-processing.  It is not a library: its whole body sits
;; inside one anonymous `(let () ...)`, so `require`ing it sees nothing, and
;; loading it runs `Main-main` as a side effect.
;;
;; This module reads that file *as syntax* and splices the transformed body
;; in here, so `raco make` byte-compiles the result and there is nothing to
;; pay at load time.  Working on syntax rather than text is the point: a
;; regex over generated source cannot tell an application of `vector` from
;; the same characters inside a string literal, and cannot fail loudly when
;; the shape it assumed is gone.  Every assumption below is checked, and a
;; codegen change that breaks one is an error at compile time naming what it
;; expected.
;;
;; Three transformations:
;;
;;   1. Unwrap the `(let () ...)`, so the definitions become module-level
;;      and `(provide (all-defined-out))` can export them.
;;   2. Drop the `(void (PrimIO-unsafePerformIO Main-main))` that runs the
;;      smoke test, and the trailing `(collect-garbage)`.  A library has no
;;      business doing either on require.
;;   3. Rewrite applications of `vector` to `vector-immutable`.
;;
;; (3) is what lets Rhombus treat these values directly rather than
;; decoding them: Rhombus `==` on a *mutable* vector is identity, and terms
;; are locally nameless, so `==` is alpha-equivalence and getting identity
;; there would be unsound.  Immutable vectors compare structurally and work
;; as `Map` keys.  It is safe because the generated module never mutates a
;; vector -- checked below rather than assumed -- and its failure mode is
;; loud: `vector-set!` on an immutable vector raises.

(require (for-syntax racket/base
                     racket/list
                     syntax/modread
                     compiler/cm-accomplice))

(provide (all-defined-out))

(define-syntax (include-idris-kernel stx)
  (syntax-case stx ()
    [(_ rel-path)
     (let* ([src (syntax-source stx)]
            [dir (if (path? src)
                     (let-values ([(base _name _dir?) (split-path src)]) base)
                     (current-directory))]
            [path (build-path dir (syntax-e #'rel-path))])
       ;; Make `raco make` rebuild this module when the generated file
       ;; changes; without it a fresh `idris2` build would be ignored.
       (register-external-file path)
       ;; Read with Racket's own reader -- the parse is the reader's, not a
       ;; regex's -- then work on the s-expressions.  The syntax objects the
       ;; reader produces carry the generated module's own scopes, in which
       ;; `require` and friends are unbound here, so the forms are given this
       ;; module's context on the way out.
       (define module-datum
         (syntax->datum
          (with-module-reading-parameterization
            (lambda ()
              (call-with-input-file path
                (lambda (in)
                  (port-count-lines! in)
                  (read-syntax path in)))))))
       (define body
         (match-module module-datum path))
       ;; Assumption 1: exactly one top-level `(let () ...)` holds everything.
       (define (let-form? f)
         (and (pair? f) (eq? 'let (car f)) (pair? (cdr f)) (null? (cadr f))))
       (define-values (lets others) (partition let-form? body))
       (unless (= 1 (length lets))
         (raise-syntax-error 'include-idris-kernel
                             (format "expected exactly one top-level `(let () ...)`, found ~a"
                                     (length lets))
                             stx))
       ;; Assumption 2: nothing outside it but `require`s and a trailing
       ;; `(collect-garbage)`.
       (define kept-others
         (for/list ([f (in-list others)]
                    #:unless (and (pair? f) (eq? 'collect-garbage (car f))))
           (unless (and (pair? f) (eq? 'require (car f)))
             (raise-syntax-error 'include-idris-kernel
                                 (format "unexpected top-level form outside the `let`: ~s" f)
                                 stx))
           f))
       (define inner (cddr (car lets)))
       ;; Assumption 3: the `let` ends by forcing `Main-main`.
       (define (main-forcer? f)
         (and (pair? f) (eq? 'void (car f))
              (pair? (cdr f)) (pair? (cadr f))
              (eq? 'PrimIO-unsafePerformIO (car (cadr f)))))
       (unless (ormap main-forcer? inner)
         (raise-syntax-error 'include-idris-kernel
                             "expected a `(void (PrimIO-unsafePerformIO ...))` to drop"
                             stx))
       (define defs (filter (lambda (f) (not (main-forcer? f))) inner))
       ;; Assumption 4, the one that licenses the rewrite: every vector in
       ;; this module is born from a `(vector ...)` application, and none is
       ;; ever mutated.  Checked as an allowlist rather than a blocklist of
       ;; mutators -- a blocklist would pass `list->vector`, whose result is
       ;; mutable and would then never be `==` to anything, silently.  So:
       ;; any symbol naming a vector operation must be one of the readers
       ;; below, and bare `vector` must appear only in head position.
       ;; `bytevector` names are a different type and are not vectors.
       (define vector-readers
         '(vector-ref vector-length vector? vector->list
           blodwen-vector-ref blodwen-vector-length blodwen-vector-list
           blodwen-is-vector))
       (define (vector-name? sym)
         (let ([str (symbol->string sym)])
           (and (regexp-match? #rx"vector" str)
                (not (regexp-match? #rx"bytevector" str)))))
       (let scan ([d defs] [head? #f])
         (cond
           [(pair? d)
            ;; `(car d)` is in head position; the arguments are not.
            (let ([h (car d)])
              (when (and (symbol? h) (vector-name? h))
                (unless (or (eq? h 'vector) (memq h vector-readers))
                  (raise-syntax-error
                   'include-idris-kernel
                   (format "generated code uses `~a`; only `(vector ...)` may build a vector here, so the immutable rewrite is not safe"
                           h)
                   stx)))
              (unless (symbol? h) (scan h #t)))
            (for-each (lambda (x) (scan x #f)) (cdr d))]
           [(symbol? d)
            ;; A vector name outside head position is either a mutation or a
            ;; higher-order use the rewrite would miss.
            (when (vector-name? d)
              (unless (memq d vector-readers)
                (raise-syntax-error
                 'include-idris-kernel
                 (format "generated code mentions `~a` outside application position; the immutable rewrite would miss it"
                         d)
                 stx)))]
           [else (void)]))
       ;; The rewrite: only `vector` in application head position.
       (define (rewrite f)
         (cond
           [(pair? f)
            (cons (if (eq? 'vector (car f)) 'vector-immutable (rewrite (car f)))
                  (let loop ([rest (cdr f)])
                    (cond
                      [(pair? rest) (cons (rewrite (car rest)) (loop (cdr rest)))]
                      [else rest])))]
           [else f]))
       (datum->syntax stx (cons 'begin (append kept-others (map rewrite defs)))))]))

(begin-for-syntax
  ;; The reader hands back `(module <name> <lang> (#%module-begin form ...))`
  ;; or `(module <name> <lang> form ...)`, depending on the language.
  (define (match-module m path)
    (unless (and (pair? m) (eq? 'module (car m)) (>= (length m) 4))
      (error 'include-idris-kernel "~a: not a module form" path))
    (let ([forms (cdddr m)])
      (if (and (= 1 (length forms))
               (pair? (car forms))
               (eq? '#%module-begin (caar forms)))
          (cdar forms)
          forms))))

(include-idris-kernel "idris_kernel_gen.rkt")
