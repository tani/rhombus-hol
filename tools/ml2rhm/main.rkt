#lang racket/base
;; ml2rhm: translate HOL Light's OCaml sources to Rhombus in the style of
;; rhombus/hol.
;;
;;   racket tools/ml2rhm/main.rkt [--out DIR] HOL-LIGHT-DIR [FILE.ml ...]
;;
;; Without FILE arguments every .ml file of the checkout is translated. Each
;; file is resolved against the modules HOL Light loads before it: the core
;; sequence of hol_lib.ml, then the file's `needs` closure. A free name
;; imports from the latest earlier module that defines it, as an `only:`
;; list; names no HOL Light module defines come from private/ocaml.rhm.
(require racket/cmdline
         racket/list
         racket/string
         racket/path
         racket/file
         racket/match
         "grammar.rkt"
         "emit.rkt"
         "ast.rkt")

(define out-dir (make-parameter "ml2rhm-out"))
(define private-prefix (make-parameter "private/"))

(define-values (hol files)
  (command-line
   #:once-each
   [("--out") dir "output directory (default ml2rhm-out)" (out-dir dir)]
   [("--private") prefix "path of rhombus/hol/private relative to the output root"
                  (private-prefix prefix)]
   #:args (hol-dir . files) (values (simplify-path (path->complete-path hol-dir)) files)))

(define (rel->path rel) (build-path hol rel))

;; ------------------------------------------------------------- parsing cache
(define parsed (make-hash))  ; rel -> (list items comments) or #f
(define (parse rel)
  (hash-ref! parsed rel
             (lambda ()
               (with-handlers ([exn:fail? (lambda (e) (cons 'error (exn-message e)))])
                 (define-values (items comments jrh?) (parse-ml-file (rel->path rel)))
                 (list items comments)))))
(define (ok? p) (and (pair? p) (not (eq? (car p) 'error))))

;; --------------------------------------------------------------- load order
(define core
  (for/list ([m (regexp-match* #rx"(?:loads|loadt|needs) \"([^\"]+)\""
                               (file->string (rel->path "hol_lib.ml")) #:match-select cadr)])
    m))

(define (needs-of rel)
  (define p (parse rel))
  (if (ok? p)
      (for*/list ([it (car p)]
                  #:when (t:expr? it)
                  [s (in-value (needs-string (t:expr-e it)))]
                  #:when s)
        s)
      '()))
(define (needs-string e)
  (match e
    [(e:app (e:var (or "needs" "loads" "loadt")) (list (e:const 'string s))) s]
    [_ #f]))

;; modules loaded before rel, in order
(define (prior rel)
  (cond
    [(member rel core) (takef core (lambda (m) (not (equal? m rel))))]
    [else
     (define seen (make-hash))
     (define order '())
     (let visit ([m rel])
       (unless (or (hash-ref seen m #f) (member m core))
         (hash-set! seen m #t)
         (for ([n (needs-of m)]) (when (file-exists? (rel->path n)) (visit n)))
         (unless (equal? m rel) (set! order (cons m order)))))
     (append core (reverse order))]))

;; names a module defines: values, constructors, exceptions, records, modules
(define defs-cache (make-hash))
(define (module-defs rel)
  (hash-ref! defs-cache rel
             (lambda ()
               (define p (parse rel))
               (if (ok? p)
                   (let* ([items (flatten-includes (car p))]
                          [names (append (defined-names items) (type-names items))])
                     (list->set* (append names
                                         (for/list ([n names] #:when (hash-ref operator-aliases n #f))
                                           (hash-ref operator-aliases n)))))
                   (hash)))))
(define (list->set* l) (for/hash ([x l]) (values x #t)))
(define (type-names items)
  (append*
   (for/list ([it items])
     (match it
       [(t:type _ decls)
        (append*
         (for/list ([d decls])
           (match (tydecl-kind d)
             [(list 'variant ctors) (map car ctors)]
             [(list 'record _) '()]
             [_ '()])))]
       [(t:exception _ n _) (list n)]
       [(t:module _ n _ _) (list n)]
       [_ '()]))))

(define (camel s)
  (string-append*
   (for/list ([w (string-split s "_")] #:unless (string=? w ""))
     (string-append (string-upcase (substring w 0 1)) (substring w 1)))))

(define (module-alias rel)
  (camel (path->string (path-replace-extension (file-name-from-path rel) #""))))

;; where the port keeps a module that is not at the mirrored path
(define port-layout
  (hash "preterm.ml" "private/type_inference.rhm"
        "printer.ml" "private/theory_support.rhm"))

(define (rhm-of rel)
  (hash-ref port-layout rel
            (lambda () (path->string (path-replace-extension (string->path rel) #".rhm")))))

;; import path of target (a rel .ml or a private file) from the module rel
(define (import-path from target-rhm)
  (define from-dir (let-values ([(d n _) (split-path (string->path (rhm-of from)))])
                     (if (path? d) d (string->path "."))))
  (define rp (find-relative-path (simplify-path (path->complete-path from-dir (current-directory)))
                                 (simplify-path (path->complete-path target-rhm (current-directory)))))
  (path->string rp))

;; ----------------------------------------------------------------- translate
(define (translate rel)
  (define p (parse rel))
  (unless (ok? p) (error 'ml2rhm "~a: ~a" rel (cdr p)))
  (define items (car p))
  (define comments (cadr p))
  (define before (prior rel))
  (define own (module-defs rel))
  (define uses (make-hash))        ; module rel -> ordered names
  (define aliases (make-hash))     ; module rel -> alias
  (define stdlib '())
  (define (owner name)
    (for/first ([m (reverse before)] #:when (hash-ref (module-defs m) name #f)) m))
  (define (use! name)
    (define m (owner name))
    (cond
      [(not m) (unless (member name stdlib) (set! stdlib (append stdlib (list name))))]
      [(hash-ref own name #f) (hash-set! aliases m (module-alias m))]
      [else (hash-update! uses m (lambda (l) (if (member name l) l (append l (list name)))) '())]))
  (define (resolve name)
    (define m (owner name))
    (and m (hash-ref own name #f) (module-alias m)))
  (define line-starts
    (let ([t (file->string (rel->path rel))])
      (list->vector (cons 0 (for/list ([m (regexp-match-positions* #rx"\n" t)]) (cdr m))))))
  (define (line-of off)
    ;; binary search for the last line start <= off
    (let loop ([lo 0] [hi (sub1 (vector-length line-starts))])
      (if (>= lo hi) (add1 lo)
          (let ([mid (quotient (+ lo hi 1) 2)])
            (if (<= (vector-ref line-starts mid) off) (loop mid hi) (loop lo (sub1 mid)))))))
  (define e (env (regexp-replace* #rx"[^A-Za-z0-9_]" (path->string (path-replace-extension (file-name-from-path rel) #"")) "_")
                 resolve use! #f #f line-of
                 (let ([h (make-hash '(("Some" . 1) ("Failure" . 1) ("Not_found" . 0)
                                       ("Invalid_argument" . 1) ("None" . 0)))])
                   (for ([m (append before (list rel))])
                     (define pm (parse m))
                     (when (ok? pm)
                       (for ([(k v) (ctor-arities (flatten-includes (car pm)))]) (hash-set! h k v))))
                   h)))
  (define-values (lead body exports) (emit-module items comments e))
  (define text (string-join (append body) "\n"))
  (define quotes? (regexp-match? #rx"@hol[|][{]" text))
  (define decls? (regexp-match? #rx"(?m:^ *(variant|record) )" text))
  (define base-dir (let-values ([(d n _) (split-path (string->path (rhm-of rel)))]) (if (path? d) d #f)))
  (define (imp target-rel-rhm)
    ;; relative path from this module's directory
    (if base-dir
        (path->string (find-relative-path (simplify-path (path->complete-path base-dir "/r/"))
                                          (simplify-path (path->complete-path target-rel-rhm "/r/"))))
        target-rel-rhm))
  (define imports
    (append
     (for*/list ([m before] #:when (or (hash-ref uses m #f) (hash-ref aliases m #f))
                 [line (in-list
                        (append
                         (if (hash-ref uses m #f)
                             (list* (format "  ~s open:" (imp (rhm-of m)))
                                    "    only:"
                                    (for/list ([n (hash-ref uses m)])
                                      (string-append "      " (mangle-export n))))
                             '())
                         (if (hash-ref aliases m #f)
                             (list (format "  ~s as ~a" (imp (rhm-of m)) (hash-ref aliases m)))
                             '())))])
       line)
     (if (null? stdlib) '()
         (list* (format "  ~s open:" (imp (string-append (private-prefix) "ocaml.rhm")))
                "    only:"
                (for/list ([n stdlib]) (string-append "      " (mangle-export n)))))
     (if quotes? (list (format "  ~s open" (imp (string-append (private-prefix) "hol_quote.rhm")))) '())
     (if decls? (list (format "  ~s open" (imp (string-append (private-prefix) "declarations.rhm")))) '())))
  (define lines
    (append
     (list "#lang rhombus"
           (format "// Direct translation of the pinned HOL Light ~a, generated by tools/ml2rhm." rel)
           "")
     (if (null? lead) '() (append lead (list "")))
     (if (null? imports) '() (append (list "import:") imports (list "")))
     (if (null? exports) '() (append (list "export:") (for/list ([x exports]) (string-append "  " x)) (list "")))
     body
     (list "")))
  (define out (build-path (out-dir) (rhm-of rel)))
  (make-directory* (let-values ([(d n _) (split-path out)]) d))
  (call-with-output-file out #:exists 'truncate
    (lambda (o) (write-string (string-join lines "\n") o))))

(define (mangle-export n) (mangle-id n))

(define targets
  (if (null? files)
      (sort (for/list ([f (in-directory hol)]
                       #:when (regexp-match? #rx"[.]ml$" (path->string f))
                       #:unless (regexp-match? #rx"/pa_j/" (path->string f)))
              (path->string (find-relative-path hol f)))
            string<?)
      files))

(define failed
  (for/fold ([bad '()]) ([rel targets])
    (with-handlers ([exn:fail? (lambda (e)
                                 (eprintf "~a: ~a\n" rel (let ([m (exn-message e)]) (substring m 0 (min 300 (string-length m)))))
                                 (cons rel bad))])
      (translate rel)
      bad)))
(printf "translated ~a of ~a files into ~a\n" (- (length targets) (length failed)) (length targets) (out-dir))
