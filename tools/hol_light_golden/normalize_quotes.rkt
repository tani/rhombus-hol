#lang racket/base
;; One-time source migration. Shrubbery source locations keep replacements
;; inside each quotation; host bindings and comments are never renamed.
(require shrubbery/parse racket/file racket/list racket/match racket/port
         racket/string file/gunzip
         "../../rhombus/hol/tests/support/reference.rkt")

(define (identifier name)
  (if (regexp-match? #px"^[A-Za-z_][A-Za-z0-9_]*$" name)
      (if (member name '("var" "const" "fun" "if" "forall" "exists" "exists1" "as" "_"))
          (format "#{~s}" (string->symbol name)) name)
      (format "#{~s}" (string->symbol name))))
(define (type-source t)
  (match t
    [(list "V" name) (identifier name)]
    [(list "T" "fun" (list a b))
     (string-append (if (match a [(list "T" "fun" _) #t] [_ #f])
                       (string-append "(" (type-source a) ")") (type-source a))
                    " -> " (type-source b))]
    [(list "T" name args)
     (define n (if (equal? name "prod") "pair" name))
     (if (null? args) n
         (string-append n "(" (string-join (map type-source args) ", ") ")"))]))

(define (children stx) (or (syntax->list stx) '()))
(define (tag stx) (and (pair? (children stx)) (syntax-e (car (children stx)))))
(define (parts stx) (cdr (children stx)))
(define (atom-name stx)
  (define x (syntax-e stx))
  (cond [(symbol? x) (symbol->string x)] [(string? x) x] [else #f]))
(define (locations stx)
  (append (if (syntax-position stx)
              (list (cons (sub1 (syntax-position stx))
                          (+ (sub1 (syntax-position stx)) (or (syntax-span stx) 0)))) '())
          (append-map locations (children stx))))
(define (position stx) (apply min (map car (locations stx))))
(define (end stx) (apply max (map cdr (locations stx))))
(define (op? stx name) (equal? (syntax->datum stx) `(op ,name)))

;; Escaping an identifier does not remove a binding to a term macro. These
;; names still need an explicit declaration reference; other symbolic names
;; can use the ordinary identifier parser.
(define term-macro-names
  '("var" "const" "fun" "if" "forall" "exists" "exists1"
    "&&" "||" "==>" "<=>" "==" "!=" "!" "+" "-" "*" "/"
    "<" "<=" ">" ">=" "::" "#%call" "#%parens" "#%literal"))
(struct declaration (kind target name) #:transparent)
(struct binder (id name [replacement #:mutable]) #:transparent)
(struct reference (start finish destination scope) #:transparent)

(define schemas
  (let ([out (open-output-bytes)])
    (call-with-input-file "rhombus/hol/tests/golden/hol_light.tsv.gz"
      (lambda (in) (gunzip-through-ports in out)))
    (for/hash ([line (in-list (port->lines (open-input-bytes (get-output-bytes out))))]
               #:when (string-prefix? line "const\t"))
      (define fields (string-split line "\t"))
      (values (cadr fields) (type-source (decode-reference (caddr fields)))))))

(define total 0)
(define renamed-binders 0)
(define paths
  (if (zero? (vector-length (current-command-line-arguments)))
      (find-files (lambda (p) (regexp-match? #rx"[.]rhm$" (path->string p))) "rhombus/hol")
      (map string->path (vector->list (current-command-line-arguments)))))
(for ([path (in-list paths)]
      ;; The native frontend's hand-written tests intentionally exercise
      ;; qualified references beneath shadowing binders.
      #:unless (or (regexp-match? #rx"/private/" (path->string path))
                   (and (zero? (vector-length (current-command-line-arguments)))
                        (equal? (path->string path) "rhombus/hol/tests/hol_quote.rhm"))))
  (define text (file->string path))
  (define in (open-input-string text))
  (port-count-lines! in)
  (read-line in) ; #lang, retaining absolute source positions
  (define tree (parse-all in #:source path))
  (define edits '())
  (define (edit a b replacement)
    (unless (equal? (substring text a b) replacement)
      (set! edits (cons (list a b replacement) edits))))
  (define (replace-token stx replacement) (edit (position stx) (end stx) replacement))
  (define (quote-block block)
    (define groups (parts block))
    (define declarations (drop-right groups 1))
    (define names (make-hash))
    (define qualified-names (make-hash))
    (define seen-constants (make-hash))
    (define var-counts (make-hash))
    (for ([g (in-list declarations)])
      (define xs (parts g))
      (when (eq? (syntax-e (car xs)) 'var)
        (define alias? (and (>= (length xs) 4) (eq? (syntax-e (caddr xs)) 'as)))
        (define name (atom-name (if alias? (cadddr xs) (cadr xs))))
        (hash-update! var-counts name add1 0)))
    (for ([g (in-list declarations)] [i (in-naturals)])
      (define xs (parts g))
      (define kind (syntax-e (car xs)))
      (define id (cadr xs))
      (define old (syntax-e id))
      (define alias? (and (>= (length xs) 4) (eq? (syntax-e (caddr xs)) 'as)))
      (define kernel-name (atom-name (if alias? (cadddr xs) id)))
      (define colon (for/first ([x (in-list xs)] #:when (op? x '::)) x))
      (define rename?
        (and alias? (not (regexp-match? #px"\\s" kernel-name))
             (or (eq? kind 'const) (= (hash-ref var-counts kernel-name 0) 1))))
      (define target (if rename? (identifier kernel-name) (substring text (position id) (end id))))
      (define target-name (if rename? kernel-name (atom-name id)))
      (define d (declaration kind target target-name))
      (hash-set! qualified-names (list kind old) d)
      ;; Match quotation elaboration: a free variable takes precedence over a
      ;; constant with the same surface name, regardless of declaration order.
      (when (or (eq? kind 'var) (not (hash-has-key? names old)))
        (hash-set! names old d))
      (cond
        [(and (eq? kind 'const) (hash-has-key? seen-constants kernel-name))
         (edit (position g) (position (list-ref groups (add1 i))) "")]
        [else
         (when (eq? kind 'const) (hash-set! seen-constants kernel-name #t))
         (when rename?
           (replace-token id target)
           (edit (end id) (position colon) " "))
         (when (and (eq? kind 'const) (hash-has-key? schemas kernel-name))
           (edit (end colon) (end g) (string-append " " (hash-ref schemas kernel-name))))]))
    (define declared-vars
      (for/list ([d (in-hash-values qualified-names)] #:when (eq? (declaration-kind d) 'var))
        (declaration-name d)))
    (define (qualified? d)
      (or (member (declaration-name d) term-macro-names)
          (and (eq? (declaration-kind d) 'const)
               (member (declaration-name d) declared-vars))))
    (define binders '())
    (define references '())
    (define used-names (make-hash))
    (define (reserve stx)
      (when (symbol? (syntax-e stx))
        (hash-set! used-names (symbol->string (syntax-e stx)) #t))
      (for-each reserve (children stx)))
    (reserve block)
    (for ([d (in-hash-values qualified-names)])
      (hash-set! used-names (declaration-name d) #t))
    (define (record-reference a b destination scope)
      (when destination
        (set! references (cons (reference (position a) (end b) destination scope) references))))
    ;; Resolve every original occurrence before scheduling any edits. In
    ;; particular, a qualified reference bypasses lexical binders, while a
    ;; plain reference follows the original innermost binding.
    (define (resolve stx scope)
      (cond
        [(null? (children stx))
         (define old (syntax-e stx))
         (when (symbol? old)
           (define bound (findf (lambda (b) (eq? old (binder-name b))) scope))
           (record-reference stx stx (or bound (hash-ref names old #f)) scope))]
        [(eq? (tag stx) 'group)
         (define xs (parts stx))
         (define binder-index
           (for/first ([x (in-list xs)] [i (in-naturals)]
                        #:when (and (memq (syntax-e x) '(fun forall exists exists1))
                                    ;; An escaped/qualified declaration with a
                                    ;; keyword name is not a binding form.
                                    (equal? (substring text (position x) (end x))
                                            (symbol->string (syntax-e x)))
                                    (or (zero? i) (not (op? (list-ref xs (sub1 i)) '|.|)))
                                    (< (+ i 1) (length xs))
                                    (ormap (lambda (term) (eq? (tag term) 'block))
                                           (drop xs (+ i 2))))) i))
         (define colon-index (index-where xs (lambda (x) (op? x '::))))
         (cond
           [binder-index
            (define binding (list-ref xs (add1 binder-index)))
            (define ids
              (if (eq? (tag binding) 'parens)
                  (for/list ([g (in-list (parts binding))]) (car (parts g)))
                  (list binding)))
            (define bound (for/list ([id (in-list ids)]) (binder id (syntax-e id) #f)))
            (set! binders (append bound binders))
            (for ([x (in-list (take xs binder-index))]) (resolve x scope))
            (for ([x (in-list (drop xs (add1 binder-index)))] #:when (eq? (tag x) 'block))
              (resolve x (append (reverse bound) scope)))]
           [else
            (let loop ([remaining (if colon-index (take xs colon-index) xs)])
              (cond
                [(null? remaining) (void)]
                [(and (>= (length remaining) 3)
                      (memq (syntax-e (car remaining)) '(var const))
                      (op? (cadr remaining) '|.|))
                 (define key (list (syntax-e (car remaining)) (syntax-e (caddr remaining))))
                 (define d (hash-ref qualified-names key
                                     (lambda () (error 'normalize "undeclared reference ~a in ~a" key path))))
                 (record-reference (car remaining) (caddr remaining) d scope)
                 (loop (cdddr remaining))]
                [else (resolve (car remaining) scope) (loop (cdr remaining))]))])]
        [(eq? (tag stx) 'op) (void)]
        [else (for ([x (in-list (parts stx))]) (resolve x scope))]))
    (resolve (last groups) '())
    (define (fresh-name base)
      (let loop ([i 2])
        (define name (format "~a_~a" base i))
        (if (hash-has-key? used-names name) (loop (add1 i))
            (begin (hash-set! used-names name #t) (identifier name)))))
    ;; Only rename binders that would capture a declaration reference after
    ;; removing its qualifier (or after resolving an old declaration alias).
    ;; Reserve all existing names, including names used in nested binders.
    (for ([ref (in-list (reverse references))]
          #:when (declaration? (reference-destination ref)))
      (define d (reference-destination ref))
      (unless (qualified? d)
        (for ([b (in-list (reference-scope ref))]
              #:when (and (equal? (symbol->string (binder-name b)) (declaration-name d))
                          (not (binder-replacement b))))
          (set-binder-replacement! b (fresh-name (binder-name b)))
          (set! renamed-binders (add1 renamed-binders)))))
    (for ([b (in-list binders)] #:when (binder-replacement b))
      (replace-token (binder-id b) (binder-replacement b)))
    (for ([ref (in-list references)])
      (define destination (reference-destination ref))
      (define replacement
        (cond [(binder? destination) (binder-replacement destination)]
              [(qualified? destination)
               (format "~a.~a" (declaration-kind destination) (declaration-target destination))]
              [else (declaration-target destination)]))
      (when replacement (edit (reference-start ref) (reference-finish ref) replacement))))
  (define (walk stx)
    (define xs (children stx))
    (when (pair? xs)
      (define blocks
        (if (eq? (tag stx) 'group)
            (for/list ([a (in-list xs)] [b (in-list (cdr xs))]
                       #:when (and (eq? (syntax-e a) 'hol) (eq? (tag b) 'block)))
              b) '()))
      (for ([b (in-list blocks)]) (quote-block b))
      (for ([x (in-list (cdr xs))] #:unless (memq x blocks)) (walk x))))
  (walk tree)
  (unless (null? edits)
    (define result text)
    (define previous (string-length text))
    (for ([change (in-list (sort edits > #:key car))])
      (match-define (list a b replacement) change)
      (when (> b previous) (error 'normalize "overlapping edits in ~a" path))
      (set! previous a)
      (set! result (string-append (substring result 0 a) replacement (substring result b))))
    (display-to-file result path #:exists 'truncate)
    (set! total (+ total (length edits)))))
(printf "Normalized ~a quotation source spans; renamed ~a shadowing binders.\n" total renamed-binders)
