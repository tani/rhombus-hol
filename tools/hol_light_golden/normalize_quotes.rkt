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

(define schemas
  (let ([out (open-output-bytes)])
    (call-with-input-file "rhombus/hol/tests/golden/hol_light.tsv.gz"
      (lambda (in) (gunzip-through-ports in out)))
    (for/hash ([line (in-list (port->lines (open-input-bytes (get-output-bytes out))))]
               #:when (string-prefix? line "const\t"))
      (define fields (string-split line "\t"))
      (values (cadr fields) (type-source (decode-reference (caddr fields)))))))

(define total 0)
(for ([path (in-list (find-files (lambda (p) (regexp-match? #rx"[.]rhm$" (path->string p))) "rhombus/hol"))]
      #:unless (regexp-match? #rx"/private/" (path->string path)))
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
      (hash-set! names old (list kind target target-name))
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
      (for/list ([value (in-hash-values names)] #:when (eq? (car value) 'var)) (caddr value)))
    (define (rewrite stx scope)
      (cond
        [(null? (children stx))
         (define old (syntax-e stx))
         (when (and (symbol? old) (hash-has-key? names old) (not (member old scope)))
           (match-define (list kind target target-name) (hash-ref names old))
           (define qualified?
             (or (member (string->symbol target-name) scope)
                 (and (eq? kind 'const) (member target-name declared-vars))
                 (not (regexp-match? #px"^[A-Za-z_][A-Za-z0-9_]*$" target-name))
                 (member target-name '("var" "const" "fun" "if" "forall" "exists" "exists1" "as" "_"))))
           (replace-token stx (if qualified? (format "~a.~a" kind target) target)))]
        [(eq? (tag stx) 'group)
         (define xs (parts stx))
         (define binder-index
           (for/first ([x (in-list xs)] [i (in-naturals)]
                        #:when (memq (syntax-e x) '(fun forall exists exists1))) i))
         (define colon-index (index-where xs (lambda (x) (op? x '::))))
         (cond
           [binder-index
            (define binding (list-ref xs (add1 binder-index)))
            (define bound
              (if (eq? (tag binding) 'parens)
                  (for/list ([g (in-list (parts binding))]) (syntax-e (car (parts g))))
                  (list (syntax-e binding))))
            (for ([x (in-list (take xs binder-index))]) (rewrite x scope))
            (for ([x (in-list (drop xs (add1 binder-index)))] #:when (eq? (tag x) 'block))
              (rewrite x (append bound scope)))]
           [else
            (define qualified-indices
              (append-map
               (lambda (i)
                 (if (and (< (+ i 2) (length xs))
                          (memq (syntax-e (list-ref xs i)) '(var const))
                          (op? (list-ref xs (add1 i)) '|.|))
                     (list i (add1 i) (+ i 2)) '()))
               (range (length xs))))
            (for ([x (in-list (if colon-index (take xs colon-index) xs))] [i (in-naturals)]
                  #:unless (member i qualified-indices)) (rewrite x scope))])]
        [(eq? (tag stx) 'op) (void)]
        [else (for ([x (in-list (parts stx))]) (rewrite x scope))]))
    (rewrite (last groups) '()))
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
(printf "Normalized ~a quotation source spans.\n" total)
