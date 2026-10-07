#lang racket/base
;; Historical HOL Light snapshots are data, never kernel theorems. Parse
;; their encoding once per comparison and match typed trees, not regexes.
(require racket/list racket/match)
(provide reference-equivalent? decode-reference)

(define (decode text)
  (define in (open-input-string text))
  (define (take expected)
    (unless (equal? (read-char in) expected)
      (error 'reference "malformed encoding: ~s" text)))
  (define (name)
    (define value (read in))
    (unless (string? value) (error 'reference "expected a quoted name"))
    value)
  (define (type)
    (case (read-char in)
      [(#\V) (list "V" (name))]
      [(#\T)
       (define n (name))
       (take #\()
       (define args
         (if (equal? (peek-char in) #\)) '()
             (let loop ()
               (define t (type))
               (if (equal? (peek-char in) #\,)
                   (begin (read-char in) (cons t (loop))) (list t)))))
       (take #\))
       (list "T" n args)]
      [else (error 'reference "expected a type")]))
  (define (term)
    (case (peek-char in)
      [(#\v #\c)
       (define tag (string (read-char in)))
       (define n (name))
       (take #\:)
       (list tag n (type))]
      [(#\()
       (read-char in)
       (define f (term))
       (take #\space)
       (define x (term))
       (take #\))
       (list "app" f x)]
      [(#\\)
       (read-char in)
       (define v (term))
       (take #\.)
       (list "abs" v (term))]
      [else (error 'reference "expected a term")]))
  (define result
    (case (peek-char in)
      [(#\V #\T) (type)]
      [(#\[)
       (read-char in)
       (define hyps
         (if (equal? (peek-char in) #\]) '()
             (let loop ()
               (define h (term))
               (if (equal? (peek-char in) #\;)
                   (begin (read-char in) (cons h (loop))) (list h)))))
       (take #\]) (take #\|) (take #\-)
       (list "thm" hyps (term))]
      [else (term)]))
  (unless (eof-object? (peek-char in)) (error 'reference "trailing data"))
  result)

(define decode-reference decode)

;; Each namespace has its own injective name correspondence. In particular,
;; a type variable, free term variable and generated constant never share
;; an entry merely because their printed names coincide.
(define (bind-name state kind left right)
  (define l (list 'left kind left))
  (define r (list 'right kind right))
  (cond
    [(hash-has-key? state l) (and (equal? (hash-ref state l) right) state)]
    [(hash-has-key? state r) #f]
    [else (hash-set (hash-set state l right) r left)]))

(define (generated? name)
  ;; _0 is the ordinary numeral constant, not a fresh name.
  (and (not (equal? name "_0")) (regexp-match? #px"^_[0-9]+$" name)))

(define (match-type left right state)
  (match* (left right)
    [((list "V" a) (list "V" b)) (bind-name state 'type a b)]
    [((list "T" a as) (list "T" b bs))
     (and (equal? a b) (= (length as) (length bs))
          (for/fold ([s state]) ([x (in-list as)] [y (in-list bs)])
            (and s (match-type x y s))))]
    [(_ _) #f]))

(define (bound-index v env)
  (for/first ([x (in-list env)] [i (in-naturals)] #:when (equal? x v)) i))

(define (match-term left right state [left-env '()] [right-env '()])
  (match* (left right)
    [((list "v" a at) (list "v" b bt))
     (define s (match-type at bt state))
     (define ai (bound-index left left-env))
     (define bi (bound-index right right-env))
     (and s
          (cond [(and ai bi) (and (= ai bi) s)]
                [(or ai bi) #f]
                [else (bind-name s 'free (list a at) (list b bt))]))]
    [((list "c" a at) (list "c" b bt))
     (define s (match-type at bt state))
     (and s (if (and (generated? a) (generated? b))
                (bind-name s 'constant a b)
                (and (equal? a b) s)))]
    [((list "app" af ax) (list "app" bf bx))
     (define s (match-term af bf state left-env right-env))
     (and s (match-term ax bx s left-env right-env))]
    [((list "abs" (and av (list "v" _ at)) ab)
      (list "abs" (and bv (list "v" _ bt)) bb))
     (define s (match-type at bt state))
     (and s (match-term ab bb s (cons av left-env) (cons bv right-env)))]
    [(_ _) #f]))

;; Hypotheses are a set. Trying permutations keeps the same variable/type
;; correspondence across the conclusion and every hypothesis.
(define (match-hypotheses left right state)
  (cond
    [(null? left) (and (null? right) state)]
    [else
     (for/or ([candidate (in-list right)] [i (in-naturals)])
       (define s (match-term (car left) candidate state))
       (and s (match-hypotheses (cdr left)
                                (append (take right i) (drop right (add1 i))) s)))]))

(define (reference-equivalent? left-text right-text)
  (define left (decode left-text))
  (define right (decode right-text))
  (and
   (match* (left right)
     [((list "thm" ah ac) (list "thm" bh bc))
      (define s (match-term ac bc (hash)))
      (and s (= (length ah) (length bh)) (match-hypotheses ah bh s))]
     [((list (or "V" "T") _ ...) (list (or "V" "T") _ ...))
      (match-type left right (hash))]
     [(_ _) (match-term left right (hash))])
   #t))
