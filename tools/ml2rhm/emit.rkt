#lang racket/base
;; Rhombus emitter in the style of rhombus/hol: curried `fun` definitions,
;; tuples as `[a, b]`, OCaml lists as `PairList`, references as `Box`,
;; `@hol|{...}|` quotations, tactic infixes (`then_tac`, `or_tac`, ...),
;; `match`/`try`/`if` alternatives and `_prime` for primed names.
(require racket/list
         racket/string
         racket/match
         "ast.rkt")
(provide emit-module
         format-api
         ctor-arities
         flatten-includes
         mangle-id
         operator-aliases
         (struct-out env)
         defined-names
         free-names)

(define WIDTH 92)

;; -------------------------------------------------------------------------
;; Documents: a rendered expression is a list of lines (relative
;; indentation) plus its syntactic kind, which decides parenthesisation:
;;   'atom   closed: names, literals, calls, brackets
;;   'op     binary operator expression with a precedence and a family
;;   'unary  !e, -e
;;   'open   fun, if, match, try, block:, throw (extends to the right)
;; -------------------------------------------------------------------------

(struct r (lines kind prec fam [chain #:auto #:mutable] [src-paren #:auto #:mutable]) #:transparent)
(define (r* lines kind prec fam chain)
  (define x (r lines kind prec fam))
  (set-r-chain! x chain)
  x)
(define (atom . lines) (r lines 'atom 99 #f))
(define (atom* lines) (r lines 'atom 99 #f))
(define (open* lines) (r lines 'open 0 #f))
(define (single? x) (= (length (r-lines x)) 1))
(define (line1 x) (car (r-lines x)))
(define (spaces n) (make-string n #\space))
(define (indent lines [n 2])
  (for/list ([l lines]) (if (string=? l "") l (string-append (spaces n) l))))
(define (fits? s) (<= (string-length s) WIDTH))

;; prefix + lines + suffix, with continuation lines aligned under the
;; first character after the prefix.
(define (wrap prefix lines suffix)
  (define n (string-length prefix))
  (define body (cons (string-append prefix (car lines)) (indent (cdr lines) n)))
  (append (drop-right body 1) (list (string-append (last body) suffix))))

;; a document on one line: `\` continuations and aligned arguments joined
(define (flat-line x)
  (string-join (for/list ([l (r-lines x)]) (string-trim (regexp-replace #rx" [\\]$" l ""))) " "))

(define (paren x)
  (atom* (wrap "(" (r-lines x) ")")))

;; -------------------------------------------------------------------------
;; Names
;; -------------------------------------------------------------------------

(define rhombus-reserved
  '("fun" "def" "let" "if" "cond" "match" "try" "throw" "block" "import"
    "export" "class" "interface" "namespace" "operator" "macro" "syntax"
    "values" "for" "when" "unless" "while" "meta" "module" "annot" "this"
    "super" "mutable" "final" "override" "method" "property" "constructor"
    "extends" "implements" "field" "private" "protected" "internal" "is_a"
    "described_as" "veneer" "enum" "use_static" "begin"))

(define (mangle-id s)
  (cond
    [(regexp-match #rx"^[(] *(.*[^ ]) *[)]$" s) => (lambda (m) (op-function-name (cadr m)))]
    [else
     (define base (regexp-replace* #rx"'" s "_prime"))
     (if (member base rhombus-reserved) (string-append "hol_" base) base)]))

;; operators defined as functions in the port
(define operator-names
  (hash "o" "o" "F_F" "F_F" "upto" "upto" "THEN" "THEN" "THENL" "THENL"
        "ORELSE" "ORELSE" "THENC" "THENC" "ORELSEC" "ORELSEC"
        "THEN_TCL" "THEN_TCL" "ORELSE_TCL" "ORELSE_TCL"
        "--" "range" "|->" "fpf_define" "|=>" "fpf_singleton" "@" "append"
        "|>" "|>" "++" "++" "|||" "|||" ">>" ">>"
        "lsl" "lsl" "lsr" "lsr" "asr" "asr" "land" "land" "lor" "lor" "lxor" "lxor"))

(define (op-function-name op)
  (hash-ref operator-names op (lambda () (format "#{~a}" op))))

;; the Rhombus infix operator a module exports for an OCaml operator it
;; defines: `let (THEN) = ...` in tactics.ml goes with then_tac
(define operator-aliases
  (hash "(THEN)" "then_tac" "(THENL)" "then_list" "(ORELSE)" "or_tac"
        "(THENC)" "then_conv" "(ORELSEC)" "or_conv"
        "(|||)" "|||" "(++)" "++" "(>>)" ">>"))

;; Rhombus infix operators the port declares for OCaml infix definitions:
;; OCaml name -> (list rhombus-op left right precedence-lines)
(define infix-declarations
  (hash "|||" (list "|||" #f #f '())
        "++" (list "++" #f #f '("~stronger_than: |||"))
        ">>" (list ">>" #f #f '("~same_as: |||" "~weaker_than: ++"))
        "THENC" (list "then_conv" "conv1" "conv2" '())
        "ORELSEC" (list "or_conv" "conv1" "conv2" '("~same_as: then_conv"))
        "THEN" (list "then_tac" "tac1" "tac2" '("~same_as: then_conv or_conv"))
        "THENL" (list "then_list" "tac1" "tac2l" '("~same_as: then_tac then_conv or_conv"))
        "ORELSE" (list "or_tac" "tac1" "tac2" '("~same_as: then_tac then_list then_conv or_conv"))))

(define (operator-name-of n)
  (cond [(regexp-match #rx"^[(] *(.*[^ ]) *[)]$" n) => cadr] [else #f]))

;; operator (a OP b): ... for `let (|||) a b ... = body`
(define (operator-def-lines op params body)
  (match-define (list rop _ _ precs) (hash-ref infix-declarations op))
  (for ([p precs]) (for ([o (cdr (string-split p))]) (use-operator! o)))
  (define a (car params))
  (define b (cadr params))
  (with-locals (append (pat-vars a) (pat-vars b))
    (lambda ()
      (append (list (format "operator (~a ~a ~a):" (param a) rop (param b))
                    "  ~associativity: ~left")
              (map (lambda (l) (string-append "  " l)) precs)
              (indent
               (if (null? (cddr params))
                   (stmts body)
                   (r-lines (fun-doc (cddr params) body))))))))

;; after `let (THEN) = ...`: the infix operator that calls it
(define (operator-alias-lines name)
  (match-define (list rop a b precs) (hash-ref infix-declarations name))
  (for ([p precs]) (for ([o (cdr (string-split p))]) (use-operator! o)))
  (append (list (format "operator (~a ~a ~a):" a rop b) "  ~associativity: ~left")
          (map (lambda (l) (string-append "  " l)) precs)
          (list (format "  ~a(~a)(~a)" name a b))))

;; reference to an operator used as a function: a definition of this module
;; or an import
(define (op-ref op)
  (define key (string-append "(" op ")"))
  (cond
    [(scope-lookup key) => values]
    [else ((env-use! (current-env)) key) (op-function-name op)]))

;; an infix operator from another module is imported under its own name
(define (use-operator! rop)
  (define key (for/first ([(k v) operator-aliases] #:when (equal? v rop)) k))
  (when (and key (not (scope-lookup key)))
    ((env-use! (current-env)) rop)))

(define module-renames
  (hash "List" "OCamlList" "String" "OCamlString" "Char" "OCamlChar"
        "Int" "OCamlInt" "Array" "OCamlArray" "Hashtbl" "Hashtbl" "Buffer" "OCamlBuffer"))

(define (mangle-path s)
  (define parts (string-split s "."))
  (cond
    [(= (length parts) 1) (mangle-id s)]
    [else
     (define mods (drop-right parts 1))
     (string-join
      (append (cons (hash-ref module-renames (car mods) (car mods)) (cdr mods))
              (list (mangle-id (last parts))))
      ".")]))

(define (camel s)
  (string-append*
   (for/list ([w (string-split s "_")] #:unless (string=? w ""))
     (string-append (string-upcase (substring w 0 1)) (substring w 1)))))

;; -------------------------------------------------------------------------
;; Emission environment
;; -------------------------------------------------------------------------

;; env:
;;   modname   the module's name (for versioned redefinitions)
;;   resolve   free value name -> (or/c #f string): the alias to qualify it
;;             with when the module also defines that name later
;;   use!      records a free name the module takes from elsewhere
;;   records   field name -> (cons RecordName (listof field))
;;   counts    name -> number of toplevel definitions of that name
(struct env (modname resolve use! records counts line-of ctor-arity included) #:transparent)

;; The functions of OCaml's Format, as private/format.rhm provides them.
;; printer.ml's `include Format` makes them part of the printer.
(define format-api
  '("formatter" "std_formatter" "err_formatter" "str_formatter" "flush_str_formatter" "formatter_of_buffer" "make_formatter" "pp_print_string" "pp_print_as" "pp_print_int" "pp_print_char" "pp_print_bool" "pp_print_float" "pp_print_break" "pp_print_custom_break" "pp_print_space" "pp_print_cut" "pp_force_newline" "pp_print_if_newline" "pp_print_newline" "pp_print_flush" "pp_open_box" "pp_open_hbox" "pp_open_vbox" "pp_open_hvbox" "pp_open_hovbox" "pp_close_box" "pp_open_tbox" "pp_close_tbox" "pp_print_tbreak" "pp_print_tab" "pp_set_tab" "pp_set_margin" "pp_get_margin" "pp_set_max_indent" "pp_get_max_indent" "pp_set_max_boxes" "pp_get_max_boxes" "pp_over_max_boxes" "pp_set_ellipsis_text" "pp_get_ellipsis_text" "print_string" "print_as" "print_int" "print_char" "print_break" "print_space" "print_cut" "print_newline" "print_flush" "force_newline" "open_box" "open_hbox" "open_vbox" "open_hvbox" "open_hovbox" "close_box" "set_margin" "get_margin" "set_max_indent" "get_max_indent" "set_max_boxes" "get_max_boxes" "printf" "fprintf" "asprintf"))

;; a constructor declared `C of (a * b)` has one field holding a tuple
(define (tuple-field? n)
  (eqv? 1 (hash-ref (env-ctor-arity (current-env)) n #f)))

(define current-env (make-parameter #f))
(define locals (make-parameter (hash)))       ; locally bound names

;; Definition scopes, innermost first: the module, then each
;; `module ... = struct` namespace. A scope maps a name to the number of its
;; definitions so far, or to the qualified name an `open` makes visible.
(struct scope (defined counts) #:transparent)
(define scopes (make-parameter '()))
(define namespaces (make-parameter (make-hash)))   ; namespace -> exported names
(define (defined) (scope-defined (car (scopes))))

(define (versioned name k [sc (car (scopes))])
  (define total (hash-ref (scope-counts sc) name 1))
  (if (>= k total)
      (mangle-id name)
      (format "~a_~a_v~a" (env-modname (current-env)) (mangle-id name) k)))

(define (scope-lookup name)
  (for/or ([sc (scopes)])
    (define v (hash-ref (scope-defined sc) name #f))
    (cond [(number? v) (versioned name v sc)]
          [(string? v) v]
          [else #f])))

;; OCaml Stdlib names that HOL Light theories also define: the adapter
;; provides the Stdlib function under another name
(define stdlib-renames (hash "int_of_num" "hol_int_of_num"))

(define (ref-name name)
  (cond
    [(regexp-match #rx"^[(] *(.*[^ ]) *[)]$" name) => (lambda (m) (op-value (cadr m)))]
    [(regexp-match? #rx"[.]" name) (path-ref name)]
    [(hash-ref (locals) name #f) (mangle-id name)]
    [(scope-lookup name) => values]
    [else
     (define name* (if ((env-resolve (current-env)) name) name (hash-ref stdlib-renames name name)))
     ((env-use! (current-env)) name*)
     (define alias ((env-resolve (current-env)) name))
     (if alias
         (string-append alias "." (mangle-id name))
         (mangle-id name*))]))

;; M.x: a namespace of this module, Num (whose functions the port defines
;; unqualified), or a module to import, renamed to its adapter if it has one
(define (path-ref name)
  (define parts (string-split name "."))
  (define m (car parts))
  (cond
    [(scope-lookup m) (mangle-path name)]
    [(and (equal? m "Num") (= (length parts) 2)) (ref-name (cadr parts))]
    [else
     ((env-use! (current-env)) (hash-ref module-renames m m))
     (mangle-path name)]))

(define (with-locals names thunk)
  (parameterize ([locals (for/fold ([h (locals)]) ([n names]) (hash-set h n #t))])
    (thunk)))

;; -------------------------------------------------------------------------
;; Patterns
;; -------------------------------------------------------------------------

(define (pat-vars p)
  (match p
    [(p:var n) (list n)]
    [(p:constr _ a) (if a (pat-vars a) '())]
    [(p:tuple ps) (append-map pat-vars ps)]
    [(p:list ps) (append-map pat-vars ps)]
    [(p:array ps) (append-map pat-vars ps)]
    [(p:cons h t) (append (pat-vars h) (pat-vars t))]
    [(p:or a b) (pat-vars a)]
    [(p:alias q n) (cons n (pat-vars q))]
    [(p:typed q _) (pat-vars q)]
    [(p:record fs) (append-map (lambda (f) (pat-vars (cdr f))) fs)]
    [(p:label _ q) (pat-vars q)]
    [_ '()]))

(define (lit kind v)
  (case kind
    [(string char) (string-literal v)]
    [(int) (int-literal v)]
    [(float) (float-literal v)]))

(define (string-literal s)
  (define out (open-output-string))
  (write-char #\" out)
  (for ([c s])
    (case c
      [(#\") (write-string "\\\"" out)]
      [(#\\) (write-string "\\\\" out)]
      [(#\newline) (write-string "\\n" out)]
      [(#\tab) (write-string "\\t" out)]
      [(#\return) (write-string "\\r" out)]
      [else
       (if (or (char<? c #\space) (char=? c #\rubout))
           (write-string (format "\\x~a" (string-pad (number->string (char->integer c) 16))) out)
           (write-char c out))]))
  (write-char #\" out)
  (get-output-string out))
(define (string-pad s) (if (= (string-length s) 1) (string-append "0" s) s))

(define (int-literal v)
  (define s (regexp-replace* #rx"_" (regexp-replace #rx"[lLn]$" v "") ""))
  (cond
    [(regexp-match #rx"^(-?)0[xX](.*)$" s) => (lambda (m) (format "~a~a" (cadr m) (string->number (caddr m) 16)))]
    [(regexp-match #rx"^(-?)0[oO](.*)$" s) => (lambda (m) (format "~a~a" (cadr m) (string->number (caddr m) 8)))]
    [(regexp-match #rx"^(-?)0[bB](.*)$" s) => (lambda (m) (format "~a~a" (cadr m) (string->number (caddr m) 2)))]
    [else s]))

(define (float-literal v)
  (define s (regexp-replace* #rx"_" v ""))
  (cond [(regexp-match? #rx"[.]$" s) (string-append s "0")]
        [(regexp-match? #rx"[.][eE]" s) (regexp-replace #rx"[.]" s ".0")]
        [else s]))

(define constructor-renames
  (hash "Invalid_argument" "InvalidArgument"))

;; constructors resolve like values: a module's own, imported, or OCaml's
(define (constr-name n)
  (cond
    [(regexp-match? #rx"[.]" n) (mangle-path n)]
    [else
     (define m (hash-ref constructor-renames n n))
     (cond
       [(scope-lookup n) => values]
       [else ((env-use! (current-env)) m)
             (define alias ((env-resolve (current-env)) n))
             (if alias (string-append alias "." m) m)])]))

(define (pat p)
  (match p
    [(p:var n) (mangle-id n)]
    [(p:any) "_"]
    [(p:const k v) (lit k v)]
    [(p:constr "true" #f) "#true"]
    [(p:constr "false" #f) "#false"]
    [(p:constr "()" #f) "_"]
    [(p:constr "[]" #f) "PairList []"]
    [(p:constr n #f) (string-append (constr-name n) "()")]
    ;; `C _` matches every field of a constructor with several
    [(p:constr n (p:any))
     (define k (hash-ref (env-ctor-arity (current-env)) n 1))
     (format "~a(~a)" (constr-name n) (string-join (make-list (max k 1) "_") ", "))]
    [(p:constr n (p:tuple ps))
     (if (tuple-field? n)
         (format "~a([~a])" (constr-name n) (string-join (map pat ps) ", "))
         (format "~a(~a)" (constr-name n) (string-join (map pat ps) ", ")))]
    [(p:constr n a) (format "~a(~a)" (constr-name n) (pat a))]
    [(p:tuple ps) (format "[~a]" (string-join (map pat ps) ", "))]
    [(p:list ps) (format "PairList [~a]" (string-join (map pat ps) ", "))]
    [(p:cons _ _)
     (define-values (heads tail) (cons-chain-pat p))
     (match tail
       [(p:list ps) (format "PairList [~a]" (string-join (map pat (append heads ps)) ", "))]
       [(p:constr "[]" #f) (format "PairList [~a]" (string-join (map pat heads) ", "))]
       [_ (format "PairList [~a, & ~a]" (string-join (map pat heads) ", ") (pat tail))])]
    [(p:or a b) (format "~a || ~a" (pat a) (pat b))]
    [(p:alias q n) (format "~a as ~a" (pat q) (mangle-id n))]
    [(p:typed q _) (pat q)]
    [(p:record (list (cons "contents" q))) (format "Box(~a)" (pat q))]
    [(p:record fs) (record-pattern fs)]
    [(p:range a b) "_"]
    [(p:array ps) (format "Array(~a)" (string-join (map pat ps) ", "))]
    [(p:label _ q) (pat q)]))

(define (cons-chain-pat p)
  (match p
    [(p:cons h t) (let-values ([(hs tl) (cons-chain-pat t)]) (values (cons h hs) tl))]
    [_ (values '() p)]))

(define (record-info field-names)
  (define recs (env-records (current-env)))
  (for/or ([f field-names])
    (hash-ref recs (last (string-split f ".")) #f)))

(define (record-pattern fs)
  (define info (record-info (map car fs)))
  (cond
    [info
     (format "~a(~a)" (car info)
             (string-join
              (for/list ([f (cdr info)])
                (define hit (assoc f (map (lambda (x) (cons (last (string-split (car x) ".")) (cdr x))) fs)))
                (if hit (pat (cdr hit)) "_"))
              ", "))]
    [else "_"]))

;; A function parameter: unit and typed patterns simplify, others as patterns.
(define (param p)
  (match p
    [(p:constr "()" #f) "_"]
    [(p:typed q _) (param q)]
    [_ (pat p)]))

;; -------------------------------------------------------------------------
;; Expressions
;; -------------------------------------------------------------------------

;; Rhombus operator table: name -> (list prec family assoc)
(define (op-info rop)
  (case rop
    [("||") '(1 std right)] [("&&") '(2 std right)]
    [("==" "!=" "<" ">" "<=" ">=" "===") '(3 std none)]
    [("+" "-") '(4 std left)] [("*" "/" "div" "mod") '(5 std left)]
    [("**") '(6 std right)] [("+&") '(4 cat any)]
    [("then_tac" "then_list" "or_tac" "then_conv" "or_conv") '(3 hol left)]
    [("|||" ">>") '(3 pc left)] [("++") '(4 pc left)]
    [("|>") '(1 pipe left)]
    [else #f]))

;; OCaml operator -> Rhombus infix operator, or #f for a function call
(define (rhombus-op op)
  (case op
    [("=" "=/") "=="] [("<>" "<>/") "!="] [("==") "==="]
    [("<" "</") "<"] [(">" ">/") ">"] [("<=" "<=/") "<="] [(">=" ">=/") ">="]
    [("&&") "&&"] [("||") "||"]
    [("+" "+." "+/") "+"] [("-" "-." "-/") "-"] [("*" "*." "*/") "*"]
    [("/") "div"] [("/." "//") "/"] [("mod") "mod"] [("**" "**/") "**"]
    [("^") "+&"]
    [("THEN") "then_tac"] [("THENL") "then_list"] [("ORELSE") "or_tac"]
    [("THENC") "then_conv"] [("ORELSEC") "or_conv"]
    [("|||" "++" ">>" "|>") op]
    [else #f]))

(define (needs-paren? x parent-prec parent-fam side parent-assoc)
  (match (if (and (r-src-paren x) (eq? (r-kind x) 'op)) 'open (r-kind x))
    ['atom #f]
    ['open #t]
    ['unary (and parent-fam (not (eq? parent-fam 'std))) ]
    ['op
     (define p (r-prec x))
     (cond
       [(not (eq? (r-fam x) parent-fam))
        ;; ||/&& over comparisons and arithmetic are the only cross-level
        ;; relations Rhombus declares; any other mix gets parentheses
        #t]
       [(< p parent-prec) #t]
       [(> p parent-prec) #f]
       [(eq? parent-assoc 'any) #f]
       [else (not (eq? side parent-assoc))])]))

(define (operand x prec fam side assoc)
  (if (needs-paren? x prec fam side assoc) (paren x) x))

(define (binop rop a b)
  (match-define (list prec fam assoc) (op-info rop))
  (define x (operand a prec fam 'left assoc))
  (define y (operand b prec fam 'right assoc))
  ;; a chain of one operator, collected so that a long chain breaks once
  ;; per operator, the way the port lays out THEN sequences
  (define left-ops (if (and (eq? (r-kind a) 'op) (r-chain a) (equal? (car (r-chain a)) rop)
                            (not (needs-paren? a prec fam 'left assoc)))
                       (cdr (r-chain a))
                       (list x)))
  (define operands (append left-ops (list y)))
  (define one (and (andmap single? operands)
                   (string-join (map line1 operands) (string-append " " rop " "))))
  (if (and one (fits? one))
      (r* (list one) 'op prec fam (cons rop operands))
      (r* (append*
           (for/list ([o operands] [i (in-naturals)])
             (if (< i (sub1 (length operands)))
                 (append (drop-right (r-lines o) 1)
                         (list (string-append (last (r-lines o)) " " rop " \\")))
                 (r-lines o))))
          'op prec fam (cons rop operands))))

;; f(a)(b)(c): each argument group inline when it fits, the others aligned
(define (call-doc head groups)
  ;; groups: list of (listof r) -- each group is one parenthesised list
  (define rendered
    (for/list ([g groups])
      (define items (map r-lines g))
      (define flat (and (andmap (lambda (l) (= (length l) 1)) items)
                        (string-join (map car items) ", ")))
      (if flat (list flat) (join-aligned items))))
  (let loop ([lines (list head)] [gs rendered])
    (cond
      [(null? gs) (atom* lines)]
      [else
       (define g (car gs))
       (define last-line (last lines))
       (define candidate (and (= (length g) 1) (string-append last-line "(" (car g) ")")))
       (cond
         [candidate
          (loop (append (drop-right lines 1) (list candidate)) (cdr gs))]
         [(> (string-length last-line) 40)
          ;; break: open the group at the end of the line, body indented
          (loop (append (drop-right lines 1)
                        (list (string-append last-line "("))
                        (indent g 2)
                        (list ")"))
                (cdr gs))]
         [else
          (loop (append (drop-right lines 1) (wrap (string-append last-line "(") g ")"))
                (cdr gs))])])))

;; items (each a list of lines) separated by commas, aligned
(define (join-aligned items)
  (append*
   (for/list ([it items] [i (in-naturals)])
     (if (< i (sub1 (length items)))
         (append (drop-right it 1) (list (string-append (last it) ",")))
         it))))

(define (bracket open close items)
  (define ls (map r-lines items))
  (define flat (and (andmap (lambda (l) (= (length l) 1)) ls)
                    (string-append open (string-join (map car ls) ", ") close)))
  (if (and flat (fits? flat))
      (atom flat)
      (atom* (wrap open (join-aligned ls) close))))

;; application spine
(define (unparen e) (if (e:paren? e) (unparen (e:paren-e e)) e))

(define (flatten-app e)
  (match (unparen e)
    [(e:app f args) (let-values ([(h as) (flatten-app f)]) (values h (append as args)))]
    [_ (values e '())]))

(define (ex e)
  (match e
    [(e:var n) (atom (ref-name n))]
    [(e:const k v) (atom (lit k v))]
    [(e:quote text) (atom (quotation text))]
    [(e:constr "true" #f) (atom "#true")]
    [(e:constr "false" #f) (atom "#false")]
    [(e:constr "()" #f) (atom "#void")]
    [(e:constr "[]" #f) (atom "PairList []")]
    [(e:constr n #f) (atom (string-append (constr-name n) "()"))]
    [(e:constr n (e:tuple items))
     (if (tuple-field? n)
         (call-doc (constr-name n) (list (list (bracket "[" "]" (map ex items)))))
         (call-doc (constr-name n) (list (map ex items))))]
    [(e:constr n a) (call-doc (constr-name n) (list (list (ex a))))]
    [(e:tuple items) (bracket "[" "]" (map ex items))]
    [(e:list items) (bracket "PairList [" "]" (map ex items))]
    [(e:array items) (call-doc "Array" (list (map ex items)))]
    [(e:cons _ _)
     (define-values (heads tail) (cons-chain e))
     (match tail
       [(e:list items) (bracket "PairList [" "]" (map ex (append heads items)))]
       [(e:constr "[]" #f) (bracket "PairList [" "]" (map ex heads))]
       [_ (if (= (length heads) 1)
              (call-doc "PairList.cons" (list (list (ex (car heads)) (ex tail))))
              (bracket "PairList [" "]"
                       (append (map ex heads)
                               (list (let ([t (ex tail)])
                                       (atom* (wrap "& " (r-lines t) "")))))))])]
    [(e:app _ _) (app e)]
    [(e:infix op a b) (infix op a b)]
    [(e:neg _ a) (unary "-" (ex a))]
    [(e:prefix "!" a) (let ([x (ex a)]) (atom* (wrap "" (r-lines (if (eq? (r-kind x) 'atom) x (paren x))) ".value")))]
    [(e:prefix "~-" a) (unary "-" (ex a))]
    [(e:prefix op a) (call-doc (format "#{~a}" op) (list (list (ex a))))]
    [(e:field obj name)
     (define x (ex obj))
     (atom* (wrap "" (r-lines (if (eq? (r-kind x) 'atom) x (paren x)))
                  (string-append "." (field-name name))))]
    [(e:index obj idx kind)
     (if (eq? kind 'string)
         (call-doc "OCamlString.get" (list (list (ex obj)) (list (ex idx))))
         (let ([x (ex obj)])
           (atom* (wrap "" (r-lines (if (eq? (r-kind x) 'atom) x (paren x)))
                        (string-append "[" (line1 (ex idx)) "]")))))]
    [(e:record base fields) (record-expr base fields)]
    [(e:typed e _) (ex e)]
    [(e:paren inner)
     (define x (ex inner))
     (define y (r (r-lines x) (r-kind x) (r-prec x) (r-fam x)))
     (set-r-chain! y (r-chain x))
     (set-r-src-paren! y #t)
     y]
    [(e:opname op) (atom (op-value op))]
    [(e:label _ e) (ex e)]
    [(e:assert e) ((env-use! (current-env)) "assert") (call-doc "assert" (list (list (ex e))))]
    [(e:lazy e) (call-doc "lazy" (list (list (ex e))))]
    [(e:fun params body) (fun-doc params body)]
    [(e:function cases) (function-doc cases)]
    [(e:if c t f) (if-doc c t f)]
    [(e:match s cases) (match-doc s cases)]
    [(e:try b cases) (try-doc b cases)]
    [(or (e:let _ _ _) (e:seq _ _) (e:letopen _ _) (e:letmodule _ _ _)
         (e:setfield _ _ _) (e:setindex _ _ _ _) (e:while _ _) (e:for _ _ _ _ _))
     (define lines (stmts e))
     (if (= (length lines) 1)
         (atom* lines)
         (open* (cons "block:" (indent lines))))]))

;; a reference's only field is `contents`; Box calls it value
(define (field-name n)
  (define b (last (string-split n ".")))
  (if (equal? b "contents") "value" (mangle-id b)))

(define (cons-chain e)
  (match (if (and (e:paren? e) (e:cons? (unparen e))) (unparen e) e)
    [(e:cons h t) (let-values ([(hs tl) (cons-chain t)]) (values (cons h hs) tl))]
    [_ (values '() e)]))

(define (unary op x)
  (r (r-lines (atom* (wrap op (r-lines (if (memq (r-kind x) '(atom)) x (paren x))) "")))
     'unary 7 'std))

(define (quotation text)
  (cond
    [(and (> (string-length text) 0)
          (char=? (string-ref text (sub1 (string-length text))) #\:))
     (string-literal (substring text 0 (sub1 (string-length text))))]
    [(regexp-match? #rx"}[|]" text)
     (format "parse_term(~a)" (string-literal text))]
    [else (string-append "@hol|{" text "}|")]))

(define (op-value op)
  (cond
    [(rhombus-op op)
     => (lambda (rop)
          (if (op-info rop)
              (format "fun(x): fun(y): x ~a y" rop)
              (op-ref op)))]
    [(member op '("::")) "fun(x): fun(y): PairList.cons(x, y)"]
    [(member op '("!")) "fun(x): x.value"]
    [(member op '(":=")) "fun(x): fun(y): x.value := y"]
    [else (op-ref op)]))

(define (app e)
  (define-values (h args) (flatten-app e))
  (match* (h args)
    [((e:var "not") (list a)) (unary "!" (ex a))]
    [((e:var "ref") (list a)) (call-doc "Box" (list (list (ex a))))]
    [((e:var "raise") (list a)) (open* (r-lines (atom* (wrap "throw " (r-lines (ex a)) ""))))]
    [((e:var "!=") (list a b)) (unary "!" (paren (binop "===" (ex a) (ex b))))]
    [(_ _)
     (define head (ex h))
     (define head-line
       (if (and (single? head) (eq? (r-kind head) 'atom)) (line1 head)
           (let ([p (paren head)]) (if (single? p) (line1 p) #f))))
     (if head-line
         (call-doc head-line (for/list ([a args]) (list (ex a))))
         ;; multi-line head: parenthesise and call
         (let* ([p (paren head)]
                [tail (call-doc "" (for/list ([a args]) (list (ex a))))])
           (atom* (append (drop-right (r-lines p) 1)
                          (wrap (last (r-lines p)) (r-lines tail) "")))))]))

(define (infix op a b)
  (define rop (rhombus-op op))
  (cond
    [(equal? op ":=")
     (define x (ex a))
     (define y (ex b))
     (open* (wrap (string-append (line1 (if (eq? (r-kind x) 'atom) x (paren x))) ".value := ")
                  (r-lines y) ""))]
    [(equal? op "!=") (unary "!" (paren (binop "===" (ex a) (ex b))))]
    [(and rop (op-info rop)) (use-operator! rop) (binop rop (ex a) (ex b))]
    [else (call-doc (op-ref op) (list (list (ex a)) (list (ex b))))]))

(define (record-expr base fields)
  (cond
    [(and (not base) (= (length fields) 1) (equal? (car (car fields)) "contents"))
     (call-doc "Box" (list (list (ex (cdr (car fields))))))]
    [base
     (define x (ex base))
     (define assigns
       (for/list ([f fields])
         (format "~a = ~a" (mangle-id (last (string-split (car f) "."))) (string-join (r-lines (ex (cdr f))) " "))))
     (atom (format "~a with (~a)" (line1 (if (eq? (r-kind x) 'atom) x (paren x))) (string-join assigns ", ")))]
    [else
     (define info (record-info (map car fields)))
     (define by-name (for/list ([f fields]) (cons (last (string-split (car f) ".")) (cdr f))))
     (if info
         (call-doc (car info)
                   (list (for/list ([f (cdr info)])
                           (define hit (assoc f by-name))
                           (if hit (ex (cdr hit)) (atom "#void")))))
         (bracket "{" "}" (for/list ([f by-name]) (atom (format "~a: ~a" (car f) (line1 (ex (cdr f))))))))]))

;; fun(p1): fun(p2): body
(define (fun-doc params body)
  (define names (append-map pat-vars params))
  (define heads (for/list ([p params]) (format "fun(~a):" (param p))))
  (with-locals names
    (lambda () (open* (nest-heads heads (stmts body))))))

;; heads: "fun f(a):" "fun(b):" ...; body: lines
(define (nest-heads heads body)
  (define one (and (= (length body) 1)
                   (string-append (string-join heads " ") " " (car body))))
  (cond
    [(and one (fits? one)) (list one)]
    [(null? (cdr heads)) (cons (car heads) (indent body))]
    [else (cons (car heads) (indent (nest-heads (cdr heads) body)))]))

(define (function-doc cases)
  (open* (cons "fun(arg):" (indent (r-lines (match-doc* "arg" cases))))))

;; one-line renderings of if/match that also have a multi-line form, for
;; positions where their `|` would be read as the enclosing alternatives
(define multi-line-form (make-hash))   ; one-line text -> lines

(define (alternatives head alts)
  ;; alts: list of (cons label-string body-lines) where label ends with ":"
  ;; or is "" for if-branches
  (append (if (string? head) (list head) head)
          (append*
           (for/list ([a alts])
             (define label (car a))
             (define body0 (cdr a))
             ;; a one-line if/match opening the branch would lend its `|`
             ;; to these alternatives: use its multi-line form there
             (define body
               (if (and (pair? body0) (hash-ref multi-line-form (car body0) #f))
                   (append (hash-ref multi-line-form (car body0)) (cdr body0))
                   body0))
             (define first (if (string=? label "") "| " (string-append "| " label " ")))
             (define one (and (= (length body) 1) (string-append first (car body))))
             (cond
               [(and one (fits? one)) (list one)]
               [(string=? label "") (wrap "| " body "")]
               [else (cons (string-append "| " label) (indent body 4))])))))

(define (if-doc c t f)
  (define cx (let ([x (ex c)]) (if (eq? (r-kind x) 'open) (paren x) x)))
  (define cline (if (single? cx) (line1 cx) (line1 (paren cx))))
  (define tl (stmts t))
  (define fl (if f (stmts f) (list "#void")))
  (define one (and (= (length tl) 1) (= (length fl) 1) (single? cx)
                   (format "if ~a | ~a | ~a" cline (car tl) (car fl))))
  (define multi
    (alternatives (if (single? cx) (string-append "if " cline)
                      (wrap "if " (r-lines (paren cx)) ""))
                  (list (cons "" tl) (cons "" fl))))
  (if (and one (fits? one) (not (regexp-match? #rx"[|]" (string-append (car tl) (car fl)))))
      (let ([lines (list one)])
        (hash-set! multi-line-form one multi)
        (open* lines))
      (open* multi)))

(define (case-label c)
  (define p (pat (mcase-pat c)))
  (with-locals (pat-vars (mcase-pat c))
    (lambda ()
      (define guard (and (mcase-guard c) (flat-line (let ([g (ex (mcase-guard c))]) (if (eq? (r-kind g) 'open) (paren g) g)))))
      (values (string-append p (if guard (string-append " when " guard) "") ":")
              (stmts (mcase-body c))))))

(define (or-alternatives p)
  (match p
    [(p:or a b) (append (or-alternatives a) (or-alternatives b))]
    [_ (list p)]))

;; Rhombus or-patterns bind no variables, so an OCaml case `p1 | p2 -> e`
;; whose patterns bind becomes one case per alternative.
(define (split-or-cases cases)
  (append*
   (for/list ([c cases])
     (define p (mcase-pat c))
     (if (and (p:or? p) (pair? (pat-vars p)))
         (for/list ([q (or-alternatives p)]) (mcase q (mcase-guard c) (mcase-body c)))
         (list c)))))

(define (match-doc* scrut cases0)
  (define cases (split-or-cases cases0))
  (open* (alternatives (if (string? scrut) (string-append "match " scrut) (wrap "match " scrut ""))
                       (for/list ([c cases])
                         (define-values (label body) (case-label c))
                         (cons label body)))))

(define (match-doc s cases)
  (define sx (let ([x (ex s)]) (if (eq? (r-kind x) 'open) (paren x) x)))
  (match-doc* (if (single? sx) (line1 sx) (r-lines (paren sx))) cases))

(define (try-doc b cases0)
  (define cases (split-or-cases cases0))
  (define body (stmts b))
  (define handlers
    (for/list ([c cases])
      (define-values (label hbody) (case-label c))
      (cons label hbody)))
  (define catch-lines
    (if (= (length handlers) 1)
        (let* ([h (car handlers)] [one (string-append "~catch " (car h) " " (string-join (cdr h) ""))])
          (if (and (= (length (cdr h)) 1) (fits? one))
              (list one)
              (cons (string-append "~catch " (car h)) (indent (cdr h) 4))))
        (cons "~catch"
              (cdr (alternatives "" handlers)))))
  (open* (cons "try:" (indent (append body catch-lines)))))

;; -------------------------------------------------------------------------
;; Statements: let ... in and sequences flatten into block lines
;; -------------------------------------------------------------------------

(define (stmts e)
  (match e
    [(e:paren inner) #:when (not (e:infix? (unparen inner))) (stmts inner)]
    [(e:let rec? bindings body)
     (define names (append-map binding-names bindings))
     (if rec?
         ;; a `let rec f` that shadows an f of the same block cannot be a
         ;; second `fun f` there: it becomes `let f:` around its own `fun f`
         (let ([shadowing (filter (lambda (n) (hash-ref (locals) n #f)) names)])
           (with-locals names
             (lambda ()
               (append (append-map
                        (lambda (b)
                          (define n (binding-name b))
                          (define lines (local-binding b #t))
                          (if (and n (member n shadowing))
                              (append (list (format "let ~a:" (mangle-id n)))
                                      (indent lines)
                                      (list (string-append "  " (mangle-id n))))
                              lines))
                        bindings)
                       (stmts body)))))
         (let loop ([bs bindings] [acc '()])
           (cond
             [(null? bs) (with-locals names (lambda () (append acc (stmts body))))]
             [else
              (define lines (local-binding (car bs) #f))
              (with-locals (binding-names (car bs))
                (lambda () (loop (cdr bs) (append acc lines))))])))]
    [(e:seq a b) (append (stmts a) (stmts b))]
    [(e:letopen _ body) (stmts body)]
    [(e:letmodule name m body)
     (append (module-lines m) (stmts body))]
    [(e:setfield obj name v)
     (define x (ex obj))
     (r-lines (atom* (wrap (string-append (line1 (if (eq? (r-kind x) 'atom) x (paren x))) "."
                                          (field-name name) " := ")
                           (r-lines (ex v)) "")))]
    [(e:setindex obj idx kind v)
     (define x (ex obj))
     (r-lines (atom* (wrap (format "~a[~a] := " (line1 (if (eq? (r-kind x) 'atom) x (paren x))) (line1 (ex idx)))
                           (r-lines (ex v)) "")))]
    [(e:while c body)
     (cons (format "while ~a:" (line1 (ex c))) (indent (stmts body)))]
    [(e:for v from dir to body)
     (define head
       (if (eq? dir 'to)
           (format "for (~a in ~a ..= ~a):" (pat v) (line1 (ex from)) (line1 (ex to)))
           (format "for (~a in OCamlInt.downto(~a)(~a)):" (pat v) (line1 (ex from)) (line1 (ex to)))))
     (cons head (indent (with-locals (pat-vars v) (lambda () (stmts body)))))]
    [(e:app (e:var "raise") (list a)) (wrap "throw " (r-lines (ex a)) "")]
    [_ (r-lines (ex e))]))

(define (binding-names b)
  (pat-vars (binding-pat b)))

(define (binding-name b)
  (match (binding-pat b)
    [(p:var n) n]
    [(p:typed (p:var n) _) n]
    [_ #f]))

;; `let rec f x = ...` -> fun f(x): ...;  `let f x = ...` -> let f = fun(x): ...
(define (local-binding b rec?)
  (define name (binding-name b))
  (define params (binding-params b))
  (define body (unparen (binding-body b)))
  (cond
    [(and rec? name (pair? params)) (fun-def-lines "fun" (mangle-id name) params body)]
    [(and rec? name (e:function? body))
     (fun-def-lines "fun" (mangle-id name) (list (p:var "arg")) #f #:cases (e:function-cases body))]
    [(and rec? name (e:fun? body))
     (fun-def-lines "fun" (mangle-id name) (e:fun-params body) (e:fun-body body))]
    [(pair? params)
     (value-lines "let" (pat (binding-pat b)) (e:fun params body))]
    [else (value-lines "let" (pat (binding-pat b)) body)]))

;; let x = e  |  let x:\n  lines
(define (value-lines kw lhs body)
  (define x0 (ex body))
  ;; a one-line if/match value is parenthesised, so that its `|` cannot
  ;; join an enclosing alternative
  (define x (if (and (eq? (r-kind x0) 'open) (single? x0) (regexp-match? #rx" [|] " (line1 x0)))
                (paren x0)
                x0))
  (define lines (if (eq? (r-kind x) 'open)
                    (let ([s (stmts body)]) s)
                    (r-lines x)))
  (match body
    [(or (e:let _ _ _) (e:seq _ _))
     (cons (format "~a ~a:" kw lhs) (indent (stmts body)))]
    [_
     (define one (and (single? x) (string-append kw " " lhs " = " (line1 x))))
     (cond
       [(and one (fits? one)) (list one)]
       [(and (eq? (r-kind x) 'atom) (fits? (string-append kw " " lhs " = " (car (r-lines x)))))
        (wrap (string-append kw " " lhs " = ") (r-lines x) "")]
       [else (cons (format "~a ~a:" kw lhs) (indent (r-lines x)))])]))

;; fun f(a): fun(b): body  (or clause form for `function`)
(define (fun-def-lines kw name params body #:cases [cases #f])
  (define names (append-map pat-vars params))
  (define heads
    (cons (format "~a ~a(~a):" kw name (param (car params)))
          (for/list ([p (cdr params)]) (format "fun(~a):" (param p)))))
  (with-locals names
    (lambda ()
      (cond
        [cases (nest-heads heads (r-lines (match-doc* "arg" cases)))]
        [(e:function? body)
         (nest-heads (append heads (list "fun(arg):"))
                     (r-lines (match-doc* "arg" (e:function-cases body))))]
        [else (nest-heads heads (stmts body))]))))

;; -------------------------------------------------------------------------
;; Toplevel
;; -------------------------------------------------------------------------

(define (toplevel-names item)
  (match item
    [(t:let _ _ bs) (filter values (map binding-name-or-tuple bs))]
    [_ '()]))
(define (binding-name-or-tuple b) (binding-name b))

;; every toplevel value name the module defines, in order, with repeats
(define (defined-names items)
  (append*
   (for/list ([it items])
     (match it
       [(t:let _ _ bs)
        (append-map (lambda (b)
                      (define n (binding-name b))
                      (cond [n (list n)]
                            [else (pat-vars (binding-pat b))]))
                    bs)]
       [_ '()]))))

;; free value names used by the items (approximate: ignores shadowing by
;; local bindings, which the emitter resolves exactly)
(define (free-names items) '())

(define (bump! n) (hash-update! (defined) n (lambda (v) (if (number? v) (add1 v) 1)) 0))

;; in a `let rec` group every name is bumped before its members are emitted
(define (def-item b rec?)
  (define name (binding-name b))
  (define params (binding-params b))
  (define body (unparen (binding-body b)))
  (define (current n) (let ([v (hash-ref (defined) n 0)]) (if (number? v) v 0)))
  (define (this-name n) (versioned n (if rec? (current n) (add1 (current n)))))
  (define op (and name (operator-name-of name)))
  (cond
    [(and op (member op '("|||" "++" ">>")) (>= (length params) 2))
     (begin0 (operator-def-lines op params body) (bump! name))]
    [(and name (or (pair? params) (and rec? (or (e:fun? body) (e:function? body)))))
     (define target (this-name name))
     (begin0
       (cond
         [(pair? params) (fun-def-lines "fun" target params body)]
         [(e:fun? body) (fun-def-lines "fun" target (e:fun-params body) (e:fun-body body))]
         [else (fun-def-lines "fun" target (list (p:var "arg")) #f #:cases (e:function-cases body))])
       (unless rec? (bump! name)))]
    [(and name (e:function? body))
     (define target (this-name name))
     (begin0 (fun-def-lines "fun" target (list (p:var "arg")) #f #:cases (e:function-cases body))
             (unless rec? (bump! name)))]
    [name
     (define target (this-name name))
     (begin0 (value-lines "def" target body) (unless rec? (bump! name)))]
    [else
     ;; pattern definitions: let a, b = ... ; let _ = e ; let () = e
     (match (binding-pat b)
       [(or (p:any) (p:constr "()" #f)) (stmts body)]
       [p
        (define vars (pat-vars p))
        (define lhs
          (match p
            [(p:tuple ps) (format "[~a]" (string-join
                                         (for/list ([q ps])
                                           (match q
                                             [(or (p:var n) (p:typed (p:var n) _)) (this-name n)]
                                             [_ (pat q)]))
                                         ", "))]
            [_ (pat p)]))
        (begin0 (value-lines "def" lhs body)
                (for-each bump! vars))])]))

(define (item-lines it)
  (match it
    [(t:let _ rec? bs)
     (when rec? (for ([b bs]) (define n (binding-name b)) (when n (bump! n))))
     (define defs (append* (add-between (for/list ([b bs]) (def-item b rec?)) (list ""))))
     ;; THEN, THENL, ORELSE, THENC and ORELSEC get their infix operators
     (define ops
       (for*/list ([b bs]
                   [n (in-list (pat-vars (binding-pat b)))]
                   [op (in-value (operator-name-of n))]
                   #:when (and op (hash-ref infix-declarations op #f)
                               (not (member op '("|||" "++" ">>")))))
         (operator-alias-lines op)))
     (append defs (append* (for/list ([o ops]) (cons "" o))))]
    [(t:expr _ (e:app (e:var (or "needs" "loads" "loadt")) _)) '()]
    [(t:expr _ e) (stmts e)]
    [(t:type _ decls)
     (for* ([d decls])
       (match (tydecl-kind d)
         [(list 'variant ctors) (for ([c ctors]) (hash-set! (defined) (car c) (car c)))]
         [(list 'record _) (hash-set! (defined) (camel (tydecl-name d)) (camel (tydecl-name d)))]
         [_ (void)]))
     (append* (add-between (filter pair? (map type-lines decls)) (list "")))]
    [(t:exception _ name args)
     (hash-set! (defined) name name)
     (list (format "class ~a(~a)" name (string-join (field-names args) ", ")))]
    [(t:module _ name params body) (hash-set! (defined) name name) (module-item name params body)]
    [(t:modtype _ name) (list (format "// module type ~a: signature not translated" name))]
    [(t:open _ path)
     ;; a namespace of this module: its names become visible unqualified
     (define names (hash-ref (namespaces) path #f))
     (when names
       (for ([n names]) (hash-set! (defined) n (string-append path "." (mangle-id n)))))
     (list (format "// open ~a" path))]
    [(t:include _ (m:path "Format"))
     (set-box! (env-included (current-env)) #t)
     (for ([n format-api]) (hash-set! (defined) n n))
     (list "// include Format: its functions are imported and exported above")]
    [(t:include _ m) (list "// include: not translated")]
    [(t:external _ name) (list (format "// external ~a: not translated" name))]
    [(t:directive _ name arg) (list (format "// #~a" name))]))

(define (module-lines m)
  (item-lines m))

(define (module-item name params body)
  (match body
    [(m:struct items)
     (define counts (make-hash))
     (for ([n (defined-names items)]) (hash-update! counts n add1 0))
     (define inner
       (parameterize ([scopes (cons (scope (make-hash) counts) (scopes))])
         (items-lines items '())))
     (define names (remove-duplicates (defined-names items)))
     (hash-set! (namespaces) name (append names (declared-names items)))
     (hash-set! (defined) name name)
     (define exports (remove-duplicates (append (map mangle-id names) (declared-names items))))
     (append (list (format "namespace ~a:" name))
             (indent (if (null? exports) '()
                         (list (string-append "export: " (string-join exports " ")))))
             (indent inner))]
    [(m:app (m:path f) (m:path arg))
     (cond
       [(member f '("Map.Make" "Set.Make"))
        ((env-use! (current-env)) (if (equal? f "Map.Make") "OCamlMap" "OCamlSet"))
        (list (format "def ~a = ~a(~a.compare)" name
                      (if (equal? f "Map.Make") "OCamlMap.Make" "OCamlSet.Make") arg))]
       [else (list (format "def ~a = ~a(~a)" name f arg))])]
    [(m:path p) (list (format "def ~a = ~a" name p))]
    [_ (list (format "// module ~a: not translated" name))]))

(define (field-names tys)
  (define raw
    (for/list ([t tys])
      (match t
        [(ty:con n _) (let ([b (last (string-split n "."))])
                        (if (member b '("string")) "message" b))]
        [(ty:var _) "value"]
        [(ty:arrow _ _) "f"]
        [(ty:tuple _) "pair"]
        [_ "value"])))
  (for/list ([n raw] [i (in-naturals)])
    (define k (count (lambda (m) (equal? m n)) raw))
    (define name (mangle-id n))
    (if (> k 1) (format "~a~a" name (add1 (count (lambda (m) (equal? m n)) (take raw i)))) name)))

(define (type-lines d)
  (match (tydecl-kind d)
    [(list 'variant ctors)
     (cons (format "variant ~a:" (mangle-id (tydecl-name d)))
           (indent (for/list ([c ctors])
                     (format "~a(~a)" (car c) (string-join (field-names (cadr c)) ", ")))))]
    [(list 'record fields)
     (list (format "record ~a(~a)" (camel (tydecl-name d))
                   (string-join (map (lambda (f) (mangle-id (cadr f))) fields) ", ")))]
    [_ '()]))

;; constructors, records, exceptions and modules the items declare
(define (declared-names items)
  (append*
   (for/list ([it items])
     (match it
       [(t:type _ decls)
        (append*
         (for/list ([d decls])
           (match (tydecl-kind d)
             [(list 'variant ctors) (map car ctors)]
             [(list 'record _) (list (camel (tydecl-name d)))]
             [_ '()])))]
       [(t:exception _ n _) (list n)]
       [(t:module _ n _ _) (list n)]
       [_ '()]))))

;; constructor -> number of declared fields, over items and their modules
(define (ctor-arities items #:nested [nested? #t])
  (define h (make-hash))
  (let walk ([items items] [top? #t])
    (for ([it items])
      (match it
        [(t:type _ decls)
         (for ([d decls])
           (match (tydecl-kind d)
             [(list 'variant ctors) (for ([c ctors]) (hash-set! h (car c) (length (cadr c))))]
             [_ (void)]))]
        [(t:exception _ n args) (hash-set! h n (length args))]
        [(t:module _ _ _ (m:struct inner)) (when nested? (walk inner #f))]
        [_ (void)])))
  h)

;; record types of the module: field -> (cons RecordName fields)
(define (collect-records items)
  (define h (make-hash))
  (let walk ([items items])
    (for ([it items])
      (match it
        [(t:type _ decls)
         (for ([d decls])
           (match (tydecl-kind d)
             [(list 'record fields)
              (define names (map cadr fields))
              (for ([f names]) (hash-set! h f (cons (camel (tydecl-name d)) names)))]
             [_ (void)]))]
        [(t:module _ _ _ (m:struct inner)) (walk inner)]
        [_ (void)])))
  h)

;; Comments: (cons offset text) -> // lines
(define (comment-lines text)
  (define ls (string-split text "\n" #:trim? #f))
  (for/list ([l ls] [i (in-naturals)])
    (define t (string-trim (if (= i 0) l (regexp-replace #rx"^ ?" l "")) #:left? #f))
    (define t2 (string-trim t))
    (if (string=? t2 "") "//" (string-append "// " (if (= i 0) (string-trim t) t)))))

(define (banner-comment text)
  ;; (* ---- *) style boxes: strip the frame
  (comment-lines text))

;; Comments are (cons offset text). Consecutive comments stay together; a
;; blank source line between two comments, or between a comment and the next
;; item, is kept.
(define (line-of off) ((env-line-of (current-env)) off))
(define (comment-end c) (line-of (+ (car c) (string-length (cdr c)) 3)))

(define (comment-block cs)
  (let loop ([cs cs] [prev #f] [out '()])
    (cond
      [(null? cs) out]
      [else
       (define c (car cs))
       (define gap (and prev (> (- (line-of (car c)) (comment-end prev)) 1)))
       (loop (cdr cs) c (append out (if gap (list "") '()) (comment-lines (cdr c))))])))

(define (items-lines items comments)
  (let loop ([items items] [comments comments] [out '()])
    (cond
      [(null? items)
       (define tail (comment-block comments))
       (if (null? tail) out (append out (list "") tail))]
      [else
       (define it (car items))
       (define pos (item-pos it))
       (define-values (before after) (splitf-at comments (lambda (c) (< (car c) pos))))
       (define lines (item-lines it))
       (define cmt (comment-block before))
       (define gap (and (pair? before) (> (- (line-of pos) (comment-end (last before))) 1)))
       (define block (append cmt (if (and gap (pair? lines)) (list "") '()) lines))
       (loop (cdr items) (drop-inside after (next-pos items))
             (if (null? block) out
                 (append out (if (null? out) '() (list "")) block)))])))

;; comments inside the item just emitted are dropped
(define (drop-inside comments next)
  (if next (filter (lambda (c) (>= (car c) next)) comments) comments))
(define (next-pos items)
  (and (pair? (cdr items)) (item-pos (cadr items))))

;; `module M = struct ... end` followed by `include M` in the same file (as
;; fusion.ml does with Hol) is emitted inline.
(define (flatten-includes items)
  (define local-modules
    (for/list ([it items] #:when (t:module? it)) (t:module-name it)))
  (define included
    (for/list ([it items] #:when (and (t:include? it) (m:path? (t:include-m it))
                                      (member (m:path-name (t:include-m it)) local-modules)))
      (m:path-name (t:include-m it))))
  (append*
   (for/list ([it items])
     (match it
       [(t:module _ name '() (m:struct inner))
        #:when (member name included)
        (flatten-includes inner)]
       [(t:include _ (m:path name)) #:when (member name included) '()]
       [_ (list it)]))))

(define (item-pos it)
  (match it
    [(t:let p _ _) p] [(t:expr p _) p] [(t:type p _) p] [(t:exception p _ _) p]
    [(t:module p _ _ _) p] [(t:modtype p _) p] [(t:open p _) p] [(t:include p _) p]
    [(t:external p _) p] [(t:directive p _ _) p]))

;; -------------------------------------------------------------------------
;; Module
;; -------------------------------------------------------------------------

;; emit-module : items comments env header-lines -> (values body-lines exports)
(define (emit-module items0 comments e)
  (define items (flatten-includes items0))
  (define counts (make-hash))
  (for ([n (defined-names items)]) (hash-update! counts n add1 0))
  (define e* (struct-copy env e [records (collect-records items)] [counts counts]))
  (parameterize ([current-env e*] [scopes (list (scope (make-hash) counts))]
                 [namespaces (make-hash)] [locals (hash)])
    ;; the leading comments (banner) go before the imports
    (define first-pos (if (pair? items) (item-pos (car items)) +inf.0))
    (define-values (lead rest) (splitf-at comments (lambda (c) (< (car c) first-pos))))
    (define body (items-lines items rest))
    (define exports
      (remove-duplicates (append (map mangle-id (defined-names items))
                                 (for/list ([n (defined-names items)]
                                            #:when (hash-ref operator-aliases n #f))
                                   (hash-ref operator-aliases n))
                                 (declared-names items))))
    (values (comment-block lead)
            body
            exports)))
