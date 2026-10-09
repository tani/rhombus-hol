#lang racket/base
;; LALR grammar for the OCaml subset HOL Light is written in. The structure
;; and the precedence table follow OCaml's own parser.mly; HOL Light's infix
;; words (pa_j: `expr: AFTER "<"`) form one left-associative level between
;; the comparison operators and `^`/`@`.
(require parser-tools/yacc
         parser-tools/lex
         racket/list
         racket/string
         "lexer.rkt"
         "ast.rkt")
(provide parse-ml parse-ml-file)

(define (off p) (position-offset p))
(define (path . xs) (string-join xs "."))

(define ml-parser
  (parser
   (src-pos)
   (debug "/tmp/claude-0/-home-user-rhombus-hol/f8cf9599-de7b-55a9-b575-ecf48a5fa2ba/scratchpad/yacc.txt")
   (start implementation)
   (end EOF)
   (tokens value-tokens punct-tokens)
   (error (lambda (ok? name val start end)
            (raise (exn:fail (format "parse error at offset ~a line ~a: unexpected ~a ~a"
                                     (position-offset start) (position-line start)
                                     name (or val ""))
                             (current-continuation-marks)))))
   (precs
    (nonassoc IN)
    (nonassoc below_SEMI)
    (nonassoc SEMI)
    (nonassoc LET)
    (nonassoc below_WITH)
    (nonassoc FUNCTION WITH)
    (nonassoc AND)
    (nonassoc THEN)
    (nonassoc ELSE)
    (nonassoc LESSMINUS)
    (right COLONEQUAL)
    (nonassoc AS)
    (left BAR)
    (nonassoc below_COMMA)
    (left COMMA)
    (right MINUSGREATER)
    (right OR BARBAR)
    (right AMPERSAND AMPERAMPER)
    (nonassoc below_EQUAL)
    (left INFIXOP0 EQUAL LESS GREATER)
    (left HOLINFIX)
    (right INFIXOP1)
    (right COLONCOLON)
    (left INFIXOP2 PLUS PLUSDOT MINUS MINUSDOT)
    (left INFIXOP3 STAR)
    (right INFIXOP4)
    (nonassoc prec_unary_minus)
    (nonassoc prec_constant_constructor)
    (nonassoc prec_constr_appl)
    (nonassoc below_SHARP)
    (nonassoc HASH)
    (nonassoc below_DOT)
    (nonassoc DOT)
    (nonassoc QUOTATION BANG BEGIN CHAR FALSE FLOAT INT LBRACE LBRACKET
              LBRACKETBAR LIDENT LPAREN NEW PREFIXOP STRING TRUE UIDENT TILDE QUESTION))
   (grammar
    (implementation
     [(structure) $1])
    ;; ---------------------------------------------------------------- items
    (structure
     [(structure_tail) $1]
     [(seq_expr structure_tail) (cons (t:expr (off $1-start-pos) $1) $2)])
    (structure_tail
     [() '()]
     [(SEMISEMI structure) $2]
     [(structure_item structure_tail) (cons $1 $2)]
     ;; camlp5 also takes an `assert` phrase without a preceding `;;`
     [(ASSERT simple_expr structure_tail) (cons (t:expr (off $1-start-pos) (e:assert $2)) $3)])
    (structure_item
     [(LET rec_flag let_bindings) (t:let (off $1-start-pos) $2 (reverse $3))]
     [(TYPE type_declarations) (t:type (off $1-start-pos) (reverse $2))]
     [(TYPE NONREC type_declarations) (t:type (off $1-start-pos) (reverse $3))]
     [(EXCEPTION UIDENT constructor_arguments) (t:exception (off $1-start-pos) $2 $3)]
     [(EXCEPTION UIDENT EQUAL mod_longident) (t:exception (off $1-start-pos) $2 '())]
     [(EXTERNAL val_ident COLON core_type EQUAL strings) (t:external (off $1-start-pos) $2)]
     [(MODULE UIDENT module_binding)
      (t:module (off $1-start-pos) $2 (car $3) (cdr $3))]
     [(MODULE TYPE ident EQUAL module_type) (t:modtype (off $1-start-pos) $3)]
     [(MODULE TYPE ident) (t:modtype (off $1-start-pos) $3)]
     [(OPEN mod_longident) (t:open (off $1-start-pos) $2)]
     [(INCLUDE module_expr) (t:include (off $1-start-pos) $2)]
     [(HASH LIDENT) (t:directive (off $1-start-pos) $2 #f)]
     [(HASH LIDENT simple_expr) (t:directive (off $1-start-pos) $2 $3)])
    (strings [(STRING) (list $1)] [(STRING strings) (cons $1 $2)])
    (module_binding
     [(EQUAL module_expr) (cons '() $2)]
     [(COLON module_type EQUAL module_expr) (cons '() $4)]
     [(LPAREN UIDENT COLON module_type RPAREN module_binding)
      (cons (cons $2 (car $6)) (cdr $6))])
    (module_expr
     [(mod_longident) (m:path $1)]
     [(STRUCT structure END) (m:struct $2)]
     [(FUNCTOR LPAREN UIDENT COLON module_type RPAREN MINUSGREATER module_expr)
      (m:functor $3 $8)]
     [(module_expr LPAREN module_expr RPAREN) (m:app $1 $3)]
     [(LPAREN module_expr RPAREN) $2]
     [(LPAREN module_expr COLON module_type RPAREN) $2])
    (module_type
     [(mod_longident) $1]
     [(SIG signature END) 'sig]
     [(module_type WITH with_constraints) $1]
     [(FUNCTOR LPAREN UIDENT COLON module_type RPAREN MINUSGREATER module_type) 'functor]
     [(LPAREN module_type RPAREN) $2])
    (with_constraints
     [(with_constraint) #f]
     [(with_constraints AND with_constraint) #f])
    (with_constraint
     [(TYPE type_parameters label_longident EQUAL core_type) #f]
     [(TYPE type_parameters label_longident COLONEQUAL core_type) #f]
     [(MODULE mod_longident EQUAL mod_longident) #f])
    (signature
     [() '()]
     [(signature signature_item) '()]
     [(signature SEMISEMI) '()])
    (signature_item
     [(VAL val_ident COLON core_type) #f]
     [(EXTERNAL val_ident COLON core_type EQUAL strings) #f]
     [(TYPE type_declarations) #f]
     [(EXCEPTION UIDENT constructor_arguments) #f]
     [(MODULE UIDENT COLON module_type) #f]
     [(MODULE TYPE ident EQUAL module_type) #f]
     [(MODULE TYPE ident) #f]
     [(OPEN mod_longident) #f]
     [(INCLUDE module_type) #f])
    (rec_flag [() #f] [(REC) #t] [(NONREC) #f])
    ;; ---------------------------------------------------------- expressions
    (seq_expr
     [(expr) (prec below_SEMI) $1]
     [(expr SEMI) $1]
     [(expr SEMI seq_expr) (e:seq $1 $3)])
    (expr
     [(simple_expr) (prec below_SHARP) $1]
     [(simple_expr simple_labeled_expr_list) (e:app $1 (reverse $2))]
     [(LET rec_flag let_bindings IN seq_expr) (e:let $2 (reverse $3) $5)]
     [(LET OPEN mod_longident IN seq_expr) (e:letopen $3 $5)]
     [(LET MODULE UIDENT module_binding IN seq_expr)
      (e:letmodule $3 (t:module (off $1-start-pos) $3 (car $4) (cdr $4)) $6)]
     [(FUNCTION opt_bar match_cases) (e:function (reverse $3))]
     [(FUN labeled_simple_pattern fun_def)
      (e:fun (cons $2 (car $3)) (cdr $3))]
     ;; camlp5 accepts an unparenthesised tuple: fun x,y -> e
     [(FUN pattern_comma_list MINUSGREATER seq_expr)
      (e:fun (list (p:tuple (reverse $2))) $4)]
     [(MATCH seq_expr WITH opt_bar match_cases) (e:match $2 (reverse $5))]
     [(TRY seq_expr WITH opt_bar match_cases) (e:try $2 (reverse $5))]
     [(expr_comma_list) (prec below_COMMA) (e:tuple (reverse $1))]
     [(constr_longident simple_expr) (prec below_SHARP) (e:constr $1 $2)]
     [(IF seq_expr THEN expr ELSE expr) (e:if $2 $4 $6)]
     [(IF seq_expr THEN expr) (e:if $2 $4 #f)]
     [(WHILE seq_expr DO seq_expr DONE) (e:while $2 $4)]
     [(FOR pattern EQUAL seq_expr TO seq_expr DO seq_expr DONE) (e:for $2 $4 'to $6 $8)]
     [(FOR pattern EQUAL seq_expr DOWNTO seq_expr DO seq_expr DONE) (e:for $2 $4 'downto $6 $8)]
     [(expr COLONCOLON expr) (e:cons $1 $3)]
     [(expr INFIXOP0 expr) (e:infix $2 $1 $3)]
     [(expr INFIXOP1 expr) (e:infix $2 $1 $3)]
     [(expr INFIXOP2 expr) (e:infix $2 $1 $3)]
     [(expr INFIXOP3 expr) (e:infix $2 $1 $3)]
     [(expr INFIXOP4 expr) (e:infix $2 $1 $3)]
     [(expr HOLINFIX expr) (e:infix $2 $1 $3)]
     [(expr PLUS expr) (e:infix "+" $1 $3)]
     [(expr PLUSDOT expr) (e:infix "+." $1 $3)]
     [(expr MINUS expr) (e:infix "-" $1 $3)]
     [(expr MINUSDOT expr) (e:infix "-." $1 $3)]
     [(expr STAR expr) (e:infix "*" $1 $3)]
     [(expr EQUAL expr) (e:infix "=" $1 $3)]
     [(expr LESS expr) (e:infix "<" $1 $3)]
     [(expr GREATER expr) (e:infix ">" $1 $3)]
     [(expr OR expr) (e:infix "||" $1 $3)]
     [(expr BARBAR expr) (e:infix "||" $1 $3)]
     [(expr AMPERSAND expr) (e:infix "&&" $1 $3)]
     [(expr AMPERAMPER expr) (e:infix "&&" $1 $3)]
     [(expr COLONEQUAL expr) (e:infix ":=" $1 $3)]
     [(MINUS expr) (prec prec_unary_minus) (e:neg "-" $2)]
     [(MINUSDOT expr) (prec prec_unary_minus) (e:neg "-." $2)]
     [(simple_expr DOT label_longident LESSMINUS expr) (e:setfield $1 $3 $5)]
     [(simple_expr DOT LPAREN seq_expr RPAREN LESSMINUS expr) (e:setindex $1 $4 'array $7)]
     [(simple_expr DOT LBRACKET seq_expr RBRACKET LESSMINUS expr) (e:setindex $1 $4 'string $7)]
     [(ASSERT simple_expr) (prec below_SHARP) (e:assert $2)]
     [(LAZY simple_expr) (prec below_SHARP) (e:lazy $2)])
    (simple_expr
     [(val_longident) (e:var $1)]
     [(constant) $1]
     [(QUOTATION) (e:quote $1)]
     [(constr_longident) (prec prec_constant_constructor) (e:constr $1 #f)]
     [(LPAREN seq_expr RPAREN) (e:paren $2)]
     [(BEGIN seq_expr END) (e:paren $2)]
     [(BEGIN END) (e:constr "()" #f)]
     [(LPAREN seq_expr type_constraint RPAREN) (e:typed $2 $3)]
     [(simple_expr DOT label_longident) (e:field $1 $3)]
     [(simple_expr DOT LPAREN seq_expr RPAREN) (e:index $1 $4 'array)]
     [(simple_expr DOT LBRACKET seq_expr RBRACKET) (e:index $1 $4 'string)]
     [(mod_longident DOT LPAREN seq_expr RPAREN) (e:letopen $1 $4)]
     [(LBRACE record_expr RBRACE) $2]
     [(LBRACKETBAR expr_semi_list opt_semi BARRBRACKET) (e:array (reverse $2))]
     [(LBRACKETBAR BARRBRACKET) (e:array '())]
     [(LBRACKET expr_semi_list opt_semi RBRACKET) (e:list (reverse $2))]
     [(PREFIXOP simple_expr) (e:prefix $1 $2)]
     [(BANG simple_expr) (e:prefix "!" $2)])
    (simple_labeled_expr_list
     [(labeled_simple_expr) (list $1)]
     [(simple_labeled_expr_list labeled_simple_expr) (cons $2 $1)])
    (labeled_simple_expr
     [(simple_expr) (prec below_SHARP) $1]
     [(TILDE LIDENT) (e:label $2 (e:var $2))]
     [(TILDE LIDENT COLON simple_expr) (e:label $2 $4)]
     [(QUESTION LIDENT) (e:label $2 (e:var $2))])
    (let_bindings
     [(let_binding) (list $1)]
     [(let_bindings AND let_binding) (cons $3 $1)])
    (let_binding
     [(val_ident fun_binding) (binding (p:var $1) (car $2) (cdr $2))]
     [(pattern EQUAL seq_expr) (binding $1 '() $3)])
    (fun_binding
     [(strict_binding) $1]
     [(type_constraint EQUAL seq_expr) (cons '() $3)])
    (strict_binding
     [(EQUAL seq_expr) (cons '() $2)]
     [(labeled_simple_pattern fun_binding) (cons (cons $1 (car $2)) (cdr $2))])
    (match_cases
     [(match_case) (list $1)]
     [(match_cases BAR match_case) (cons $3 $1)])
    (match_case
     [(pattern MINUSGREATER seq_expr) (mcase $1 #f $3)]
     [(pattern WHEN seq_expr MINUSGREATER seq_expr) (mcase $1 $3 $5)])
    (fun_def
     [(MINUSGREATER seq_expr) (cons '() $2)]
     [(COLON simple_core_type MINUSGREATER seq_expr) (cons '() $4)]
     [(labeled_simple_pattern fun_def) (cons (cons $1 (car $2)) (cdr $2))])
    (expr_comma_list
     [(expr_comma_list COMMA expr) (cons $3 $1)]
     [(expr COMMA expr) (list $3 $1)])
    (record_expr
     [(simple_expr WITH lbl_expr_list) (e:record $1 $3)]
     [(lbl_expr_list) (e:record #f $1)])
    (lbl_expr_list
     [(lbl_expr) (list $1)]
     [(lbl_expr SEMI lbl_expr_list) (cons $1 $3)]
     [(lbl_expr SEMI) (list $1)])
    (lbl_expr
     [(label_longident EQUAL expr) (cons $1 $3)]
     [(label_longident) (cons $1 (e:var $1))])
    (expr_semi_list
     [(expr) (list $1)]
     [(expr_semi_list SEMI expr) (cons $3 $1)])
    (type_constraint
     [(COLON core_type) $2]
     [(COLON core_type COLON GREATER core_type) $2])
    (opt_bar [() #f] [(BAR) #f])
    (opt_semi [() #f] [(SEMI) #f])
    (constant
     [(INT) (e:const 'int $1)]
     [(FLOAT) (e:const 'float $1)]
     [(STRING) (e:const 'string $1)]
     [(CHAR) (e:const 'char $1)])
    (signed_constant
     [(INT) (p:const 'int $1)]
     [(FLOAT) (p:const 'float $1)]
     [(STRING) (p:const 'string $1)]
     [(CHAR) (p:const 'char $1)]
     [(MINUS INT) (p:const 'int (string-append "-" $2))]
     [(MINUS FLOAT) (p:const 'float (string-append "-" $2))])
    ;; ------------------------------------------------------------ patterns
    (labeled_simple_pattern
     [(simple_pattern) $1]
     [(TILDE LIDENT) (p:label $2 (p:var $2))]
     [(TILDE LPAREN LIDENT RPAREN) (p:label $3 (p:var $3))]
     [(TILDE LIDENT COLON simple_pattern) (p:label $2 $4)]
     [(QUESTION LIDENT) (p:label $2 (p:var $2))]
     [(QUESTION LPAREN LIDENT EQUAL seq_expr RPAREN) (p:label $3 (p:var $3))])
    (pattern
     [(simple_pattern) $1]
     [(pattern AS val_ident) (p:alias $1 $3)]
     [(pattern_comma_list) (prec below_COMMA) (p:tuple (reverse $1))]
     [(constr_longident pattern) (prec prec_constr_appl) (p:constr $1 $2)]
     [(pattern COLONCOLON pattern) (p:cons $1 $3)]
     [(pattern BAR pattern) (p:or $1 $3)])
    (pattern_comma_list
     [(pattern_comma_list COMMA pattern) (cons $3 $1)]
     [(pattern COMMA pattern) (list $3 $1)])
    (simple_pattern
     [(val_ident) (prec below_EQUAL) (p:var $1)]
     [(UNDERSCORE) (p:any)]
     [(signed_constant) $1]
     [(CHAR DOTDOT CHAR) (p:range $1 $3)]
     [(constr_longident) (p:constr $1 #f)]
     [(LBRACE lbl_pattern_list RBRACE) (p:record $2)]
     [(LBRACKET pattern_semi_list opt_semi RBRACKET) (p:list (reverse $2))]
     [(LBRACKETBAR pattern_semi_list opt_semi BARRBRACKET) (p:array (reverse $2))]
     [(LBRACKETBAR BARRBRACKET) (p:array '())]
     [(LPAREN pattern RPAREN) $2]
     [(LPAREN pattern COLON core_type RPAREN) (p:typed $2 $4)])
    (pattern_semi_list
     [(pattern) (list $1)]
     [(pattern_semi_list SEMI pattern) (cons $3 $1)])
    (lbl_pattern_list
     [(lbl_pattern) (list $1)]
     [(lbl_pattern SEMI) (list $1)]
     [(lbl_pattern SEMI UNDERSCORE) (list $1)]
     [(lbl_pattern SEMI UNDERSCORE SEMI) (list $1)]
     [(lbl_pattern SEMI lbl_pattern_list) (cons $1 $3)])
    (lbl_pattern
     [(label_longident EQUAL pattern) (cons $1 $3)]
     [(label_longident) (cons $1 (p:var $1))])
    ;; --------------------------------------------------------------- types
    (type_declarations
     [(type_declaration) (list $1)]
     [(type_declarations AND type_declaration) (cons $3 $1)])
    (type_declaration
     [(type_parameters LIDENT type_kind) (tydecl $2 $1 $3)])
    (type_parameters
     [() '()]
     [(type_parameter) (list $1)]
     [(LPAREN type_parameter_list RPAREN) (reverse $2)])
    (type_parameter
     [(QUOTE ident) $2]
     [(PLUS QUOTE ident) $3]
     [(MINUS QUOTE ident) $3])
    (type_parameter_list
     [(type_parameter) (list $1)]
     [(type_parameter_list COMMA type_parameter) (cons $3 $1)])
    (type_kind
     [() 'abstract]
     [(EQUAL core_type) $2]
     [(EQUAL PRIVATE core_type) $3]
     [(EQUAL constructor_declarations) (list 'variant (reverse $2))]
     [(EQUAL BAR constructor_declarations) (list 'variant (reverse $3))]
     [(EQUAL PRIVATE constructor_declarations) (list 'variant (reverse $3))]
     [(EQUAL PRIVATE BAR constructor_declarations) (list 'variant (reverse $4))]
     [(EQUAL LBRACE label_declarations opt_semi RBRACE) (list 'record (reverse $3))]
     [(EQUAL core_type EQUAL opt_bar constructor_declarations) (list 'variant (reverse $5))]
     [(EQUAL core_type EQUAL LBRACE label_declarations opt_semi RBRACE) (list 'record (reverse $5))])
    (constructor_declarations
     [(constructor_declaration) (list $1)]
     [(constructor_declarations BAR constructor_declaration) (cons $3 $1)])
    (constructor_declaration
     [(constr_ident constructor_arguments) (list $1 $2)])
    (constr_ident
     [(UIDENT) $1]
     [(LPAREN RPAREN) "()"]
     [(LPAREN COLONCOLON RPAREN) "::"]
     [(FALSE) "false"]
     [(TRUE) "true"])
    (constructor_arguments
     [() '()]
     [(OF core_type_list) (reverse $2)])
    (label_declarations
     [(label_declaration) (list $1)]
     [(label_declarations SEMI label_declaration) (cons $3 $1)])
    (label_declaration
     [(mutable_flag LIDENT COLON core_type) (list $1 $2 $4)])
    (mutable_flag [() #f] [(MUTABLE) #t])
    (core_type
     [(core_type2) $1]
     [(core_type2 AS QUOTE ident) $1])
    (core_type2
     [(simple_core_type_or_tuple) $1]
     [(core_type2 MINUSGREATER core_type2) (ty:arrow $1 $3)]
     [(LIDENT COLON core_type2 MINUSGREATER core_type2) (ty:arrow $3 $5)]
     [(QUESTION LIDENT COLON core_type2 MINUSGREATER core_type2) (ty:arrow $4 $6)])
    (simple_core_type_or_tuple
     [(simple_core_type) $1]
     [(simple_core_type STAR core_type_list) (ty:tuple (cons $1 (reverse $3)))])
    (core_type_list
     [(simple_core_type) (list $1)]
     [(core_type_list STAR simple_core_type) (cons $3 $1)])
    (simple_core_type
     [(simple_core_type2) (prec below_SHARP) $1]
     [(LPAREN core_type_comma_list RPAREN) (prec below_SHARP)
      (if (= (length $2) 1) (car $2) (ty:tuple (reverse $2)))])
    (simple_core_type2
     [(QUOTE ident) (ty:var $2)]
     [(UNDERSCORE) (ty:var "_")]
     [(type_longident) (ty:con $1 '())]
     [(simple_core_type2 type_longident) (ty:con $2 (list $1))]
     [(LPAREN core_type_comma_list RPAREN type_longident) (ty:con $4 (reverse $2))])
    (core_type_comma_list
     [(core_type) (list $1)]
     [(core_type_comma_list COMMA core_type) (cons $3 $1)])
    ;; --------------------------------------------------------------- names
    (ident [(UIDENT) $1] [(LIDENT) $1])
    (val_ident
     [(LIDENT) $1]
     [(LPAREN operator RPAREN) (string-append "(" $2 ")")])
    (operator
     [(PREFIXOP) $1] [(INFIXOP0) $1] [(INFIXOP1) $1] [(INFIXOP2) $1]
     [(INFIXOP3) $1] [(INFIXOP4) $1] [(HOLINFIX) $1] [(BANG) "!"]
     [(PLUS) "+"] [(PLUSDOT) "+."] [(MINUS) "-"] [(MINUSDOT) "-."]
     [(STAR) "*"] [(EQUAL) "="] [(LESS) "<"] [(GREATER) ">"] [(OR) "or"]
     [(BARBAR) "||"] [(AMPERSAND) "&"] [(AMPERAMPER) "&&"]
     [(COLONEQUAL) ":="] [(COLONCOLON) "::"])
    (val_longident
     [(val_ident) $1]
     [(mod_longident DOT LIDENT) (path $1 $3)])
    (constr_longident
     [(mod_longident) (prec below_DOT) $1]
     [(LBRACKET RBRACKET) "[]"]
     [(LPAREN RPAREN) "()"]
     [(FALSE) "false"]
     [(TRUE) "true"])
    (mod_longident
     [(UIDENT) $1]
     [(mod_longident DOT UIDENT) (path $1 $3)])
    (label_longident
     [(LIDENT) $1]
     [(mod_longident DOT LIDENT) (path $1 $3)])
    (type_longident
     [(LIDENT) $1]
     [(mod_longident DOT LIDENT) (path $1 $3)]))))

;; parse-ml : input-port -> (values items comments)
;; With #:jrh #f the plain OCaml identifier rule applies, as for files that
;; HOL Light compiles with ocamlc rather than loading through pa_j.
(define (parse-ml in #:jrh [jrh #t])
  (port-count-lines! in)
  (define sink (box '()))
  (define items
    (parameterize ([comment-sink sink] [jrh-lexer (box jrh)])
      (ml-parser (lambda () (ml-lexer in)))))
  (values items (reverse (unbox sink))))

;; parse-ml-file : path -> (values items comments jrh?)
;; Tries pa_j's lexer first and plain OCaml lexing if that fails.
(define (parse-ml-file f)
  (with-handlers ([exn:fail?
                   (lambda (e)
                     (with-handlers ([exn:fail? (lambda (_) (raise e))])
                       (define-values (items comments)
                         (call-with-input-file f (lambda (in) (parse-ml in #:jrh #f))))
                       (values items comments #f)))])
    (define-values (items comments) (call-with-input-file f parse-ml))
    (values items comments #t)))
