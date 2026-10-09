#lang racket/base
;; Lexer for the OCaml dialect of HOL Light, as read by camlp5 with HOL
;; Light's pa_j extension: `...` quotations, the JRH identifier rule (a
;; capital followed only by lower-case characters is a constructor, any
;; other capitalised name is a value), and the infix words o, upto, F_F,
;; THEN, THENL, ORELSE, THENC, ORELSEC, THEN_TCL and ORELSE_TCL.
(require racket/string
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre))
(provide value-tokens punct-tokens ml-lexer comment-sink jrh-lexer)

(define-tokens value-tokens
  (LIDENT UIDENT INT FLOAT STRING CHAR QUOTATION HOLINFIX
   INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4 PREFIXOP))

(define-empty-tokens punct-tokens
  (EOF AND AS ASSERT BEGIN CLASS CONSTRAINT DO DONE DOWNTO ELSE END EXCEPTION
   EXTERNAL FALSE FOR FUN FUNCTION FUNCTOR IF IN INCLUDE INHERIT INITIALIZER
   LAZY LET MATCH METHOD MODULE MUTABLE NEW NONREC OBJECT OF OPEN OR PRIVATE
   REC SIG STRUCT THEN TO TRUE TRY TYPE VAL VIRTUAL WHEN WHILE WITH
   AMPERAMPER AMPERSAND BANG BAR BARBAR BARRBRACKET COLON COLONCOLON
   COLONEQUAL COMMA DOT DOTDOT EQUAL GREATER HASH LBRACE LBRACKET
   LBRACKETBAR LESS LESSMINUS LPAREN MINUS MINUSDOT MINUSGREATER PLUS
   PLUSDOT QUESTION QUOTE RBRACE RBRACKET RPAREN SEMI SEMISEMI STAR TILDE
   UNDERSCORE
   ;; precedence-only pseudo tokens
   below_SEMI below_WITH below_COMMA below_EQUAL below_SHARP below_DOT
   prec_unary_minus prec_constant_constructor prec_constr_appl))

;; Comments are not tokens; they are collected here, with their start
;; offsets, so the emitter can place them between definitions.
(define comment-sink (make-parameter (box '())))

(define jrh-lexer (make-parameter (box #t)))

(define keywords
  (hash "and" token-AND "as" token-AS "assert" token-ASSERT "begin" token-BEGIN
        "class" token-CLASS "constraint" token-CONSTRAINT "do" token-DO
        "done" token-DONE "downto" token-DOWNTO "else" token-ELSE "end" token-END
        "exception" token-EXCEPTION "external" token-EXTERNAL "false" token-FALSE
        "for" token-FOR "fun" token-FUN "function" token-FUNCTION
        "functor" token-FUNCTOR "if" token-IF "in" token-IN "include" token-INCLUDE
        "inherit" token-INHERIT "initializer" token-INITIALIZER "lazy" token-LAZY
        "let" token-LET "match" token-MATCH "method" token-METHOD
        "module" token-MODULE "mutable" token-MUTABLE "new" token-NEW
        "nonrec" token-NONREC "object" token-OBJECT "of" token-OF "open" token-OPEN
        "or" token-OR "private" token-PRIVATE "rec" token-REC "sig" token-SIG
        "struct" token-STRUCT "then" token-THEN "to" token-TO "true" token-TRUE
        "try" token-TRY "type" token-TYPE "val" token-VAL "virtual" token-VIRTUAL
        "when" token-WHEN "while" token-WHILE "with" token-WITH))

(define hol-infixes
  '("o" "upto" "F_F" "THENC" "THEN" "THENL" "ORELSE" "ORELSEC" "THEN_TCL" "ORELSE_TCL"))

(define (classify-ident s)
  (cond
    ;; pa_j's switches for its own identifier rule read as true/false
    [(string=? s "unset_jrh_lexer") (set-box! (jrh-lexer) #f) (token-FALSE)]
    [(string=? s "set_jrh_lexer") (set-box! (jrh-lexer) #t) (token-TRUE)]
    [(hash-ref keywords s #f) => (lambda (k) (k))]
    [(member s hol-infixes) (token-HOLINFIX s)]
    [(member s '("mod" "land" "lor" "lxor")) (token-INFIXOP3 s)]
    [(member s '("lsl" "lsr" "asr")) (token-INFIXOP4 s)]
    [(string=? s "_") (token-UNDERSCORE)]
    ;; pa_j's jrh_identifier: upper-case first letter and an only-lower-case
    ;; rest make a constructor (UIDENT), every other identifier is a value.
    [(and (not (unbox (jrh-lexer))) (char-upper-case? (string-ref s 0)))
     (token-UIDENT s)]
    [(and (char-upper-case? (string-ref s 0))
          (let ([rest (substring s 1)])
            (and (string=? (string-downcase rest) rest)
                 (not (string=? (string-upcase rest) rest)))))
     (token-UIDENT s)]
    [else (token-LIDENT s)]))

(define (classify-op s)
  (case s
    [("=") (token-EQUAL)] [("<") (token-LESS)] [(">") (token-GREATER)]
    [("|") (token-BAR)] [("||") (token-BARBAR)] [("&") (token-AMPERSAND)]
    [("&&") (token-AMPERAMPER)] [("->") (token-MINUSGREATER)]
    [("<-") (token-LESSMINUS)] [("*") (token-STAR)] [("+") (token-PLUS)]
    [("-") (token-MINUS)] [("+.") (token-PLUSDOT)] [("-.") (token-MINUSDOT)]
    [else
     (define c (string-ref s 0))
     (cond
       [(and (char=? c #\*) (> (string-length s) 1) (char=? (string-ref s 1) #\*))
        (token-INFIXOP4 s)]
       [(memv c '(#\* #\/ #\%)) (token-INFIXOP3 s)]
       [(memv c '(#\+ #\-)) (token-INFIXOP2 s)]
       [(memv c '(#\@ #\^)) (token-INFIXOP1 s)]
       [else (token-INFIXOP0 s)])]))

;; Nested comments; strings inside comments are skipped as OCaml does.
(define (read-comment port start)
  (define out (open-output-string))
  (let loop ([depth 1])
    (define c (read-char port))
    (cond
      [(eof-object? c) (error 'ml-lexer "unterminated comment at ~a" start)]
      [(and (char=? c #\*) (eqv? (peek-char port) #\)))
       (read-char port)
       (if (= depth 1) (void) (begin (write-string "*)" out) (loop (sub1 depth))))]
      [(and (char=? c #\() (eqv? (peek-char port) #\*))
       (read-char port) (write-string "(*" out) (loop (add1 depth))]
      ;; a character literal such as '"' does not open a string
      [(and (char=? c #\') (let ([n (peek-string 3 0 port)])
                              (and (string? n)
                                   (or (and (>= (string-length n) 2) (char=? (string-ref n 1) #\'))
                                       (and (= (string-length n) 3) (char=? (string-ref n 0) #\\)
                                            (char=? (string-ref n 2) #\'))))))
       (define n (peek-string 3 0 port))
       (write-char c out)
       (write-string (read-string (if (char=? (string-ref n 1) #\') 2 3) port) out)
       (loop depth)]
      [(char=? c #\")
       (write-char c out)
       (let sloop ()
         (define d (read-char port))
         (cond [(eof-object? d) (void)]
               [(char=? d #\\) (write-char d out) (write-char (read-char port) out) (sloop)]
               [(char=? d #\") (write-char d out)]
               [else (write-char d out) (sloop)]))
       (loop depth)]
      [else (write-char c out) (loop depth)]))
  (get-output-string out))

;; OCaml string literal body (after the opening quote) -> the string value.
(define (read-string-literal port)
  (define out (open-output-string))
  (let loop ()
    (define c (read-char port))
    (cond
      [(eof-object? c) (error 'ml-lexer "unterminated string")]
      [(char=? c #\") (void)]
      [(char=? c #\\)
       (define d (read-char port))
       (case d
         [(#\n) (write-char #\newline out)] [(#\t) (write-char #\tab out)]
         [(#\r) (write-char #\return out)] [(#\b) (write-char #\backspace out)]
         [(#\space) (write-char #\space out)]
         [(#\newline)                       ; line continuation
          (let skip () (when (memv (peek-char port) '(#\space #\tab)) (read-char port) (skip)))]
         [(#\x) (write-char (integer->char (string->number (string (read-char port) (read-char port)) 16)) out)]
         [(#\o) (write-char (integer->char (string->number (string (read-char port) (read-char port) (read-char port)) 8)) out)]
         [else
          (if (char-numeric? d)
              (write-char (integer->char (string->number (string d (read-char port) (read-char port)))) out)
              (write-char d out))])
       (loop)]
      [else (write-char c out) (loop)]))
  (get-output-string out))

(define (read-quotation port)
  (define out (open-output-string))
  (let loop ()
    (define c (read-char port))
    (cond [(eof-object? c) (error 'ml-lexer "unterminated quotation")]
          [(char=? c #\`) (void)]
          [else (write-char c out) (loop)]))
  (get-output-string out))

(define (char-literal s)
  ;; s includes the quotes
  (define body (substring s 1 (sub1 (string-length s))))
  (if (char=? (string-ref body 0) #\\)
      (read-string-literal (open-input-string (string-append body "\"")))
      body))

(define-lex-abbrevs
  [lower (:/ #\a #\z)] [upper (:/ #\A #\Z)] [digit (:/ #\0 #\9)]
  [identchar (:or lower upper digit #\_ #\')]
  [ident (:: (:or lower upper #\_) (:* identchar))]
  [core-op (:or #\$ #\& #\* #\+ #\- #\/ #\= #\> #\@ #\^ #\|)]
  [op-char (:or #\~ #\! #\? core-op #\% #\< #\: #\.)]
  [decimal (:: digit (:* (:or digit #\_)))]
  [int-lit (:: (:or decimal
                    (:: #\0 (:or #\x #\X) (:+ (:or digit (:/ #\a #\f) (:/ #\A #\F) #\_)))
                    (:: #\0 (:or #\o #\O) (:+ (:or (:/ #\0 #\7) #\_)))
                    (:: #\0 (:or #\b #\B) (:+ (:or #\0 #\1 #\_))))
               (:? (:or #\l #\L #\n)))]
  [float-lit (:or (:: decimal #\. (:* (:or digit #\_)) (:? (:: (:or #\e #\E) (:? (:or #\+ #\-)) decimal)))
                  (:: decimal (:or #\e #\E) (:? (:or #\+ #\-)) decimal))]
  [char-lit (:or (:: #\' (:~ #\\ #\' #\newline) #\')
                 (:: #\' #\\ (:or #\\ #\' #\" #\n #\t #\b #\r #\space) #\')
                 (:: #\' #\\ digit digit digit #\')
                 (:: #\' #\\ #\x (:or digit (:/ #\a #\f) (:/ #\A #\F)) (:or digit (:/ #\a #\f) (:/ #\A #\F)) #\'))])

(define ml-lexer
  (lexer-src-pos
   [(eof) (token-EOF)]
   [(:+ (:or #\space #\tab #\newline #\return #\page)) (return-without-pos (ml-lexer input-port))]
   ["(*" (let ([text (read-comment input-port (position-offset start-pos))])
           (define sink (comment-sink))
           (set-box! sink (cons (cons (position-offset start-pos) text) (unbox sink)))
           (return-without-pos (ml-lexer input-port)))]
   [#\" (token-STRING (read-string-literal input-port))]
   [#\` (token-QUOTATION (read-quotation input-port))]
   [char-lit (token-CHAR (char-literal lexeme))]
   [#\' (token-QUOTE)]
   [float-lit (token-FLOAT lexeme)]
   [int-lit (token-INT lexeme)]
   [ident (classify-ident lexeme)]
   ["(" (token-LPAREN)] [")" (token-RPAREN)]
   ["[|" (token-LBRACKETBAR)] ["|]" (token-BARRBRACKET)]
   ["[" (token-LBRACKET)] ["]" (token-RBRACKET)]
   ["{" (token-LBRACE)] ["}" (token-RBRACE)]
   ["," (token-COMMA)] [";" (token-SEMI)] [";;" (token-SEMISEMI)]
   ["." (token-DOT)] [".." (token-DOTDOT)]
   [":" (token-COLON)] ["::" (token-COLONCOLON)] [":=" (token-COLONEQUAL)]
   ["#" (token-HASH)]
   ["!" (token-BANG)]
   ["!=" (token-INFIXOP0 "!=")]
   [(:: #\! (:+ op-char)) (token-PREFIXOP lexeme)]
   [(:: (:or #\~ #\?) (:+ op-char)) (token-PREFIXOP lexeme)]
   ["~" (token-TILDE)] ["?" (token-QUESTION)]
   [(:: (:or core-op #\% #\<) (:* op-char)) (classify-op lexeme)]))
