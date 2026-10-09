#lang racket/base
;; Abstract syntax of the OCaml subset that HOL Light uses.
(provide (all-defined-out))

;; Expressions
(struct e:var (name) #:prefab)              ; value path, "List.map" or "x"
(struct e:const (kind value) #:prefab)      ; kind: 'int 'float 'string 'char
(struct e:constr (name arg) #:prefab)       ; constructor, arg or #f
(struct e:quote (text) #:prefab)            ; `...` quotation
(struct e:app (fn args) #:prefab)           ; f a b c
(struct e:infix (op a b) #:prefab)          ; a op b
(struct e:neg (op a) #:prefab)              ; -a, -.a
(struct e:prefix (op a) #:prefab)           ; !a, ~-a and other prefix operators
(struct e:tuple (items) #:prefab)
(struct e:list (items) #:prefab)            ; [a; b]
(struct e:cons (h t) #:prefab)              ; h :: t
(struct e:let (rec? bindings body) #:prefab)
(struct e:letopen (path body) #:prefab)
(struct e:letmodule (name module body) #:prefab)
(struct e:fun (params body) #:prefab)       ; fun p1 p2 -> body
(struct e:function (cases) #:prefab)
(struct e:match (scrut cases) #:prefab)
(struct e:try (body cases) #:prefab)
(struct e:if (c t e) #:prefab)              ; e is #f without else
(struct e:seq (a b) #:prefab)
(struct e:field (obj name) #:prefab)
(struct e:setfield (obj name v) #:prefab)
(struct e:index (obj idx kind) #:prefab)    ; kind: 'array .( ) or 'string .[ ]
(struct e:setindex (obj idx kind v) #:prefab)
(struct e:record (base fields) #:prefab)    ; fields: (list (cons name expr))
(struct e:array (items) #:prefab)
(struct e:typed (e ty) #:prefab)
(struct e:paren (e) #:prefab)               ; parentheses written in the source
(struct e:while (c body) #:prefab)
(struct e:for (v from dir to body) #:prefab)
(struct e:assert (e) #:prefab)
(struct e:lazy (e) #:prefab)
(struct e:opname (op) #:prefab)             ; (+), (o) as a value
(struct e:label (name e) #:prefab)          ; ~name:e

;; Patterns
(struct p:var (name) #:prefab)
(struct p:any () #:prefab)
(struct p:const (kind value) #:prefab)
(struct p:constr (name arg) #:prefab)
(struct p:tuple (items) #:prefab)
(struct p:list (items) #:prefab)
(struct p:cons (h t) #:prefab)
(struct p:or (a b) #:prefab)
(struct p:alias (p name) #:prefab)
(struct p:typed (p ty) #:prefab)
(struct p:record (fields) #:prefab)         ; (list (cons name pattern))
(struct p:range (a b) #:prefab)
(struct p:array (items) #:prefab)
(struct p:label (name p) #:prefab)          ; ~x, ?x, ?(x = default)

;; let binding: name/pattern, parameters, body
(struct binding (pat params body) #:prefab)
(struct mcase (pat guard body) #:prefab)

;; Types
(struct ty:var (name) #:prefab)
(struct ty:con (name args) #:prefab)
(struct ty:arrow (a b) #:prefab)
(struct ty:tuple (items) #:prefab)

;; Type declarations: kind is 'abstract, (ty:...) alias, (list 'variant ctors)
;; with ctors (list name arg-types), or (list 'record fields) with fields
;; (list mutable? name type).
(struct tydecl (name params kind) #:prefab)

;; Toplevel items, each with the source offset where it starts
(struct t:let (pos rec? bindings) #:prefab)
(struct t:expr (pos e) #:prefab)
(struct t:type (pos decls) #:prefab)
(struct t:exception (pos name args) #:prefab)
(struct t:module (pos name params body) #:prefab)   ; body: list of items or module path/app
(struct t:modtype (pos name) #:prefab)
(struct t:open (pos path) #:prefab)
(struct t:include (pos m) #:prefab)
(struct t:external (pos name) #:prefab)
(struct t:directive (pos name arg) #:prefab)

(struct m:path (name) #:prefab)             ; module expression: path
(struct m:app (f arg) #:prefab)             ; functor application
(struct m:struct (items) #:prefab)
(struct m:functor (param body) #:prefab)
