#lang eopl
; lang : Simple Module

;lang : concrete & abstract syntax tree
;----------------------------------------------------
;concrete syntax tree:


;Program :: = {ModuleDef}* Expression


;ModuleDef :: = module Identifer interface Interface body ModuleBody

;Interface :: = [ {Declare}* ]
;Declare :: = Indentifer : Type

;ModuleBody :: = [ {Definition}* ]
;Definition :: = Identifer = Expression

;Expression :: = Number
;              | -(Expression, Expression)
;              | zero? (Expression)
;              | if Expression then Expression else Expression
;              | Identifer
;              | let Identifer = Expression in Expression
;              | proc (Idenfifer : Type) Expression
;              | (Expression Expression)
;              | from Identifer take Identifer

;Type :: = Int
;        | Bool
;        | (Type -> Type)


; abstract syntax tree
(define-datatype program program?
  (a-program (a-program1 (list-of moduleDef?)) (a-program2 expression?)))

(define-datatype moduleDef moduleDef?
  (a-module-def (a-module-def3 symbol?) (a-module-def4 interface?) (a-module-def5 moduleBody?)))

(define-datatype interface interface?
  (a-interface (a-interface6 (list-of declear?))))

(define-datatype declear declear?
  (a-declear (a-declear7 symbol?) (a-declear8 type?)))

(define-datatype moduleBody moduleBody?
  (a-module-body (a-module-body9 (list-of definition?))))

(define-datatype definition definition?
  (a-definition (a-definition10 symbol?) (a-definition11 expression?)))

(define-datatype expression expression?
   (const-exp (const-exp12 number?))
   (diff-exp (diff-exp13 expression?) (diff-exp14 expression?))
   (zero?-exp (zero?-exp15 expression?))
   (if-exp (if-exp16 expression?) (if-exp17 expression?) (if-exp18 expression?))
   (var-exp (var-exp19 symbol?))
   (let-exp (let-exp20 symbol?) (let-exp21 expression?) (let-exp22 expression?))
   (proc-exp (proc-exp23 symbol?) (proc-exp24 type?) (proc-exp25 expression?))
   (call-exp (call-exp26 expression?) (call-exp27 expression?))
   (qulified-var-exp (qulified-var-exp28 symbol?) (qulified-var-exp29 symbol?)))

(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type (proc-type30 type?) (proc-type31 type?)))





; scan&parse
;----------------------------------------------------
(define scanner-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifer (letter (arbno (or letter digit "-" "_" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))
;   (class (regexp) action)
; string (keyword) from parser-spec (eg: "-","if","let","=",...) has a higher priority than regexp in scanner-spec.


(define parser-spec
 '((program ((arbno moduleDef) expression) a-program)
   (moduleDef ("module" identifer "interface" interface "body" moduleBody) a-module-def)
   (interface ("[" (arbno declear) "]") a-interface)
   (declear (identifer ":" type) a-declear)
   (moduleBody ("[" (arbno definition) "]") a-module-body)
   (definition (identifer "=" expression) a-definition)
   (expression (number) const-exp)
   (expression ("-" "(" expression "," expression ")") diff-exp)
   (expression ("zero?" "(" expression ")") zero?-exp)
   (expression ("if" expression "then" expression "else" expression) if-exp)
   (expression (identifer) var-exp)
   (expression ("let" identifer "=" expression "in" expression) let-exp)
   (expression ("proc" "(" identifer ":" type ")" expression) proc-exp)
   (expression ("(" expression expression ")") call-exp)
   (expression ("from" identifer "take" identifer) qulified-var-exp)
   (type ("int") int-type)
   (type ("bool") bool-type)
   (type ("(" type "->" type ")") proc-type)))
;  (algebric-data-type (concrete-syntax-with-class/string/ADT) constructor)
; class/string : terminator
; ADT : nonterminator


; scan&parse : string -> program
(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))








; type checker
;==================================================================================
;==================================================================================

; type environment
;----------------------------------------------------
(define-datatype tenv tenv?
  (empty-tenv)
  (extend-tenv (var symbol?)
               (ty type?) ; !!! tenv store types of var
               (e tenv?)))

; init-tenv
(define init-tenv
     (extend-tenv
      'i (int-type)
      (extend-tenv
       'v (int-type)
       (extend-tenv
        'x (int-type)
        (empty-tenv)))))


; apply-tenv : symbol * tenv -> type
(define apply-tenv
  (lambda (var en)
    (cases tenv en
      (empty-tenv  () (eopl:error "apply-tenv : Unbound variable : ~s" var))
      (extend-tenv (v ty e)
                   (if (equal? v var)
                       ty
                       (apply-tenv var e))))))





; type checker
;----------------------------------------------------
; the access control of module is realised by type checker, well typed
; programs should not contain codes that try to access bindings that do not appear
; in the interface (aka: private var). So the env for eval do not need to store the interface.


; auxiliary function:
; check-equal-type! : type * type * exp -> Unspec
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (if (not (equal? ty1 ty2))
        (eopl:error "types didn't match: " (type-to-external-form ty1) "!=" (type-to-external-form ty2) "in" exp)
        '())))


; to make the output type easy to read, we define these function
;type-to-external-form : ty -> list
(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type (arg-ty res-ty)
                 (list (type-to-external-form arg-ty)
                       '->
                       (type-to-external-form res-ty))))))


;type-of : exp * tenv -> type
(define type-of
  (lambda (exp tenv)
    (cases expression exp
      (const-exp (num) (int-type))
      (var-exp (var) (apply-tenv var tenv))
      (diff-exp (exp1 exp2) (let ((ty1 (type-of exp1 tenv))
                                  (ty2 (type-of exp2 tenv)))
                              (begin (check-equal-type! ty1 (int-type) exp1)
                                     (check-equal-type! ty2 (int-type) exp2)
                                     (int-type))))
      (zero?-exp (exp) (let ((ty (type-of exp tenv)))
                         (begin (check-equal-type! ty (int-type) exp)
                                (bool-type))))
      (if-exp (exp1 exp2 exp3) (let ((ty1 (type-of exp1 tenv))
                                     (ty2 (type-of exp2 tenv))
                                     (ty3 (type-of exp3 tenv)))
                                 (begin (check-equal-type! ty1 (bool-type) exp1)
                                        (check-equal-type! ty2 ty3 exp)
                                        ty2)))
      (let-exp (var exp1 body) (type-of body (extend-tenv var
                                                         (type-of exp1 tenv)
                                                         tenv)))
      (proc-exp (var argty exp1) (let ((resty (type-of exp1 (extend-tenv var argty tenv))))
                                (proc-type argty resty)))
      (call-exp (rand rator) (let ((rand-ty (type-of rand tenv))
                                   (rator-ty (type-of rator tenv)))
                               (cases type rand-ty
                                 (proc-type (argty resty) (begin (check-equal-type! argty rator-ty exp)
                                                                 resty))
                                 (else (eopl:error "operand :" rand "is not a proc-type, but" rand-ty))))))))

;type-of-program : program -> type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp) (type-of exp init-tenv)))))

;check : string -> list:(easy read type)
(define check 
  (lambda (str)
    (type-to-external-form (type-of-program (scan&parse str))))) ;!!! pretty print with : type-to-external-form





; interpreter
;==================================================================================
;==================================================================================
; to make it simple we make the lang immutable, so that it do not contain a store.


;environment
;----------------------------------------------------
(define-datatype env env?
  (empty-env)
  (extend-env (var symbol?)
              (val expval?)
              (senv env?))
  (extend-env-with-module (name symbol?)
                          (menv module-val?)
                          (senv env?)))





; eval mudules --> module-val
;----------------------------------------------------
; we do not use value-of to eval module, because module will not
; become a expval after eval, but a env: module-val.
(define-datatype module-val module-val?
  (a-module (bindings env?)))





; eval expression --> expval  
;----------------------------------------------------
 (define-datatype proc proc?
   (a-procedure (var symbol?)
                (body expression?)
                (senv env?)))

(define-datatype expval expval?
  (int-val (ival number?))
  (bool-val (bval boolean?))
  (proc-val (proc proc?)))









; test
;----------------------------------------------------

;> (check "123")
;  int

;> (check "zero?(123)")
;  bool

;> (check "-(12,5)")
;  int

;> (check "if zero?(0) then 123 else 345")
;  int

;> (check "let x = 123 in x")
;  int

;> (check "proc (x:int) proc(y:bool) -(x,1)")
;  (int -> (bool -> int))

;> (check "let f = proc (x:int) -(x,1) in (f 5)")
;  int
