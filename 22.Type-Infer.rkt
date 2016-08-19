#lang eopl
; a type inference and checker for lang-letrec

;language-letrec : concrete & abstract syntax tree
;----------------------------------------------------
;concrete syntax tree:

;Program :: = Expression

;Expression :: = Number
;              | -(Expression, Expression)
;              | zero? (Expression)
;              | if Expression then Expression else Expression
;              | Identifer
;              | let Identifer = Expression in Expression
;              | proc (Idenfifer : option-type) Expression
;              | letrec option-type Identifer (Identifer : option-type) = Expression in Expression
;              | (Expression Expression)

;option-type :: = ?
;               | Type

;Type :: = Int
;        | Bool
;        | (Type -> Type)


; abstract syntax tree
(define-datatype program program?
  (a-program (a-program1 expression?)))

(define-datatype expression expression?
  (const-exp (const-exp2 number?))
  (diff-exp (diff-exp3 expression?) (diff-exp4 expression?))
  (zero?-exp (zero?-exp5 expression?))
  (if-exp (if-exp6 expression?) (if-exp7 expression?) (if-exp8 expression?))
  (var-exp (var-exp9 symbol?))
  (let-exp (let-exp10 symbol?) (let-exp11 expression?) (let-exp12 expression?))
  (proc-exp (proc-exp13 symbol?) (proc-exp14 option-type?) (proc-exp15 expression?))
  (letrec-exp
   (letrec-exp16 option-type?)
   (letrec-exp17 symbol?)
   (letrec-exp18 symbol?)
   (letrec-exp19 option-type?)
   (letrec-exp20 expression?)
   (letrec-exp21 expression?))
  (call-exp (call-exp22 expression?) (call-exp23 expression?)))

(define-datatype option-type option-type?
  (no-type)
  (a-type (ty type?)))

(define-datatype type type?
  (int-type)
  (bool-type)
  (proc-type (arg-ty type?)
             (res-ty type?))
  (tvar-type (id number?)))  ;!!! tvar-type do not appear in AST, it is used as a kind of return value of function : optype->type
                             ; where no-type will be returned as "tvar-type xxx", it works as a type variable. 


;in AST                 -->           in tenv & subst
;option-type            -->                type
;     |                                      |
;     |--- atype type(int/bool/proc)   -->   |--- type(int/bool/proc)
;     |--- no-type                     -->   |--- type(tvar-type)


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
 '((program (expression) a-program)
   (expression (number) const-exp)
   (expression ("-" "(" expression "," expression ")") diff-exp)
   (expression ("zero?" "(" expression ")") zero?-exp)
   (expression ("if" expression "then" expression "else" expression) if-exp)
   (expression (identifer) var-exp)
   (expression ("let" identifer "=" expression "in" expression) let-exp)
   (expression ("proc" "(" identifer ":" option-type ")" expression) proc-exp)
   (expression ("letrec" option-type identifer "(" identifer ":" option-type ")" "=" expression "in" expression) letrec-exp)
   (expression ("(" expression expression ")") call-exp)
   (option-type ("?") no-type)
   (option-type (type) a-type)
   (type ("int") int-type)
   (type ("bool") bool-type)
   (type ("(" type "->" type ")") proc-type)))
;  (algebric-data-type (concrete-syntax-with-class/string/ADT) constructor)
; class/string : terminator
; ADT : nonterminator


; scan&parse : string -> program
(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))







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


;substitution
;----------------------------------------------------
; substitution just like a store, it sotres the real type
; of a unknown type

;---auxiliary function

;apply-one-subst : type * type(tvar-type) * type -> type
(define apply-one-subst
  (lambda (ty tv0 ty0)   ;!!! the func will replace all tv0 in ty with ty0
    (cases type ty
      (int-type () ty)
      (bool-type () ty)
      (proc-type (argty resty)
                 (proc-type (apply-one-subst argty tv0 ty0)
                            (apply-one-subst resty tv0 ty0)))
      (tvar-type (num) (if (equal? ty tv0)
                           ty0
                           ty)))))

;apply-subst-to-type : type * subst -> type
(define apply-subst-to-type ; this func will replace all tvar-type in type with its cooresponsding binding in subst. 
  (lambda (ty subst)
    (cases type ty
      (int-type () ty)
      (bool-type () ty)
      (proc-type (argty resty) (proc-type (apply-subst-to-type argty subst)
                                          (apply-subst-to-type resty subst)))
      (tvar-type (num) (let ((temp (assoc ty subst)))
                         (if temp
                             (cdr temp)
                             ty))))))

;-------
; empty-subst : () -> subst
(define empty-subst
  (lambda () '()))

; extend-subst : type(tvar-type) * type * subst -> subst
(define extend-subst
  (lambda (tv ty subst)
    (cons (cons tv ty)
          (map (lambda (p)
                 (cons (car p)
                       (apply-one-subst (cdr p) tv ty)))
               subst))))




; unifier
;----------------------------------------------------
; in full type marked lang we use "check-equal-type" to check constraint and find type
; error, but here in type inference lang, instead we use "unifier" to add those constraint
; to subst and check type error if it has. Because in type inference lang a lot of type is unknow,
; we can not get its type immediately to check, nut to add the constraint to subst for further use.


;-----auxiliary function
; tvar-type? : type->bool
(define tvar-type?
  (lambda (ty)
    (cases type ty
      (tvar-type (num) #t)
      (else #f))))

; proc-type? : type -> bool
(define proc-type?
  (lambda (ty)
    (cases type ty
      (proc-type (lty rty) #t)
      (else #f))))

; proc-type->argty : type(proc-type) -> type
(define proc-type->argty
  (lambda (ty)
    (cases type ty
      (proc-type (lty rty) lty)
      (else (eopl:error "type " ty " is not a proc-type")))))

; proc-type->resty : type(proc-type) -> type
(define proc-type->resty
  (lambda (ty)
    (cases type ty
      (proc-type (lty rty) rty)
      (else (eopl:error "type " ty " is not a proc-type")))))

; report-on-occurence-violation -> unspec
(define report-on-occurence-violation
  (lambda (ty1 ty2 exp)
    (eopl:error "the type "ty1 "should not appeared in type " ty2)))

;--------
; unifier : type * type * subst * exp -> subst + (error report)
(define unifier
  (lambda (ty1 ty2 subst exp) ;!!! exp in unifier just provide additional info when error happens.
    (let ((newty1 (apply-subst-to-type ty1 subst))   ;
          (newty2 (apply-subst-to-type ty2 subst)))  ; we need to replace tvar-type in ty1 and ty2 with its bindings in subst.
      (cond ((equal? newty1 newty2) subst)
            ((tvar-type? newty1) (if (no-occurence? newty1 newty2)
                                     (extend-subst newty1 newty2 subst)
                                     (report-on-occurence-violation newty1 newty2 exp)))
            ((tvar-type? newty2) (if (no-occurence? newty2 newty1)
                                     (extend-subst newty2 newty1 subst)
                                     (report-on-occurence-violation newty2 newty1 exp)))
            ((and (proc-type? newty1) (proc-type? newty2)) (let ((subst1 (unifier (proc-type->argty newty1)
                                                                                  (proc-type->argty newty1)
                                                                                  subst
                                                                                  exp)))
                                                             (let ((subst2 (unifier (proc-type->resty newty1)
                                                                                    (proc-type->resty newty2)
                                                                                    subst1
                                                                                    exp)))
                                                               subst2)))
            (else (eopl:error "unifier error: " newty1 newty2 "in" exp))))))



; auxiliary function
; no-occurence? : type(tvar-type) * type -> bool
(define no-occurence?
  (lambda (tv ty)
    (cases type ty
      (int-type () #t)
      (bool-type () #t)
      (proc-type (argty resty) (and (no-occurence? tv argty)
                                    (no-occurence? tv resty)))
      (tvar-type (num) (not (equal? tv ty))))))


; type checker
;----------------------------------------------------

;--- auxiliary function:

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
                       (type-to-external-form res-ty)))
      (tvar-type (num) (string->symbol (string-append "ty" (number->string num)))))))


; type-of will not only return a type but a subst, so we define a new value as its return type.
(define-datatype answer answer?
  (a-answer (ty type?)
            (st subst?)))

(define subst? list?)

; optype->type : option-type -> type
(define optype->type
  (lambda (opty)
    (cases option-type opty
      (no-type () (fresh-tvar-type))
      (a-type (ty) ty))))

; fresh-tvar-type : () -> type(tvar-type)
(define fresh-tvar-type
  (let ((num 0))    ; num is a state inside the clusure of function fresh-tvar-type
    (lambda ()
      (set! num (+ num 1))
      (tvar-type num))))


;--------
;type-of : exp * tenv * subst -> answer
(define type-of
  (lambda (exp tenv subst)
    (cases expression exp
      (const-exp (num) (a-answer (int-type) subst))
      (var-exp (var) (a-answer (apply-tenv var tenv) subst))
      (diff-exp (exp1 exp2) (cases answer (type-of exp1 tenv subst)
                              (a-answer (ty1 subst1) (let ((subst11 (unifier ty1 (int-type) subst1 exp1)))
                                                       (cases answer (type-of exp2 tenv subst11)
                                                         (a-answer (ty2 subst2) (let ((subst22 (unifier ty2 (int-type) subst2 exp2)))
                                                                                  (a-answer (int-type) subst22))))))))
      (zero?-exp (exp) (cases answer (type-of exp tenv subst)
                         (a-answer (ty1 subst1) (let ((subst2 (unifier ty1 (int-type) subst1 exp)))
                                                  (a-answer (bool-type) subst2)))))
      (if-exp (exp1 exp2 exp3) (cases answer (type-of exp1 tenv subst)
                                 (a-answer (ty1 subst1) (let ((subst11 (unifier ty1 (bool-type) subst1 exp1)))
                                                          (cases answer (type-of exp2 tenv subst11)
                                                            (a-answer (ty2 subst2)
                                                                      (cases answer (type-of exp3 tenv subst2)
                                                                        (a-answer (ty3 subst3) (let ((subst33 (unifier ty2 ty3 subst3 exp)))
                                                                                                 (a-answer ty2 subst33))))))))))
      (let-exp (var exp1 body) (cases answer (type-of exp1 tenv subst)
                                 (a-answer (ty1 subst1) (type-of body
                                                                 (extend-tenv var ty1 tenv)
                                                                 subst1))))
      (proc-exp (var optionty body) (let ((tvar (optype->type optionty)))
                                      (cases answer (type-of body
                                                             (extend-tenv var tvar tenv)
                                                             subst)
                                        (a-answer (bodyty subst1)
                                                  (a-answer (proc-type tvar bodyty) subst1)))))
      (call-exp (rand rator) (cases answer (type-of rand tenv subst)
                               (a-answer (randty subst1)
                                         (cases answer (type-of rator tenv subst1)
                                           (a-answer (ratorty subst2)
                                                     (cases type randty
                                                       (proc-type (lty rty) (let ((subst3 (unifier lty ratorty subst2 exp)))
                                                                              (a-answer rty subst3)))
                                                       (else (eopl:error "the type of" rand "is not a proc-type"))))))))
      (letrec-exp (opresty pname var opvarty pbody body) (let ((resty (optype->type opresty))
                                                               (varty (optype->type opvarty)))
                                                           (cases answer (type-of pbody
                                                                                  (extend-tenv pname
                                                                                               (proc-type varty resty)
                                                                                               (extend-tenv var varty tenv))
                                                                                  subst)
                                                             (a-answer (ty1 subst1) (let ((subst2 (unifier ty1 resty subst1 exp)))
                                                                                      (type-of body
                                                                                               (extend-tenv pname
                                                                                                            (proc-type varty resty)
                                                                                                            tenv)
                                                                                               subst2)))))))))

;type-of-program : program -> type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
                 (cases answer (type-of exp init-tenv (empty-subst))
                   (a-answer (ty subst) (apply-subst-to-type ty subst)))))))


;check : string -> list:(easy read type)
(define check 
  (lambda (str)
    (type-to-external-form (type-of-program (scan&parse str))))) ;!!! pretty print with : type-to-external-form

; test
;----------------------------------------------------

;> (check "let f = proc (x:?) -(x,1) in (f 5)")
;  int

;> (check "proc (x:?) proc(y:?) -(x,1)")
;  (int -> (ty3 -> int))
