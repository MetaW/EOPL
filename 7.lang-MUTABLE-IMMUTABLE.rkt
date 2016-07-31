#lang eopl
;lang-MUTABLE-IMMUTABLE


;concrete & abstract syntax tree & scanner/parser
;=====================================================================

;---concrete syntax tree:

;Program :: = Expression

;Expression :: = Number
;              | -(Expression, Expression)
;              | zero? (Expression)
;              | if Expression then Expression else Expression
;              | Identifer
;              | let Identifer = Expression in Expression
;              | proc (Idenfifer) Expression
;              | (Expression Expression)
;              | begin Expression {; Expression}* end
;              | set Identifer = Expression
;              | letmutable Identifer = Expression in Expression


;---scanner&grammar spec
(define scanner-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifer (letter (arbno (or letter digit "-" "_" "?"))) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))
;   (class (regexp) action)
; string (keyword) from grammar-spec (eg: "-","if","let","=",...) has a higher priority than that in scanner-spec.


(define grammar-spec
 '((program (expression) a-program)
   (expression (number) const-exp)
   (expression ("-" "(" expression "," expression ")") diff-exp)
   (expression ("zero?" "(" expression ")") zero?-exp)
   (expression ("if" expression "then" expression "else" expression) if-exp)
   (expression (identifer) var-exp)
   (expression ("let" identifer "=" expression "in" expression) let-exp)
   (expression ("proc" "(" identifer ")" expression) proc-exp)
   (expression ("(" expression expression ")") call-exp)
   (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
   (expression ("set" identifer "=" expression) assign-exp)
   (expression ("letmutable" identifer "=" expression "in" expression) letmu-exp)))
;  (algebric-data-type (reg-exp of concrete-syntax with class/string/ADT) constructor)
; class/string -> terminator
; ADT -> nonterminator


;---abstract syntax tree

; use auto-generated datatype for program and expression
;(sllgen:make-define-datatypes scanner-spec grammar-spec)

;see what is generated by calling (show-the-datatypes), the result is following:
;(define show-the-datatypes
;  (lambda () (sllgen:list-define-datatypes scanner-spec grammar-spec)))


;the following datatype can be auto-generated as mentioned above.
(define-datatype program program?
  (a-program (a-program27 expression?)))

(define-datatype expression expression?
   (const-exp (const-exp28 number?))
   (diff-exp (diff-exp29 expression?)
             (diff-exp30 expression?))
   (zero?-exp (zero?-exp31 expression?))
   (if-exp (if-exp32 expression?)
           (if-exp33 expression?)
           (if-exp34 expression?))
   (var-exp (var-exp35 symbol?))
   (let-exp (let-exp36 symbol?)
            (let-exp37 expression?)
            (let-exp38 expression?))
   (proc-exp (proc-exp39 symbol?)
             (proc-exp40 expression?))
   (call-exp (call-exp41 expression?)
             (call-exp42 expression?))
   (begin-exp (begin-exp47 expression?)
              (begin-exp48 (list-of expression?)))
   (assign-exp (var symbol?)
               (exp expression?))
   (letmu-exp (var symbol?)
              (exp expression?)
              (body expression?)))



; auto-generated scanner & parser:

; scan&parse : string -> program
(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar-spec))


; expressed value & denoted value 
;=====================================================================
;expval : num-val, bool-val, proc-val
;denval : ref(expval), expval

;------ scheme value : number, bool, proc, ref

; datatype proc is not necessary
(define-datatype proc proc?
  (procedure (var symbol?)
             (body expression?)
             (en env?)))
; ref type = number => address in store
(define ref?
  (lambda (ref)
    (number? ref)))

;------ expressed value
; expval
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc proc?)))


; extractor : expval -> number
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (eopl:error "expval extract error in expval->num: ~s" val)))))

; extractor : expval -> bool
(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (eopl:error "expval extract error in expval->bool: ~s" val)))))

; extractor : expval -> proc
(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (eopl:error "expval extract error in expval->bool: ~s" val)))))


;------ dennoted value

(define-datatype denval denval?
  (den-ref (ref ref?))
  (den-expv (expv expval?)))

; extractor : denval -> ref
(define denval->ref
  (lambda (val)
    (cases denval val
      (den-ref (ref) ref)
      (else (eopl:error "denval extract error in denval->ref: ~s" val)))))

; extractor : denval -> expval
(define denval->expval
  (lambda (val)
    (cases denval val
      (den-expv (expv) expv)
      (else (eopl:error "denval extract error in denval->expval: ~s" val)))))


; environment & store
;=====================================================================
;env   : var --- ref/expval
;store :         ref--- expval


;---environment---   

(define-datatype env env?
  (empty-env)
  (extend-env (var symbol?)
              (val denval?) ; !!! in this lang env stores denval(expval+ref).
              (e env?)))

; init-env
(define init-env
  (extend-env
   'i (den-ref 2)
   (extend-env
    'v (den-ref 1)
    (extend-env
     'x (den-ref 0)
     (empty-env)))))


; apply-env : symbol * env -> denval
(define apply-env
  (lambda (var en)
    (cases env en
      (empty-env () (eopl:error "Unbound variable : ~s" var))
      (extend-env (v val e)
                  (if (equal? v var)
                      val
                      (apply-env var e))))))



;---store---
;unlike env, store is global
(define the-store 'uninitialized)

;---interface-for-store

;empty-store : () -> '()
(define empty-store
  (lambda () '()))

(define get-store
  (lambda () the-store))

;---
(define init-store!
  (lambda ()
    (set! the-store (list (num-val 1) (num-val 5) (num-val 10)))))

; eval
;=====================================================================

; auxiliary function for value-of

; apply-procdure : proc * expval -> expval
(define apply-procedure
  (lambda (proc0 val)
    (cases proc proc0
      (procedure (var body en) (value-of body (extend-env var (den-expv val) en))))))

; apply-newref : expval -> ref
(define apply-newref
  (lambda (val)
    (let ([ref (length the-store)])
      (set! the-store (append the-store (list val)))
      ref)))

; apply-deref : ref -> expval
(define apply-deref
  (lambda (ref)
    (list-ref the-store ref)))

; apply-setref : ref * expval -> unspecified
(define apply-setref!
  (lambda (ref val)
    (define in-setref!
      (lambda (store ref)
        (cond ((null? store) (eopl:error "uninitilized store"))
              ((= 0 ref) (cons val (cdr store)))
              (else (cons (car store)
                          (in-setref! (cdr store) (- ref 1)))))))
    (set! the-store (in-setref! the-store ref))))




; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (let ([denv (apply-env var env)])
                       (cases denval denv
                         (den-ref (ref) (apply-deref ref))
                         (den-expv (expv) expv))))
      (diff-exp (exp1 exp2) (num-val
                             (- (expval->num (value-of exp1 env))
                                (expval->num (value-of exp2 env)))))
      (zero?-exp (exp)
                 (let ((val (expval->num (value-of exp env))))
                   (if (= val 0)
                       (bool-val #t)
                       (bool-val #f))))
      (if-exp (exp1 exp2 exp3)
              (let ((condi (expval->bool (value-of exp1 env))))
                (if condi
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp body) (value-of body
                                        (extend-env var
                                                    (den-expv (value-of exp env))
                                                    env)))
      (proc-exp (param body) (proc-val (procedure param body env)))
      (call-exp (procid exp)
                (let ((proci (expval->proc (value-of procid env)))
                      (param (value-of exp env)))
                  (apply-procedure proci param)))
      (begin-exp (exp exps)
                 (define inner
                   (lambda (expr exprs)
                     (let ((v1 (value-of expr env)))
                         (if (null? exprs)
                         v1
                         (inner (car exprs) (cdr exprs))))))
                 (inner exp exps))
      (assign-exp (var exp) (let ([denv (apply-env var env)])
                              (cases denval denv
                                (den-ref (ref) (apply-setref! ref (value-of exp env)))
                                (den-expv (expv) (eopl:error "Can not assign a value to immutable variable: ~s" var)))))
      (letmu-exp (var exp body) (value-of body
                                        (extend-env var
                                                    (den-ref (apply-newref (value-of exp env)))
                                                    env))))))



; value-of-program : Program -> Expval
(define value-of-program
  (lambda (pgm)
    (init-store!)
    (cases program pgm
      (a-program (exp) (value-of exp init-env)))))


; run : String -> Expval
(define run
  (lambda (str)
    (value-of-program (scan&parse str))))



; test
;=====================================================================
;> (run "letmutable x = 10 in begin set x = 20; x end")
;  #(struct:num-val 20)

;> (run "letmutable x = 10 in let f = proc (y) set x = y in begin (f 20); x end")
;  #(struct:num-val 20)
