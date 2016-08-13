#lang eopl
; a type checker for lang-PROC

;language-PROC : concrete & abstract syntax tree
;----------------------------------------------------
;concrete syntax tree:

;Program :: = Expression

;Expression :: = Number
;              | -(Expression, Expression)
;              | zero? (Expression)
;              | if Expression then Expression else Expression
;              | Identifer
;              | let Identifer = Expression in Expression
;              | proc (Idenfifer : Type) Expression
;              | (Expression Expression)

;Type :: = Int
;        | Bool
;        | (Type -> Type)


; abstract syntax tree
(define-datatype program program?
  (a-program (exp expression?)))

(define-datatype expression expression?
  (const-exp (num number?))
  (diff-exp (exp1 expression?)
            (exp2 expression?))
  (zero?-exp (exp expression?))
  (if-exp (exp1 expression?)
          (exp2 expression?)
          (exp3 expression?))
  (var-exp (exp symbol?))
  (let-exp (var symbol?)
           (exp expression?)
           (body expression?))
  (proc-exp (var symbol?)
            (arg-ty type?)
            (body expression?))
  (call-exp (operator expression?)
            (operand expression?)))

(define-datetype type type?
  (int-type)
  (bool-type)
  (proc-type (arg-ty type?)
             (res-ty type?)))




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
   (expression ("proc" "(" identifer ":" type ")" expression) proc-exp)
   (expression ("(" expression expression ")") call-exp)
   (type ("int") int-type)
   (type ("bool") bool-type)
   (type ("(" type "->" type ")") proc-type)))
;  (algebric-data-type (concrete-syntax-with-class/string/ADT) constructor)
; class/string : terminator
; ADT : nonterminator


; scan&parse : string -> program
(define scan&parse
  (sllgen:make-string-parser scanner-spec parser-spec))


; expressed valus && denoted value
;----------------------------------------------------
;expressed value : num-val, bool-val, proc-val
;denoted value : num-val, bool-val, proc-val


; datatype proc is not necessary
(define-datatype proc proc?
  (procedure (var symbol?)
             (body expression?)
             (en env?)))

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

; auxiliary function:
; check-equal-type! : type * type * exp -> Unspec
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    ()))

; to make the output type easy to read, we define these function





; test
;----------------------------------------------------

;> (run "let f = proc (x) -(x,10) in (f 20)")
;  #(struct:num-val 10)

;> (run "let f = proc (x) proc (y) -(x,y) in ((f 5) 3)")
; #(struct:num-val 2)

;> (run "let x = 200 in let f = proc (z) -(z,x) in let x = 100 in let g = proc (z) -(z,x) in -((f 1), (g 1))")
;  #(struct:num-val -100)
