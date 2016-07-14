#lang eopl

;language-LET : concrete & abstract syntax tree
;----------------------------------------------------
; concrete syntax tree
;Program :: = Expression

;Expression :: = Number
;              | -(Expression, Expression)
;              | zero? (Expression)
;              | if Expression then Expression else Expression
;              | Identifer
;              | let Identifer = Expression in Expression


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
           (body expression?)))


; scan&parse
;----------------------------------------------------





; expressed valus <-> denoted value
;----------------------------------------------------
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?)))


(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (eopl:error "expval extract error in expval->num: ~s" val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (eopl:error "expval extract error in expval->bool: ~s" val)))))


; environment
;----------------------------------------------------
(define-datatype env env?
  (empty-env)
  (extend-env (var symbol?)
              (val expval?)
              (e env?)))

; init-env
(define init-env
  (extend-env
   'i (num-val 1)
   (extend-env
    'v (num-val 5)
    (extend-env
     'x (num-val 10)
     (empty-env)))))


; apply-env : symbol -> expval
(define apply-env
  (lambda (var en)
    (cases env en
      (empty-env () (eopl:error "Unbound variable : ~s" var))
      (extend-env (v val e)
                  (if (= v var)
                      val
                      (apply-env var e))))))


; eval
;----------------------------------------------------

; run : String -> Expval
(define run
  ())

; value-of-program : Program -> Expval
(define value-of-program
  ())

; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env var env))
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
                                                    (value-of exp env)
                                                    env))))))

