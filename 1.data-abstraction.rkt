#lang eopl

;exec 2.21
;------------------------------
(define-datatype env env?
  (empty-env)
  (extend-env (var symbol?)
              (val number?)
              (env env?)))

;;has-biding? : symbol * env -> bool
(define has-biding?
  (lambda (v e)
    (cases env e
      (empty-env () #f)
      (extend-env (var val env)
                  (if (equal? var v)
                      #t
                      (has-biding? v env))))))

;;apply-env : symbol * env -> number
(define apply-env
  (lambda (v e)
    (cases env e
      (empty-env () (eopl:error "no biding for variable: ~s" v))
      (extend-env (var val env)
                  (if (equal? var v)
                      val
                      (apply-env v env))))))




;exec 2.22
;------------------------------
(define-datatype stack stack?
  (empty-stack)
  (append-stack (val number?)
                (stk stack?)))


;binary tree
;------------------------------
(define-datatype tree tree?
  (empty-tree)
  (leaf (val number?))
  (node (val number?)
        (left tree?)
        (right tree?)))


;;insert-tree : number * tree -> tree
(define insert-tree
  (lambda (val tr)
    (cases tree tr
      (empty-tree () (leaf val))
      (leaf (v) (if (< v val)
                      (node v (empty-tree) (leaf val))
                      (node v (leaf val) (empty-tree))))
      (node (v le ri)
            (if (< v val)
                (node v le (insert-tree val ri))
                (node v (insert-tree val le) ri))))))

(define xx (insert-tree 3 (empty-tree)))
(display xx)
(newline)
(define x2 (insert-tree 5 xx))
(display x2)
(newline)
(define x3 (insert-tree 1 x2))
(display x3)

