;;; Chapter 4 


;; Exercise 4.1
(define (list-of-values-ltr exps env)
  (if (no-operands? exps)
      '()
      (let ((first (eval (first-operand exps) env)))
        (cons first
              (list-of-values (rest-operands exps) env)))))

(define (list-of-values-rtl exps env)
  (if (no-operands? exps)
      '()
      (let ((rest (list-of-values (rest-operands exps) env)))
        (cons (eval (first-operand exps) env)
              rest))))


;; Exercise 4.2
;  Admit.


;; Exercise 4.3
;  Admit.


;; Exercise 4.4
(define (and? exp)
  (tagged-list? exp 'and))
(define (and-items exp)
  (cdr exp))

(define (eval-and items env)
  (cond
    ((null? items) #t)
    (else
     (let ((first (car items))
           (rest (cdr items)))
       (if (true? (eval first))
           (eval-and rest env)
           #f)))))

(define (or? exp)
  (tagged-list? exp 'or))
(define (or-items exp)
  (cdr exp))

(define (eval-and items env)
  (cond
    ((null? items) #f)
    (else
     (let ((first (car items))
           (rest (cdr items)))
       (if (true? (eval first))
           #t
           (eval-and rest env))))))

;  and or as derived expressions
(define (and->if exp )
  (expand-and-items (and-items exp)))
(define (expand-and-items items)
  (if (null? items)
      'true
      (let ((first (car items))
            (rest (cdr items)))
        (make-if first
                 (expand-and-items rest)
                 'false))))

(define (or->if exp )
  (expand-or-items (or-items exp)))
(define (expand-or-items items)
  (if (null? items)
      'false
      (let ((first (car items))
            (rest (cdr items)))
        (make-if first
                 'true
                 (expand-or-items rest)))))

(define (make-if p c a)
  (list 'if p c a))


;; Exercise 4.5
;  Admit.


;; Exercise 4.6
(define (let? exp)
  (tagged-list? exp 'let))
(define (let-bindings exp)
  (cadr exp))
(define (let-bind-vars bindings)
  (map car bindings))
(define (let-bind-vals bindings)
  (map cadr bindings))
(define (let-body exp)
  (caddr exp))

(define (let->combination exp)
  (let ((bindings (let-bindings exp))
        (body (let-body exp)))
    (make-app
     (make-lambda (let-bind-vars bindings)
                  body)
     (let-bind-vals bindings))))

(define (make-app proc args)
  (cons proc args))


;; Exercise 4.7
(define (let*->nested-lets exp)
  (expand-let* (let-bindings exp)
               (let-body exp)))

(define (expand-let* bindings body)
  (if (null? bindings)
      body
      (let ((first (car bindings))
            (rest (cdr bindings)))
        (make-single-let first
                         (expand-let* rest body)))))

(define (make-single-let bind body)
  (cons 'let
        (cons (list bind)
              body)))
                   

