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
    ((null? items) 'true)
    (else
     (let ((first (car items))
           (rest (cdr items)))
       (if (true? (eval first))
           (eval-and rest env)
           'false)))))

(define (or? exp)
  (tagged-list? exp 'or))
(define (or-items exp)
  (cdr exp))

(define (eval-and items env)
  (cond
    ((null? items) 'false)
    (else
     (let ((first (car items))
           (rest (cdr items)))
       (if (true? (eval first))
           'true
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



;; Exercise 4.8
(define (named-let? exp)
  (variable? (cadr exp)))


;; Exercise 4.9
;  Abort.


;; Exercise 4.10 - 4.13
;  Admit.


;; Exercise 4.14
;  Abort.


;; Exercise 4.15
;  Admit.


;; Exercise 4.16
;  a
;  Admit.
;  b
(define (scan-out-defines body)
  (define (pick p body)
    (cond
      ((null? body) '())
      ((p (car body))
       (cons (car body) (pick p (cdr body))))
      (else
       (pick p (cdr body)))))
  (let ((definitions (pick definition? body))
        (rest (pick (lambda (exp) (not (definition? exp)))
                    body)))
    (append (list 'let
                  (map (lambda (def)
                         (list (definition-variable def) ''*unasigned*))
                       definitions))
            (append (map (lambda (def)
                           (list 'set (definition-variable def) (definition-value def)))
                         definitions)
                    rest))))
;  c
;  Admit.


;; Exercise 4.17 - 4.20
;  Admit.



;; Exercise 4.21
(define (f x)
  ((lambda (even? odd?)
     (even? even? odd? x))
   (lambda (ev? od? n)
     (if (= n 0)
         #t
         (od? ev? od? (- n 1))))
   (lambda (ev? od? n)
     (if (= n 0)
         #f
         (ev? ev? od? (- n 1))))))


;; Exercise 4.22 - 4.26
;  Admit.


;; Exercise 4.27
;  2
;  10
;  2


;; Exercise 4.28
;  Procedure as argument. Because all arguments will be delay,
;  they must be force when they are called in the body.


;; Exercise 4.29 - 4.31
;  Abort.


;; Exercise 4.32 - 4.34
;  Admit.


;; Exercise 4.35
(define (an-integer-between low high)
  (if (> low high)
      (amb)
      (amb low (an-integer-between (+ low 1) high))))


;; Exercise 4.36
(define (all-pythagorean-triple)
  (let ((k (an-integer-starting-from 1)))
    (let ((j (an-integer-between 1 k)))
      (let ((i (an-integer-between 1 j)))
        (require (= (+ (* i i) (* j j)) (* k k)))
        (list i j k)))))


;; Exercise 4.37
;  Yes.


;; Exercise 4.38 - 4.39
;  Admit.


;; Exercise 4.40
(define (multiple-dwelling)
  (let ((baker (amb 1 2 3 4 ))
        (cooper (amb 2 3 4 5))
        (fletcher (amb 2 3 4))
        (smith (amb 1 2 3 4 5)))
    (let ((miller (an-integer-between (+ cooper 1) 5)))
      (require
        (distinct? (list baker cooper fletcher miller smith)))
      (require (not (= (abs (- smith fletcher)) 1)))
      (require (not (= (abs (- fletcher cooper)) 1)))
      (list (list 'baker baker)
            (list 'cooper cooper)
            (list 'fletcher fletcher)
            (list 'miller miller)
            (list 'smith smith)))))


;; Exercise 4.41
;  Admit.


;; Exercise 4.4
(define (xor p q)
  (not (eq? p q)))

(define (liar-puzzle)
  (let ((betty (amb 1 2 3 4 5))
        (ethel (amb 1 2 3 4 5))
        (joan (amb 1 2 3 4 5))
        (kitty (amb 1 2 3 4 5))
        (mary (amb 1 2 3 4 5)))
    (require (xor (= kitty 2)
                  (= betty 3)))
    (require (xor (= ethel 1)
                  (= joan 2)))
    (require (xor (= joan 3)
                  (= ethel 5)))
    (require (xor (= kitty 2)
                  (= mary 4)))
    (require (xor (= mary 4)
                  (= betty 1)))
    (list (list 'betty betty)
          (list 'ethel ethel)
          (list 'joan joan)
          (list 'kitty kitty)
          (list 'mary mary))))
             


;; Exercise 4.43 - 4.44
;  Admit.
