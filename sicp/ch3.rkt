;;; Chapter 3 Modularity, Objects, and State
(load "ch2.rkt")
;(load "support/ch3.scm")

;; Exercise 3.1
(define (make-accumulator sum)
  (lambda (num)
    (begin
      (set! sum (+ sum num))
      sum)))


;; Exercise 3.2
(define (make-monitored f)
  (let ((count 0))
    (lambda (x)
      (cond
        ((equal? x 'how-many-calls?)
         count)
        ((equal? x 'reset-count)
         (set! count 0))
        (else
         (begin
           (set! count (+ count 1))
           (f x)))))))


;; Exercise 3.3
(define (make-account balance password)
  (define (withdraw amount)
    (if (>= balance amount)
        (begin (set! balance (- balance amount))
               balance)
        "Insufficient funds"))
  (define (deposit amount)
    (set! balance (+ balance amount))
    balance)
  (define (dispatch pw m)
    (cond
      ((not (equal? pw password))
       (error "Incorrect Password"))
      ((eq? m 'withdraw) withdraw)
      ((eq? m 'deposit) deposit)
      (else (error "Unknown request -- MAKE-ACCOUNT"
                   m))))
  dispatch)


;; Exercise 3.4
(define (make-account balance password)
  (let ((count 0))
    (define (withdraw amount)
      (if (>= balance amount)
          (begin (set! balance (- balance amount))
                 balance)
          "Insufficient funds"))
    (define (deposit amount)
      (set! balance (+ balance amount))
      balance)
    (define (dispatch pw m)
      (if (not (equal? pw password))
          (begin
            (set! count (+ count 1))
            (if (>= count 7)
                (call-the-cops)
                (error "Incorrect Password")))
          (begin
            (set! count 0)
            (cond
              ((eq? m 'withdraw) withdraw)
              ((eq? m 'deposit) deposit)
              (else (error "Unknown request -- MAKE-ACCOUNT"
                           m))))))
    dispatch))


;; Exercise 3.5
(define (estimate-integral p x1 x2 y1 y2 trials)
  (monte-carlo trials (p (random-in-range x1 x2)
                         (random-in-range y1 y2))))

(define (estimate-pi trials)
  (* 4
     (estimate-integral (lambda (x y)
                          (<= (+ (* x x) (* y y))))
                        -1 1 -1 1 trials)))


;; Exercise 3.6
(define random-init 7)
(define rand
  (let ((x random-init))
    (lambda (com)
      (cond
        ((equal? com 'generate)
         (begin
           (set! x (rand-update x))
           x))
        ((equal? com 'reset)
         (lambda (new)
           (set! x new)))
        (else
         (error "Unknow command"))))))


;; Exercise 3.7
(define (make-account balance password)
  (let ((passwords (list password)))
    (define (withdraw amount)
      (if (>= balance amount)
          (begin (set! balance (- balance amount))
                 balance)
          "Insufficient funds"))
    (define (deposit amount)
      (set! balance (+ balance amount))
      balance)
    (define (dispatch pw m)
      (cond
        ((not (member pw passwords))
         ((error "Incorrect Password")))
        ((eq? m 'withdraw) withdraw)
        ((eq? m 'deposit) deposit)
        ((eq? m 'joint)
         (lambda (new) (set! passwords (cons new passwords))))
        (else
         (error "Unknown request -- MAKE-ACCOUNT" m))))
    dispatch))

(define (make-joint acc pw new-pw)
  (begin
    ((acc pw 'joint) new-pw)
    acc))


;; Exercise 3.8
(define f
  (let ((last 0)
        (value 0))
    (lambda (x)
      (begin
        (if (= x last)
            (set! value 0)
            (set! value (- last value)))
        (set! last x)
        value))))


;; Exercise 3.9
;  Admit.


;; Exercise 3.10
;  Admit.


;; Exercise 3.11
;  Admit.


;; Exercise 3.12
;  (b)
;  (b c d)


;; Exercise 3.13
;  Admit.


;; Exercise 3.14
;  (a)
;  (d c b a)


;; Exercise 3.15
;  Admit.


;; Exercise 3.16
(define ex3 '(a b c))

(define temp0 (list 'b))
(define ex4 (cons 'a (cons temp0 temp0)))

(define temp1 (list 'a))
(define temp2 (cons temp1 temp1))
(define ex7 (cons temp2 temp2))

(define (make-cycle x)
  (set-cdr! (last-pair x) x)
  x)
(define exinf
  (make-cycle '(a b c)))


;; Exercise 3.17
(define (count-pairs p)
  (let ((s '()))
    (define (cp p)
      (cond
        ((not (pair? p)) 0)
        ((memq p s) 0)
        (else (begin
                (set! s (cons p s))
                (+ 1
                   (cp (car p))
                   (cp (cdr p)))))))
    (cp p)))


;; Exercise 3.18
(define (cycle? l)
  (let ((s '()))
    (define (c? l)
      (cond
        ((null? l) #f)
        ((memq l s) #t)
        (else
         (begin
           (set! s (cons l s))
           (c? (cdr l))))))
    (c? l)))


;; Exercise 3.19
(define (cycle? l)
  (define (catch? slow fast)
    (or (eq? slow fast)
        (and (pair? fast)
             (eq? slow (cdr fast)))))
  (define (run slow fast)
    (cond
      ((null? slow) #f)
      ((null? fast) #f)
      ((null? (cdr fast)) #f)
      ((catch? slow fast) #t)
      (else
       (run (cdr slow) (cddr fast)))))
  (cond
    ((null? l) #f)
    ((null? (cdr l)) #f)
    (else
     (let ((slow l)
           (fast (cdr l)))
       (run slow fast)))))


;; Exercise 3.20
;  Admit.


;; Exercise 3.21
(define (print-queue q)
  (front-ptr q))


;; Exercise 3.22
;  Admit.


;; Exercise 3.23
(define (front-ptr deque) (car deque))
(define (rear-ptr deque) (cdr deque))
(define (set-front-ptr! deque item) (set-car! deque item))
(define (set-rear-ptr! deque item) (set-cdr! deque item))

(define (make-node pre item suc)
  (cons (cons pre suc) item))
(define pre caar)
(define suc cdar)
(define item cdr)
(define (set-pre! node p)
  (set-car! (car node) p))
(define (set-suc! node s)
  (set-cdr! (car node) s))
(define (set-item! node i)
  (set-cdr! node i))

(define (make-deque)
  (cons '() '()))
(define (empty-deque? deque)
  (or (null? (front-ptr deque))
      (null? (rear-ptr deque))))

(define (front-deque deque)
  (if (empty-deque? deque)
      (write "front-deque called with an empty deque")
      (item (front-ptr deque))))
(define (rear-deque deque)
  (if (empty-deque? deque)
      (write "front-deque called with an empty deque")
      (item (rear-ptr deque))))

(define (front-insert-deque! deque item)
  (let ((new-node (make-node '() item (front-ptr deque))))
    (cond ((empty-deque? deque)
           (set-front-ptr! deque new-node)
           (set-rear-ptr! deque new-node)
           deque)
          (else
           (set-pre! (front-ptr deque) new-node)
           (set-front-ptr! deque new-node)
           deque))))

(define (rear-insert-deque! deque item)
  (let ((new-node (make-node (rear-ptr deque) item '())))
    (cond ((empty-deque? deque)
           (set-front-ptr! deque new-node)
           (set-rear-ptr! deque new-node)
           deque)
          (else
           (set-suc! (rear-ptr deque) new-node)
           (set-rear-ptr! deque new-node)
           deque))))

(define (front-delete-deque! deque)
  (cond ((empty-deque? deque)
         (write "front-delete! called with an empty deque"))
        (else
         (set-front-ptr! deque (suc (front-ptr deque)))
         (if (not (empty-deque? deque))
             (set-pre! (front-ptr deque) '()))
         deque)))

(define (rear-delete-deque! deque)
  (cond ((empty-deque? deque)
         (write "rear-delete! called with an empty deque"))
        (else
         (set-rear-ptr! deque (pre (rear-ptr deque)))
         (if (not (empty-deque? deque))
             (set-suc! (rear-ptr deque) '()))
         deque)))
