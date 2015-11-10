;;; Chapter 3 Modularity, Objects, and State
(load "ch2.rkt")
(load "support/ch3.scm")

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


;; Exercise 3.24
;  Admit.


;; Exercise 3.25
;  Admit.


;; Exercise 3.26
;  Admit.


;; Exercise 3.27
;  Admit.


;; Exercise 3.28
(define (or-gate o1 o2 output)
  (define (or-action-procedure)
    (let ((new-value
           (logical-or (get-signal o1) (get-signal o2))))
      (after-delay or-gate-delay
                   (lambda ()
                     (set-signal! output new-value)))))
  (add-action! o1 or-action-procedure)
  (add-action! o2 or-action-procedure)
  'ok)


;; Exercise 3.29
(define (or-gate o1 o2 output)
  (let ((inv1 (make-wire))
        (inv2 (make-wire))
        (out (make-wire)))
    (inverter or1 inv1)
    (inverter or2 inv2)
    (and-gate inv1 inv2 out)
    (inverter out output)
    'ok))


;; Exercise 3.30
;  Admit.


;; Exercise 3.31
;  Admit.


;; Exercise 3.32
;  Admit.


;; Exercise 3.33
(define (average a b c)
  (let ((d (make-connector))
        (e (make-connector)))
    (adder a b e)
    (multiplier c d e)
    (constant 2 d)
    'ok))


;; Exercise 3.34
;  Admit.


;; Exercise 3.35
(define (squarer a b)
  (define (process-new-value)
    (if (has-value? b)
        (if (< (get-value b) 0)
            (error "square less than 0 -- SQUARER" (get-value b))
            (set-value! a (sqrt b) me))
        (if (hase-value? a)
            (set-value! b (* a a) me))))
  (define (process-forget-value)
    (forget-value! a me)
    (forget-value! b me))
  (define (me request)
    (cond ((eq? request 'I-have-a-value)
           (process-new-value))
          ((eq? request 'I-lost-my-value)
           (process-forget-value))
          (else
           (error "Unknown request -- MULTIPLIER" request))))
  me)


;; Exercise 3.36
;  Admit.


;; Exercise 3.37
(define (c- x y)
  (let ((z (make-connector)))
    (adder y z x)
    z))

(define (c* x y)
  (let ((z (make-connector)))
    (multiplier x y z)
    z))

(define (c/ x y)
  (let ((z (make-connector)))
    (multiplier y x x)
    z))

(define (cv c)
  (let ((x (make-connector)))
    (constant c x)
    x))


;; Exercise 3.38 - 3.49
;  Admit.


;; Exercise 3.50
(define (stream-map proc . argstreams)
  (if (stream-null? (car argstreams))
      the-empty-stream
      (cons-stream
       (apply proc (map car argstreams))
       (apply stream-map
              (cons proc (map stream-cdr argstreams))))))


;; Exercise 3.51
;  Admit.


;; Exercise 3.52
;  Admit.


;; Exercise 3.53
;  (1 2 4 8 16 ... )


;; Exercise 3.54
(define (mul-streams s1 s2)
  (stream-map * s1 s2))
(define factorials
  (cons-stream 1
               (mul-streams (integers-starting-from 2)
                            factorials)))


;; Exercise 3.55
(define (partial-sums s)
  (cons-stream (car s)
               (add-streams (stream-cdr s)
                            (partial-sums s))))


;; Exercise 3.56
(define S (cons-stream 1
                       (merge (scale-stream S 2)
                              (merge (scale-stream S 3)
                                     (scale-stream S 5)))))


;; Exercise 3.57
;  Admit.


;; Exercise 3.58
;  Admit.


;; Exercise 3.59
;  a
(define (div-streams s1 s2)
  (stream-map / s1 s2))
(define (integrate-series s)
  (div-streams s (integers-starting-from 1)))
;  b
(define cosine-series
  (cons-stream 1 (stream-map - (integrate-series sine-series))))
(define sine-series
  (cons-stream 0 (integrate-series cosine-series)))


;; Exercise 3.60
;  wrong
(define (mul-series s1 s2)
  (cons-stream (* (car s1) (car s2))
               (add-streams (mul-series (stream-cdr s1) s2)
                            (mul-series s1 (stream-cdr s2)))))
(define x (add-streams (mul-series cosine-series cosine-series)
                       (mul-series sine-series sine-series)))


;; Exercise 3.61
(define (invert-unit-series s)
  (define invert
    (cons-stream 1 (stream-map - (mul-series invert
                                             (stream-cdr s)))))
  invert)


;; Exercise 3.62
(define (div-series s1 s2)
  (if (equal? (stream-car s2) 0)
      (write "Error")
      (mul-series s1 (inver-unit-series s2))))


;; Exercise 3.63
;  Admit.


;; Exercise 3.64
(define (stream-limit s t)
  (if (< (abs (- (stream-ref s 0)
                 (stream-ref s 1)))
         t)
      (stream-ref s 1)
      (stream-limit (stream-cdr s) t)))


;; Exercise 3.65
;  Admit.


;; Exercise 3.66
;  Admit.


;; Exercise 3.67
;  wrong
(define (pairs s t)
  (cons-stream
   (list (stream-car s) (stream-car t))
   (interleave
    (interleave
     (stream-map (lambda (x) (list (stream-car s) x))
                 (stream-cdr t))
     (stream-map (lambda (x) (list x (stream-car t)))
                 (stream-cdr s)))
    (pairs (stream-cdr s) (stream-cdr t)))))


;; Exercise 3.68
;  Abort.


;; Exercise 3.69


;; Exercise 3.70
(define (merge-weighted s1 s2 weight)
  (cond ((stream-null? s1) s2)
        ((stream-null? s2) s1)
        (else
         (let ((s1car (stream-car s1))
               (s2car (stream-car s2)))
           (cond
             ((< (weight s1car) (weight s2car))
              (cons-stream s1car (merge-weighted (stream-cdr s1) s2 weight)))
             ((> (weight s1car) (weight s2car))
              (cons-stream s2car (merge-weighted s1 (stream-cdr s2) weight)))
             (else
              (cons-stream s1car
                           (cons-stream s2car
                                        (merge-weighted (stream-cdr s1)
                                                        (stream-cdr s2)
                                                        weight)))))))))

(define (weighted-pairs s t weight)
  (cons-stream
   (list (stream-car s) (stream-car t))
   (merge-weighted
    (stream-map (lambda (x) (list (stream-car s) x))
                (stream-cdr t))
    (weighted-pairs (stream-cdr s) (stream-cdr t) weight)
    weight)))

;  a
(define pa
  (weighted-pairs integers integers
                  (lambda (p) (+ (car p) (cadr p)))))
;  b
(define pb
  (stream-filter
   (lambda (p)
     (let ((p1 (car p))
           (p2 (cadr p)))
       (or (= (modulo p1 2) 0)
           (= (modulo p1 3) 0)
           (= (modulo p1 5) 0)
           (= (modulo p2 2) 0)
           (= (modulo p2 3) 0)
           (= (modulo p2 5) 0))))
   (weighted-pairs integers
                   integers
                   (lambda (p)
                     (+ (* 2 (car p))
                        (* 3 (cadr p))
                        (* 5 (car p) (cadr p)))))))

;; Exercise 3.71
(define (cube-sum p)
  (+ (expt (car p) 3)
     (expt (cadr p) 3)))

(define cube-sum-stream
  (weighted-pairs integers
                  integers
                  cube-sum))

(define (dup s)
  (if (equal? (stream-ref s 0)
              (stream-ref s 1))
      (cons-stream (stream-car s)
                   (dup (stream-cdr s)))
      (dup (stream-cdr s))))

(define (uniq s)
  (if (equal? (stream-ref s 0)
              (stream-ref s 1))
      (uniq (stream-cdr s))
      (cons-stream (stream-car s)
                   (uniq (stream-cdr s)))))

(define ramanujan
  (uniq (dup (stream-map cube-sum cube-sum-stream))))


;; Exercise 3.72
;  Admit.

