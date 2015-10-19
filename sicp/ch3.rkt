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
