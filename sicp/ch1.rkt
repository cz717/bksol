;;; Chapter 1 Building Abstractions with Procedures

;; Exercise 1.1

;; Exercise 1.2
(/ (+ 5
      4
      (- 2 (- 3 (+ 6 (/ 1 3)))))
   (* 3
      (- 6 2)
      (- 2 7)))


;; Exercise 1.3
(define (square x)
  (* x x))

(define (sum-of-squares x y)
  (+ (square x) (square y)))

(define (foo a b c)
  (cond
    ((and (<= a b) (<= a c))
     (sum-of-squares b c))
    ((and (<= b a) (<= b c))
     (sum-of-squares a c))
    (else
     (sum-of-squares a b))))


;; Exercise 1.4


;; Exercise 1.5
(define (p) (p))

(define (test x y)
  (if (= x 0)
      0
      y))

(test 0 p)


;; Exercise 1.7
(define (newton-sqrt x)
  (define (good-enough? last-guess guess)
    (< (abs (/ (- last-guess guess)
               guess))
       0.001))
  (define (average x y)
    (/ (+ x y) 2))
  (define (improve guess x)
    (average guess (/ x guess)))
  (define (sqrt-iter last-guess guess x)
    (if (good-enough? last-guess guess)
        guess
        (sqrt-iter guess (improve guess x) x)))
  (sqrt-iter 2.0 1.0 x))


;; Exercise 1.8
(define (cube-root x)
  (define (improve guess x)
    (/ (+ (/ x (expt guess 2))
          (* 2 guess))
       3))
  (define (good-enough? last-guess guess)
    (< (abs (/ (- last-guess guess)
               guess))
       0.001))
  (define (cube-root-iter last-guess guess x)
    (if (good-enough? last-guess guess)
        guess
        (cube-root-iter guess
                        (improve guess x)
                        x)))
  (cube-root-iter 2.0 1.0 x))


;; Exercise 1.10
(define (A x y)
  (cond ((= y 0) 0)
        ((= x 0) (* 2 y))
        ((= y 1) 2)
        (else (A (- x 1)
                 (A x (- y 1))))))
; (f n) = (* 2 n)
; (g n) = (expt 2 n)
; (h n) = (expt 2 (expt 2 (expt 2 ... (expt 2 2)...)


;; Exercise 1.11
(define (f-rec n)
  (if (< n 3)
      n
      (+ (f-rec (- n 1))
         (* 2 (f-rec (- n 2)))
         (* 3 (f-rec (- n 3))))))

(define (f-ite n)
  (define (itef a b c n)
    (if (= n 0)
        a
        (itef b
               c
               (+ c
                 (* 2 b)
                 (* 3 a))
               (- n 1))))
  (itef 0 1 2 n))


;; Exercise 1.12
; (pascal n m) is the m th number of n th line
(define (pascal n m)
  (cond
    ((> m n) (write "Error : m > n in (pascal m n)"))
    ((= m 1) 1)
    ((= m n) 1)
    (else (+ (pascal (- n 1) (- m 1))
             (pascal (- n 1) m)))))


;; Exercise 1.15
; a. 5 times
; b. O(log a)


;; Exercise 1.16

