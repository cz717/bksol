;;; Chapter 2 Building Abstractions with Data
(load "ch1.rkt")
(load "support/ch2.scm")

;; Exercise 2.1
(define (make-rat n d)
  (let ((g (gcd (abs n) (abs d))))
    (if (< d 0)
        (cons (/ n (- 0 g))
              (/ d (- 0 g)))
        (cons (/ n g) (/ n g)))))


;; Exercise 2.2
(define make-segment cons)
(define start-segment car)
(define end-segment cdr)

(define make-point cons)
(define x-point car)
(define y-point cdr)

(define (midpoint-segment s)
  (let ((sp (start-segment s))
        (ep (end-segment s)))
    (make-point (/ (+ (x-point sp)
                      (x-point ep))
                   2)
                (/ (+ (y-point sp)
                      (y-point ep))
                   2))))


;; Exercise 2.3
(define (make-rect-diag s1 s2)
  ; s1 and s2 are two diagonal of the rectangle
  (if (equal? (midpoint-segment s1)
              (midpoint-segment s2))
      (cons s1 s2)
      (write "Error : invalid arg in (make-rect s1 s2)")))

(define (distance p1 p2)
  (sqrt (+ (expt (- (x-point p1)
                    (x-point p2))
                 2)
           (expt (- (y-point p1)
                    (y-point p2))
                 2))))

(define (long-side rectangle)
  (let ((s1 (car rectangle))
        (s2 (cdr rectangle)))
    (let ((p1 (start-segment s1))
          (p2 (end-segment s1))
          (p3 (start-segment s2)))
      (max (distance p1 p3)
           (distance p2 p3)))))

(define (short-side rectangle)
  (let ((s1 (car rectangle))
        (s2 (cdr rectangle)))
    (let ((p1 (start-segment s1))
          (p2 (end-segment s1))
          (p3 (start-segment s2)))
      (min (distance p1 p3)
           (distance p2 p3)))))

(define (perimeter rect)
  (* 2 (+ (long-side rect)
          (short-side rect))))

(define (area rect)
  (* (long-side rect) (short-side rect)))

; for test
(define a (make-point 1 0))
(define b (make-point 0 1))
(define c (make-point 3 4))
(define d (make-point 4 3))
(define s1 (make-segment a c))
(define s2 (make-segment b d))
(define rec (make-rect-diag s1 s2))


;; Exercise 2.4
(define (car24 z)
  (z (lambda (p q) q)))


;; Exercise 2.5
; encode pair (a b) into 2^a*3^b
(define (cons25 a b)
  (* (expt 2 a)
     (expt 3 b)))

(define (car25 x)
  (if (= (modulo x 2) 0)
      (+ 1 (car25 (/ x 2)))
      0))

(define (cdr25 x)
  (if (= (modulo x 3) 0)
      (+ 1 (cdr25 (/ x 3)))
      0))


;; Exercise 2.6
(define one
  (lambda (f)
    (lambda (x)
      (f x))))

(define two
  (lambda (f)
    (lambda (x)
      (f (f x)))))

(define (church-add m n)
  (lambda (f)
    (lambda (x)
      ((n f) ((m f) x)))))


;; Exercise 2.7
(define (upper-bound int)
  (max (car int) (cdr int)))
(define (lower-bound int)
  (min (car int) (cdr int)))


;; Exercise 2.8
(define (sub-interval x y)
  (make-interval
   (- (lower-bound x) (upper-bound y))
   (- (upper-bound x) (lower-bound y))))


;; Exercise 2.9
(define e1 (make-interval 2 3))
(define e2 (make-interval 3 4))
(define e3 (make-interval 5 6))
(mul-interval e1 e3)
(mul-interval e2 e3)
(div-interval e3 e1)
(div-interval e3 e2)

;; Exercise 2.10
(define (div-interval x y)
  (let ((ub (upper-bound y))
        (lb (lower-bound y)))
    (if (or (= ub 0) (= lb 0))
        (write "y may be 0 in (div-interval x y)")
        (mul-interval x
                      (make-interval (/ 1.0 ub)
                                     (/ 1.0 lb))))))


;; Exercise 2.11
(define (mul-interval x y)
  (let ((lx (lower-bound x))
        (ux (upper-bound x))
        (ly (lower-bound y))
        (uy (upper-bound y)))
    (let ((cx1 (and (< lx 0) (< ux 0)))
          (cx2 (and (< lx 0) (>= ux 0)))
          (cx3 (and (>= lx 0) (>= ux 0)))
          (cy1 (and (< ly 0) (< uy 0)))
          (cy2 (and (< ly 0) (>= uy 0)))
          (cy3 (and (>= ly 0) (>= uy 0))))
      (cond
        (cx1 (cond
               (cy1 (make-interval (* ux uy) (* lx ly)))
               (cy2 (make-interval (* lx uy) (* lx ly)))
               (cy3 (make-interval (* lx uy) (* ux ly)))))
        (cx2 (cond
               (cy1 (make-interval (* ux ly) (* lx ly)))
               (cy2 (make-interval (min (* lx uy) (* ux ly))
                                   (max (* lx ly) (* ux uy))))
               (cy3 (make-interval (* lx uy) (* ux uy)))))
        (cx3 (cond
               (cy1 (make-interval (* ux ly) (* lx uy)))
               (cy2 (make-interval (* ux ly) (* ux uy)))
               (cy3 (make-interval (* lx ly) (* ux uy)))))))))
        
