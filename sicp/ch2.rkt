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
(define upper-bound cdr)
(define lower-bound car)


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


;; Exercise 2.12
(define (make-center-percent c p)
  (make-center-width c (* c p)))
(define (percent i)
  (let ((l (lower-bound i))
        (u (upper-bound i)))
    (/ (- u l) (+ u l))))


;; Exercise 2.13
; let i1 = (make-center-percent c1 p1)
;     i2 = (make-center-percent c2 p2)
; (mul-interval i1 i2)
; = ((lower i1)*(lower i2), (upper i1)*(upper i2))
; = (c1*(1-p1)*c2*(1-p2), c1*(1+p1)*c2(1+p2))
; = (c1*c2*(1-p1-p2+p1*p2), c1*c2*(1+p1+p2+p1*p2))
; = (c1*c2*[1-(p1+p2)], c1*c2*[1+(p1+p2)])
; = (make-center-percent (* c1 c2) (+ p1 p2))


;; Exercise 2.14
;  Admit.


;; Exercise 2.15
;  Abort.


;; Exercise 2.16
;  Abort.


;; Exercise 2.17
(define (last-pair x)
  (if (null? (cdr x))
      x
      (last-pair (cdr x))))


;;;; define nil
(define nil '())


;; Exercise 2.18
(define (reserve x)
  (define (help a b)
    (if (null? a)
        b
        (help (cdr a)
              (cons (car a) b))))
  (help x nil))


;; Exercise 2.19
(define first-denomination car)
(define except-first-denomination cdr)
(define no-more? null?)


;; Exercise 2.20
(define (same-parity x . y)
  (cond
    ((even? x)
     (cons x (filter even? y)))
    ((odd? x)
     (cons x (filter odd? y)))))


;; Exercise 2.21
(define (square-list items)
  (if (null? items)
      nil
      (cons (square (car items))
            (square-list (cdr items)))))

(define (square-list items)
  (map square items))


;; Exercise 2.22
;  Admit.


;; Exercise 2.23
(define (for-each2 proc items)
  (if (null? items)
      #t
      (begin
        (proc (car items))
        (for-each2 proc (cdr items)))))


;; Exercise 2.24
;  tree interpretation:
;    (1 (2 (3 4)))
;     _____|____
;     |    ____|____
;     1    |    ___|___
;          2    |     |
;               3     4
;  box-and-pointer interpretation:
;    Admit.


;; Exercise 2.25
(car (cdr (car (cdr (cdr '(1 3 (5 7) 9))))))
(car (car '((7))))
(cadr (cadr (cadr (cadr (cadr (cadr '(1 (2 (3 (4 (5 (6 7))))))))))))

;; Exercise 2.26
;  (1 2 3 4 5 6)
;  ((1 2 3) 4 5 6)
;  ((1 2 3) (4 5 6))


;; Exercise 2.27
(define (deep-reserve x)
  (define (help a b)
    (cond
      ((null? a) b)
      ((not (pair? a))
       a)
      (else
       (help (cdr a)
             (cons (help (car a) nil)
                   b)))))
  (help x nil))


;; Exercise 2.28
(define (fringe x)
  (cond
    ((null? x) nil)
    ((pair? (car x))
     (fringe (append (car x) (cdr x))))
    (else
     (cons (car x) (fringe (cdr x))))))


;; Exercise 2.29
;  a
(define left-branch car)
(define right-branch cadr)

(define branch-length car)
(define branch-structure cadr)
;  b
(define (total-weight mobile)
  (if (not (pair? mobile))
      mobile
      (let ((lb (left-branch mobile))
            (rb (right-branch mobile)))
        (+ (branch-weight lb)
           (branch-weight rb)
           (total-weight (branch-structure lb))
           (total-weight (branch-structure rb))))))
;  c
(define (balance? mobile)
  (if (not (pair? mobile))
      #t
      (let ((lb (left-branch mobile))
            (rb (right-branch mobile)))
        (let ((ll (branch-length lb))
              (ls (branch-structure lb))
              (rl (branch-length rb))
              (rs (branch-structure rb)))
          (and (balance? ls)
               (balance? rs)
               (= (* ll (total-weight ls))
                  (* rl (total-weight rs))))))))
;  d
(define right-branch cdr)
(define branch-structure cdr)


;; Exercise 2.30
(define (square-tree tree)
  (cond
    ((null? tree) nil)
    ((not (pair? tree)) (square tree))
    (else (cons (square-tree (car tree))
                (square-tree (cdr tree))))))

(define (square-tree tree)
  (map (lambda (sub-tree)
         (if (pair? sub-tree)
             (square-tree sub-tree)
             (square sub-tree)))
       tree))


;; Exercise 2.31
(define (tree-map proc tree)
  (cond
    ((null? tree) nil)
    ((not (pair? tree)) (proc tree))
    (else (cons (tree-map proc (car tree))
                (tree-map proc (cdr tree))))))


;; Exercise 2.32
(define (subsets s)
  (if (null? s)
      (list nil)
      (let ((rest (subsets (cdr s))))
        (append rest (map (lambda (x) (cons (car s) x))
                          rest)))))


;; Exercise 2.33
