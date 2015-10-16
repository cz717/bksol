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
(define (reverse218 x)
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
  (define (p s)
    (if (pair? s)
        (total-weight s)
        s))
  (+ (p (branch-structure (left-branch mobile)))
     (p (branch-structure (right-branch mobile)))))
;  c
(define (balance? mobile)
  (define (b m)
    (if (pair? m)
        (let ((lb (left-branch m))
              (rb (right-branch m)))
          (let ((ls (branch-structure lb))
                (rs (branch-structure rb)))
            (let ((b1 (b ls))
                  (b2 (b rs)))
              (cond ((= b1 #f) #f)
                    ((= b2 #f) #f)
                    ((= (* b1 (branch-length lb))
                        (* b2 (branch-length rb)))
                     (+ b1 b2))
                    (else #f))))))
    m)
  (not (= (b mobile) #f)))
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
(define (map233 p sequence)
  (accumulate (lambda (x y) (cons (p x) y)) nil sequence))

(define (append233 seq1 seq2)
  (accumulate cons seq2 seq1))

(define (length233 sequence)
  (accumulate (lambda (x y) (+ 1 y)) 0 sequence))


;; Exercise 2.34
(define (horner-eval x coefficient-sequence)
  (accumulate (lambda (this-coeff higher-terms)
                (+ this-coeff (* x higher-terms)))
              0
              coefficient-sequence))


;; Exercise 2.35
(define (count-leaves t)
  (accumulate +
              0
              (map (lambda (x)
                     (if (pair? x)
                         (count-leaves x)
                         1))
                    t)))


;; Exercise 2.36
(define (accumulate-n op init seqs)
  (if (null? (car seqs))
      nil
      (cons (accumulate op init (map car seqs))
            (accumulate-n op init (map cdr seqs)))))


;; Exercise 2.37
(define (matrix-*-vector m v)
  (map (lambda (x) (dot-product x v)) m))

(define (transpose mat)
  (accumulate-n cons nil mat))

(define (matrix-*-matrix m n)
  (let ((cols (transpose n)))
    (map (lambda (x)
           (matrix-*-vector cols x))
         m)))


;; Exercise 2.38
;  Abort.


;; Exercise 2.39
(define (reverse1 sequence)
  (fold-right (lambda (x y) <??>) nil sequence))

(define (reverse2 sequence)
  (fold-left (lambda (x y) (cons y x)) nil sequence))


;; Exercise 2.40
(define (unique-pairs n)
  (flatmap
   (lambda (x)
     (map (lambda (y) (list x y))
          (enumerate-interval 1 (- x 1))))
   (enumerate-interval 1 n)))

(define (prime-sum-pair n)
  (map make-pair-sum
       (filter prime-sum?
               (unique-pairs n))))


;; Exercise 2.41
(define (unique-orded-trip n s)
  (map
   (lambda (x)
     (list (car x) (cadr x) (- s (car x) (cadr x))))
   (filter
    (lambda (x)
      (let ((t (- s (car x) (cadr x))))
        (and (and (> t 0) (<= t n))
             (not (or (= (car x) (cadr x))
                      (= (car x) t)
                      (= (cadr x) t))))))
    (flatmap
     (lambda (x)
       (map (lambda (y) (list x y))
            (enumerate-interval 1 n)))
     (enumerate-interval 1 n)))))


;; Exercise 2.42
(define empty-board '())

(define (adjoin-position new-row k rest-of-queens)
  (append rest-of-queens (list new-row)))

(define (safe? k positions)
  (define (not-check p x kth)
    (let ((xth (car p)))
      (if (>= x k)
          #t
          (if (not (or (= xth kth)
                       (= (- kth k) (- xth x))
                       (= (+ kth k) (+ xth x))))
              (not-check (cdr p) (+ x 1) kth)
              #f))))
  (define (nth n l)
    (if (= n 1)
        (car l)
        (nth (- n 1) (cdr l))))
  (not-check positions 1 (nth k positions)))


;; Exercise 2.43
;  (* T (expt 8 8))


;; Exercise 2.44
(define (up-split painter n)
  (if (= n 0)
      painter
      (let ((smaller (up-split painter (- n 1))))
        (below painter (beside smaller smaller)))))


;; Exercise 2.45
(define (split t1 t2)
  (lambda (painter n)
    (if (= n 0)
        painter
        (let ((smaller ((split t1 t2) painter (- n 1))))
          (t1 painter (t2 smaller smaller))))))


;; Exercise 2.46
(define make-vect cons)
(define xcor-vect car)
(define ycor-vect cdr)

(define (add-vect v1 v2)
  (make-vect (+ (xcor-vect v1) (xcor-vect v2))
             (+ (ycor-vect v1) (ycor-vect v2))))

(define (sub-vect v1 v2)
  (make-vect (- (xcor-vect v1) (xcor-vect v2))
             (- (ycor-vect v1) (ycor-vect v2))))

(define (scale-vect s v)
  (make-vect (* s (xcor-vect v))
             (* s (ycor-vect v))))


;; Exercise 2.47
;  the 1st implementation
(define (make-frame origin edge1 edge2)
  (list origin edge1 edge2))

(define origin-frame car)
(define edge1-frame cadr)
(define edge2-frame caddr)

;  the 2nd implementation
(define (make-frame origin edge1 edge2)
  (cons origin (cons edge1 edge2)))

(define origin-frame car)
(define edge1-frame cadr)
(define edge2-frame cddr)


;; Exercise 2.48
(define make-segment cons)
(define start-segment car)
(define end-segment cdr)
  

;; Exercise 2.49
;  a
(define (draw-outline frame)
  (let ((bl (make-vect 0.0 0.0))
        (br (make-vect 1.0 0.0))
        (ul (make-vect 0.0 1.0))
        (ur (make-vect 1.0 1.0)))
    (segments->painter
     (list (make-segment bl ul)
           (make-segment bl br)
           (make-segment ul ur)
           (make-segment br ur)))))
;  b
(define (draw-x frame)
  (let ((bl (make-vect 0.0 0.0))
        (br (make-vect 1.0 0.0))
        (ul (make-vect 0.0 1.0))
        (ur (make-vect 1.0 1.0)))
    (segments->painter
     (list (make-segment bl ur)
           (make-segment br ul)))))
;  c
(define (draw-diamond frame)
  (let ((bm (make-vect 0.5 0.0))
        (um (make-vect 0.5 1.0))
        (lm (make-vect 0.0 0.5))
        (rm (make-vect 1.0 0.5)))
    (segments->painter
     (list (make-segment bm lm)
           (make-segment bm rm)
           (make-segment um lm)
           (make-segment bm rm)))))
;  d
; Admit.


;; Exercise 2.50
(define (flip-horiz painter)
  (transform-painter painter
                     (make-vect 1.0 0.0)
                     (make-vect 0.0 0.0)
                     (make-vect 1.0 1.0)))

(define (rotate180 painter)
  (transform-painter painter
                     (make-vect 1.0 1.0)
                     (make-vect 0.0 1.0)
                     (make-vect 1.0 0.0)))

(define (rotate270 painter)
  (transform-painter painter
                     (make-vect 1.0 0.0)
                     (make-vect 0.0 0.0)
                     (make-vect 1.0 1.0)))


;; Exercise 2.51
(define (below painter1 painter2)
  (let ((split-point (make-vect 0.0 0.5)))
    (let ((paint-below
           (transform-painter painter1
                              (make-vect 0.0 0.0)
                              (make-vect 1.0 0.0)
                              split-point))
          (paint-above
           (transform-painter painter2
                              split-point
                              (make-vect 1.0 0.5)
                              (make-vect 0.0 1.0))))
      (lambda (frame)
        (paint-below frame)
        (paint-above frame)))))

(define (below painter1 painter2)
  (rotate90 (beside (rotate90 painter1)
                    (rotate90 painter2))))


;; Exercise 2.52
;  Admit.


;; Exercise 2.53
;  (a b c)
;  ((george))
;  ((y1 y2))
;  (y1 y2)
;  #f
;  #f
;  (red shoes blue socks)


;; Exercise 2.54
(define (equal?254 a b)
  (cond
    ((and (symbol? a) (symbol? b))
     (eq? a b))
    ((and (null? a) (null? b))
     #t)
    ((and (pair? a) (pair? b))
     (and (equal?254 (car a) (car b))
          (equal?254 (cdr a) (cdr b))))
    (else
     #f)))


;; Exercise 2.55
; ''abracadabra is actualy (quote (quote abracadabra)),
; which is a list of symbol (quote abracadabra).


;; Exercise 2.56
(define (exponentiation? a)
  (and (pair? a) (eq? (car a) '**)))

(define (base e) (cadr e))

(define (exponent e) (caddr e))

(define (make-exponentiation b e)
  (cond
    ((=number? e 0) 1)
    ((=number? e 1) b)
    ((and (number? b) (number? e))
     (expt b e))
    (else
     (list '** b e))))

(define (deriv exp var)
  (cond ((number? exp) 0)
        ((variable? exp)
         (if (same-variable? exp var) 1 0))
        ((sum? exp)
         (make-sum (deriv (addend exp) var)
                   (deriv (augend exp) var)))
        ((product? exp)
         (make-sum
           (make-product (multiplier exp)
                         (deriv (multiplicand exp) var))
           (make-product (deriv (multiplier exp) var)
                         (multiplicand exp))))
        ((exponentiation? exp)
         (make-prodcuct
          (exponent exp)
          (make-product
           (make-exponentiation (base exp) (- (exponent exp) 1))
           (deriv (base (base exp) var)))))
        (else
         (error "unknown expression type -- DERIV" exp))))


;; Exercise 2.57
(define (make-sum a1 a2 . an)
  (append (list '+ a1 a2) an))

(define (sum? x)
  (and (pair? x) (eq? (car x) '+)))

(define (addend s) (cadr s))

(define (augend s)
  (if (> (length s) 3)
      (cons '+ (cddr s))
      (caddr s)))


;; Exercise 2.58
;  a
(define (make-sum a1 a2)
  (list a1 '+ a2))
(define (sum? x)
  (and (pair? x) (eq? (cadr x) '+)))
(define (addend s) (car s))
(define (augend s) (caddr s))

(define (make-product a1 a2)
  (list a1 '* a2))
(define (product? x)
  (and (pair? x) (eq? (cadr x) '*)))
(define (multiplier s) (car s))
(define (multiplicand s) (caddr s))

;  b
(define (make-sum a1 a2)
  (append
   (if (pair? a1) a1 (list a1))
   '(+)
   (if (pair? a2) a2 (list a2))))

(define (sum? x)
  (memq? '+ x))

(define (addend s)
  (define (list-head l k)
    (if (zero? k)
        '()
        (cons (car l) (list-head (cdr l) (- k 1)))))
  (let ((k (- (length s)
              (length (memq '+ s)))))
    (if (> k 1)
        (list-head s k)
        (car s))))

(define (augend s)
  (let ((x (memq '+ s)))
    (if (> (length x) 2)
        (cdr x)
        (cadr x))))

(define (make-product a1 a2)
  (append
   (if (product? a1) a1 (list a1))
   '(*)
   (if (product? a2) a2 (list a2))))

(define (product? x)
  (and (pair? x) (eq? (cadr x) '*)))

(define (multiplier s) (car s))
(define (multiplicand s)
  (if (> (length s) 3)
      (cddr s)
      (caddr s)))

;  test
(define a1 (make-sum 'y 2))
(define a2 (make-sum 'x a1))
(define a3 (make-product 3 a2))
(define a4 (make-sum 'x a3))


;; Exercise 2.59
(define (union-set s1 s2)
  (cond
    ((null? s1) s2)
    ((element-of-set? (car s1) s2)
     (union-set (cdr s1) s2))
    (else
     (union-set (cdr s1) (adjoin-set (car s1) s2)))))


;; Exercise 2.60
(define (element-of-set? x set)
  (cond ((null? set) #f)
        ((equal? x (car set)) #t)
        (else (element-of-set? x (cdr set)))))

(define (adjoin-set x set)
  (cons x set))

(define (intersection-set set1 set2)
  (cond ((or (null? set1) (null? set2)) '())
        ((element-of-set? (car set1) set2)
         (cons (car set1)
               (intersection-set (cdr set1) set2)))
        (else (intersection-set (cdr set1) set2))))

(define (union-set s1 s2)
  (append s1 s2))


;; Exercise 2.61
(define (adjoin-set x set)
  (cond
    ((null? set) (list x))
    ((> x (car set))
     (cons (car set) (adjoin-set x (cdr set))))
    ((equal? x (car set))
     set)
    ((< x (car set))
     (cons x set))))


;; Exercise 2.62
(define (union-set set1 set2)
  (cond
    ((null? set1) set2)
    ((null? set2) set1)
    (else
     (let ((x1 (car set1)) (x2 (car set2)))
       (cond
         ((= x1 x2)
          (cons x1 (union-set (cdr set1) (cdr set2))))
         ((< x1 x2)
          (cons x1 (union-set (cdr set1) set2)))
         ((< x2 x1)
          (cons x2 (union-set set1 (cdr set2)))))))))


;; Exercise 2.63
;  a not
;  b same


;; Exercise 2.64
;  Admit.


;; Exercise 2.65
;  Admit.


;; Exercise 2.66
(define (lookup? given-key set)
  (cond ((null? set) #f)
        ((= given-key (key (entry set))) (entry set))
        ((< given-key (key (entry set)))
         (element-of-set? given-key (left-branch set)))
        ((> given-key (key (entry set)))
         (element-of-set? given-key (right-branch set)))))


;; Exercise 2.67
;  Admit.


;; Exercise 2.68
(define (encode-symbol s tree)
  (cond
    ((leaf? tree)
     '())
    ((not (element-of-set? s (symbols tree)))
     (write "given symbol not in the tree"))
    ((element-of-set? s (symbols (left-branch tree)))
     (cons 0 (encode-symbol s (left-branch tree))))
    ((element-of-set? s (symbols (right-branch tree)))
     (cons 1 (encode-symbol s (right-branch tree))))))

    
;; Exercise 2.69
(define (successive-merge trees)
  (cond
    ((null? trees) '())
    ((= (length trees) 1)
     (car trees))
    (else
     (successive-merge
      (adjoin-set (make-code-tree (car trees) (cadr trees))
                  (cddr trees))))))


;; Exercise 2.70
;  Admit.


;; Exercise 2.71
;  1, n-1


;; Exercise 2.72
;  O(1), O(n)


;; Exercise 2.73
