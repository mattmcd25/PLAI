#lang plai-typed
;; Matt McDonald

;; Starter code for CS 4536 hw 1
;; Dan Dougherty, adapted from code by Kathi Fisler
;; Jan 2018
;;
;; Some test cases are given.  Add some of your own!

;; ---------------------------------------------------------

;; This is convenient during program development:
;; " (undefined) " can be used as a place-holder for any expression,
;; for example something you want to postpone writing as you work on
;; other things.
;;
;; Don't forget the parens when using it...
(define (undefined) (error 'undefined "") )

;; ---------------------------------------------------------

; Produces the sum of the numbers in the list
(define (sum [L : (listof number)]) : number
  (foldr + 0 L))

(test (sum empty) 0)
(test (sum (list -3 3)) 0)
(test (sum (list 1 2 3)) 6)

;; ---------------------------------------------------------

; Produces the sum of the negative numbers in the list
(define (sum-negative [L : (listof number)]) : number
  (sum (filter (lambda (x) (< x 0)) L)))

(test (sum-negative (list 1 3 5 7)) 0)
(test (sum-negative (list -3 -4 0)) -7)

(test (sum-negative (list -3 -4 0 1 3 5 7)) -7)

;; ---------------------------------------------------------

; Produces list with same elts as input list, except negative
;  numbers have been replaced with 0
(define (raise [L : (listof number)]) : (listof number)
  (map (lambda (x) (if (< x 0) 0 x)) L))
  
(test (raise (list 69 -10 54)) (list 69 0 54))

(test (raise (list 70)) (list 70))
(test (raise empty) empty)

;; ---------------------------------------------------------
  
; alternating : list[A] -> list[A]
; Produces list of every other element from the input list
(define (alternating L)
  (let ([alternate (lambda (L)
                     (cond [(empty? L) empty]
                           [(cons? L) (alternating (rest L))]))])
    (cond [(empty? L) empty]
          [(cons? L) (cons (first L) (alternate (rest L)))])))
  
(test (alternating (list 1 2 3 4)) (list 1 3))
(test (alternating (list "hi" "there" "mom")) (list "hi" "mom"))

(test (alternating (list 1)) (list 1))
(test (alternating empty) empty)

;; ---------------------------------------------------------

; the datatypes

(define-type Scores
  [scores (midterm : number) (final : number) (grade : string)])
 
(define-type Student
  [undergrad (name : string) (grade : Scores) (grad-year : number)]
  [graduate (name : string) (grade : Scores) (program : string)])

(define std1 (undergrad "Amy" (scores 90 83 "") 2015))
(define std2 (graduate "Phil" (scores 70 50 "") "PhD"))
(define std3 (graduate "Xin" (scores 80 85 "") "MS"))
(define std4 (undergrad "Gompei" (scores 50 40 "") 1900))

(define std1g (undergrad "Amy" (scores 90 83 "high pass") 2015))
(define std2g (graduate "Phil" (scores 70 50 "fail") "PhD"))
(define std3g (graduate "Xin" (scores 80 85 "pass") "MS"))
(define std4g (undergrad "Gompei" (scores 50 40 "fail") 1900))

(define f (undergrad "Fail" (scores 50 50 "") 2000))
(define f2 (undergrad "Fail" (scores 50 50 "fail") 2000))
(define p (undergrad "Pass" (scores 65 65 "") 2000))
(define p2 (undergrad "Pass" (scores 65 65 "pass") 2000))
(define h (undergrad "High" (scores 85 85 "") 2000))
(define h2 (undergrad "High" (scores 85 85 "high pass") 2000))

;; ---------------------------------------------------------
;; assign-grades

; Produce a score with the course grade computed from midterm and final grades
(define (compute-grade [s : Scores]) : Scores
  (let* ([m (scores-midterm s)]
         [f (scores-final s)]
         [avg (/ (+ m f) 2)])
    (if (>= avg 85)
        (scores m f "high pass")
        (if (>= avg 65)
            (scores m f "pass")
            (scores m f "fail")))))

; Augment each student in input list with a course grade
(define (assign-grades [studL : (listof Student)]) : (listof Student)
  (let ([update (lambda (s) (cond [(undergrad? s) (undergrad (undergrad-name s)
                                                    (compute-grade (undergrad-grade s))
                                                    (undergrad-grad-year s))]
                         [(graduate? s) (graduate (graduate-name s)
                                                  (compute-grade (graduate-grade s))
                                                  (graduate-program s))]))])
  (map update studL)))

(test (assign-grades (list std1 std2 std3 std4))
      (list std1g std2g std3g std4g))

(test (assign-grades (list f p h)) (list f2 p2 h2))
(test (assign-grades empty) empty)

;; ---------------------------------------------------------
  
; determine whether all phd students have passing course grades
(define (all-phd-pass? [studL : (listof Student)]) : boolean
  (let ([gradedL (assign-grades studL)])
    (not (foldr (lambda (x y) (or x y)) false (map (lambda (s) (string=? "fail" (scores-grade (graduate-grade s)))) (filter graduate? gradedL))))))

(test (all-phd-pass? (list std1g std3g)) true)
(test (all-phd-pass? (list std1g std2g std3g)) false)

(test (all-phd-pass? (list std3g std4g)) true)
(test (all-phd-pass? (list std3 std4)) true)
(test (all-phd-pass? empty) true)
(test (all-phd-pass? (list std1 std2 std3)) false)

;; ---------------------------------------------------------
;; rainfall

  
;; produce average of non-negative numbers that appear before -999 in a list
(define (rainfall [L : (listof number)]) : number
  (let ([readings (filter (lambda (n) (>= n 0)) (clean L))])
    (if (= (length readings) 0)
        -1
        (/ (sum readings) (length readings)))))

(define (take-until f l)
  (cond [(empty? l) empty]
        [(cons? l) (if (f (first l))
                       empty
                       (cons (first l) (take-until f (rest l))))]))

(define (clean [L : (listof number)]) : (listof number)
  (take-until (lambda (n) (= n -999)) L))

(test (rainfall (list 5 3 1)) 3)
(test (rainfall (list -4 -2 -999)) -1)
(test (rainfall (list 5 -2 3 -4 1 -999 555)) 3)
(test (rainfall empty) -1)

;; ---------------------------------------------------------
;; shopping cart

(define-type CartItem
  [item (name : string) (price : number)])

; determine the total price of a list of items
(define (cart-total [itemL : (listof CartItem)]) : number
  (sum (map item-price itemL)))


; produce total price of cart items, taking into account shoe and hat discounts
(define (checkout [itemL : (listof CartItem)]) : number
  (let* ([subtotal (cart-total itemL)]
         [shoes (filter (lambda (i) (string=? "shoes" (item-name i))) itemL)]         
         [shoe-cost (cart-total shoes)]
         [shoe-discount (if (>= shoe-cost 100) (* 0.2 shoe-cost) 0)]
         [hats (filter (lambda (i) (string=? "hat" (item-name i))) itemL)]
         [hat-discount (if (>= (length hats) 2) 10 0)])
    (- (- subtotal shoe-discount) hat-discount)))

; check no discounts
(test (checkout (list (item "apple" 25) (item "bag" 50)
                      (item "toothpaste" 85) (item "cheese" 15)))
      175)

; check shoes discount
(test (checkout (list (item "shoes" 25) (item "bag" 50)
                      (item "shoes" 85) (item "hat" 15)))
      153)

; check hat discount
(test (checkout (list (item "hat" 25) (item "bag" 50)
                      (item "shoes" 85) (item "hat" 15)))
      165)

; check both discounts
(test (checkout (list (item "shoes" 25) (item "hat" 50)
                      (item "shoes" 85) (item "hat" 15)))
      143)