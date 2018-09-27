#lang plai-typed

(require "first-class-funcs.mjmcdonald.rkt")

; =============== BASIC MATH ===============
(test (run '3) (numV 3)) ; test numbers are a valid program
(test (run '(+ (* 5 (+ 7 3)) 4)) (numV 54)) ; addition and multiplication
(test (run '(- 7 4)) (numV 3)) ; subtraction works

; =============== CONDITIONALS ===============
(test (run/env '(if0 (- 2 x) 6 8) (list (bind 'x (numV 2)))) (numV 6)) ; test if0 when true
(test (run '(if0 (+ 2 2) 6 8)) (numV 8)) ; if0 false

; =============== FUNCTIONS ===============
(test (run '(fun (x) (+ x 3))) (closV (list 'x) (plusC (idC 'x) (numC 3)) mt-env)) ; test lambdas evaluate to closures
(test (run '((fun (x) (+ x 3)) 7)) (numV 10)) ; test functions can be applied anonymously
(test (run '(((fun (x) (fun (x) (+ x 2))) 3) 4)) (numV 6)) ; test scoping
(test (run '(((fun (x) (fun (y) (+ x y))) 3) 4)) (numV 7)) ; test scoping
(test (run '((fun (x y) (+ x y)) 2 3)) (numV 5)) ; test multiple arguments
(test (run '((fun () (+ 3 4)))) (numV 7)) ; test zero arguments

; =============== WITH ===============
(test (run '(with ((f (fun (x) (* x 2)))) (f 5))) (numV 10)) ; with function
(test (run '(with ((x 6)) x)) (numV 6)) ; with variable
(test (run '(with ((x 6)) (with ((y x)) y))) (numV 6)) ; test nested withs
(test (run '(with ((x 3) (f (fun (x) (* x 2)))) (f x))) (numV 6)) ; with function and variable

; =============== UNBOUND ERRORS ===============
(test/exn (run '(+ 2 x)) "unbound") ; test unbound variable
(test/exn (run '(with ((x 5)) y)) "unbound") ; test unbound with definition
(test/exn (run '(with ((x 6) (y x)) y)) "unbound") ; test with behaves as 'let' NOT 'let*'

; =============== TYPE ERRORS ===============
(test/exn (run '(3 4)) "type") ; test number instead of function
(test/exn (run '(if0 (fun (x) 5) 3 4)) "type") ; test if0 with a function
(test/exn (run '(+ (fun (x) 5) 4)) "type") ; test + with a function
(test/exn (run '(* (fun (x) 3) 7)) "type") ; test * with a function

; =============== MULTIPLE ERRORS ===============
(test/exn (run '(with ((x 4) (x 3)) x)) "multiple") ; test same name with definition
(test/exn (run '(fun (x x) (+ x 2))) "multiple") ; test same name function argument
(test/exn (run '((fun (x y x) 3) 4 4 4)) "multiple") ; same name function argument

; =============== LENGTH ERRORS ===============
(test/exn (run '((fun (x y) (+ x y)) 1 2 3)) "length") ; test too many args
(test/exn (run '((fun (x y z) (+ x y)) 1 2)) "length") ; test not enough args

; =============== PARSING ERRORS ===============
(test/exn (run '((fun (3) (+ 3 1)) 3)) "not a symbol") ; test invalid argument name
(test/exn (run '("hi")) "expected")
(test/exn (run '"hi") "expected")

; =============== MISC TESTS ===============
(define-syntax-rule (ycomb expr) ; recursive functions with Y combinator
  '(with ((Y (fun (le) ((fun (f) (f f)) (fun (f) (le (fun (x) ((f f) x)))))))) expr))

(define-syntax-rule (factorial z)
  (ycomb (with ((test (Y (fun (fact) (fun (n) (if0 n 1 (* n (fact (- n 1)))))))))
                        (test z))))

(test (run (factorial 6)) (numV 720))
(test (run (factorial 5)) (numV 120))
(test (run (factorial 1)) (numV 1))

(define-syntax-rule (fibbonaci z)
  (ycomb (with ((test (Y (fun (fib) (fun (n) (if0 n 0 (if0 (- n 1) 1 (+ (fib (- n 1)) (fib (- n 2))))))))))
                        (test z))))

(test (run (fibbonaci 0)) (numV 0))
(test (run (fibbonaci 1)) (numV 1))
(test (run (fibbonaci 7)) (numV 13))

(test (run '(with ((plus (fun (x y) (+ x y))) ; playing around with higher order functions
                   (partial (fun (f x) (fun (y) (f x y)))))
                  (with ((plus2 (partial plus 2)))
                        (plus2 5)))) (numV 7))

(test (run '(with ((sub (fun (x y) (- x y)))
                   (partial (fun (f x) (fun (y) (f x y))))
                   (flip (fun (f) (fun (a b) (f b a)))))
                  (with ((sub2 (partial (flip sub) 2)))
                        (sub2 5)))) (numV 3))