#lang plai-typed

(require "mutation.mjmcdonald.rkt")

;; ========================================== UTILITIES TO REPLACE RUN/ENV ==========================================
;; a run-command using the given env and sto just returning values
(define (run/all-v sexp env sto)
  (v*s-v (run/all sexp env sto)))


;; a run-command using the given env and sto
(define (run/all sexp env sto)
  (interp (desugar (parse sexp)) env sto))




; ========================================== MISCELLANEOUS TESTS, FROM HOMEWORK 2 ==========================================
; =============== BASIC MATH ===============
(test (run-v '3) (numV 3)) ; test numbers are a valid program
(test (run-v '(+ (* 5 (+ 7 3)) 4)) (numV 54)) ; addition and multiplication
(test (run-v '(- 7 4)) (numV 3)) ; subtraction works
(test (run/all-v '(+ x 1) (list (bind 'x 1)) (list (cell 1 (numV 2)))) (numV 3))

; =============== CONDITIONALS ===============
(test (run/all-v '(if0 (- 2 x) 6 8) (list (bind 'x 1)) (list (cell 1 (numV 2)))) (numV 6)) ; test if0 when true
(test (run-v '(if0 (+ 2 2) 6 8)) (numV 8)) ; if0 false

; =============== FUNCTIONS ===============
(test (run-v '(fun (x) (+ x 3))) (closV (list 'x) (plusC (idC 'x) (numC 3)) mt-env)) ; test lambdas evaluate to closures
(test (run-v '((fun (x) (+ x 3)) 7)) (numV 10)) ; test functions can be applied anonymously
(test (run-v '(((fun (x) (fun (x) (+ x 2))) 3) 4)) (numV 6)) ; test scoping
(test (run-v '(((fun (x) (fun (y) (+ x y))) 3) 4)) (numV 7)) ; test scoping
(test (run-v '((fun (x y) (+ x y)) 2 3)) (numV 5)) ; test multiple arguments
(test (run-v '((fun () (+ 3 4)))) (numV 7)) ; test zero arguments
(test (run-v '(with ((x 16)) (with ((f (fun (a) x)) (x 32)) (f 0)))) (numV 16)) ; closure

; =============== WITH ===============
(test (run-v '(with ((f (fun (x) (* x 2)))) (f 5))) (numV 10)) ; with function
(test (run-v '(with ((x 6)) x)) (numV 6)) ; with variable
(test (run-v '(with ((x 6)) (with ((y x)) y))) (numV 6)) ; test nested withs
(test (run-v '(with ((x 3) (f (fun (x) (* x 2)))) (f x))) (numV 6)) ; with function and variable

; =============== UNBOUND ERRORS ===============
(test/exn (run '(+ 2 x)) "unbound") ; test unbound variable
(test/exn (run '(with ((x 5)) y)) "unbound") ; test unbound with definition
(test/exn (run '(with ((x 6) (y x)) y)) "unbound") ; test with behaves as 'let' NOT 'let*'

; =============== TYPE ERRORS ===============
(test/exn (run '(3 4)) "non-closure") ; test number instead of function
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

(test (run-v (factorial 6)) (numV 720))
(test (run-v (factorial 5)) (numV 120))
(test (run-v (factorial 1)) (numV 1))

(define-syntax-rule (fibbonaci z)
  (ycomb (with ((test (Y (fun (fib) (fun (n) (if0 n 0 (if0 (- n 1) 1 (+ (fib (- n 1)) (fib (- n 2))))))))))
                        (test z))))

(test (run-v (fibbonaci 0)) (numV 0))
(test (run-v (fibbonaci 1)) (numV 1))
(test (run-v (fibbonaci 7)) (numV 13))

(test (run-v '(with ((plus (fun (x y) (+ x y))) ; playing around with higher order functions
                   (partial (fun (f x) (fun (y) (f x y)))))
                  (with ((plus2 (partial plus 2)))
                        (plus2 5)))) (numV 7))

(test (run-v '(with ((sub (fun (x y) (- x y)))
                   (partial (fun (f x) (fun (y) (f x y))))
                   (flip (fun (f) (fun (a b) (f b a)))))
                  (with ((sub2 (partial (flip sub) 2)))
                        (sub2 5)))) (numV 3))




; ========================================== TESTS FROM HOMEWORK 3 ==========================================
; override-store
(test (fetch 1 (override-store (cell 1 (numV 6)) mt-store)) (numV 6))
(test (fetch 1 (override-store (cell 1 (numV 6)) (list (cell 1 (numV 5))))) (numV 6))

; desugar
(test (desugar (seqS (list (numS 1) (numS 2) (numS 3) (numS 4)))) (seqC (numC 1) (seqC (numC 2) (seqC (numC 3) (numC 4))))) ; 4
(test (desugar (seqS (list (numS 1) (numS 2) (numS 3)))) (seqC (numC 1) (seqC (numC 2) (numC 3)))) ; 3
(test (desugar (seqS (list (numS 1) (numS 2)))) (seqC (numC 1) (numC 2))) ; 2
(test (desugar (seqS (list (numS 1)))) (numC 1)) ; 1
(test/exn (desugar (seqS empty)) "empty")

; interp list
(test (vs*s-vs (interp-list (list (multC (numC 8) (numC 2)) (numC 32) (if0C (numC 0) (numC 64) (numC 128))) mt-env mt-store))              
      (list (numV 16) (numV 32) (numV 64)))
(test (run-v '(with ((x 6)) (+ (seq (set x 5) 5) x))) (numV 10)) ; interp list in +
(test (run-v '(with ((x 6)) (+ x (seq (set x 5) 5)))) (numV 11))
(test (run-v '(with ((x 2)) (* (seq (set x 3) 5) x))) (numV 15)) ; interp list in *
(test (run-v '(with ((x 2)) (* x (seq (set x 3) 5)))) (numV 10))
(test (run-v '(with ((x 3) (f (fun (x y) (+ x y)))) (f (seq (set x 4) 6) x))) (numV 10)) ; interp list in apply

; seq
(test (run-v '(seq 1 2 3 4 5)) (numV 5)) ; basic test
(test/exn (run-v '(seq (box (seq (set x 10) x)) x)) "unbound") ; scoping with mutation

; boxes
(test (run-v '(with ((b (box (* 3 (+ 3 1))))) (unbox b))) (numV 12)) ; basic box and unbox
(test (run-v '(with ((b (box 6))) (seq (setbox b 10) (unbox b)))) (numV 10)) ; setbox
(test (run-v '(with ((b 11)) (set b 7))) (numV 7)) ; set
(test (run-v '(with ((x 0)) (unbox (box (seq (set x 1) x))))) (numV 1))
(test (run-v '(with ((b 5)) (with ((a b)) (seq (set b 9) a)))) (numV 5)) ; example 1 from class
(test (run-v '(with ((b (box 5))) (with ((a b)) (seq (setbox b 9) (unbox a))))) (numV 9)) ; example 2 from class
(test (run-v '(with ((b (box 5))) (with ((a b)) (seq (set b (box 9)) (unbox a))))) (numV 5)) ; example 3 from class

(test (run-v '(with ((f 0)) (seq (set f (fun (x) (if0 x 1 (* x (f (- x 1)))))) (f 5)))) (numV 120)) ; recursion with mutation