#lang plai-typed

(require "type-inf.mjmcdonald.rkt")

;; 1. Generic Test
;; 2. Using some function to generate its input
;; 3. Using its output in another function
;; 4. Generating invalid input (ERROR)
;; 5. Using output incorrectly (ERROR)

"Tests for num" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test (generate-constraints (numS 5)) (list (ceq (typevar-subexp (numS 5)) (typeconstant 'number))))
(test/type '5 (numT))
""

"Tests for bool" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type (symbol->s-exp 'tru) (boolT))
(test/type (symbol->s-exp 'fls) (boolT))
""

"Tests for empty" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type (symbol->s-exp 'tempty) (tlistT (varT 'list)))
""

"Tests for plus" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(+ 3 5) (numT))
(test/type/exn '(+ 3 tru) "type error")
(test/type/exn '(+ fls 5) "type error")
(test/type/exn '(+ 3 (+ fls 5)) "type error")
""

"Tests for minus" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(- 5 3) (numT))
(test/type '(- 5 (+ 1 2)) (numT))
(test/type/exn '(- 3 tru) "type error")
""

"Tests for mult" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(* 5 3) (numT))
(test/type '(* 5 (+ 1 2)) (numT))
(test/type/exn '(* 3 tru) "type error")
""

"Tests for iszero" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(iszero 6) (boolT))
(test/type '(iszero (+ 6 (* 4 5))) (boolT))
(test/type/exn '(iszero tru) "type error")
(test/type/exn '(+ (iszero tru) 6) "type error")
""

"Tests for if" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(bif tru 0 1) (numT))
(test/type '(bif (iszero 6) tru fls) (boolT))
(test/type/exn '(bif 0 0 1) "type error")
(test/type/exn '(bif tru tru 1) "type error")
""

"Tests for cons" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(tcons 1 tempty) (tlistT (numT)))
(test/type '(tcons 1 (tcons 2 (tcons 3 tempty))) (tlistT (numT)))
(test/type/exn '(tcons 1 (tcons tru tempty)) "type error")
(test/type/exn '(tcons 1 1) "type error")
(test/type/exn '(tcons (tcons 1 tempty) 2) "type error")
""

"Tests for isempty" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(tempty? tempty) (boolT))
(test/type '(tempty? (tcons 1 tempty)) (boolT))
(test/type '(tempty? (tcons 1 (tcons 2 tempty))) (boolT))
(test/type '(bif (tempty? tempty) 1 0) (numT))
(test/type/exn '(iszero (tempty? tempty)) "type error")
(test/type/exn '(tempty? 1) "type error")
""

"Tests for tfirst" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(tfirst (tcons 1 tempty)) (numT))
(test/type '(+ (tfirst (tcons 1 tempty)) 2) (numT))
(test/type/exn '(+ (tfirst (tcons fls tempty)) 0) "type error")
(test/type/exn '(tfirst 1) "type error")
""

"Tests for trest" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(trest (tcons 1 tempty)) (tlistT (numT)))
(test/type/exn '(+ (trest (tcons 1 tempty)) 2) "type error")
(test/type '(tempty? (trest (tcons fls tempty))) (boolT))
(test/type/exn '(trest 1) "type error")
""

"Tests for fun" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(fun (y) (+ y 1)) (funT (numT) (numT)))
(test/type '(fun (y) (tcons 1 y)) (funT (tlistT (numT)) (tlistT (numT))))
(test/type '(fun (y) (tfirst y)) (funT (tlistT (varT 'x)) (varT 'y)))
(test/type '(tcons (fun (a) a) (tcons (fun (b) b) tempty)) (tlistT (funT (varT 'x) (varT 'x))))
(test/type/exn '(+ (fun (y) 5) 1) "type error")
""

"Tests for app" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(fun (g) (fun (x) ((fun (y) (+ y 1)) (g x)))) (funT (funT (varT 'x) (numT)) (funT (varT 'x) (numT))))
(test/type '((fun (g) (+ g 1)) 6) (numT))
(test/type '((fun (g) (fun (x) (+ x g))) 1) (funT (numT) (numT)))
(test/type '(+ ((fun (x) (+ x 1)) 1) 1) (numT))
(test/type/exn '((+ x 1) 1) "type error")
(test/type/exn '(((fun (x) (+ x 1)) 4) 5) "type error")
""

"Tests for with" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(with ((x 5)) (+ x 5)) (numT))
(test/type '(with ([succ (fun (x) (+ x 1))]) (succ 9)) (numT))
(test/type '(bif (with ([not (fun (b) (bif b fls tru))]) (not tru)) 0 1) (numT))
(test/type '(with ([list1 (tcons 1 tempty)]) (tcons tru tempty)) (tlistT (boolT)))
(test/type '(with ([list1 (tcons 1 tempty)]) (with ([list2 (tcons tru tempty)]) (+ (tfirst list1) 9))) (numT))
(test/type/exn '(with ([succ (fun (x) (+ x 1))]) (succ tru)) "type error")
(test/type/exn '(with ([x 4]) (bif x 0 1)) "type error")
(test/type/exn '(+ (with ([x 5]) tru) 1) "type error")
""

"Tests for rec" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(rec ((x 5)) (+ x 5)) (numT))
(test/type '(rec ([succ (fun (x) (+ x 1))]) (succ 9)) (numT))
(test/type '(bif (rec ([not (fun (b) (bif b fls tru))]) (not tru)) 0 1) (numT))
(test/type '(rec ([list1 (tcons 1 tempty)]) (tcons tru tempty)) (tlistT (boolT)))
(test/type '(rec ([list1 (tcons 1 tempty)]) (rec ([list2 (tcons tru tempty)]) (+ (tfirst list1) 9))) (numT))
(test/type/exn '(rec ([succ (fun (x) (+ x 1))]) (succ tru)) "type error")
(test/type/exn '(rec ([x 4]) (bif x 0 1)) "type error")
(test/type/exn '(+ (rec ([x 5]) tru) 1) "type error")
(test/type '(rec ([f (fun (x) (bif (iszero x) 1 (* x (f (- x 1)))))]) f) (funT (numT) (numT)))
""

"Tests from class notes" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test/type '(+ x 2) (numT))
(test/type '(fun (x) (+ x 2)) (funT (numT) (numT)))
(test/type '(bif (f 2) 3 4) (numT))
(test/type '(f (f 2)) (numT))
(test/type '(f (f x)) (varT 'x))
(test/type '(bif (f x) (g x) (f 2)) (boolT))
(test/type/exn '(bif (f x) x (f 2)) "type error")
(test/type '(rec ([sum (fun (x) (bif (tempty? x) 0 (+ (tfirst x) (sum (trest x)))))]) sum) (funT (tlistT (numT)) (numT)))
(test/type '(rec ([f (fun (x) (bif (tempty? x) 0 (+ 1 (f (trest x)))))]) f) (funT (tlistT (varT 'x)) (numT)))
(test/type/exn '(fun (x) (x x)) "type error")
""