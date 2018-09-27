#lang plai

#| This is just a HINT of some of the many things you can/should test
about an object implementation (And it will get you started with
examples of the format for classes.)

The test file *we* will run on your code has about 35 tests, by the
way!


I implemented all features, so all will be tested.
|#

(require "objects.mjmcdonald.rkt")

;; test suite for the objects assignment

;;
;; The Classes
;;

; parent-less class
(define CTop
  '(class Top ()
     (parent Object)
     (private (pr1 4) (pr2 6))
     (public (pub1 8) (pub2 10))
     (add-private (fun (x) (+ x pr1)))
     (add-publics (fun () (+ pub1 pub2)))
     ;(try-parent (fun () parent))
     ))
       
; no private vars, override a parent's public var
(define CMid
  '(class Middle (c1 c2)
     (parent Top)
     (private (pr3 100))
     (public (pub1 2) (pub3 7))
     (get-constr (fun () c2))
     (inc-constr (fun () (seq (set c2 (+ c2 1)) c2)))
     (use-publics (fun () (* pub1 pub3)))
     (add-pub-parent-priv (fun () (+ pub3 pr1)))
     (get-parent-pub1 (fun () (send parent get-pub1)))
     (inc-private (fun () (seq (set pr3 (+ 1 pr3)) pr3)))
     (check-parent-pub (fun () pub2))
     ))

; calls parent constructor in creation
(define CBottom
  '(class Bottom ()
     (parent Middle 99 100)
     (private)
     (public)
     ))

; box that holds values
(define CBox
  '(class Box (x)
     (parent Object)
     (private)
     (public)
     (get-value (fun () x))
     (set-value (fun (y) (set x y)))
     (invoke (fun (y) (x y)))
     ))

(define CLASSES (list CBox CTop CMid CBottom))

;;
;; THE TESTS  
;;

;; =========== Tests about constructors ===========
(test/exn (run/classes '(send (new Middle 0 1) get-c1) CLASSES) "unbound") ; can't get constructors
(test/exn (run/classes '(send (new Middle 0 1) set-c1 2) CLASSES) "unbound") ; can't set constructors
(test (run/classes '(with ((con 5)) (seq (send (new Middle 1 con) inc-constr) con)) CLASSES) (numV 5)) ; can't be accessed from outside
(test (run/classes '(with ((con 5)) (with ((mid (new Middle 1 con))) (seq (set con 6) (send mid get-constr)))) CLASSES) (numV 5)) ; can't be modified from outside

;; =========== Tests about privates ===========
(test/exn (run/classes '(send (new Middle 0 1) get-pr3) CLASSES) "unbound") ; privates dont have getters
(test/exn (run/classes '(send (new Middle 0 1) set-pr3 99) CLASSES) "unbound") ; privates dont have setters

;; =========== Tests about publics ===========
(test (run/classes '(send (new Middle 0 1) get-pub1) CLASSES) (numV 2)) ; publics have getters
(test (run/classes '(send (new Middle 0 1) set-pub1 10) CLASSES) (numV 10)) ; publics have setters
(test (run/classes '(with ((obj (new Middle 0 1))) (seq (send obj set-pub1 10) (send obj get-pub1))) CLASSES) (numV 10)) ; publics can be mutated
(test (run/classes '(with ((obj1 (new Middle 0 1)) (obj2 (new Middle 0 1))) (seq (send obj1 set-pub1 10) (send obj2 get-pub1))) CLASSES) (numV 2)) ; objects each have their own vars

;; =========== Tests about methods ===========
(test (run/classes '(send (new Middle 0 1) inc-private) CLASSES) (numV 101)) ; privates exist and methods can use privates
(test (run/classes '(with ((obj (new Middle 0 1))) (send obj use-publics)) CLASSES) (numV 14)) ; publics can be used in methods, too
(test/exn (run/classes '(send (new Top) get-constr) CLASSES) "unbound") ; no connection from parent to child methods

;; =========== Tests about inheritances ===========
(test (run/classes '(send (new Middle 0 1) add-private 1) CLASSES) (numV 5)) ; can dispatch to parent's methods
(test (run/classes '(send (new Middle 0 1) get-parent-pub1) CLASSES) (numV 8)) ; methods can call parent
(test/exn (run/classes '(send (new Middle 1 2) add-pub-parent-priv) CLASSES) "unbound") ; can't access parent's private
(test (run/classes '(send (new Middle 0 1) get-pub2) CLASSES) (numV 10)) ; can access parent's publics (via getter)
(test (run/classes '(with ((mid (new Middle 0 1))) (seq (send mid set-pub2 1000) (send mid get-pub2))) CLASSES) (numV 1000)) ; can set parent's publics 
(test (run/classes '(send (new Bottom) get-constr) CLASSES) (numV 100)) ; parent constructors work
(test/exn (run/classes '(send (new Middle 0 1) check-parent-pub) CLASSES) "unbound") ; can't access parent pubs in methods

; ============ Tests about objects in objects ===========
(test (run/classes '(with ((box1 (new Box 1)) (box2 (new Box 2))) (send box1 get-value)) CLASSES) (numV 1)) ; testing box class
(test (run/classes '(with ((box1 (new Box 1)) (box2 (new Box 2))) (seq (send box1 set-value box2) (send (send box1 get-value) get-value))) CLASSES) (numV 2)) ; box in box
(test (run/classes '(with ((mid (new Middle 0 (new Box 1)))) (send (send mid get-constr) get-value)) CLASSES) (numV 1)) ; box in a middle
(test (run/classes '(with ((box-maker (new Box (fun (x) (new Box x))))) (send (send box-maker invoke 6) get-value)) CLASSES) (numV 6)) ; boxes that make other boxes


;; ============ tests from the professor ============
;;===== desugaring into the right types of things =======

; are objects closures?
(test (closV? (run/classes '(new Top) CLASSES)) 
      true)


;;====== tests about referencing variables ==================

; can methods reference public variables?

(test (run/classes '(send (new Middle 0 1) use-publics) CLASSES)
      (numV 14))

; can methods use getters to access parent's private variables?

(test/exn (run/classes '(send (new Middle 1 2) add-pub-parent-priv) CLASSES)
          "unbound")

;; ======= tests about sharing variables ==========

; do two objects of the same class have their own private vars?

(test (run/classes '(with ([m1 (new Middle 1 2)]
                           [m2 (new Middle 11 12)])
                          (seq (send m1 set-pub1 0)
                               (send m2 get-pub1)))
                   CLASSES)
      (numV 2))

; if we set a variable that is defined in both class and parent, is
; the parent one unchanged?

(test (run/classes '(with ([m1 (new Middle 1 2)])
                          (seq (send m1 set-pub1 25)
                               (send m1 get-parent-pub1)))
                   CLASSES)
      (numV 8))

;;==== tests about methods across inheritance ============

;;===== tests about setters =============

;; ====== tests of objects inside objects =============
