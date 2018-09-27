#lang plai-typed
;; Kathi Fisler

;; Programs to review in helping students get (back) up to speed in Racket

;; Most of the time, when we implement programming languages, we are writing
;; functions over recursively-defined data types, such as lists or trees. So
;; we're going to emphasize those sorts of programs here.


;-------------------------------------------------------

;;;; BASIC LIST FUNCTION -- total length of strings in a list

; first, this is what the function looks like without types

; total-length : (listof string) -> number
; produce length of string concatenated from all elts in list
(define (total-length stringList)
  (cond [(empty? stringList) 0]
        [(cons? stringList)
         (+ (string-length (first stringList))
            (total-length (rest stringList)))]))

; don't forget to write tests

(test (total-length empty) 0)
(test (total-length (list "goat" "big")) 7)

; here's what the program looks like with types
;   note that you can omit either/both the input/output types
; produce length of string concatenated from all elts in list
(define (total-length2 [stringList : (listof string)]) : number
  (cond [(empty? stringList) 0]
        [(cons? stringList)
         (+ (string-length (first stringList))
            (total-length2 (rest stringList)))]))

; some particular things to note here:
; - we used cons? rather than else for second test : get used to this, as
;   we will often add cases to existing definitions in this course, and
;   the more specific the type, the less old code you have to edit
; - there is a basic structure to a program that processes a list

#|
(define (listFunc inputL)
  (cond [(empty? inputL) ...]
        [(cons? inputL) ... (first inputL)
                        ... (listFunc (rest inputL)) ...]))
|#

; this structure breaks into the two cases of a list, then calls
; the function recursively on the rest of the list (which is also
; a list). You can start from this template whenever you have to write
; a recursive function that processes a list

;-------------------------------------------------------

;;;; PRACTICE LIST FUNCTION: COUNT-NEW-ELEMENTS

; Write a function that takes two lists of strings and returns
; the number of strings in the first list that are NOT in the
; second list

; return number of elements of first list that are NOT in second list
(define (count-new [checkL : (listof string)] [knownL : (listof string)]) : number
  (cond [(empty? checkL) 0]
        [(cons? checkL)
         (if (member (first checkL) knownL)
             (count-new (rest checkL) knownL)
             (+ 1 (count-new (rest checkL) knownL)))]))

(test (count-new empty (list "var1" "var2")) 0)
(test (count-new (list "var1") empty) 1)
(test (count-new (list "var1" "var2" "var1") (list "var2" "var3")) 2)

; things to note here:
; - member is built-in, checks whether item is in a list
; - there is an if construct, but use cond if have more than one test
;   (rather than nested if expressions -- too ugly!)

;; You can also write this function using built-in list iterators as follows:

(define (count-new2 [checkL : (listof string)] [knownL : (listof string)]) : number
  (length
   (filter (lambda (elt) (not (member elt knownL)))
           checkL)))

; things to note here:
; - lambda creates an anonymous function.  Here, a function with one input (elt)
; - can't use type annotations with lambda arguments
; - filter takes a predicate and returns list of elts for which predicate returns true
; - length produces the length of a list

;-------------------------------------------------------

;;;; PRACTICE WITH BINARY TREES

; Lets define binary trees over numbers.  First, need a datatype for this, since
; trees aren't built-in the way lists are

(define-type Numtree
  [leaf (num : number)]
  [inner (num : number) (left : Numtree) (right : Numtree)])

; defining an example of data
(define tree1 (inner 2
                     (leaf 5)
                     (inner 10
                            (leaf 3)
                            (leaf 8))))

; in-order : Numtree -> (listof number)
; produce list of elts in tree in left to right order
(define (in-order (atree : Numtree)) : (listof number)
  (type-case Numtree atree
    [leaf (n) (list n)]
    [inner (n l r) (append
                    (in-order l)
                    (append (list n)
                            (in-order r)))]))

; things to note:
; - in plai-typed, append (and other operators like +) are binary,
;   rather than take arbitrarily many arguments
; - (cons n (in-order r)) would be cleaner, but doesn't show binary append
; - the names you use for the fields within a type-case don't have to
;   match those from the original definition
; - as with lists, there is a core "template" at work here -- both the
;   left and right subtrees are Numtree, so we process them with recursion

;;;;; WORKING WITH BOOLEANS

; determine whether a given number is in a numtree
(define (contains? (atree : Numtree) (anum : number)) : boolean
  (type-case Numtree atree
    [leaf (n) (= n anum)]
    [inner (n l r) (or (= n anum)
                       (contains? l anum)
                       (contains? r anum))]))

(test (contains? (leaf 6) 10) false)
(test (contains? tree1 10) true)
