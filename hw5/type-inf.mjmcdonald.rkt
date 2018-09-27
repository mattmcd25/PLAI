#lang plai-typed
#|
Type inference for a simply-typed calculus
Dan Dougherty February 2018
(starter file)
|#

;; Some handy utilities
(require (typed-in racket/sandbox
                   [call-with-limits : (number boolean (-> 'a) -> 'a)]))
(require (typed-in racket/base [gensym : (symbol -> symbol)])
         (typed-in racket/base [andmap : (('a 'a -> boolean) (listof 'a) (listof 'a) -> boolean)])
         (typed-in racket/base [ormap : (('a -> boolean) (listof 'a) -> boolean)])
         )

;; useful placeholder while developing
(define (undefined) (error 'undefined "") )

;; ------
;; Types 
;; ------

;; the varT type captures type parameters.  For example, the
;; identity function has type funT((varT'a) (varT 'a)), where
;; 'a is variable over types
(define-type Type
  [numT]
  [boolT]
  [tlistT (elem : Type)]
  [funT (arg : Type) (return : Type)]
  [varT (v : symbol)])

;; -----------
;; Expressions
;; -----------
(define-type ExprS
  [numS (n : number)]
  [boolS (b : boolean)]
  [temptyS]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [idS (i : symbol)]
  [appS (f : ExprS) (arg : ExprS)]
  [iszeroS (e : ExprS)]
  [bifS (c : ExprS) (t : ExprS) (e : ExprS)]
  [lamS (param : symbol) (body : ExprS)]
  [recS  (var : symbol) (val : ExprS) (body : ExprS)]
  [withS (var : symbol) (val : ExprS) (body : ExprS)]
  [tconsS (e : ExprS) (l : ExprS)]
  [tisEmptyS (e : ExprS)]
  [tfirstS (e : ExprS)]
  [trestS (e : ExprS)]
  )

;;
;; Parsing Expressions
;;
;;  parse : s-expression -> ExprS
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) 
     (case (s-exp->symbol s)
       [(tru) (boolS true)]
       [(fls) (boolS false)]
       [(tempty) (temptyS)]
       [else (idS (s-exp->symbol s))])]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond [(s-exp-symbol? (first sl)) ;; built-in construct or calling function through an identifier
              (case (s-exp->symbol (first sl))
                [(+) (plusS (parse (second sl)) (parse (third sl)))]
                [(*) (multS (parse (second sl)) (parse (third sl)))]
                [(-) (bminusS (parse (second sl)) (parse (third sl)))]
                [(iszero) (iszeroS (parse (second sl)))]
                [(bif) (bifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
                [(fun)  (if (= (length sl) 3)
                            (lamS (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl)))
                            (error 'parse
                                   
                                   (string-append "parse error: Malformed lambda expression (expected 3 parts)"
                                                  (to-string s))))]
                [(with) (let ([bindings (s-exp->list (second sl))]
                              [body (third sl)])
                          (cond [(= 1 (length bindings))
                                 (let ([binding (s-exp->list (first bindings))])
                                   (withS (s-exp->symbol (first binding))
                                          (parse (second binding))
                                          (parse body)))]
                                [else (error 'parse "parse error: bad format in with bindings")]))]
                [(rec)  (let ([bindings (s-exp->list (second sl))]
                              [body (third sl)])
                          (cond [(= 1 (length bindings)) ;; binding has form ((var val))
                                 (let ([binding (s-exp->list (first bindings))])
                                   (recS (s-exp->symbol (first binding))
                                         (parse (second binding))
                                         (parse body)))]
                                [else (error 'parse "parse error: badformat in rec bindings")]))]
                
                [(tcons) (tconsS (parse (second sl)) (parse (third sl)))]
                [(tempty?) (tisEmptyS (parse (second sl)))]
                [(tfirst) (tfirstS (parse (second sl)))]
                [(trest) (trestS (parse (second sl)))]
                [else ;; must be a function application
                 (appS (idS (s-exp->symbol (first sl)))
                       (parse (second sl)))])]
             [else (appS (parse (first sl))
                         (parse (second sl)))]))]
    [else (error 'parse "parse error: unexpected syntax")]))

;; --------------
;; Type Inference
;; --------------

;; type-of :: ExprS -> Type
;; this will call generate-constraints and unify, in a way that
;;  is consistent with your types for these functions
(define (type-of (e : ExprS)) : Type
  (let* ([clist (generate-constraints e)]
         [slist (unify clist)])
    (let ([ans (lookup-type e slist)])
      (term2type ans))))

;; term2type : Constraint-Term -> Type
;; generate a Type from a constraint-term
(define (term2type [t : Constraint-Term]) : Type
  (cond [(typeconstant? t) (let ([ctype (typeconstant-name t)])
                             (cond [(eq? ctype 'number) (numT)]
                                   [(eq? ctype 'boolean) (boolT)]
                                   [else (error 'term2type
                                                (string-append "handle typeconstant "
                                                               (to-string ctype)))]))]
        [(typevar-subexp? t) (varT (gensym 'tvar))] 
        [(typevar-generated? t) (varT (typevar-generated-name t))]
        [(constructor? t)
         (cond [(symbol=? (constructor-type t) 'arrow)
                (funT (term2type (first (constructor-terms t))) 
                      (term2type (second (constructor-terms t))))]
               [(symbol=? (constructor-type t) 'list)
                (tlistT (term2type (first (constructor-terms t))))])]))


;; ---------------------
;; Generating Constraints
;; ----------------------
;;
;; Constraints and Constraint-Terms 
;;
(define-type Constraint-Term
  ;; constant type, ie number or boolean
  [typeconstant (name : symbol)]
  ;; type-variable associated with a (sub)expression
  [typevar-subexp (name : ExprS)]
  ;; other type-variables we need to make
  [typevar-generated (name : symbol)]
  ;; compound types, arrow or list
  [constructor (type : symbol) (terms : (listof Constraint-Term))]
  )

;; an equation between Constraint-Terms
(define-type Constraint
  [ceq (left : Constraint-Term)
       (right : Constraint-Term)])

;; captures "replace the variable i by the constraint-term t"
(define-type Substitution
  [subs (i : Constraint-Term)
   (t : Constraint-Term)])

;; generate-constraints : ExprS -> (listof Constraint)
;; generates the constraints for a given ExprS to then be solved
(define (generate-constraints [cexpr : ExprS]) : (listof Constraint)
  (let ([this (typevar-subexp cexpr)])
    (type-case ExprS cexpr
      ;; Constants
      [numS (n) (list (ceq this (typeconstant 'number)))]
      [boolS (v) (list (ceq this (typeconstant 'boolean)))]
      [temptyS () (list (ceq this (constructor 'list (list (typevar-generated (gensym 'list))))))]
      
      ;; Built-ins on Numbers
      [plusS (l r) (generate-math-constraints cexpr l r)]
      [bminusS (l r) (generate-math-constraints cexpr l r)]
      [multS (l r) (generate-math-constraints cexpr l r)]
      
      ;; Built-ins on Booleans
      [iszeroS (e) (append (list (ceq (typevar-subexp e) (typeconstant 'number))
                                 (ceq (typevar-subexp cexpr) (typeconstant 'boolean)))
                           (generate-constraints e))]
      [bifS (c t e) (append (generate-constraints c)
                            (append (generate-constraints t)
                                    (append (generate-constraints e)
                                            (list (ceq (typevar-subexp c) (typeconstant 'boolean))
                                                  (ceq this (typevar-subexp e))
                                                  (ceq this (typevar-subexp t))
                                                  (ceq (typevar-subexp t) (typevar-subexp e))))))]
      
      ;; Built-ins on Lists
      [tconsS (e l) (append (generate-constraints e)
                            (append (generate-constraints l)
                                    (list (ceq (typevar-subexp l) (constructor 'list (list (typevar-subexp e))))
                                          (ceq this (typevar-subexp l))
                                          )))]
      [tisEmptyS (e) (append (generate-constraints e)
                             (list (ceq this (typeconstant 'boolean))
                                   (ceq (typevar-subexp e) (constructor 'list (list (typevar-generated (gensym 'list)))))
                                   ))]
      [tfirstS (e) (append (generate-constraints e)
                           (list (ceq (typevar-subexp e) (constructor 'list (list this)))))]
      [trestS (e) (append (generate-constraints e)
                          (list (ceq this (typevar-subexp e))
                                (ceq (typevar-subexp e) (constructor 'list (list (typevar-generated (gensym 'list)))))))]
      
      ;; Variables and Functions
      [idS (i) (list (ceq this (typevar-generated i)))]
      [lamS (param body) (append (generate-constraints body)
                                 (list (ceq this
                                            (constructor 'arrow
                                                         (list (typevar-generated param)
                                                               (typevar-subexp body))))
                                       ))]
      [appS (f arg) (append (generate-constraints f)
                            (append (generate-constraints arg)
                                    (list (ceq 
                                            (typevar-subexp f) 
                                            (constructor 'arrow (list 
                                                                  (typevar-subexp arg) 
                                                                  this))))))]
      
      ;; Withs
      [withS (var val body) (append (generate-constraints val)
                                    (append (generate-constraints body)
                                            (list (ceq this (typevar-subexp body))
                                                  (ceq (typevar-generated var) (typevar-subexp val)))))]
      [recS (var val body) (append (generate-constraints val)
                                    (append (generate-constraints body)
                                            (list (ceq this (typevar-subexp body))
                                                  (ceq (typevar-generated var) (typevar-subexp val)))))] 
      )))

;; generate-math-constraints : ExprS ExprS ExprS -> (listof Constraint)
;; helper function for the common pattern for plus, minus, and mult
(define (generate-math-constraints e l r)
  (append (generate-constraints l)
          (append (generate-constraints r)
                  (list (ceq (typevar-subexp l) (typeconstant 'number))
                        (ceq (typevar-subexp r) (typeconstant 'number))
                        (ceq (typevar-subexp e) (typeconstant 'number))))))

;; ------------
;; Unification
;; ------------

;; unify :  (listof Constraint) -> (listof Substitution)
;; unifies the list of constraints into a set of 'solved' substitutions 
(define (unify [clist : (listof Constraint)]) : (listof Substitution)
  (unifyloop clist empty))

;; unifyloop :  (listof Constraint) x (listof Substitution) -> (listof Substitution)
;; repeatedly 'solves' constraints until only substitutions are left
(define (unifyloop [clist : (listof Constraint)] [slist : (listof Substitution)]) : (listof Substitution)
  (cond
    [(empty? clist) slist]
    [(cons? clist)
     (let ([left (ceq-left (first clist))]
           [right (ceq-right (first clist))])
       (if (term-eq? left right) 
           (unifyloop (rest clist) slist)
           (type-case Constraint-Term left
             [typevar-generated (s) (unify-typevar left right s clist slist)]
             [typevar-subexp (e) (unify-subexp left right e clist slist)]
             [typeconstant (name) (unify-constant left right name clist slist)]
             [constructor (type1 terms1) (unify-constructor left right type1 terms1 clist slist)])))]))

;; unify-typevar : typevar-generated x Constraint-Term x symbol x (listof Constraint) x (listof Substitution) -> (listof Substitution)
;; unifies the constraints, given the first left is a generated typevar
(define (unify-typevar left right s clist slist)
  (type-case (optionof Constraint-Term) (lookup left slist)
    [some (bound)
     (unifyloop (cons (ceq bound right)
                      (rest clist))
                slist)]
    [none ()
     (unifyloop (e+r2 left right (rest clist))
                (extend+replace left right slist))]))

;; unify-subexp : typevar-subexp x Constraint-Term x ExprS x (listof Constraint) x (listof Substitution) -> (listof Substitution)
;; unifies the constraints, given the first left is a subexpression
(define (unify-subexp left right e clist slist)
  (type-case (optionof Constraint-Term) (lookup left slist)
    [some (bound)
     (unifyloop (cons (ceq bound right)
                      (rest clist))
                slist)]
    [none ()
     (unifyloop (e+r2 left right (rest clist))
                (extend+replace left right slist))]))

;; unify-constant : typeconstant x Constraint-Term x symbol x (listof Constraint) x (listof Substitution) -> (listof Substitution)
;; unifies the constraints, given the first left is a constant
(define (unify-constant left right name clist slist) 
  (type-case Constraint-Term right
    [typeconstant (name2) 
     (if (symbol=? name name2)
         (unifyloop (rest clist) slist)
         (error 'unify "type error: differing constant"))]
    [constructor (type terms) (error 'unify "type error: constant = constructor")]
    [else (unifyloop (cons (ceq right left)
                           (rest clist))
                     slist)]))

;; unify-constructor : constructor x Constraint-Term x symbol x (listof Constraint-Term) x (listof Constraint) x (listof Substitution) -> (listof Substitution)
;; unifies the constraints, given the first left is a constructor
(define (unify-constructor left right type1 terms1 clist slist) 
  (type-case Constraint-Term right
    [constructor (type2 terms2) 
     (if (and (symbol=? type1 type2)
              (= (length terms1) (length terms2)))
         (unifyloop (append (zip ceq terms1 terms2)
                            (rest clist))
                    slist)
         (error 'unify "type error: differing constructors"))]
    [typeconstant (type) (error 'unify "type error: constructor = constant")]
    [else (unifyloop (cons (ceq right left)
                           (rest clist))
                     slist)]))

;; extend+replace : Constraint-Term x Constraint-Term x (listof Substitution) -> (listof Substitution)
;; replaces all instances of var with val in the substitutions if there is no cycle
(define (extend+replace var val slist)
  (if (a-in-t? var val)
      (error 'unify "type error: variable appears in its definition")
      (cons (subs var val) (sub-t-in-s var val slist))))

;; e+r2 : Constraint-Term x Constraint-Term x (listof Constraint) -> (listof Constraint)
;; replaces all instances of var with val in the constrains if there is no cycle
(define (e+r2 var val clist)
  (if (a-in-t? var val)
      (error 'unify "type error: variable appears in its definition")
      (sub-t-in-c var val clist)))
      
;; Constraint-Term x (listof Substitution) -> Constraint-Term
;; lookup value of term in slist
(define (lookup term slist)
  (let ([result (filter (lambda (sub) (term-eq? (subs-i sub) term)) slist)])
    (if (= (length result) 0)
        (none)
        (some (subs-t (first result))))))

;; zip : ('a x 'b -> 'c) x (listof 'a) x (listof 'b) -> (listof 'c)
;; zips two lists (of equal length!) together with the specified function
(define (zip f ts us)
  (if (empty? ts) empty      
      (cons (f (first ts) (first us)) 
            (zip f (rest ts) (rest us)))))

;; a-in-t? : Constraint-Term x Constraint-Term -> boolean
;; checks if the typevar 'a appears in t
(define (a-in-t? a t)
  (if (term-eq? a t)
      true
      (type-case Constraint-Term t
        [typeconstant (name) false]
        [typevar-subexp (expr) false]
        [typevar-generated (name) (and (typevar-generated? a)
                                       (symbol=? (typevar-generated-name a) name))]
        [constructor (type terms) (ormap (lambda (t) (a-in-t? a t)) terms)])))

;; sub-t-in-s : Constraint-Term x Constraint-Term x (listof Substitution) -> (listof Substitution)
;; performs the substitution of t in for a in the list of substitutions
(define (sub-t-in-s a t slist)
  (map (lambda (x) (type-case Substitution x
                     [subs (l r) (subs (sub-t-in-ct a t l)
                                       (sub-t-in-ct a t r))])) slist))

;; sub-t-in-c : Constraint-Term x Contraint-Term x (listof Constraint) -> (listof Constraint)
;; performs the substitution of t in for a in the list of constraints
(define (sub-t-in-c a t clist)
  (map (lambda (x) (type-case Constraint x
                     [ceq (l r) (ceq (sub-t-in-ct a t l)
                                     (sub-t-in-ct a t r))])) clist))

;; sub-t-in-ct : Constraint-Term x Constraint-Term x Constraint-Term -> Constraint-Term
;; performs the substitution of t in for a in one constraint term
(define (sub-t-in-ct a t r)
  (type-case Constraint-Term r
    [constructor (type terms) (constructor type (map (lambda (x) (sub-t-in-ct a t x)) terms))]
    [else (if (term-eq? a r) t r)]))


;; term-eq? : Constraint-Term x Constraint-Term -> boolean
;; just an equality predicate for constraint terms
(define (term-eq? t1 t2)
  (cond [(typeconstant? t1) (and (typeconstant? t2)
                                 (symbol=? (typeconstant-name t1)
                                           (typeconstant-name t2)))]
        [(typevar-subexp? t1) (if (typevar-subexp? t2) ; uses eq? for empty, equal? otherwise!
                                  (if (equal? (typevar-subexp-name t1) (temptyS))
                                      (eq? (typevar-subexp-name t1)
                                           (typevar-subexp-name t2))
                                      (equal? (typevar-subexp-name t1)
                                              (typevar-subexp-name t2)))
                                  false)]
        [(typevar-generated? t1) (and (typevar-generated? t2)
                                      (symbol=? (typevar-generated-name t1)
                                                (typevar-generated-name t2)))]
        [(constructor? t1) (and (constructor? t2)
                                (symbol=? (constructor-type t1)
                                          (constructor-type t2))
                                (andmap (lambda (a b) (term-eq? a b))
                                        (constructor-terms t1)
                                        (constructor-terms t2)))]))

;;  lookup-type : ExprS x (listof Substitution) -> Constraint-Term
(define (lookup-type cexpr clist)
  (cond [(empty? clist) (error 'lookup-type "expression not found")]
        [(cons? clist) (cond [(term-eq? (typevar-subexp cexpr)
                                        (subs-i (first clist)))
                              (subs-t (first clist))]
                             [(term-eq? (typevar-subexp cexpr)
                                        (subs-t (first clist)))
                              (subs-i (first clist))]
                             [else 
                              (lookup-type cexpr (rest clist))])]))

;; ---------
;; Utilities
;; ---------

; alpha-renaming to all unique vars
; can't limit to regenerating vars defined in scopes -- if have unbound var, could have a
;  name clash even though it didn't arise in a previous binding
(define-type Rename [renamebind (old : symbol) (new : symbol)])

;;  lookup-alpha : symbol x (listof Rename) -> symbol
(define (lookup-alpha oldname renameList)
  (let ([res (filter (lambda (rn) (eq? oldname (renamebind-old rn))) renameList)])
    (if (cons? res) 
        (renamebind-new (first res))
        oldname)))

(define (alpha-rename [renamings : (listof Rename)] [expr : ExprS]) : ExprS
  (type-case ExprS expr
    [numS (n) expr]
    [boolS (v) expr]
    [plusS (l r) (plusS (alpha-rename renamings l) (alpha-rename renamings r))]
    [multS (l r) (multS (alpha-rename renamings l) (alpha-rename renamings r))]
    [bminusS (l r) (bminusS (alpha-rename renamings l) (alpha-rename renamings r))]
    [iszeroS (t) (iszeroS (alpha-rename renamings t))]
    [bifS (t ifdo elsedo) (bifS (alpha-rename renamings t)
                                (alpha-rename renamings ifdo)
                                (alpha-rename renamings elsedo))]
    [idS (name) (idS (lookup-alpha name renamings))]
    [withS (param val body)
     (let ([newparam (gensym param)])
       (withS newparam (alpha-rename renamings val) 
              (alpha-rename (cons (renamebind param newparam) renamings) body)))]
    [recS (param val body)
     (let* ([newparam (gensym param)]
            [newL (cons (renamebind param newparam) renamings)])
       (recS newparam (alpha-rename newL val) 
             (alpha-rename newL body)))]
    [lamS (param body)
     (let ([newparam (gensym param)])
       (lamS newparam (alpha-rename (cons (renamebind param newparam) renamings) body)))]
    [appS (f val) (appS (alpha-rename renamings f) (alpha-rename renamings val))]
    [temptyS () expr]
    [tconsS (f r) (tconsS (alpha-rename renamings f) (alpha-rename renamings r))]
    [tisEmptyS (l) (tisEmptyS (alpha-rename renamings l))]
    [tfirstS (l) (tfirstS (alpha-rename renamings l))]
    [trestS (l) (trestS (alpha-rename renamings l))]))

;; equality checker for types that supports type variables.
;;  two types are equal if there exists a one-to-one mapping between
;;  their variable names under which the types become lexically identical
#|
Here are some examples of type=? so you can see what it should do.  Feel free
to delete this from your code once you understand type=?

(test (type=? (varT 'a) (varT 'b)) true)

(test (type=? (funT (varT 'a) (varT 'a)) 
(funT (numT) (numT)))
false)

(test (type=? (funT (varT 'a) (varT 'a)) 
(funT (varT 'b) (varT 'b)))
true)

(test (type=? (funT (varT 'a) (varT 'b)) 
(funT (varT 'b) (varT 'b)))
false)

(test (type=? (funT (varT 'a) (varT 'b)) 
(funT (varT 'b) (varT 'a)))
true)

(test (type=? (funT (varT 'a) (varT 'a)) 
(funT (varT 'b) (varT 'a)))
false)
|#

;;
;; type=? : Type x Type ->  boolean
(define (type=? (t1 : Type) (t2 : Type)) : boolean
  (local ([define ht1 (make-hash empty)] ; maps vars in t1 to vars in t2
          [define ht2 (make-hash empty)] ; vice versa
          [define (teq? t1 t2)
           (cond
             [(and (numT? t1) (numT? t2)) true]
             [(and (boolT? t1) (boolT? t2)) true]
             [(and (tlistT? t1) (tlistT? t2))
              (teq? (tlistT-elem t1) (tlistT-elem t2))]
             [(and (funT? t1) (funT? t2))
              (and (teq? (funT-arg t1) (funT-arg t2))
                   (teq? (funT-return t1) (funT-return t2)))]
             [(and (varT? t1) (varT? t2))
              ;; v1 is the type that ht1 says that t1 maps to,
              ;; or the var of t2 if no mapping exists
              ;; v2 is analogous
              (let ([v1 (let ([r (hash-ref ht1 (varT-v t1))])
                          (if (some? r) 
                              ; var is in the hash, return the mapped value
                              (some-v r)
                              ; else add new mapping to hash and return the newly mapped variable
                              (begin (hash-set! ht1 (varT-v t1) (varT-v t2))
                                     (varT-v t2))))]
                    [v2 (let ([r (hash-ref ht2 (varT-v t2))])
                          (if (some? r)
                              (some-v r)
                              (begin (hash-set! ht2 (varT-v t2) (varT-v t1))
                                     (varT-v t1))))])
                ; we have to check both mappings, so that distinct variables
                ; are kept distinct. i.e. a -> b should not be isomorphic to
                ; c -> c under the one-way mapping a => c, b => c.
                (and (symbol=? (varT-v t2) v1) (symbol=? (varT-v t1) v2)))]
             [else false])]) ; types aren't equal
    (teq? t1 t2)))

(define (append3 l1 l2 l3) (append l1 (append l2 l3)))
(define (append4 l1 l2 l3 l4) (append l1 (append3 l2 l3 l4)))


;; ---
;; API
;; ---
(define (infer-type sexp)
  (call-with-limits 
    10 #f
    (lambda () (type-of (alpha-rename empty (parse sexp))))))

;; test/type :  s-expression x Type -> void
(define (test/type p t)
  (test (type=? (infer-type p) t) true))

;; test/type/exn :  s-expression x Type -> void
(define (test/type/exn p errstr)
  (test/exn (infer-type p) errstr))

