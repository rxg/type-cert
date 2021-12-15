#lang plai
(define (... . args) (cons '... args))
(print-only-errors #t)

;; We have a bunch of equations of the form t1 = t2
;; where there might be variables (e.g., X, Y, Z, etc.) in t1 and t2

;; Example 1:
;; (number -> X) = (number -> number)
;;  solution: X := number

;; Example 2:
;; (X -> empty) = number
;;  no solution: number is never a function type

;; Example 3:
;; (X -> Y) = (Z -> W)
;;  infinite solutions, as long as X = Z and Y = W

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type Expressions

;; Variable is Symbol
;; interp.  a placeholder for a type expression
(define (variable? x)
  (symbol? x))

(define-type TypeExpr
  #;[emptyType]    ;; NO OPERATIONS, NO VALUES!
  [numType]
  [funType (arg TypeExpr?) (result TypeExpr?)]
  [unifVar (id variable?)]
  [paramType (id variable?)])
;; interp. an expression of a type that has 0 or more as yet unknown components,
;;         denoted by variables X.  Corresponds to the following BNF:
;; <TypeExpr> ::= empty | number | <Type> -> <Type> | X | P
;; NEW: Type Parameters P indicate "any type will do" as a solution.
#;
(define (fn-for-type-expr texpr)
  (type-case TypeExpr texpr
    #;[emptyType () (...)]
    [numType () (...)]
    [funType (arg res) (... (fn-for-type-expr arg)
                            (fn-for-type-expr res))]
    [unifVar (X) (... X)]
    [paramType (X) (... X)]))


;; TypeExpr -> String
;; pretty-prints a type expression
(define (print-type-expr texpr)
  (type-case TypeExpr texpr
    #;[emptyType () "empty"]
    [numType () "number"]
    [funType (arg res)
             (format "(~a -> ~a)" (print-type-expr arg) (print-type-expr res))]
    [unifVar (X) (symbol->string X)]
    [paramType (X) (format "(param ~s)" (symbol->string X))]))

;; TypeExpr -> TypeExpr
;; produce a type like tX0, but with parameters replaced by fresh variables
(define (freshen-texpr tX0)
  ;; Accumulator: param-table is (listof (list Symbol TypeExpr))
  ;; Invariant: maps parameter ids seen in tX0 to fresh unifVars
  (local [(define param-table (void))
          (define (fresh X)
            (cond [(assoc X param-table) => cadr]
                  [else
                   (let ([tX^ (unifVar (gensym 'XX))])
                     (begin (set! param-table (cons (list X tX^)
                                                    param-table))
                            tX^))]))
          (define (fn-for-type-expr texpr)
            (type-case TypeExpr texpr
              [numType () (numType)]
              [funType (arg res) (funType (fn-for-type-expr arg)
                                      (fn-for-type-expr res))]
              [unifVar (X) (unifVar X)]
              [paramType (X) (fresh X)]))]
    (begin
      (set! param-table empty)
      (fn-for-type-expr tX0))))

;; Type is one of
;; - (emptyType)
;; - (numType)
;; - (funType Type Type)
;; interp. a TypeExpr containing no variables

#;
(define (fn-for-type type)
  (match type
    #;[(emptyType) (...)]
    [(paramType x) (... x)]
    [(numType) (...)]
    [(funType arg res) (... (fn-for-type arg)
                            (fn-for-type res))]))


;; TypeExpr -> (listof Variable)
;; produces the (free) variables that appear in the given type expression
(define (free-vars texpr)
  (type-case TypeExpr texpr
    #;[emptyType () '()]
    [numType () '()]
    [funType (t1 t2) (append (free-vars t1) (free-vars t2))]
    [unifVar (X) (list X)]
    [paramType (X) '()]))


;; Any -> Boolean
;; produces true if x is a type, otherwise false
(define (Type? x)
  (and (TypeExpr? x)
       (equal? (free-vars x) '())))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Substitutions

;; (substof X) is Variable -> X
;; interp. a mapping from type variables to objects of type X


;; (substof TypeExpr)
;; a substitution that maps all variables to their corresponding type expression
(define (empty-subst X) (unifVar X))


;; X -> (substof X)
;; produces a subst that always maps to X
(define (const-subst X) (λ (Y) X))

;; (substof TypeExpr)
;; map each unification variable to a unique type parameter, unless excepted
(define (parameterize X exceptions)
  (if (member X exceptions)
      (unifVar X)
      (paramType X)))

;; Variable TypeExpr -> (substof TypeExpr)
;; produces a substitution that replaces X with texpr, otherwise acts like empty-subst
(define (make-subst X texpr)
  (λ (Y)
    (if (equal? X Y)
        texpr
        (empty-subst Y))))


;; Given a type substitution, we can "apply" it to a type expression,
;; i.e. replace each variable with whatever the substitution maps it to

;; (substof TypeExpr) TypeExpr -> TypeExpr
;; replaces all type variables in texpr with their mapping in subst
(define (apply-subst subst texpr)
  (type-case TypeExpr texpr
    #;[emptyType () (emptyType)]
    [numType () (numType)]
    [funType (dom range)
             (funType (apply-subst subst dom)
                      (apply-subst subst range))]
    [unifVar (X) (subst X)]
    ;; type parameters are NOT unification variables.  We just use the same
    ;; id as a trick to create one unique parameter for each unique variable
    [paramType (X) (paramType X)]))


;; (substof TypeExpr) (substof TypeExpr) -> (substof TypeExpr)
;; composes two substitutions by applying them sequentially
(define (compose-subst subst2 subst1)
  (λ (Y) (apply-subst subst2 (subst1 Y))))


;; Finally, we can turn a (substof TypeExpr) into a (substof Type)
;; by applying the substitution and then replacing any variables with parameters

;; (substof TypeExpr) (listof Symbol) -> (substof Type)
;; adapts the given substitution to produce parameters in place of any variables
(define (finalize-subst subst exceptions)
  (compose-subst (λ (X) (parameterize X exceptions)) subst))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Equations

(define-type Equation
  [assert-equal (lhs TypeExpr?) (rhs TypeExpr?)])
;; interp.  an equation over type expressions

(define (apply-subst-eqn subst eqn)
  (type-case Equation eqn
    [assert-equal (lhs rhs)
                  (assert-equal (apply-subst subst lhs)
                                (apply-subst subst rhs))]))

;; TODO: Add examples here!

;; SystemOfEqns is (listof Equation)
;; interp.  a system of equations over types

;; (substof TypeExpr) SystemOfEqns -> SystemOfEqns
;; apply subst to all the expressions in soeqns
(define (apply-subst-soeqns subst soeqns)
  (map (λ (eqn) (apply-subst-eqn subst eqn)) soeqns))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unification -- a procedure for solving systems of type equations

;; Given a system of equations soeqn, we we want to produce a (substof Type)
;; subst such that for every (assert-equal texpr1 texpr2) in soeqn:
;; (equal? (apply-subst subst texpr1)
;;         (apply-subst subst texpr2))

;; This is kind of like high-school algebra: we're trying to
;; "solve for X and Y and ..." in a system of equations, but our equations
;; are over type expressions rather than polynomials, etc. and our
;; substitution replaces variables with types instead of numbers.

;; We build a solution to our constraint set using our helper function,
;; then use (substof TypeExpr) -> (substof Type) to map any unconstrained
;; variables to emptyType.

;; In the literature, this algorithm for solving systems of equation is called
;; "unification", because the substitution "unifies" both sides of each equation.

;; unify : SystemOfEqns Boolean -> (substof Type)
;; produces a substitution that solves the given system of equations
(define (unify-with-exceptions soeqns exceptions)
  (finalize-subst   
   (unify--with-subst soeqns)
   exceptions))

(define (unify soeqns) (unify-with-exceptions soeqns '()))
;; TODO: Complete this function!

;; unify--with-subst : SystemOfEqns -> (substof TypeExpr)
;; produces a substitution of type expressions that solves the given system of equations
(define (unify--with-subst soeqns)
  (cond
    ;; *Any* substitution solves an empty system of equations (think about it),
    ;; so use the empty one, because it makes the fewest commitments
    [(empty? soeqns) empty-subst]
    [else
     (let ([eqn (first soeqns)]
           [soeqns^ (rest soeqns)])
       (match eqn
         ;; Vacuous equation, discard
         [(assert-equal (unifVar X) (unifVar X))
          (unify--with-subst soeqns^)]
         ;; Variable on the left: map it to the type expression on the right
         ;; Question: when can this go wrong?
         [(assert-equal (unifVar X) texpr2)
          (begin
            (when (member X (free-vars texpr2)) ;; occurs check
              (error 'unify "Cannot solve ~a = ~a." (unifVar X) texpr2))
            (let* ([subst1 (make-subst X texpr2)]
                   [subst2 (unify--with-subst
                            (apply-subst-soeqns subst1 soeqns^))])
              (compose-subst subst2 subst1)))]
         ;; Variable on the right: map it to the type expression on the left
         ;; (same idea as above)
         [(assert-equal texpr1 (unifVar X))
          (begin
            (when (member X (free-vars texpr1)) ;; occurs check
              (error 'unify "Cannot solve ~a = ~a." X (print-type-expr texpr1)))
            (let* ([subst1 (make-subst X texpr1)]
                   [subst2 (unify--with-subst
                            (apply-subst-soeqns subst1 soeqns^))])
              (compose-subst subst2 subst1)))]
         ;; Structural cases: if we have two types, they can only
         ;; be unified if they have the same constructors,
         ;; and we can unify their fields
         #;[(assert-equal (emptyType) (emptyType))
            (unify--with-subst soeqns^)]
         [(assert-equal (paramType x) (paramType x))
          (unify--with-subst soeqns^)]
         [(assert-equal (numType) (numType))
          (unify--with-subst soeqns^)]
         [(assert-equal (funType arg1 res1) (funType arg2 res2))
          (unify--with-subst (cons (assert-equal arg1 arg2)
                                   (cons (assert-equal res1 res2)
                                         soeqns^)))]
         ;; Everything else,
         ;; e.g. (numType) (emptyType)
         ;; (funType t1 t2) (numType)
         [(assert-equal texpr1 texpr2)
          (error 'unify "Cannot solve ~a = ~a." (print-type-expr texpr1) (print-type-expr texpr2))]))]))

;;;;;;;;;;;;;;
;; Examples ;;
;;;;;;;;;;;;;;

;; TypeExpr TypeExpr -> (substof Type)
;; helper to unify two type expressions
(define (unify-pair texpr1 texpr2)
  (unify (list (assert-equal texpr1 texpr2))))

;; test helper to print and unify two types,
;; print the solution, and check that the substitution
;; actually makes the two sides equal
(define-syntax-rule (test-unify t1 t2)
  (let* ([soln (unify-pair t1 t2)]
         [t1Sub (apply-subst soln t1)]
         [t2Sub (apply-subst soln t2)])
    (begin
      #;(printf "Solving equation ~a = ~a\n" (print-type-expr t1) (print-type-expr t2))
      #;(for ([x (remove-duplicates (append (free-vars t1) (free-vars t2)))])
          (printf "  ~a := ~a\n" x (print-type-expr (soln x))))
      (test t1Sub t2Sub))))

;; examples without variables
(test/exn (unify-pair (numType) (paramType 'X)) "Cannot solve")
(test-unify (numType) (numType))
(test-unify  (paramType 'X) (paramType 'X))
(test/exn (unify-pair (paramType 'X) (paramType 'Y)) "Cannot solve")
(test-unify
 (funType (numType) (numType))
 (funType (numType) (numType)))

;; examples with variables
(test-unify (numType) (unifVar 'x))
(test-unify
 (funType (unifVar 'x) (numType))
 (funType (unifVar 'y) (numType)))

;; (x -> number) = (number -> x)
(test-unify
 (funType (unifVar 'x) (numType))
 (funType (numType) (unifVar 'x)))

;; TODO: Add more examples!
