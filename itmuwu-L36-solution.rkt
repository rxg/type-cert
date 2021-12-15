#lang plai
(print-only-errors)
(define (... . args) (cons '... args)) ;; enables us to use ... in templates
(require "datatype-311.rkt")

;; *Implicitly-typed* Tiny mostly useless language with with (ITMUWU)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(require "solver.rkt") ;; For TypeExpr, Type, and unify


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility
;; A testing helper: use match in PLAI tests
;; WARNING: failures yield messy messages!
(define-syntax test/match
  (syntax-rules ()
    [(_ expr pat)
     (test (match expr
             [pat #t]
             [else #f #;(error 'test/match
                               "failed:\nexpected pattern: ~a\ngot ~a"
                               'pat expr)])
           #t)]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Relevant declarations from t9-solution.rkt repeated here for reference

;; Variable is symbol

#;
(define-type TypeExpr
  [emptyType]    ;; NO OPERATIONS, NO VALUES!
  [numType]
  [funType (arg TypeExpr?) (result TypeExpr?)]
  [unifVar (id variable?)]
  ;; * NEW!  an arbitrary number of different "empty types"
  [paramType (id variable?)])
;; interp. an expression of a type that has 0 or more as yet unknown components,
;;         denoted by variables X.  Corresponds to the following BNF:
;; <TypeExpr> ::= empty | number | <Type> -> <Type> | X

;; Type is one of
;; - (emptyType)
;; - (numType)
;; - (funType Type Type)
;; interp. a TypeExpr containing no variables
;; <Type> ::= empty | number | <Type> -> <Type>

;; Type? : Any -> Boolean
;; produce true if x is a type, otherwise false

;; print-type-expr : TypeExpr -> String
;; pretty-prints a type expression

;; freshen-texpr : TypeExpr -> TypeExpr
;; produce a type like tX0, but with parameters replaced by fresh variables


;; (substof X) is Variable -> X

;; empty-subst : (substof X)
;; a substitution that maps all variables to their corresponding type expression

;; make-subst : Variable TypeExpr -> TypeExprSub
;; produce a subst that replaces X with texpr, otherwise acts like empty-subst

;; apply-subst : (substof TypeExpr) TypeExpr -> TypeExpr
;; apply-subst : (substof Type) TypeExpr -> Type
;; replace all type variables in texpr with their mapping in subst

#;
(define-type Equation
  [assert-equal (lhs TypeExpr?) (rhs TypeExpr?)])
;; interp.  An equation over type expressions.

;; Example
#;
(define E1
  (assert-equal (funType (numType) (unifVar 'X))
                (funType (unifVar 'Y) (emptyType))))

;; SystemOfEqns is (listof Equation)
;; interp. a system of equations over types.

;; unify : SystemOfEqns -> (substof Type)
;; produce a substitution that solves the given system of equations


;; end of bits from t9-solution.rkt
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type TMU
  [num (n number?)]
  [add (lhs TMU?) (rhs TMU?)]
  [id (x symbol?)]
  [fixFun (f symbol?) (x symbol?) (body TMU?)]
  ;;  [fixFun (f symbol?) (f-type Type?) (x symbol?) (body TMU?)]  ** FORMERLY
  [app (rator TMU?) (rand TMU?)]
  [with (name identifier?) (named TMU?) (body TMU?)]
  [poly-with (name identifier?) (named TMU?) (body TMU?)])
;; interp. abstract syntax of a language with the following BNF:
;; <TMU> ::= <number>
;;         | {+ <TMU> <TMU>}
;;         | <id>
;;         | {fixFun <id> {<id>} <TMU>}
;;           (** formerly {fixFun {<id> : <Type>} {<id>} <TMU>} **)
;;         | {<TMU> <TMU>}
#;
(define (fn-for-tmu tmu)
  (type-case TMU tmu
    [num (n) (... n)]
    [add (lhs rhs) (... (fn-for-tmu lhs) (fn-for-tmu rhs))]
    [id (x) (... x)]
    [fixFun (f x body) (... f x (fn-for-tmu body))]
    ; [fixFun (f f-type x body) ** formerly **
    ;         (... f f-type x (fn-for-tmu body))]
    [app (rator rand) (... (fn-for-tmu rator) (fn-for-tmu rand))]
    [with (name named body) (... name (fn-for-tmu named) (fn-for-tmu body))]
    [poly-with (name named body)
               (... name (fn-for-tmu named) (fn-for-tmu body))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Capture-avoiding substitution

;; TMU -> (listof Symbol)
;; produce the free identifier instances in  tmu0
(define (free-instances tmu0)
  ;; Accumulator: bound is (listof Symbol)
  ;; Invariant: identifiers bound in tmu0 around tmu
  (local [(define (fn-for-tmu tmu bound)
            (type-case TMU tmu
              [num (n) empty]
              [add (lhs rhs)
                   (append (fn-for-tmu lhs bound) (fn-for-tmu rhs bound))]
              [id (x) (if (member x bound)
                          empty
                          (list x))]
              [fixFun (f x body)
                      (fn-for-tmu body (cons f (cons x bound)))]
              [app (rator rand)
                   (append (fn-for-tmu rator bound) (fn-for-tmu rand bound))]
              [with (name named body)
                    (append (fn-for-tmu named bound)
                            (fn-for-tmu body (cons name bound)))]
              [poly-with (name named body)
                         (append (fn-for-tmu named bound)
                                 (fn-for-tmu body (cons name bound)))]))]
    (fn-for-tmu tmu0 empty)))

;; TMU Var TMU -> TMU
;; produce the result of substituting tmux for x in tmu, avoiding capture
(define (subst tmu x tmux)
  (type-case TMU tmu
    [num (n) (num n)]
    [add (lhs rhs) (add (subst lhs x tmux) (subst rhs x tmux))]
    [id (x^) (if (symbol=? x^ x)
                 tmux
                 (id x^))]
    [fixFun (f x^ body)
            (let ([f^ (if (member f (free-instances tmux))
                          (gensym 'f)
                          f)]
                  [x^^ (if (member x^ (free-instances tmux))
                           (gensym 'x)
                           x^)])
              (fixFun f^ x^^ (subst (subst (subst body x^ (id x^^)) f (id f^))
                                    x tmux)))]
    [app (rator rand) (app (subst rator x tmux) (subst rand x tmux))]
    [with (name named body)
          (let ([name^ (if (member name (free-instances tmux))
                           (gensym 'name)
                           name)])
            (with name^ (subst named x tmux)
                  (subst (subst body name (id name^)) x tmux)))]
    [poly-with (name named body)
               (let ([name^ (if (member name (free-instances tmux))
                                (gensym 'name)
                                name)])
                 (poly-with name^ (subst named x tmux)
                            (subst (subst body name (id name^)) x tmux)))]))

(test/match (subst (fixFun 'f 'x (id 'q))
                   'q (id 'x))
            (fixFun f x (id 'x)))

;; Alphabetic Equivalence (alpha-equivalence)

;; TMU TMU -> Boolean
;; produce true if tmu1 and tmu2 are the same but for bound identifiers
(define (alpha-equiv? tmu1 tmu2)
  (match (list tmu1 tmu2)
    [(list (num n1) (num n2)) (= n1 n2)]
    [(list (add lhs1 rhs1) (add lhs2 rhs2))
     (and (alpha-equiv? lhs1 lhs2) (alpha-equiv? rhs1 rhs2))]
    [(list (id x1) (id x2)) (symbol=? x1 x2)]
    [(list (fixFun f1 x1 body1) (fixFun f2 x2 body2))
     (let ([f^ (gensym 'f)]
           [x^ (gensym 'x)])
       (alpha-equiv? (subst (subst body1 x1 (id x^)) f1 (id f^))
                     (subst (subst body2 x2 (id x^)) f2 (id f^))))]
    [(list (app rator1 rand1) (app rator2 rand2))
     (and (alpha-equiv? rator1 rator2) (alpha-equiv? rand1 rand2))]
    [(list (with x1 named1 body1) (with x2 named2 body2))
     (and x1 x2
          (alpha-equiv? named1 named2)
          (let ([x^ (gensym 'x)])
            (alpha-equiv? (subst body1 x1 (id x^))
                          (subst body2 x2 (id x^)))))]
    [(list (poly-with x1 named1 body1) (poly-with x2 named2 body2))
     (and x1 x2
          (alpha-equiv? named1 named2)
          (let ([x^ (gensym 'x)])
            (alpha-equiv? (subst body1 x1 (id x^))
                          (subst body2 x2 (id x^)))))]
    [else #f]))


(test (alpha-equiv? (num 7) (num 7)) #t)
(test (alpha-equiv? (num 7) (num 9)) #f)
(test (alpha-equiv? (fixFun 'f 'x (app (id 'x) (id 'f)))
                    (fixFun 'g 'y (app (id 'y) (id 'g))))
      #t)
(test (alpha-equiv? (fixFun 'f 'x (app (id 'x) (id 'f)))
                    (fixFun 'g 'y (app (id 'g) (id 'y))))
      #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Environments

;; (envof X) is (listof (list Symbol X))

;; Any -> Boolean
;; produce true if the given object is an (envof X)
(define ((envof? X?) x)
  (match x
    [(list `(,x ,v) ...) #:when (and (andmap symbol? x)
                                     (andmap X? v)) #t]
    [else #f]))

;; (listof Symbol) -> Boolean
;; produce true if each symbol in x* appears only once
(define (unique? lox)
  (cond
    [(empty? lox) #t]
    [else ;; (cons? lox)
     (and (not (member (first lox) (rest lox)))
          (unique? (rest lox)))]))

(test (unique? '()) #t)
(test (unique? '(a)) #t)
(test (unique? '(a b c d)) #t)
(test (unique? '(a b c b)) #f)
(test (unique? '(a a c d)) #f)

;; Env
;; empty environment
(define empty-env '())

;; (envof X) (listof Symbol) (listof X) -> (envof X)
;; produce an environment that binds distinct symbols in x* to values in v*.
;; ASSUME: (= (length x*) (length v*))
;; ASSUME: (unique? x*)
(define (extend-env* env x* v*)
  (append (map list x* v*) env))

(test (extend-env* empty-env '(x y z) '(5 6 7)) '((x 5)
                                                  (y 6)
                                                  (z 7)))
(test (extend-env*
       (extend-env* empty-env '(x y z) '(5 6 7))
       '(a x c) '(5 6 7))
      '((a 5)
        (x 6)
        (c 7)
        (x 5)
        (y 6)
        (z 7)))

;; (envof X) Symbol -> X
;; produce the binding for the given symbol.
;; Effect: signal an error if no binding is found.
(define (lookup-env env x)
  (cond [(empty? env) (error 'lookup-env "unbound identifier: ~a" x)]
        [else (if (symbol=? x (car (first env)))
                  (cadr (first env))
                  (lookup-env (rest env) x))]))

(test (lookup-env (extend-env*
                   (extend-env* empty-env '(x y z) '(5 6 7))
                   '(a x c) '(5 6 7))
                  'z)
      7)


;; (envof X) Symbol -> Boolean
;; produce true if the environment binds x, otherwise false
(define (in-env? env x)
  (cond [(assoc x env) #t]
        [else #f]))

(test (in-env? (extend-env*
                (extend-env* empty-env '(x y z) '(5 6 7))
                '(a x c) '(5 6 7))
               'z)
      #t)

(test (in-env? (extend-env*
                (extend-env* empty-env '(x y z) '(5 6 7))
                '(a x c) '(5 6 7))
               'q)
      #f)


;; (envof X) (listof Symbol) -> (envof X)
;; remove the initial bindings of env indicated by loid
(define (shrink-env env loid)
  (cond
    [(empty? loid) env]
    [else ; (cons? loid)
     (if (symbol=? (caar env) (first loid))
         (shrink-env (rest env) (rest loid))
         (error 'shrink-env "Binding mismatch: ~a ∈ ~a"  (first loid) env))]))


(test (shrink-env empty-env empty) empty-env)

(test (shrink-env (extend-env* empty-env (list 'x 'y) (list 7 8))
                  (list 'x))
      (extend-env* empty-env (list 'y) (list 8)))

(test (shrink-env (extend-env* empty-env (list 'x 'y) (list 7 8))
                  (list 'x 'y)) empty-env)

(test/exn (shrink-env (extend-env* empty-env (list 'x 'y) (list 7 8))
                      (list 'y)) "mismatch")

;; (envof X) (envof X) (listof Symbol) (listof X) -> Boolean
;; produce true if env0 = (extend-env* env^ x*0 v*0) for some env^, else false
;; ASSUME: (= (length x*) (length v*))
;; ASSUME: (unique? x*)
(define (extends-env? env0 x*0 v*0)
  (let loop ([x* x*0] [v* v*0] [env env0])
    (cond [(empty? x*) #t]
          [else (match env0
                  [(cons (list x^ v^)  env^)
                   (and (equal? (first x*) x^)
                        (equal? (first v*) v^)
                        (loop (rest x*) (rest v*) (rest env)))]
                  [else #f])])))

;; (envof TypeExpr) -> (listof Symbol)
;; Produce a list of all of the variables in env0
(define (free-env-vars env0)
  (foldr append empty
         (for/list ([b env0])
           (match-let ([(list x tX) b])
             (free-vars tX)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type Checking

;; Tenv is (envof Type)
;; interp. The type associated to each identifier in the surrounding context
(define Tenv? (envof? Type?))

(define (identifier? x)
  (local [(define RESERVED '(number + fixFun :))]
    (and (symbol? x)
         (not (memq x RESERVED)))))


;; tenv ⊢ tmu : type judgment.

(define-type TMU/wt

  ;; [num/wt]
  ;; ----------------------
  ;;    tenv ⊢ n : number
  [num/wt (tenv Tenv?) (n number?)]

  ;; [add/wt]  tenv1 ⊢ tmu1 : number   tenv2 ⊢ tmu2 : number
  ;; ------------------------------------------------------------
  ;;            tenv1 ⊢ {+ tmu1 tmu2} : number
  ;; CHECK: tenv1 = tenv2
  [add/wt (tmu/wt1 TMU/wt?) (tmu/wt2 TMU/wt?)
          #:when (equal? (tmu/wt-tenv tmu/wt1) (tmu/wt-tenv tmu/wt2))]

  ;; [id/wt]
  ;; ------------------------
  ;;     tenv ⊢ x : type
  ;; CHECK: (lookup-env tenv x) = type
  [id/wt (tenv Tenv?) (x identifier?)
         #:when (in-env? tenv x)]

  ;; [fixFun/wt]  tenv2 ⊢ tmu : type1
  ;; ------------------------------------------------------------
  ;;            tenv1 ⊢ {fixFun f {x} tmu} : type3
  ;; CHECK: tenv2 = (extend-env tenv1
  ;;                            (list f x)
  ;;                            (list type3 type0))
  ;; CHECK: type3 = type0 -> type1
  ;; * Notice that x has type type0 in the above rule, which matches the domain
  ;;   type of the function (type3).
  ;; * The type annotation for f, i.e. type3, matches the type of the overall
  ;;   term.
  [fixFun/wt (f identifier?) (f-type Type?) (x identifier?) (tmu/wt TMU/wt?)
             #:when (and (funType? f-type)
                         (match-let ([(funType param-type result-type) f-type]
                                     [tenv1 (tmu/wt-tenv tmu/wt)])
                           (extends-env? tenv1
                                         (list f x)
                                         (list f-type param-type))
                           (equal? (tmu/wt-type tmu/wt) result-type)))]

  ;; [app/wt]  tenv1 ⊢ tmu1 : type1   tenv2 ⊢ tmu2 : type2
  ;; ------------------------------------------------------------
  ;;            tenv1 ⊢ {tmu1 tmu2} : type3
  ;; CHECK: tenv1 = tenv2
  ;; CHECK: type1 = type2 -> type3
  [app/wt (tmu/wt1 TMU/wt?) (tmu/wt2 TMU/wt?)
          #:when (and (equal? (tmu/wt-tenv tmu/wt1) (tmu/wt-tenv tmu/wt2))
                      (funType? (tmu/wt-type tmu/wt1))
                      (match-let ([(funType param-type result-type)
                                   (tmu/wt-type tmu/wt1)])
                        (equal? (tmu/wt-type tmu/wt2) param-type)))]

  ;; [with/wt]  tenv1 ⊢ tmu1 : type1    tenv2 ⊢ tmu2 : type2
  ;; ---------------------------------------------------------------
  ;;          tenv1 ⊢ {with {x tmu1} tmu2} : type2
  ;; CHECK: tenv2 = (extend-env tenv1  x type1)
  [with/wt (x identifier?) (tmu/wt1 TMU/wt?) (tmu/wt2 TMU/wt?)
           #:when (equal? (tmu/wt-tenv tmu/wt2)
                          (extend-env* (tmu/wt-tenv tmu/wt1)
                                       (list x)
                                       (list (tmu/wt-type tmu/wt1))))]

  ;; [poly-with/wt]  tenv ⊢ tmu1 : type1
  ;;                 tenv ⊢ tmu2^ : type2
  ;; ---------------------------------------------------------------
  ;;          tenv1 ⊢ {with {x tmu1} tmu2} : type2
  ;; CHECK: tmu2^ ≈ (subst tmu2 x tmu1)
  [poly-with/wt (x identifier?) (tmu/wt1 TMU/wt?) (tmu2 TMU?)
                (tmu/wt2^ TMU/wt?)
                #:when (alpha-equiv?
                        (tmu/wt-tmu tmu/wt2^)
                        (subst tmu2 x (tmu/wt-tmu tmu/wt1)))]
  )


; template
#;
(define (fn-for-tmu/wt tmu/wt)
  (type-case TMU/wt tmu/wt
    [num/wt (tenv n) (... tenv n)]
    [add/wt (tmu/wt1 tmu/wt2)
            (... (fn-for-tmu/wt tmu/wt1)
                 (fn-for-tmu/wt tmu/wt2))]
    [id/wt (tenv x) (... tenv x)]
    [fixFun/wt (f type x tmu/wt)
               (... f type x (fn-for-tmu/wt tmu/wt))]
    [app/wt (tmu/wt1 tmu/wt2)
            (... (fn-for-tmu/wt tmu/wt1)
                 (fn-for-tmu/wt tmu/wt2))]
    [with/wt (x tmu/wt1 tmu/wt2)
             (... x
                  (fn-for-tmu/wt tmu/wt1)
                  (fn-for-tmu/wt tmu/wt2))]
    [poly-with/wt (x tmu/wt1 tmu2 tmu/wt2^)
                  (... x
                       (fn-for-tmu/wt tmu/wt1)
                       (fn-for-tmu tmu2)
                       (fn-for-tmu/wt tmu/wt2^))]))


;;
;; Selectors
;;

;; TMU/wt -> Tenv
;; produce the type environment associated with the given derivation
(define (tmu/wt-tenv tmu/wt)
  (type-case TMU/wt tmu/wt
    [num/wt (tenv n) tenv]
    [add/wt (tmu/wt1 tmu/wt2)
            (tmu/wt-tenv tmu/wt1)] ; arbitrarily choose left since they're equal
    [id/wt (tenv x) tenv]
    [fixFun/wt (f type x tmu/wt^)
               (let ([tenv (tmu/wt-tenv tmu/wt^)])
                 (shrink-env tenv (list f x)))]
    [app/wt (tmu/wt1 tmu/wt2)
            (tmu/wt-tenv tmu/wt1)]
    [with/wt (x tmu/wt1 tmu/wt2)
             (tmu/wt-tenv tmu/wt1)]
    [poly-with/wt (x tmu/wt1 tmu2 tmu/wt2^)
                  (tmu/wt-tenv tmu/wt1)]))


;; TMU/wt -> TMU
;; produce the tmu expression associated with the given derivation
(define (tmu/wt-tmu tmu/wt)
  (type-case TMU/wt tmu/wt
    [num/wt (tenv n) (num n)]
    [add/wt (tmu/wt1 tmu/wt2)
            (add (tmu/wt-tmu tmu/wt1)
                 (tmu/wt-tmu tmu/wt2))]
    [id/wt (tenv x) (id x)]
    [fixFun/wt (f f-type x tmu/wt)
               (fixFun f x (tmu/wt-tmu tmu/wt))]
    ;;             (fixFun f f-type x (tmu/wt-tmu tmu/wt))]  ** FORMERLY **
    [app/wt (tmu/wt1 tmu/wt2)
            (app (tmu/wt-tmu tmu/wt1)
                 (tmu/wt-tmu tmu/wt2))]
    [with/wt (x tmu/wt1 tmu/wt2)
             (with x
                   (tmu/wt-tmu tmu/wt1)
                   (tmu/wt-tmu tmu/wt2))]
    [poly-with/wt (x tmu/wt1 tmu2 tmu/wt2^)
                  (poly-with x
                             (tmu/wt-tmu tmu/wt1)
                             tmu2)]))


;; TMU/wt -> Type
;; produce the type associated with the given derivation
(define (tmu/wt-type tmu/wt)
  (type-case TMU/wt tmu/wt
    [num/wt (tenv n) (numType)]
    [add/wt (tmu/wt1 tmu/wt2)
            (numType)]
    [id/wt (tenv x) (lookup-env tenv x)]
    [fixFun/wt (f f-type x tmu/wt)
               f-type] ; return self-reference's type
    [app/wt (tmu/wt1 tmu/wt2)
            (funType-result (tmu/wt-type tmu/wt1))]
    [with/wt (x tmu/wt1 tmu/wt2)
             (tmu/wt-type tmu/wt2)]
    [poly-with/wt (x tmu/wt1 tmu2 tmu/wt2^)
                  (tmu/wt-type tmu/wt2^)]))


;; Support for Examples

;; A non-terminating iteration, ever spiraling downwards
(define badIter
  ;;(fixFun 'f (funType (numType) (numType)) 'x ** FORMERLY
  (fixFun 'f  'x
          (app (id 'f) (add (num -1) (id 'x)))))

;The typing environment inside the body of badIter
(define theTenv `((f ,(funType (numType) (numType))) (x ,(numType))))

;Typing derivation for badIter
(define deriv
  (fixFun/wt 'f (funType (numType) (numType)) 'x
             (app/wt (id/wt theTenv 'f)
                     (add/wt (num/wt theTenv -1) (id/wt theTenv 'x)))))

;; Examples

;; Make sure the typing derivation is for the empty environment
(test (tmu/wt-tenv deriv) '())

;; Make sure the type of the derivation is Num -> Num
(test (tmu/wt-type deriv) (funType (numType) (numType)))

;; Make sure the expression for the derivation is
;; the function we defined above
(test (tmu/wt-tmu deriv) badIter)

;; Make sure the type of the derivation is Num -> Num
(test (tmu/wt-type deriv) (funType (numType) (numType)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type Inference - Who Knew High School Algebra Would Ever Be Useful?!?!

;; Data Type Expressions (X-Types): Data Types with variables where we
;;   want types

;; TenvX is (envof TypeExpr)
;; interp. The type *expression* associated to each identifier
(define TenvX? (envof? TypeExpr?))

;; (substof Type) TenvX -> Tenv
;; produce a type environment from the given substitution and tenv expression
(define (apply-subst-tenvX subst tenvX)
  (for/list ([binding tenvX])
    (match binding
      [(list x texpr) (list x (apply-subst subst texpr))])))


;; TMU/wtX - Type Derivation *Expressions*,
;; Same as TMU/wt, except:
;; 1) Types are now Type *Expressions*
;; 2) Type Environments are now Type Environment *Expressions*
;; 3) NO SIDE CONDITIONS!

;; Same as TMU/wt otherwise
(define-type TMU/wtX
  [num/wtX (tenvX TenvX?) (n number?)]
  [add/wtX (tmu/wtX1 TMU/wtX?) (tmu/wtX2 TMU/wtX?)]
  [id/wtX (tenvX TenvX?) (x identifier?)]
  [fixFun/wtX (f identifier?) (f-typeX TypeExpr?) (x identifier?)
              (tmu/wtX TMU/wtX?)]
  [app/wtX (tmu/wtX1 TMU/wtX?) (tmu/wtX2 TMU/wtX?)]
  [with/wtX (x identifier?) (tmu/wtX1 TMU/wtX?) (tmu/wtX2 TMU/wtX?)]
  [poly-with/wtX (x identifier?) (tmu/wtX1 TMU/wtX?) (tmu2 TMU?)
                 (tmu/wtX2^ TMU/wtX?)])

; template
#;
(define (fn-for-tmu/wtX tmu/wtX)
  (type-case TMU/wtX tmu/wtX
    [num/wtX (tenvX n) (... tenvX n)]
    [add/wtX (tmu/wtX1 tmu/wtX2)
             (... (fn-for-tmu/wtX tmu/wtX1)
                  (fn-for-tmu/wtX tmu/wtX2))]
    [id/wtX (tenv x) (... tenv x)]
    [fixFun/wtX (f typeX x tmu/wtX)
                (... f typeX x (fn-for-tmu/wtX tmu/wtX))]
    [app/wtX (tmu/wtX1 tmu/wtX2)
             (... (fn-for-tmu/wtX tmu/wtX1)
                  (fn-for-tmu/wtX tmu/wtX2))]
    [with/wtX (x tmu/wtX1 tmu/wtX2)
              (... x
                   (fn-for-tmu/wtX tmu/wtX1)
                   (fn-for-tmu/wtX tmu/wtX2))]
    [poly-with/wtX (x tmu/wtX1 tmu/wtX2 tmu/wtX2^)
                   (... x
                        (fn-for-tmu/wtX tmu/wtX1)
                        (fn-for-tmu/wtX tmu/wtX2)
                        (fn-for-tmu/wtX tmu/wtX2^))]))


;; PROBLEM: Complete the implementation of apply-subst-tmu/wtX

;; (substof Type) TMU/wtX -> TMU/wt
;; produce a typing derivation from a substitution and derivation expression
(define (apply-subst-tmu/wtX subst tmu/wt)
  (type-case TMU/wtX tmu/wt
    [num/wtX (tenvX n)
             (num/wt (apply-subst-tenvX subst tenvX) n)]
    [add/wtX (tmu/wtX1 tmu/wtX2)
             (add/wt (apply-subst-tmu/wtX subst tmu/wtX1)
                     (apply-subst-tmu/wtX subst tmu/wtX2))]
    [id/wtX (tenvX x)
            (id/wt (apply-subst-tenvX subst tenvX) x)]
    [fixFun/wtX (f typeX x tmu/wtX)
                (fixFun/wt f
                           (apply-subst subst typeX)
                           x
                           (apply-subst-tmu/wtX subst tmu/wtX))]
    [app/wtX (tmu/wtX1 tmu/wtX2)
             (app/wt (apply-subst-tmu/wtX subst tmu/wtX1)
                     (apply-subst-tmu/wtX subst tmu/wtX2))]
    [with/wtX (x tmu/wtX1 tmu/wtX2)
              (with/wt x
                       (apply-subst-tmu/wtX subst tmu/wtX1)
                       (apply-subst-tmu/wtX subst tmu/wtX2))]
    [poly-with/wtX (x tmu/wtX1 tmu2 tmu/wtX2^)
                   (poly-with/wt x
                                 (apply-subst-tmu/wtX subst tmu/wtX1)
                                 tmu2
                                 (apply-subst-tmu/wtX subst tmu/wtX2^))]))


;; PROBLEM: Complete the implementation of tmu->tmu/wtX

;; TMU -> (list TMU/wtX SystemOfEqns)
;; produce a TMU/wtX derivation *expression* of tenv ⊢ tmu : texpr and a
;; system of equations that must be satisfied for a proper TMU/wt to exist
;; Effect: signal an error if no such derivation expression exists.
(define (tmu->tmu/wtX tmu0)
  ;; Accumulator: soeqns is SystemOfEqns
  ;; Invariant: collects all equations deemed necessary so far
  (local [(define soeqns (void))
          ;; TypeExpr TypeExpr -> Void
          ;; produces void
          ;; Effect: Adds the equation typeX1 = typeX2 to soeqns
          (define (assert-equal! texpr1 texpr2)
            (set! soeqns (cons (assert-equal texpr1 texpr2) soeqns)))

          ;; -> TypeExpr
          ;; produce some type expression
          ;; Effect: generates a fresh unification variable
          (define (some-type!) (unifVar (gensym 'X)))

          ;; -> TypeExpr
          ;; produce some function type expression
          ;; Effect: generates a fresh unification variable
          (define (some-function-type!) (funType (some-type!) (some-type!)))

          ;; TMU/wtX -> TypeX
          ;; produce a type expression that represents the type of the judgment
          ;; Effect:                  
          (define (tmu/wtX-typeX tmu/wtX)
            (type-case TMU/wtX tmu/wtX
              [num/wtX (tenvX n) (numType)]
              [add/wtX (tmu/wtX1 tmu/wtX2) (numType)]
              [id/wtX (tenvX x) (lookup-env tenvX x)]
              [fixFun/wtX (f f-typeX x tmu/wtX)
                          f-typeX]
              [app/wtX (tmu/wtX1 tmu/wtX2)
                       (funType-result
                        (assert-funType! (tmu/wtX-typeX tmu/wtX1)))]
              [with/wtX (x tmu/wtX1 tmu/wtX2)
                        (tmu/wtX-typeX tmu/wtX2)]
              [poly-with/wtX (x tmu/wtX1 tmu2 tmu/wtX2^)
                             (tmu/wtX-typeX tmu/wtX2^)]))
          
          ;; TMU TenvX TypeX -> TMU/wtX
          ;; produce a derivation of tenvX ⊢ tmu : typeX^
          ;; Effect: adds typeX^ = typeX to soeqns
          (define (synth&assert tmu tenvX typeX)
            (let ([tmu/wtX (tmu->tmu/wtX--acc tmu tenvX)])
              (begin
                (assert-equal! (tmu/wtX-typeX tmu/wtX) typeX)
                tmu/wtX)))
          ;; Type -> funType
          ;; produce type if type is a function type
          ;; Effect: signal an error if type is not a function type
          (define (assert-funType! typeX)
            (let ([f-typeX (some-function-type!)])
              (begin
                (assert-equal! f-typeX typeX)
                f-typeX)))
          ;; TMU TenvX -> TMU/wtX
          (define (tmu->tmu/wtX--acc tmu tenvX)
            (type-case TMU tmu
              [num (n) (num/wtX tenvX n)]
              [add (lhs rhs) (add/wtX (synth&assert lhs tenvX (numType))
                                      (synth&assert rhs tenvX (numType)))]
              [id (x)
                  (begin
                    (unless (in-env? tenvX x)
                      (error 'tmu->tmu/wtX "Unbound identifier: ~s" x))
                    (id/wtX tenvX x))]
              [fixFun (f #;f-type x body)
                      (let ([f-type (some-function-type!)])
                        (match-let ([(funType arg-type result-type) f-type])
                          (let ([body/wtX (synth&assert
                                           body
                                           (extend-env* tenvX
                                                        (list f x)
                                                        (list f-type arg-type))
                                           result-type)])
                            (fixFun/wtX f f-type x body/wtX))))]
              [app (rator rand)
                   (let* ([rator/wtX (tmu->tmu/wtX--acc rator tenvX)]
                          [rator-type (tmu/wtX-typeX rator/wtX)])
                     (match-let ([(funType arg-type result-type)
                                  (assert-funType! rator-type)])
                       (let ([rand/wtX (synth&assert rand tenvX arg-type)])
                         (app/wtX rator/wtX rand/wtX))))]
              [with (name named body)
                    (let* ([named/wtX (tmu->tmu/wtX--acc named tenvX)]
                           [named-type (tmu/wtX-typeX named/wtX)]
                           [body/wtX
                            (tmu->tmu/wtX--acc
                             body
                             (extend-env* tenvX
                                          (list name)
                                          (list named-type)))])
                      (with/wtX name named/wtX body/wtX))]
              [poly-with
               (name named body)
               (let* ([named/wtX (tmu->tmu/wtX--acc named tenvX)]
                      [body^ (subst body name named)]
                      [body^/wtX
                       (tmu->tmu/wtX--acc
                        body^ tenvX)])
                 (poly-with/wtX name named/wtX body body^/wtX))]))]
    (begin
      (set! soeqns empty)
      (list (tmu->tmu/wtX--acc tmu0 empty-env) soeqns)))) 


;; TMU Tenv -> TMU/wt
;; produce a TMU/wt derivation of tenv ⊢ tmu : type for some type
;; Effect: signal an error if no such derivation exists.

;; Accumulator: tenv is Tenv
;; Invariant: tenv associates identifiers with the types of tmu expressions
;;            to which they are bound in the surrounding context.
#;
(define (tmu->tmu/wt tmu tenv)
  (local [;; TMU Tenv Type -> TMU/wt
          ;; produce a derivation of tenv ⊢ tmu : type
          ;; Effect: signal an error if this is not possible
          (define (synth&check tmu tenv type)
            (let ([tmu/wt (tmu->tmu/wt tmu tenv)])
              (begin
                (unless (equal? (tmu/wt-type tmu/wt) type)
                  (error 'check "type mismatch: ~s ≠ ~s"
                         (tmu/wt-type tmu/wt) type ))
                tmu/wt)))
          ;; Type -> funType
          ;; produce type if type is a function type
          ;; Effect: signal an error if type is not a function type
          (define (assert-funType type)
            (begin
              (unless (funType? type)
                (error 'tmu->tmu/wt "Not a function type: ~s" type))
              type))]
    (type-case TMU tmu
      [num (n) (num/wt tenv n)]
      [add (lhs rhs) (add/wt (synth&check lhs tenv (numType))
                             (synth&check rhs tenv (numType)))]
      [id (x)
          (begin
            (unless (in-env? tenv x)
              (error 'tmu->tmu/wt "Unbound identifier: ~s" x))
            (id/wt tenv x))]
      [fixFun (f f-type x body)
              (match-let ([(funType arg-type result-type)
                           (assert-funType f-type)])
                (let ([body/wt (synth&check
                                body
                                (extend-env* tenv
                                             (list f x)
                                             (list f-type arg-type))
                                result-type)])
                  (fixFun/wt f f-type x body/wt)))]
      [app (rator rand)
           (let* ([rator/wt (tmu->tmu/wt rator tenv)]
                  [rator-type (tmu/wt-type rator/wt)])
             (match-let ([(funType arg-type result-type)
                          (assert-funType rator-type)])
               (let ([rand/wt (synth&check rand tenv arg-type)])
                 (app/wt rator/wt rand/wt))))])))


;; TMU -> TMU/wt
;; produce a TMU/wt derivation of '() ⊢ tmu : texpr
;; Effect: signal an error if no such derivation exists.
(define (tmu->tmu/wt tmu)
  (match-let ([(list tmu/wtX soeqns) (tmu->tmu/wtX tmu)])
    (let ([subst (unify soeqns)])
      (apply-subst-tmu/wtX subst tmu/wtX))))


(define (tmu->tmu/wt0 tmu) (tmu->tmu/wt tmu))

(test (tmu->tmu/wt0 (num 7))
      (num/wt '() 7))
;(test (tmu->tmu/wt (num 7) `((x ,(numType))))
;      (num/wt (list (list 'x (numType))) 7))
;(test (tmu->tmu/wt (num 7) `((x ,(funType (numType) (numType)))))
;      (num/wt (list (list 'x (funType (numType) (numType)))) 7))
;(test (tmu->tmu/wt (id 'x) `((x ,(funType (numType) (numType)))))
;      (id/wt (list (list 'x (funType (numType) (numType)))) 'x))
;(test/exn (tmu->tmu/wt (id 'y) `((x ,(funType (numType) (numType)))))
;          "Unbound")

(define (emptyType) (paramType 'X))

(test/match
 (tmu->tmu/wt0 (fixFun 'f 'x (id 'x)))
 (fixFun/wt 'f (funType (paramType X) (paramType X))
            'x
            (id/wt (list (list 'f (funType (paramType X) (paramType X)))
                         (list 'x (paramType X))) 'x)))


(test/match (tmu->tmu/wt0 (fixFun 'f
                                  'x
                                  (app (id 'f) (id 'x))))
            (fixFun/wt
             'f
             (funType (paramType X) (paramType Y))
             'x
             (app/wt
              (id/wt (list (list 'f (funType (paramType X) (paramType Y)))
                           (list 'x (paramType X)))
                     'f)
              (id/wt (list (list 'f (funType (paramType X) (paramType Y)))
                           (list 'x (paramType X)))
                     'x))))

(test/match
 (tmu->tmu/wt0 (fixFun 'f 
                       'x
                       (app (id 'f)
                            (app (id 'f) (id 'x)))))
 
 (fixFun/wt
  'f
  (funType (paramType X) (paramType X))
  'x
  (app/wt
   (id/wt (list (list 'f (funType (paramType X) (paramType X)))
                (list 'x (paramType X))) 'f)
   (app/wt
    (id/wt (list (list 'f (funType (paramType X) (paramType X)))
                 (list 'x (paramType X))) 'f)
    (id/wt (list (list 'f (funType (paramType X) (paramType X)))
                 (list 'x (paramType X))) 'x)))))

(test (tmu->tmu/wt0 (fixFun 'f #;(funType (numType) (numType))
                            'x (add (id 'x) (id 'x))))
      (fixFun/wt
       'f
       (funType (numType) (numType))
       'x
       (add/wt
        (id/wt (list (list 'f (funType (numType) (numType)))
                     (list 'x (numType)))
               'x)
        (id/wt (list (list 'f (funType (numType) (numType)))
                     (list 'x (numType)))
               'x))))

(test/match (tmu->tmu/wt0 (fixFun 'f 
                                  'x (app (id 'x) (num 2))))
            (fixFun/wt
             'f
             (funType (funType (numType) (paramType X))
                      (paramType X))
             'x
             (app/wt
              (id/wt (list
                      (list 'f (funType (funType (numType) (paramType X))
                                        (paramType X)))
                      (list 'x (funType (numType) (paramType X))))
                     'x)
              (num/wt (list
                       (list 'f (funType (funType (numType) (paramType X))
                                         (paramType X)))
                       (list 'x (funType (numType) (paramType X))))
                      2))))

(test (tmu->tmu/wt0 (app (fixFun 'f 
                                 'x (id 'x)) (num 7)))
      (app/wt (fixFun/wt 'f (funType (numType) (numType))
                         'x
                         (id/wt (list (list 'f (funType (numType) (numType)))
                                      (list 'x (numType))) 'x))
              (num/wt '() 7)))



;; TMU -> TMU
;; reproduce the given tmu if it is a well-typed program ('() ⊢ type : type)
;; Effect: signal an error if not
(define (typecheck-tmu tmu)
  (let ([tmu/wt (tmu->tmu/wt tmu)])
    (begin
      ;; Trust But Verify!
      (unless (and (equal? (tmu/wt-tenv tmu/wt) '())
                   (equal? (tmu/wt-tmu tmu/wt) tmu))
        (error 'typecheck
               "Liar Liar Pants on Fire!\n I wanted: ~a\nYou gave me: ~a.\n"
               (format "'() ⊢ ~s : type for some type" tmu)
               (format "~a ⊢ ~a : ~a"
                       (tmu/wt-tenv tmu/wt)
                       (tmu/wt-tmu tmu/wt)
                       (print-type-expr (tmu/wt-type tmu/wt)))))

      tmu)))

(test (typecheck-tmu (num 7)) (num 7))
(test (typecheck-tmu (app (fixFun 'f
                                  'x (id 'x)) (num 7)))
      (app (fixFun 'f
                   'x (id 'x)) (num 7)))

(test/match (typecheck-tmu (fixFun 'f
                                   'x
                                   (app (id 'f)
                                        (app (id 'f) (id 'x)))))
            (fixFun 'f
                    'x
                    (app (id 'f)
                         (app (id 'f) (id 'x)))))

(test/exn (typecheck-tmu (id 'x)) "")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "with" examples

(test (typecheck-tmu (with 'x (num 7) (add (id 'x) (id 'x))))
      (with 'x (num 7) (add (id 'x) (id 'x))))

(test
 (typecheck-tmu (with 'f0 (fixFun 'f 'x (id 'x))
                      (app (id 'f0) (num 7))))
 (with 'f0 (fixFun 'f 'x (id 'x))
       (app (id 'f0) (num 7))))

(test
 (typecheck-tmu (with 'f0 (fixFun 'f 'x (id 'x))
                      (app (id 'f0) (fixFun 'f 'x (id 'x)))))
 (with 'f0 (fixFun 'f 'x (id 'x))
       (app (id 'f0) (fixFun 'f 'x (id 'x)))))

;; FAILS TYPE CHECKING
#;(test
 (typecheck-tmu (with 'f0 (fixFun 'f 'x (id 'x))
                      (app (id 'f0) (id 'f0))))
 (with 'f0 (fixFun 'f 'x (id 'x))
       (app (id 'f0) (id 'f0))))

;; PASSES TYPE CHECKING
(test
 (typecheck-tmu (poly-with 'f0 (fixFun 'f 'x (id 'x))
                      (app (id 'f0) (id 'f0))))
 (poly-with 'f0 (fixFun 'f 'x (id 'x))
       (app (id 'f0) (id 'f0))))