#lang plai
(print-only-errors)
(define (... . args) (cons '... args)) ; for templates
(require rackunit)
(require "datatype-311.rkt")

;; Ensure that a derivation can be constructed
(define-syntax-rule (test/data try)
  (check-not-exn (λ () try)))

;; Detect errors during construction of a type derivation
(define-syntax-rule (test/data-exn try)
  (check-exn exn:fail? (λ () try)))


;;
;; Doru - A language named by popular request
;;  "Be careful what you wish for"
;;       -- Doru Kesriyeli (November 23, 2020 late morning, Vancouver Time)
;;


;; Identifier is Symbol
;; interp.  a legal Doru identifier

;; any -> Boolean
;; produce true if the given object is a legal identifier, otherwise false
(define (identifier? x)
  (local [(define RESERVED '(number boolean + - <  with if))]
    (and (symbol? x)
         (not (memq x RESERVED)))))


(define-type Type
  [numType]
  [boolType])
;; <TYPE> ::= number | boolean
;; interp. a static type in the language

;; Type -> string
;; produce the name of the given type
(define (type-string type)
  (type-case Type type
    [numType () "number"]
    [boolType () "boolean"]))


(define-type DORU
  [num (n number?)]
  [bool (b boolean?)]
  [add (lhs DORU?) (rhs DORU?)]
  [sub (lhs DORU?) (rhs DORU?)]
  [eqwal (lhs DORU?) (rhs DORU?)]
  [lt (lhs DORU?) (rhs DORU?)]
  [bif (predicate DORU?) (consequent DORU?) (alternative DORU?)]
  [with (name identifier?) (named DORU?) (body DORU?)]
  [id (name identifier?)])
;; interp. expressions in a typed language with arithmetic,
;; conditionals, and identifiers. Its syntax is defined by the following EBNF:
;; <DORU> ::=
;; (ARITHMETIC)
;;             <num>
;;           | {+ <DORU> <DORU>}
;;           | {- <DORU> <DORU>}
;; (COMPARISONS)
;;           | {= <DORU> <DORU>}
;;           | {< <DORU> <DORU>}
;; (IDENTIFIERS)
;;           | <id>
;;           | {with {<id> <DORU>} <DORU>}
;; (CONDITIONALS)
;;           | <bool>
;;           | {if <DORU> <DORU> <DORU>}

(define D1 (num 5))
(define D2 (bool #t))
(define D3 (bif (bool #f)
                (num 5)
                (num 6)))
(define D4 (with 'x (bif (lt (num 5) (num 6))
                         (lt (num 7) (num 0))
                         (lt (num 0) (num 7)))
                 (bif (id 'x)
                      (add (num 2) (num 3))
                      (num 9))))

#;
(define (fn-for-doru doru)
  (type-case DORU doru
    [num (n) (... n)]
    [bool (b) (... b)]
    [add (lhs rhs) (... (fn-for-doru lhs)
                        (fn-for-doru rhs))]
    [sub (lhs rhs) (... (fn-for-doru lhs)
                        (fn-for-doru rhs))]
    [eqwal (lhs rhs) (... (fn-for-doru lhs)
                          (fn-for-doru rhs))]
    [lt (lhs rhs) (... (fn-for-doru lhs)
                       (fn-for-doru rhs))]
    [bif (pred conseq altern) (... (fn-for-doru pred)
                                   (fn-for-doru conseq)
                                   (fn-for-doru altern))]
    [with (x named body) (... x
                              (fn-for-doru named)
                              (fn-for-doru body))]
    [id (x) (... x)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Environments

;; (envof X) is (listof (list symbol X))

;; any -> boolean
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


;; empty-env : Env
(define empty-env '())


;; extend-env : (envof X) Symbol X -> (envof X)
;; produce an environment that extends env to bind x to v.
(define (extend-env env x v)
  (cons (list x v) env)) 

(test (extend-env
       (extend-env
        (extend-env empty-env 'z 7)
        'y 6)
       'x 5)
      '((x 5) (y 6) (z 7)))

;; extend-env* : (envof X) (listof Symbol) (listof X) -> (envof X)
;; Produce an environment that binds distinct symbols in x* to values in v*.
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


;; lookup-env : (envof X) Symbol -> X
;; Produce the binding for the given symbol.
;; Effect: Signals an error if no binding is found.
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
  (cond [(empty? env) #f]
        [else (if (symbol=? x (car (first env)))
                  #t
                  (in-env? (rest env) x))]))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Type checking
;;


;; Tenv is (envof Type)
;; interp. The type associated to each identifier in the surrounding context
(define Tenv? (envof? Type?))

;; Well-typed (wt) DORU expressions
(define-type DORU/wt
  ;; tenv ⊢ doru : type
  ;; interp. in a context where tenv assigns types to some identifiers,
  ;;         doru has type "type".

  ;; [num/wt]
  ;; ----------------------
  ;;    tenv ⊢ n : number
  [num/wt (tenv Tenv?) (n number?)]
  
  ;; [add/wt]  tenv1 ⊢ doru1 : type1   tenv2 ⊢ doru2 : type2
  ;; ------------------------------------------------------------
  ;;            tenv1 ⊢ {+ doru1 doru2} : number
  ;; CHECK: tenv1 = tenv2
  ;; CHECK: type1 = type2 = number
  [add/wt (doru/wt1 DORU/wt?) (doru/wt2 DORU/wt?)
          #:when (and (equal? (doru/wt-tenv doru/wt1) (doru/wt-tenv doru/wt2))
                      (equal? (doru/wt-type doru/wt1) (numType))
                      (equal? (doru/wt-type doru/wt2) (numType)))]
  
  ;; [sub/wt]  tenv1 ⊢ doru1 : type1   tenv2 ⊢ doru2 : type2
  ;; ------------------------------------------------------------
  ;;            tenv1 ⊢ {- doru1 doru2} : number
  ;; CHECK: tenv1 = tenv2
  ;; CHECK: type1 = type2 = number
  [sub/wt (doru/wt1 DORU/wt?) (doru/wt2 DORU/wt?)
          #:when (and (equal? (doru/wt-tenv doru/wt1) (doru/wt-tenv doru/wt2))
                      (equal? (doru/wt-type doru/wt1) (numType))
                      (equal? (doru/wt-type doru/wt2) (numType)))]

  
  ;; [eqwal/wt]  tenv1 ⊢ doru1 : type1   tenv2 ⊢ doru2 : type2
  ;; ------------------------------------------------------------
  ;;            tenv ⊢ {= doru1 doru2} : boolean
  ;; CHECK: tenv1 = tenv2
  ;; CHECK: type1 = type2 = number
  [eqwal/wt (doru/wt1 DORU/wt?) (doru/wt2 DORU/wt?)
            #:when (and (equal? (doru/wt-tenv doru/wt1) (doru/wt-tenv doru/wt2))
                        (equal? (doru/wt-type doru/wt1) (numType))
                        (equal? (doru/wt-type doru/wt2) (numType)))]
  
  ;; [lt/wt]  tenv1 ⊢ doru1 : type1   tenv2 ⊢ doru2 : type2
  ;; ------------------------------------------------------------
  ;;            tenv ⊢ {< doru1 doru2} : boolean
  ;; CHECK: tenv1 = tenv2 
  ;; CHECK: type1 = type2 = number
  [lt/wt (doru/wt1 DORU/wt?) (doru/wt2 DORU/wt?)
         #:when (and (equal? (doru/wt-tenv doru/wt1) (doru/wt-tenv doru/wt2))
                     (equal? (doru/wt-type doru/wt1) (numType))
                     (equal? (doru/wt-type doru/wt2) (numType)))]

  ;; [id/wt]
  ;; ------------------------
  ;;     tenv ⊢ x : type1
  ;; CHECK: (lookup-env tenv x) = type1
  [id/wt (tenv Tenv?) (x identifier?)
         #:when (in-env? tenv x)]

  ;; [with/wt]  tenv1 ⊢ doru1 : type1    tenv2 ⊢ doru2 : type2
  ;; ---------------------------------------------------------------
  ;;          tenv1 ⊢ {with {x doru1} doru2} : type2
  ;; CHECK: tenv2 = (extend-env tenv1  x type1)
  [with/wt (x identifier?) (doru/wt1 DORU/wt?) (doru/wt2 DORU/wt?)
           #:when (equal? (doru/wt-tenv doru/wt2)
                          (extend-env (doru/wt-tenv doru/wt1)
                                      x
                                      (doru/wt-type doru/wt1)))]

  ;; [bool/wt] 
  ;; ------------------------------------------------------------
  ;;     tenv ⊢ b : boolean 
  [bool/wt (tenv Tenv?) (b boolean?)]
  
  ;; [if/wt]  tenv1 ⊢ doru1 : type1
  ;;          tenv2 ⊢ doru2 : type2  tenv3 ⊢ doru3 : type3
  ;; ------------------------------------------------------------
  ;;          tenv1 ⊢ {if doru1 doru2 doru3} : type2
  ;; CHECK: tenv1 = tenv2 = tenv3
  ;; CHECK: type1 = boolean
  ;; CHECK: type2 = type3
  [bif/wt (doru/wt1 DORU/wt?) (doru/wt2 DORU/wt?) (doru/wt3 DORU/wt?)
          ; ;; PROBLEM 1:  COMPLETE THE SIDE CONDITION
          ; #:when (... (fn-for-doru/wt doru/wt1)
          ;             (fn-for-doru/wt doru/wt2)
          ;             (fn-for-doru/wt doru/wt3))]
          #:when (and (equal? (doru/wt-tenv doru/wt1) (doru/wt-tenv doru/wt2))
                      (equal? (doru/wt-tenv doru/wt2) (doru/wt-tenv doru/wt3))
                      (equal? (doru/wt-type doru/wt1) (boolType))
                      (equal? (doru/wt-type doru/wt2) (doru/wt-type doru/wt3)))]

  ) ; define-type


(define (fn-for-doru/wt doru/wt)
  (type-case DORU/wt doru/wt
    [num/wt (tenv n) (... tenv n)]
    [add/wt (doru/wt1 doru/wt2)
            (... (fn-for-doru/wt doru/wt1)
                 (fn-for-doru/wt doru/wt2))]
    [sub/wt (doru/wt1 doru/wt2)
            (... (fn-for-doru/wt doru/wt1)
                 (fn-for-doru/wt doru/wt2))]
    [eqwal/wt (doru/wt1 doru/wt2)
              (... (fn-for-doru/wt doru/wt1)
                   (fn-for-doru/wt doru/wt2))] 
    [lt/wt (doru/wt1 doru/wt2)
           (... (fn-for-doru/wt doru/wt1)
                (fn-for-doru/wt doru/wt2))]    
    [id/wt (tenv x) (... tenv x)]
    [with/wt (x doru/wt1 doru/wt2)
             (... x
                  (fn-for-doru/wt doru/wt1)
                  (fn-for-doru/wt doru/wt2))]
    [bool/wt (tenv b) (... tenv b)]
    [bif/wt (doru/wt1 doru/wt2 doru/wt3)
            (... (fn-for-doru/wt doru/wt1)
                 (fn-for-doru/wt doru/wt2)
                 (fn-for-doru/wt doru/wt3))]))


;; Selectors

;; DORU/wt -> Tenv
;; produce the type environment about which the derivation's judgment holds
(define (doru/wt-tenv doru/wt)
  (type-case DORU/wt doru/wt
    [num/wt (tenv n) tenv]
    [add/wt (doru/wt1 doru/wt2)
            (doru/wt-tenv doru/wt1)]
    [sub/wt (doru/wt1 doru/wt2)
            (doru/wt-tenv doru/wt1)]
    [eqwal/wt (doru/wt1 doru/wt2)
              (doru/wt-tenv doru/wt1)]
    [lt/wt (doru/wt1 doru/wt2)
           (doru/wt-tenv doru/wt1)]    
    [id/wt (tenv x) tenv]
    [with/wt (x doru/wt1 doru/wt2)
             (doru/wt-tenv doru/wt1)]
    [bool/wt (tenv b) tenv]
    [bif/wt (doru/wt1 doru/wt2 doru/wt3)
            (doru/wt-tenv doru/wt1)]))


;; DORU/wt -> DORU
;; produce the doru about which the derivation's judgment holds
(define (doru/wt-doru doru/wt)
  (type-case DORU/wt doru/wt
    [num/wt (tenv n) (num n)]
    [add/wt (doru/wt1 doru/wt2)
            (add (doru/wt-doru doru/wt1)
                 (doru/wt-doru doru/wt2))]
    [sub/wt (doru/wt1 doru/wt2)
            (sub (doru/wt-doru doru/wt1)
                 (doru/wt-doru doru/wt2))]
    [eqwal/wt (doru/wt1 doru/wt2)
              (eqwal (doru/wt-doru doru/wt1)
                     (doru/wt-doru doru/wt2))]
    [lt/wt (doru/wt1 doru/wt2)
           (lt (doru/wt-doru doru/wt1)
               (doru/wt-doru doru/wt2))]
    [id/wt (tenv x) (id x)]
    [with/wt (x doru/wt1 doru/wt2)
             (with x                  
                   (doru/wt-doru doru/wt1)
                   (doru/wt-doru doru/wt2))]
    [bool/wt (tenv b) (bool b)]
    [bif/wt (doru/wt1 doru/wt2 doru/wt3)
            (bif (doru/wt-doru doru/wt1)
                 (doru/wt-doru doru/wt2)
                 (doru/wt-doru doru/wt3))]))


;; DORU/wt -> Type
;; produce the type about which the derivation's judgment holds
(define (doru/wt-type doru/wt)
  (type-case DORU/wt doru/wt
    [num/wt (tenv n) (numType)]
    [add/wt (doru/wt1 doru/wt2)
            (numType)]
    [sub/wt (doru/wt1 doru/wt2)
            (numType)]
    [eqwal/wt (doru/wt1 doru/wt2)
              (boolType)] 
    [lt/wt (doru/wt1 doru/wt2)
           (boolType)]
    [id/wt (tenv x) (lookup-env tenv x)]
    [with/wt (x doru/wt1 doru/wt2)
             (doru/wt-type doru/wt2)]
    [bool/wt (tenv b) (boolType)]
    [bif/wt (doru/wt1 doru/wt2 doru/wt3)
            (doru/wt-type doru/wt2)]))


;; Side-condition tests

(test/data (num/wt '() 5))
(test/data (bool/wt '() #f))
(test/data (id/wt `((x ,(numType))) 'x))
(test/data-exn (id/wt `((y ,(numType))) 'x))
(test/data (add/wt (num/wt '() 5)
                   (num/wt '() 6)))
(test/data-exn (add/wt (num/wt '() 5)
                       (num/wt `((x ,(numType))) 6)))

(test/data (with/wt 'x 
                    (num/wt '() 5)
                    (num/wt `((x ,(numType))) 6)))

(test/data-exn (with/wt 'x 
                        (num/wt '() 5)
                        (num/wt `((x ,(boolType))) 6)))

(test/data (bif/wt (bool/wt '() #t)
                   (num/wt '() 6)
                   (num/wt '() 7)))

(test/data-exn (bif/wt (num/wt '() 5)
                       (num/wt '() 6)
                       (num/wt '() 7)))

(test/data-exn (bif/wt (bool/wt '() #t)
                       (num/wt '() 6)
                       (bool/wt '() #f)))

(test/data-exn (bif/wt (bool/wt '() #t)
                       (num/wt (list (list 'x (boolType))) 6)
                       (num/wt '() 7)))


;; PROBLEM 2: COMPLETE THE DESIGN OF doru->doru/wt

;; DORU Tenv -> DORU/wt
;; produce a DORU/wt derivation of tenv ⊢ doru : type for some type
;; Effect: signal an error if no such derivation exists.

;; Accumulator: tenv is Tenv
;; Invariant: tenv associates identifiers with the types of doru expressions
;;            to which they are bound in the surrounding context.
#;(define (doru->doru/wt doru tenv) (num/wt '() 0)) ; stub

(define (doru->doru/wt doru tenv)
  (local [(define (synth&check doru tenv type)
            (let ([doru/wt (doru->doru/wt doru tenv)])
              (begin
                (unless (equal? (doru/wt-type doru/wt) type)
                  (error 'check "type mismatch"))
                doru/wt)))]
    (type-case DORU doru
      [num (n) (num/wt tenv n)]
      [bool (b) (bool/wt tenv b)]
      [add (lhs rhs)
           (let ([lhs/wt (synth&check lhs tenv (numType))]
                 [rhs/wt (synth&check rhs tenv (numType))])
             (add/wt lhs/wt rhs/wt))]
      [sub (lhs rhs)
           (let ([lhs/wt (synth&check lhs tenv (numType))]
                 [rhs/wt (synth&check rhs tenv (numType))])
             (sub/wt lhs/wt rhs/wt))]
      [eqwal (lhs rhs)
             (let ([lhs/wt (synth&check lhs tenv (numType))]
                   [rhs/wt (synth&check rhs tenv (numType))])
               (eqwal/wt lhs/wt rhs/wt))]
      [lt (lhs rhs)
          (let ([lhs/wt (synth&check lhs tenv (numType))]
                [rhs/wt (synth&check rhs tenv (numType))])
            (lt/wt lhs/wt rhs/wt))]
      [bif (pred conseq altern)
           (let ([pred/wt (synth&check pred tenv (boolType))]
                 [conseq/wt (doru->doru/wt conseq tenv)]
                 [altern/wt (doru->doru/wt altern tenv)])
             (begin
               (unless (equal? (doru/wt-type conseq/wt)
                               (doru/wt-type altern/wt))
                 (error 'doru->doru/wt "Type mismatch: ~s ≠ ~s"
                        (doru/wt-type conseq/wt)
                        (doru/wt-type altern/wt)))
               (bif/wt pred/wt conseq/wt altern/wt)))]
      [with (x named body)
            (let* ([name/wt (doru->doru/wt named tenv)]
                   [body-tenv (extend-env tenv
                                          x
                                          (doru/wt-type name/wt))]
                   [body/wt (doru->doru/wt body body-tenv)])
              (with/wt x
                       name/wt
                       body/wt))]
      [id (x)
          (begin
            (unless (in-env? tenv x)
              (error 'doru->doru/wt "Unbound identifier: ~s" x))
            (id/wt tenv x))])))

(test (doru->doru/wt D1 '()) (num/wt '() 5))
(test (doru->doru/wt D2 '()) (bool/wt '() #t))
(test (doru->doru/wt D3 '()) (bif/wt (bool/wt '() #f)
                                     (num/wt '() 5)
                                     (num/wt '() 6)))
(test (doru->doru/wt D4 '())
      (with/wt 'x (bif/wt (lt/wt (num/wt '() 5) (num/wt '() 6))
                          (lt/wt (num/wt '() 7) (num/wt '() 0))
                          (lt/wt (num/wt '() 0) (num/wt '() 7)))
               (bif/wt (id/wt (list (list 'x (boolType))) 'x)
                       (add/wt (num/wt (list (list 'x (boolType))) 2)
                               (num/wt (list (list 'x (boolType))) 3))
                       (num/wt (list (list 'x (boolType))) 9))))


(test/exn (doru->doru/wt (add (bool #f) (num 5)) '()) "")
(test/exn (doru->doru/wt (add (num 5) (bool #t)) '()) "")
(test/exn (doru->doru/wt (bif (bool #f)
                              (num 5)
                              (bool #t))
                         '()) "")


;; DORU -> DORU
;; reproduce doru if doru is a well-typed program (i.e. '() ⊢ doru : type)
;; Effect: signal an error if not
(define (typecheck-doru doru)
  (let ([doru/wt (doru->doru/wt doru '())])
    (begin
      ;; Trust But Verify!
      (unless (and (equal? (doru/wt-tenv doru/wt) '())
                   (equal? (doru/wt-doru doru/wt) doru))
        (error 'typecheck
               "Liar Liar Pants on Fire!\n I wanted: ~a\nYou gave me: ~a.\n"
               (format "'() ⊢ ~s : type for some type" doru)
               (format "~a ⊢ ~a : ~a"
                       (doru/wt-tenv doru/wt)
                       (doru/wt-doru doru/wt)
                       (type-string (doru/wt-type doru/wt)))))
                       
      doru))) 





;; DORUPgm is DORU such that '() ⊢ doru : type for some Type type

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpretation

;; Value is one of:
;; - number
;; - boolean

;; Env is (envof Value)

;; any -> boolean
;; produce true if the given object is a Value
(define (Value? x)
  (for/or ([pred? (list number? boolean?)])
    (pred? x)))


;; DORUPgm -> Value
;; produce the result of interpreting doru0
(define (interp-doru doru0)
  (local
    [(define (interp-doru--env doru env)
       (let recur ([doru doru])
         (type-case DORU doru
           [num (n) n]
           [bool (b) b]
           [add (lhs rhs) (+ (recur lhs)
                             (recur rhs))]
           [sub (lhs rhs) (- (recur lhs)
                             (recur rhs))]
           [eqwal (lhs rhs) (= (recur lhs)
                               (recur rhs))]
           [lt (lhs rhs) (< (recur lhs)
                            (recur rhs))]
           [bif (pred conseq altern)
                (if (recur pred)
                    (recur conseq)
                    (recur altern))]
           [with (x named body)
                 (let ([v (recur named)])
                   (interp-doru--env
                    body
                    (extend-env env x v)))]
           [id (x) (lookup-env env x)])))]
    (interp-doru--env doru0 empty-env)))

(test (interp-doru (num 5)) 5)
(test (interp-doru (bool #t)) #t)
(test (interp-doru (bif (bool #f)
                        (num 5)
                        (num 6)))
      6)

(test (interp-doru (with 'x (bif (lt (num 5) (num 6))
                                 (lt (num 7) (num 0))
                                 (lt (num 0) (num 7)))
                         (bif (id 'x)
                              (add (num 2) (num 3))
                              (num 9))))
      9)