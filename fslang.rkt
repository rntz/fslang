#lang racket

(require racket/hash)

(define-syntax-rule (todo)
  (error "todo"))

(define subtype? equal?)

(define term? any/c)
(define type? any/c)

;; variable context (Γ/Δ/Ω in typing judgment):
;; maps variables to which context (set, pointed, or finite support)
;; and their type
(define area? (or/c 'set 'point 'fs))
(define cx? (hash/c symbol? (list/c area? type?)
                    #:immutable #t #:flat? #t))

;; variable usage analysis results:
;; a set of variables.
;; if a pointed set var is in here, it's nil-preserved.
;; if a finite support var is in here, it's finitely supported.
;; if a set var is in here, it means nothing.
(define usage? (set/c symbol?))

;;; semantic contracts
(define value? any/c)
(define env? (hash/c symbol? value? #:immutable #t #:flat? #t))
(define row? env?)
;; A term denotes a function from environments (maps from set or pointed vars to
;; values) to finite maps (represented by hash maps) from "rows" (maps from fs
;; vars to values) to their values.
(define deno/c (-> env? (hash/c row? value? #:immutable #t #:flat? #t)))

;; three kinds of variables in context:
;; 1 - arbitrary use
;; 2 - point preserving (relevant) use
;; 3 - finite support (ie not yet grounded)
;;
;; problem: I want to use a grading system to distinguish 1 & 2.
;; but 3 seems to need left-to-right information passing.
;; can I use a non-commutative grading monoid?
(define/contract (elab term want cx)
  (-> term? (or/c #f type?) cx?
      ;; type, variable usage, denotation
      (values type? usage? deno/c))

  (define get-area car)
  (define get-type cadr)
  (define (var-area x) (get-area (hash-ref cx x)))
  (define (var-type x) (get-type (hash-ref cx x)))

  (define (cannot-infer name)
    (unless want (error 'elab "cannot infer type of ~a" name))
    want)

  (define (inferred got)
    (cond
      [(not want) got]
      [(subtype? got want) got]
      [else (error 'elab "wanted ~a, but inferred ~a" want got)]))

  (match term
    [`(is ,anno ,t)                     ; TYPE ANNOTATION
     (unless (type? anno)
       (error 'elab "type annotation is not a valid type: ~a" anno))
     (when (and want (not (subtype? anno want)))
       (error "wanted ~a, but annotated ~a" want anno))
     (elab t anno cx)]

    ['nil                               ; NIL
     (values (cannot-infer "nil")
             ;; uses all point & fs variables
             (for/set ([(x xinfo) cx] #:unless (eq? 'set (get-area xinfo)))
               x)
             (λ (_env) (hash)))]

    ;; TODO: should this be able to use set variables? they'll have types of the
    ;; wrong kind! how am I handling the adjunction / separation of syntax
    ;; classes anyway?
    [(? symbol? x)                      ; VARIABLES
     (when (eq? 'fs (var-area x))
       (error 'elab "use of ungrounded variable ~a" x))
     (values (inferred (var-type x))
             (set x)
             (λ (env) (hash (hash) (hash-ref env x))))]

    [`(,(or 'lambda 'λ) (,(? symbol? param)) ,body) ; LAMBDAS
     (match (cannot-infer "lambda")
       [`(=> ,A ,P)
        (define-values (body-type body-uses body-deno)
          (elab body P (hash-set cx param (list 'fs A))))
        (unless (set-member? body-uses param)
          (error 'elab "ungrounded lambda parameter: ~a" param))
        (values
         `(=> ,A ,body-type)
         (set-remove body-uses param)
         (λ (env)
           (define temp (make-hash))
           (for ([(row value) (body-deno env)])
             (define outer-row (todo))
             (define inner-key (hash-ref row param))
             (hash-update! temp outer-row
                           (λ (inner-map) (todo))
                           (λ () (hash)))
             )
           (todo)
           ))]

       [`(-o ,P ,Q)
        (define fs-vars
          (for/list ([(x xinfo) cx] #:when (eq? 'fs (get-area xinfo)))
            x))
        (unless (null? fs-vars)
          (error 'elab "cannot close over these fs vars in pointed lambda: ~a"
                 fs-vars))
        (define-values (body-type body-uses body-deno)
          (elab body P (hash-set cx param (list 'point P))))
        (unless (set-member? body-uses param)
          (error 'elab "lambda does not preserve nil in parameter: ~a" param))
        (values `(-o ,P ,body-type)
                (set-remove body-uses param)
                (λ (env) (todo)))]

       [`(-> ,A ,B) (todo)]
       [_ (error 'elab "bad type for lambda: ~a" want)])]

    [`(app ,fun ,arg)                       ; FUNCTION APPLICATION
     (define-values (fun-type fun-uses fun-deno) (elab fun #f cx))
     (match fun-type

       [`(=> ,A ,P)                     ; FINITE MAP APPLICATION
        (unless (symbol? arg)
          ;; TODO LATER: weaken this restriction to allow patterns.
          (error 'elab "can only apply finite maps to variables"))
        (define arg-area (var-area arg))
        (define arg-type (var-type arg))
        #;
        (unless (eq? 'fs arg-area)
          ;; TODO FIXME: this invalidates the idea that it's always legitimate
          ;; to "promote" a fs var to a set var that justifies my approach to
          ;; tensor products.
          ;;
          ;; THIS ALSO NEEDS FIXING IN THE TYPING RULES!
          ;; (ALSO IN THE DENOTATIONS!
          (error 'elab "cannot only apply finite map to a f.s. variable"))
        ;; TODO: which direction should the subtyping relationship go???
        (unless (equal? A arg-type)
          (error 'elab "applying finite map (~a => ~a) to invalid input (~a)"
                 A P arg-type))
        (values
         P
         (match arg-area
           ['point fun-uses]          ; finite map lookup does not preserve nil.
           [_ (set-add fun-uses arg)])
         (λ (env)
           (define fun-map (fun-deno env))
           (define execution-strategy
             (if (and (eq? 'fs arg-area) (not (set-member? fun-uses arg)))
                 'support
                 'lookup))
           ;; TODO: tests that exercise all three arms of this match!
           (match arg-area
             ['fs #:when (set-member? fun-uses arg) ; NOT YET COVERED
              (for/hash ([(row table) fun-map])
                (values row (hash-ref table (hash-ref row arg))))]
             ['fs                       ; covered by a test
              (for*/hash ([(row table) fun-map]
                          [(key value) table])
                (when (hash-has-key? row arg) (error 'elab "fuck"))
                (values (hash-set row arg key) value))]
             [(or 'set 'point)          ;NOT YET COVERED
              (define key (hash-ref env arg))
              (for/hash ([(row table) fun-map]
                         #:when (hash-has-key? table key))
                (values row (hash-ref table key)))]))
         )]

       [`(-o ,P ,Q)                     ; POINTED MAP APPLICATION
        ;; take all fs vars used by `fun` and make them set vars for `arg`
        (define arg-cx
          (for/hash ([(x xinfo) cx])
            (values x (match xinfo
                        [`(fs ,xtype) #:when (set-member? fun-uses x)
                         `(set ,xtype)]
                        [_ xinfo]))))
        (define-values (_arg-type arg-uses arg-deno)
          (elab arg P arg-cx))
        (values Q
                (set-union fun-uses arg-uses)
                ;; TODO: TEST THIS CODE EXTENSIVELY
                (λ (env)
                  (define fun-map (fun-deno env))
                  ;; any fs vars grounded by fun get bound in arg's environment.
                  (for*/hash
                      ([(row1 fun-val) (fun-deno env)]
                       ;; is it really as simple as a hash-union?
                       #:do [(define arg-env (hash-union env row1))]
                       [(row2 arg-val) (arg-deno arg-env)])
                    (values
                     (hash-union row1 row2)
                     (fun-val arg-val)))))]

       [`(-> ,A ,B) (todo)]             ; SET FUNCTION APPLICATION
       [_ (error 'elab "cannot apply non-function of type: ~a" fun-type)])]

    ;; Any other list with two or more elements gets elaborated into function
    ;; application, nested/curried as necessary.
    [(and fun-app (list* _ _))
     (define curried-term
       (for/fold ([fun (car fun-app)])
                 ([arg (cdr fun-app)])
         `(app ,fun ,arg)))
     (elab curried-term want cx)]

    ))


(module+ test
  (require rackunit)

  (define (test-elab term want vartypes
                     #:type [expect-type #f]
                     #:uses [expect-uses #f]
                     #:eval [eval-env #f]
                     #:to   [expect-eval any/c])
    (define cx (for/hash ([vartype vartypes])
                 (match-define (list var area type) vartype)
                 (values var (list area type))))
    (define-values (term-type term-uses term-deno)
      (elab term want cx))
    ;; The used variables should be a subset of all variables.
    (check subset? term-uses (list->set (hash-keys cx)))
    ;; The inferred type should be a subtype of the `want' type.
    (when want
     (check subtype? term-type want))
    ;; The inferred type should equal the expected type.
    (when expect-type
      (check-equal? term-type expect-type))
    ;; The used variables should equal the expected used variables.
    (when expect-uses
     (check-equal? term-uses (list->set expect-uses)))
    ;; evaluate if requested
    (when eval-env
      (define term-map (term-deno eval-env))
      (if (procedure? expect-eval)
          (check-pred expect-eval term-map)
          (check-equal? term-map expect-eval)
          )))

  (test-elab 'x #f '([x point bool])
             #:type 'bool #:uses '(x)
             #:eval (hash 'x #t) #:to (hash (hash) #t))

  (test-elab '(f x) #f '([f point (-o bool bool)]
                         [x point bool])
             #:type 'bool #:uses '(f x)
             #:eval (hash 'f (λ (x) x) 'x #t) #:to (hash (hash) #t)
             )

  (test-elab '(f x) #f '([f set (=> nat bool)]
                         [x fs nat])
             #:type 'bool
             #:uses '(f x)
             #:eval (hash 'f (hash 17 #t 23 #t))
             #:to (hash (hash 'x 23) #t (hash 'x 17) #t)
             )

  (test-elab '(f x) #f '([f set (=> nat bool)]
                         [x set nat])
             #:type 'bool
             #:uses '(f x)
             #:eval (hash 'f (hash 17 #t 23 #t) 'x 17)
             #:to (hash (hash) #t)
             )

  (test-elab 'nil 'bool '([x fs bool] [y point bool])
             #:type 'bool #:uses '(x y)
             #:eval (hash 'y #t) #:to (hash))

  (test-elab 'x #f '([x point bool] [y point bool] [z fs bool])
             #:type 'bool #:uses '(x)
             #:eval (hash 'x #f 'y #t) #:to (hash (hash) #f))

  (test-elab '(f nil)
             #f
             '([f point (-o bool bool)] [x point bool])
             #:type 'bool #:uses '(f x)
             #:eval (hash 'f (λ (x) x) 'x #t) #:to (hash))

  (test-elab '((is (-o bool bool) nil) x)
             #f
             '([x point bool])
             #:type 'bool #:uses '(x)
             #:eval (hash 'x #t) #:to (hash))

  (test-elab '(λ (x) nil)
             '(=> nat bool)
             '()
             #:type '(=> nat bool)
             ;; #:eval (hash)              ;; TODO: enable
             )

  (test-elab '(λ (x) x)
             '(-o bool bool)
             '()
             #:type '(-o bool bool)
             ;; #:eval (hash)              ;; TODO: enable
             )

  (test-elab '(λ (x) (λ (y) (x y)))
             '(-o (-o bool bool) (-o bool bool))
             '()
             ;; #:eval (hash)              ;; TODO: enable
             )

  ;; multi-argument/curried application desugaring
  (test-elab '(f x x)
             'bool
             '([f point (-o bool (-o bool bool))]
               [x point bool])
             #:uses '(f x)
             #:eval (hash 'f (λ (x) (λ (y) (and x y))) 'x #t)
             #:to (hash (hash) #t))

  (test-elab '(f x x) #f '([f set (=> nat (=> nat nat))]
                           [x set nat])
             #:type 'nat
             #:uses '(f x)
             #:eval (hash 'x 23
                          'f (hash 17 (hash 17 1717 23 1723)
                                   23 (hash 23 2323 17 2317)))
             #:to (hash (hash) 2323))

  (test-elab '(f x y) #f '([f set (=> nat (=> nat bool))]
                           [x fs nat]
                           [y fs nat])
             #:type 'bool
             #:uses '(f x y)
             #:eval (hash 'f (hash 17 (hash 17 1717 23 1723)
                                   23 (hash 23 2323 17 2317)))
             #:to (hash (hash 'x 17 'y 17) 1717
                        (hash 'x 17 'y 23) 1723
                        (hash 'x 23 'y 17) 2317
                        (hash 'x 23 'y 23) 2323))

  ;; AN ACTUAL RELATIONAL JOIN
  ;; (ok it's just set intersection BUT STILL!)
  (test-elab '(and (f x) (g x))
             #f
             '([and set (-o bool (-o bool bool))]
               [x fs nat]
               [f set (=> nat bool)]
               [g point (=> nat bool)]
               )
             #:type 'bool
             #:uses '(and f g x)
             #:eval (hash 'and (λ (x) (λ (y) (and x y)))
                          'f (hash 17 #t 23 #t)
                          'g (hash 23 #t 54 #t))
             #:to (hash (hash 'x 23) #t))

  #;
  (check-equal? #t #f)
  )
