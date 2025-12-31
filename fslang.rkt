#lang racket

;; CONNECTIVE TODOS:
;; - with-pairs and projection, so I can have boolean "or"
;; - finite map lambdas
;; - linear lambdas
;; - just/letjust
;;
;; OTHER TODOS:
;; - think about U. and context.
;; - implement 3-way grading (unused/ground/used) for fs vars
;; - use 3-way grading to implement joins instead of subquerying all the time

(require racket/hash)

(define-syntax-rule (todo)
  (error "todo"))

(define term? any/c)
(define type? any/c)
(define subtype? equal?)

;; Which kind of context: set (Γ) or pointed set (Δ) or finite support (Ω)
(define area? (or/c 'set 'point 'fs))
;; cx = a variable context (Γ/Δ/Ω in typing judgment):
;; maps variables to their area and type
(define cx? (hash/c symbol? (list/c area? type?)
                    #:immutable #t #:flat? #t))

;; variable usage analysis results:
;; a set of variables.
;; if a pointed set var is in here, it's nil-preserved.
;; if a finite support var is in here, it's finitely supported.
;; if a set var is NOT in here, it's unused.
(define usage? (set/c symbol?))

;;; semantic contracts
(define value? any/c)
(define env? (hash/c symbol? value? #:immutable #t #:flat? #t))
(define row? env?)
;; A term denotes a function from environments (maps from set or pointed vars to
;; values) to finite maps (represented by hash maps) from "rows" (maps from fs
;; vars to values) to their values.
(define deno/c (-> env? (hash/c row? value? #:immutable #t #:flat? #t)))

;; Typecheck/elaborate/interpret a term. Parameters:
;;   term   - The term to elaborate
;;   want   - The expected type; #f to try to infer it.
;;   cx     - The variable context (maps vars in scope to their area & type).
;;
;; Returned values:
;;   type   - The inferred type. A subtype of `want` if want ≠ #f.
;;   uses   - Set of vars used by the term. See usage?, above.
;;   deno   - The term's denotation. See deno/c, above.
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
       (error 'elab "wanted ~a, but annotated ~a" want anno))
     (elab t anno cx)]

    ['nil                               ; NIL
     (define point-fs-vars
       (for/set ([(x xinfo) cx]
                 #:when (match xinfo
                          [(list (or 'point 'fs) _) #t]
                          [_ #f]))
         x))
     (values (cannot-infer "nil") point-fs-vars (λ (_env) (hash)))]

    ;; TODO: should this be able to use set variables? they'll have types of the
    ;; wrong kind! how am I handling the adjunction / separation of syntax
    ;; classes anyway?
    [(? symbol? x)                      ; VARIABLES
     (match (var-area x)
       ['fs (error 'elab "use of ungrounded variable ~a" x)]
       [(or 'set 'point)
        (values (inferred (var-type x))
                (set x)
                (λ (env) (hash (hash) (hash-ref env x))))])]

    [`(,(or 'lambda 'λ) (,(? symbol? param)) ,body) ; LAMBDAS
     (match (cannot-infer "lambda")

       [`(=> ,A ,P)                     ; FINITE LAMBDA, TODO: TEST
        (define-values (body-type body-uses body-deno)
          (elab body P (hash-set cx param (list 'fs A))))
        (unless (set-member? body-uses param)
          (error 'elab "ungrounded lambda parameter: ~a" param))
        (values
         `(=> ,A ,body-type)
         (set-remove body-uses param)
         (λ (env)
           (define result (make-hash))
           (for ([(row value) (body-deno env)])
             (define key (hash-ref row param))
             (hash-update! result
                           (hash-remove row param)
                           (λ (map) (hash-set map key value))
                           (λ () (hash))))
           (hash-map/copy result values #:kind 'immutable)))]

       [`(-o ,P ,Q)                     ; POINTED LAMBDA
        (define fs-vars
          (for/list ([(x xinfo) cx] #:when (match xinfo [(list 'fs _) #t] [_ #f]))
            x))
        (unless (null? fs-vars)
          (error 'elab "cannot close over these fs vars in pointed lambda: ~a"
                 fs-vars))
        (define-values (body-type body-uses body-deno)
          (elab body Q (hash-set cx param (list 'point P))))
        (unless (set-member? body-uses param)
          (error 'elab "lambda does not preserve nil in parameter: ~a" param))
        (values `(-o ,P ,body-type)
                (set-remove body-uses param)
                (λ (env) (todo)))]

       [`(-> ,A ,B) (todo)]             ; SET LAMBDA
       [_ (error 'elab "bad type for lambda: ~a" want)])]

    [`(app ,fun ,arg)                       ; FUNCTION APPLICATION
     (define-values (fun-type fun-uses fun-deno) (elab fun #f cx))
     (match fun-type

       [`(=> ,A ,P)                     ; FINITE APPLICATION
        (unless (symbol? arg)
          ;; TODO LATER: weaken this restriction to allow patterns.
          (error 'elab "can only apply finite maps to variables"))
        (define arg-area (var-area arg))
        (define arg-type (var-type arg))
        #; ;; FIXED but need to update typing rules.
        (unless (eq? 'fs arg-area)
          ;; this invalidates the idea that it's always legitimate to "promote"
          ;; a fs var to a set var that justifies my approach to tensor
          ;; products.
          (error 'elab "cannot only apply finite map to a f.s. variable"))
        ;; TODO: which direction should the subtyping relationship go???
        ;; for now, requiring equality
        (unless (equal? A arg-type)
          (error 'elab "applying finite map (~a => ~a) to invalid input (~a)"
                 A P arg-type))
        (values
         P
         (match arg-area
           ['point fun-uses]          ; finite map lookup does not preserve nil.
           [(or 'set 'fs) (set-add fun-uses arg)])
         (λ (env)
           (define fun-map (fun-deno env))
           (match arg-area
             ['fs #:when (set-member? fun-uses arg)
              (for/hash ([(row table) fun-map])
                (values row (hash-ref table (hash-ref row arg))))]
             ['fs
              (for*/hash ([(row table) fun-map]
                          [(key value) table])
                (when (hash-has-key? row arg) (error 'elab "fuck"))
                (values (hash-set row arg key) value))]
             [(or 'set 'point)
              (define key (hash-ref env arg))
              (for/hash ([(row table) fun-map]
                         #:when (hash-has-key? table key))
                (values row (hash-ref table key)))]))
         )]

       [`(-o ,P ,Q)                     ; POINTED APPLICATION
        ;; take all fs vars used by `fun` and make them set vars for `arg`.
        (define arg-cx
          (for/hash ([(x xinfo) cx])
            (values x (match xinfo
                        [`(fs ,xtype) #:when (set-member? fun-uses x)
                         `(set ,xtype)]
                        [_ xinfo]))))
        (define-values (_arg-type arg-uses arg-deno)
          (elab arg P arg-cx))
        ;; TODO: THIS IS WRONG WRONG WRONG. we've told arg that it can use vars grounded
        ;; by fun arbitrarily, so it only records whether it USES them, not whether it
        ;; uses them (1) arbitrarily or (2) groundingly or (3) not at all. We need this in
        ;; order to figure out whether we execute as a join or a subquery.
        ;;
        ;; Variables grounded by fun that are used non-groundingly by arg, ie:
        ;; sideways information passing / subquery parameters.
        #;
        (define sideways-vars
          (for/list ([(x xinfo) cx]
                     #:when (match xinfo [`(fs ,_) #t] [_ #f])
                     #:when (set-member? fun-uses x)
                     #:when (set-member? arg-uses x))
             x))
        #; ;; THIS IS WRONG for the same reason given above.
        (if (null? sideways-vars)
          (printf "%%%%% JOIN ON ~a: ~a ====> ~a %%%%%\n"
                  (for/list ([(x xinfo) cx] #:when (match xinfo [`(fs ,_) #t] [_ #f])) x)
                  fun arg)
          (printf "***** SUBQUERY: ~a == ~a ==> ~a *****\n" fun sideways-vars arg))
        (values Q
                (set-union fun-uses arg-uses)
                ;; TODO: TEST THIS CODE EXTENSIVELY
                (λ (env)
                  ;; any fs vars grounded by fun get bound in arg's environment. TODO: if
                  ;; there's no real sideways info passing, so I can eval arg _once_ and
                  ;; then join (iterate smaller, probe larger) instead of subquerying.
                  (for*/hash ([(row1 fun-val) (fun-deno env)]
                              ;; is it really as simple as a hash-union?
                              #:do [(define arg-env (hash-union env row1))]
                              [(row2 arg-val) (arg-deno arg-env)])
                    (values
                     ;; NB. This hash-union is only guaranteed not to hit any colliding
                     ;; keys because we told `arg' that all of `fun's grounded variables
                     ;; were arbitrary, not fs, variables.
                     (hash-union row1 row2)
                     (fun-val arg-val)))))]

       [`(-> ,A ,B)                     ; SET APPLICATION
        ;; hide all pointed/fs arguments from the context
        (define arg-cx
          (for/hash ([(x xinfo) cx])
            (values x (match xinfo
                        [(list (or 'point 'fs) _) 'hidden] ;TODO: test this hiding!
                        [_ xinfo]))))
        (define-values (_arg-type arg-uses arg-deno) (elab arg A arg-cx))
        (values
         B                   ; TODO think about adjunction typing rule structure
         (set-union fun-uses arg-uses)
         (λ (env)
           (define fun-table (fun-deno env))
           (define arg-table (arg-deno env))
           ;; TODO FIXME: need to generate nil of the appropriate type in the
           ;; default case! but this shouldn't be possible. except it is because
           ;; U is silent. augh.
           (unless (= 1 (hash-count arg-table))
             (error 'elab "evaled to non-singleton: ~a" arg))
           (printf "fun ~a --> ~a\n" fun fun-table)
           (printf "arg ~a --> ~a\n" arg arg-table)
           (define arg-val (hash-ref arg-table (hash)))
           (define result
            (for/hash ([(row fun-val) fun-table])
              (values row (fun-val arg-val))))
           (printf "result => ~a\n" result)
           result
           )
         )]

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

  ;; TODO: typecheck failure tests for ILL-TYPED terms

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

  ;; Filtering a set. This was curiously harder to get working than set
  ;; intersection, below.
  (test-elab '(and (f x) (g x))
             #f
             '([and set (-o bool (-o bool bool))]
               [x fs nat]
               [f set (=> nat bool)]
               [g set (-> nat bool)]    ;is this even coherent I don't know
               )
             #:type 'bool
             #:uses '(and f g x)
             #:eval (hash 'and (λ (x) (λ (y) (and x y)))
                          'f (hash 17 #t 23 #t)
                          'g (λ (x) (< x 20)))
             ;; NB. the 23 doesn't get filtered out!
             ;; TODO: filter out nils if type has decidable point?
             #:to (hash (hash 'x 17) #t (hash 'x 23) #f)
             )

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
