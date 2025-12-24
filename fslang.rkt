#lang racket

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

(define (infer term [cx (hash)] #:want [want #f])
  (elab term want cx))

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
       [`(=> ,A ,P)
        (unless (symbol? arg)
          ;; TODO LATER: weaken this restriction to allow patterns.
          (error 'elab "can only apply finite maps to variables"))
        (unless (eq? 'fs (var-area arg))
          ;; TODO FIXME: this invalidates the idea that it's always legitimate
          ;; to "promote" a fs var to a set var that justifies my approach to
          ;; tensor products.
          ;;
          ;; THIS ALSO NEEDS FIXING IN THE TYPING RULES!
          ;; (ALSO IN THE DENOTATIONS!
          (error 'elab "cannot only apply finite map to a f.s. variable"))
        (define arg-type (var-type arg))
        ;; TODO: which direction should the subtyping relationship go???
        (unless (equal? A arg-type)
          (error 'elab "applying finite map (~a => ~a) to invalid input (~a)"
                 A P arg-type))
        (values
         P
         (set-add fun-uses arg)
         (λ (env)
           (define fun-map (fun-deno env))
           (for*/hash ([(row subtable) fun-map]
                       [(key value) subtable])
             ;; FIXME: what if `arg` is already in `row`???
             (when (hash-has-key? row arg)
               (error 'elab "shit I didn't handle this case"))
             (values (hash-set row arg key) value)))
         )]

       [`(-o ,P ,Q)
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
                (λ (env) (todo)))]

       [`(-> ,A ,B) (todo)]
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
                     #:uses [expect-uses #f])
    (define cx (for/hash ([vartype vartypes])
                 (match-define (list var area type) vartype)
                 (values var (list area type))))
    (define-values (term-type term-uses _)
      (elab term want cx))
    ;; The used variables should be a subset of all variables.
    (check subset? term-uses (list->set (hash-keys cx)))
    ;; The inferred type should be a subtype of the `want' type.
    (when want
     (check subtype? term-type want))
    ;; The inferred type should equal the expected type.
    (when expect-type
      (check-equal? expect-type term-type))
    ;; The used variables should equal the expected used variables.
    (when expect-uses
     (check-equal? (list->set expect-uses) term-uses)))

  (test-elab 'x #f '([x point bool])
             #:type 'bool #:uses '(x))

  (test-elab '(f x) #f '([f point (-o bool bool)]
                         [x point bool])
             #:type 'bool #:uses '(f x))

  (test-elab 'nil 'bool '([x fs bool] [y point bool])
             #:type 'bool #:uses '(x y))

  (test-elab 'x #f '([x point bool] [y point bool] [z fs bool])
             #:type 'bool #:uses '(x))

  (test-elab '(f nil)
             #f
             '([f point (-o bool bool)] [x point bool])
             #:type 'bool #:uses '(f x))

  (test-elab '((is (-o bool bool) nil) x)
             #f
             '([x point bool])
             #:type 'bool #:uses '(x))

  (test-elab '(λ (x) nil)
             '(=> nat bool)
             '()
             #:type '(=> nat bool))

  (test-elab '(λ (x) x)
             '(-o bool bool)
             '()
             #:type '(-o bool bool))

  (test-elab '(λ (x) (λ (y) (x y)))
             '(-o (-o bool bool) (-o bool bool))
             '())

  ;; multi-argument/curried application desugaring
  (test-elab '(f x x) 'bool '([f point (-o bool (-o bool bool))]
                              [x point bool]))

  #;
  (test-elab '(and (f x) (g x))
             #f
             '([and set (-o bool (-o bool bool))]
               [x fs nat]
               [f set (=> nat bool)]
               ;; this shouldn't type check! the argument to g is supposed to be
               ;; a pointed variable, but we're supplying a set variable.
               [g point (=> nat bool)]  ; TODO FAILS: can't yet apply a finite map to a non-fs var
               )
             #:type 'bool
             #:uses '(and f g x))

  #;
  (check-equal? #t #f)
  )

;; PROBLEM 1: what to do, dynamically, about the different ways information can
;; pass around in tensor introduction. pure relational joins vs sideways
;; information passing vs mixed. Ideally I'd use static information to decide
;; how to execute. But the most general strategy is just nested loops.
;;
;; Alternatively, I could let the user give me a variable order.
;; Then what does "exists" do to the var order, append or prepend?
;;
;; PROBLEM 2: when I see function application, how do I know whether it's
;; grounding a variable or looking it up?
;;
;; SOLUTION: I evaluate the LHS and check whether it's a finite map. if so, and
;; if argument is variable, I check whether it's bound; if so, lookup;
;; otherwise, ground. otherwise it better be ground.
;;
;; PROBLEM: how do I propagate variable bindings created by application.
;; SOLUTION: evaluation ALWAYS produces a finite map and I need to combine these.
;;
;; PROBLEM: do I produce new maps or extend an existing map?
#;
(define (eval term [env (hash)] [known (hash)])
  (match term
    ['nil (hash)]
    [(? symbol? x)
     (hash known (hash-ref (if (hash-has-key? known x) known env) x))]
    [`(just ,e) (todo)]
    [`(letjust ,(? symbol? x) ,t ,u)
     (todo)]
    [`(,t ,u)
     (for*/hash ([(fknown f) (eval t env known)]
                 ;; TODO: what if f is finite map and x is a variable?
                 [(uknown x) (eval u env fknown)])
       ;; FIXME: what about the many different kinds of function application?
       (values uknown (f x)))]
    ))
