#lang racket

;; WHAT DO I NEED TO MAKE THIS INTO A USEFUL DEMO?
;;
;; 1 good error messages about variable usage & grounding!
;; 2 non-S-expr syntax?
;; 3 ⊗-tuples
;; 4 support for auto-&-tupling of (infix?) function arguments
;; 5 a repl?
;; 6 a website w/ JS implementation? (NOT NECESSARY, BUT SUPER COOL IF POSSIBLE)
;;
;; what programs do I want to use? perhaps:
;;
;; costars x y = exists(\film. stars film x && stars film y)
;; filmCount x = sum (\film. 1 when stars film x)
;;
;; IDEA: use Topos talk examples.
;; IDEA: use Will Crichton's query language expressiveness benchmark.


;; # HOW TO GET GOOD ERROR MESSAGES #
;; - print the expression that binds the variable
;; - point to the location of use? (ugh, hard! need annotations?)
;; - say what the problem is. what kinds of problems can I have?
;;
;; # VARIABLE USAGE ERROR TYPES #
;; "use of ungrounded variable"
;; "lambda does not preserve nil in parameter"
;; "unbound variable" (currently hash-ref fails)
;; "hidden variable" - when applying set function to pointed var (now: contract failure)
;;
;; why do I have both "lambda does not preserve nil in parameter" and "hidden
;; variable"? in some sense they're the same problem. aha, currently:
;; - "does not preserve nil in parameter" = variable not used
;; - hidden = used as argument to -> function.
;;   (But this is kinda okay, as long as some other path uses it nil-preservingly?)
;;
;; Ideally I'd collect all the uses of a variable and know which uses are
;; point-preserving; for those not point preserving, I'd be able to say which
;; function application was not point preserving. So I'd be able to point to a
;; "usage path" that fails to nil-preserve the variable.

;; CONNECTIVE TODOS:
;; - just/letjust
;; - ⊗intro/elim
;;
;; OTHER TODOS:
;; - think about U and context.
;; - implement 3-way grading (unused/ground/used) for fs vars
;; - use 3-way grading to implement joins instead of subquerying all the time
;; - pattern matching?

(require racket/hash)

;; NB. Racket 'min coerces the result to inexact if any argument is - but +inf.0
;; is inexact. Hence these functions.
(define natinf? (or/c exact-nonnegative-integer? +inf.0))
(define/contract (exact-min x y)
  (-> natinf? natinf? natinf?)
  (cond [(eqv? +inf.0 x) y]
        [(eqv? +inf.0 y) x]
        [#t (min x y)]))

(define-syntax-rule (todo)
  (error "todo"))

(define term? any/c)
(define type?
  (flat-rec-contract type?
    symbol?                             ; base types
    (list/c '-o type? type?)
    (list/c '=> type? type?)
    (list/c '-> type? type?)
    (cons/c '&  (listof type?))
    ;; TODO: ⊗-tuples, maybe
    ))

(define subtype? equal?)

;; First-order types: those that support equality, i.e. contain no function types.
(define/contract (first-order? t)
  (-> type? boolean?)
  (match t
    [(? symbol?) #t]
    [`(& ,@types) (andmap first-order? types)]
    ;; TODO: ⊗-tuples, maybe
    [_ #f]))

;; Which kind of context: set (Γ) or pointed set (Δ) or finite support (Ω)
(define area? (or/c 'set 'point 'fs))
;; cx = a variable context (Γ/Δ/Ω in typing judgment):
;; maps variables to their area and type
(define cx? (hash/c symbol? (list/c area? type?)
                    #:immutable #t #:flat? #t))
(define get-area first)
(define get-type second)
(define (cx-area cx var) (get-area (hash-ref cx var)))
(define (cx-type cx var) (get-type (hash-ref cx var)))

;; variable usage analysis results:
;; a set of variables.
;; if a pointed set var is in here, it's nil-preserved.
;; if a finite support var is in here, it's finitely supported.
;; if a set var is NOT in here, it's unused - no need to put it in the environment at runtime.
(define usage? (set/c symbol?))

;;; semantic contracts
(define value? any/c)
(define env? (hash/c symbol? value? #:immutable #t #:flat? #t))
(define row? env?)
;; A term denotes a function from environments (maps from set or pointed vars to
;; values) to finite maps (represented by hash maps) from "rows" (maps from fs
;; vars to values) to their values.
(define deno-map? (hash/c row? value? #:immutable #t #:flat? #t))
(define deno/c (-> env? deno-map?))

(define/contract (make-nil type)
  (-> type? value?)
  (match type
    ['bool #f]
    ['natz 0]
    ['natinf +inf.0]
    [(? symbol? x) (error "do not know how to make nil for type: ~a" x)]
    [`(& ,@types) (for/list ([t types]) (make-nil t))]
    [`(-o ,_ ,b) (const (make-nil b))]
    [`(-> ,_ ,b) (const (make-nil b))]
    [`(=> ,_ ,_) (hash)]))


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

  (define (var-area x) (cx-area cx x))
  (define (var-type x) (cx-type cx x))

  (define (cannot-infer name)
    (unless want (error 'elab "cannot infer type of ~a" name))
    want)

  (define (inferred got)
    (cond
      [(not want) got]
      [(subtype? got want) got]
      [else (error 'elab "wanted ~a, but inferred ~a" want got)]))

  ;; left-to-right grounding: turn finitely supported variables that are
  ;; supported by `uses` into set variables.
  (define (cx-grounding cx uses)
    (for/hash ([(x xinfo) cx])
      (values x (match xinfo
                  [`(fs ,xtype) #:when (set-member? uses x) `(set ,xtype)]
                  [_ xinfo]))))

  ;; hide pointed/fs variables — used for arguments to set functions.
  (define (cx-hide cx)
    (for/hash ([(x xinfo) cx])
      (values x (match xinfo
                  [(list (or 'point 'fs) _) 'hidden]
                  [_ xinfo]))))

  ;; SET APPLICATION
  (define (elab-set-app A B fun-uses fun-deno arg)
    ;; we treat this like (-o (maybe A) B) and implicitly wrap the argument
    ;; in "just", hiding all pointed/fs variables from its context.
    (define-values (_arg-type arg-uses arg-deno) (elab arg A (cx-hide cx)))
    (values
     B                   ; TODO think about adjunction typing rule structure
     (set-union fun-uses arg-uses)
     (λ (env)
       (define fun-table (fun-deno env))
       (define arg-table (arg-deno env))
       ;; TODO FIXME: need to generate nil of the appropriate type in the
       ;; default case! but this shouldn't be possible. except it is because
       ;; U is silent. augh.
       (unless (= 1 (hash-count arg-table)) ; TODO: trip this case in a test!
         (error 'elab "evaled to non-singleton: ~a" arg))
       ;; (printf "fun ~a --> ~a\n" fun fun-table) (printf "arg ~a --> ~a\n" arg arg-table)
       (define arg-val (hash-ref arg-table (hash)))
       (define result
        (for/hash ([(row fun-val) fun-table])
          (values row (fun-val arg-val))))
       ;; (printf "result => ~a\n" result)
       result)))

  ;; POINTED APPLICATION
  (define (elab-pointed-app P Q fun-uses fun-deno arg)
    ;; take all fs vars used by `fun` and make them set vars for `arg`.
    (define-values (_arg-type arg-uses arg-deno) (elab arg P (cx-grounding cx fun-uses)))
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
                 (fun-val arg-val))))))

  #;
  (define ((tensor-combiner combine a-deno b-deno) env)
    (for*/hash ([(a-row a-val) (a-deno env)]
                [(b-row b-val) (b-deno (hash-union env a-row))])
      (values (hash-union a-row b-row) (combine a-val b-val))))

  ;; FINITE APPLICATION
  (define (elab-finite-app A P fun-uses fun-deno arg)
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
      (error 'elab "applying finite map to input of wrong type\n  map: (=> ~a ~a)\n  arg: ~a"
             A P arg-type))
    (values
     P
     (match arg-area
       ['point fun-uses] ; finite map lookup does not preserve nil wrt the argument.
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
            (values row (hash-ref table key)))]))))

  ;; FS BINDERS (eg finite lambda, aggregations): handles forms that bind fs
  ;; vars. Arguments:
  ;;
  ;;   name    The operator name (for error messages)
  ;;   zero    The initial group accumulator value, or a thunk returning it.
  ;;           For finite lambdas, this is an empty hash.
  ;;           For aggregations, this is the initial value (eg 0 for sum).
  ;;   adjoin  A function (adjoin accum key value) that extends a group accumulator
  ;;           with a key-value mapping. For finite lambdas, extends the hash.
  ;;           For aggregations, combines accum & value.
  ;;   A       The type of the bound fs var
  ;;   P       The expected body type (may be #f to infer).
  ;;
  ;; NB. Returns (values type uses deno) as usual, but type is always the type
  ;; of body, which is correct for aggregation but wrong for finite lambda.
  (define (elab-fs-binder name zero adjoin A P param body)
    (define-values (body-type body-uses body-deno)
      (elab body P (hash-set cx param `(fs ,A))))
    (unless (set-member? body-uses param)
      (error 'elab "ungrounded parameter in ~a: ~a" name param))
    (values
     body-type ;; NB. caller may need to adjust this!
     (set-remove body-uses param)
     ;; We're going from a flat table [(other-fs-vars..., param) ↦ value, ...]
     ;; to a grouped one,             [(other-fs-vars...) ↦ combine(param ↦ value, ...), ...]
     ;; the combining operation is determined by the operator:
     ;; for finite lambdas, we make a hash table of the (param ↦ value) mappings.
     ;; for aggregations, we aggregate the values and throw away the parameter values.
     (λ (env)
       (define result (make-hash))
       (for ([(row value) (body-deno env)])
         (define key (hash-ref row param))
         (hash-update! result
                       (hash-remove row param)
                       (λ (group) (adjoin group key value))
                       zero))
       (hash-map/copy result values #:kind 'immutable))))

  ;; AGGREGATION: handles aggregation binding forms, (op (var var-type) body),
  ;; which are semantically ((A => P) -o P). zero, plus should be the identity
  ;; and binary operator for the aggregation respectively.
  (define (elab-aggregation name P zero plus var var-type body)
    (unless (type? var-type)
      (error 'elab "~a parameter type is not a valid type: ~a" name var-type))
    (elab-fs-binder name zero (λ (accum k v) (plus accum v)) var-type P var body))

  (match term
    [`(as ,hideaki ,t)                     ; TYPE ANNOTATION
     (unless (type? hideaki)
       (error 'elab "type annotation is not a valid type: ~a" hideaki))
     (when (and want (not (subtype? hideaki want)))
       (error 'elab "wanted ~a, but annotated ~a" want hideaki))
     (elab t hideaki cx)]

    ;; CONSTANTS
    [(? boolean? x)
     (if (not x) (elab 'nil 'bool cx)
         (values 'bool (set) (λ (_) (hash (hash) #t))))]

    [(? exact-nonnegative-integer? n)
     (unless (member want '(nat natz natinf))
       (error 'elab "number literal needs type nat, natz, or natinf; got: ~a" want))
     (values want (set) (λ (_) (hash (hash) n)))]

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

    [`(cons ,@terms)                    ; WITH TUPLES (&)
     (define wants
       (match want
         [#f (make-list (length terms) #f)]
         [`(& ,@types)
          (unless (= (length types) (length terms)) (error "tuple of wrong length"))
          types]
         [_ (error 'elab "tuple cannot have type ~a" want)]))
     (define-values (types uses denos)
      (for/lists (_types _uses _denos)
                 ([t terms] [a wants])
        (elab t a cx)))
     ;; Usage for with-pairs is complicated:
     ;;
     ;; 1. We use set variables used by ANY term = union (because we may depend
     ;; on them at runtime).
     ;;
     ;; 2. We point-preserve anything point-preserved by ALL terms = intersection.
     ;;
     ;; 3. In theory, we finitely support anything supported by ALL terms =
     ;; intersection. However, what do we do with fs vars used by SOME but not
     ;; ALL terms? We still need them but we do not ground them. Presently we
     ;; don't have a way of reporting this via usage.
     ;;
     ;; Moreover, it raises a semantic issue: what is the denotation of such a
     ;; term? We might treat the unsupported fs vars as ordinary cartesian
     ;; arguments. But since (A -> B => P) ≇ (B => A -> P), this opens the
     ;; question of whether they go before or after the fs var arguments.
     ;;
     ;; Anyway, for now we require that the supported (used) fs vars be exactly
     ;; the same between all terms.
     (define used
       (for/set ([(x xinfo) cx]
                 ;; TODO: this could be more efficient.
                 #:when (match (get-area xinfo)
                          [(or 'point 'fs) (for/and ([u uses]) (set-member? u x))]
                          ['set (for/or ([u uses]) (set-member? u x))]))
         x))
     ;; check all fs vars used by any term are supported by whole expr
     (for* ([term-use uses] [x term-use] #:when (eq? 'fs (var-area x)))
       (unless (set-member? used x)
         (error 'elab "variable ~a is ground by some but not all with-pair components" x)))
     (values
      `(& ,@types)
      used
      (λ (env)
        (define maps (for/list ([d denos]) (d env)))
        (for/hash ([row (apply set-union (set) (map (compose list->set hash-keys) maps))])
          (values row
                  (for/list ([tp types] [m maps])
                    ;; TODO: When one subterm is missing a row the others have,
                    ;; I need to generate nil for that component.
                    (hash-ref m row (λ () (make-nil tp))))))))]

    [`(,(or 'lambda 'λ) (,(? symbol? param)) ,body) ; LAMBDAS
     (match (cannot-infer "lambda")

       [`(=> ,A ,P)                     ; FINITE LAMBDA
        (define-values (body-type uses deno)
          (elab-fs-binder 'lambda hash hash-set A P param body))
        (values `(=> ,A ,body-type) uses deno)]

       [`(-o ,P ,Q)                     ; POINTED LAMBDA; TODO: implement & test evaluation
        (define fs-vars
          (for/list ([(x xinfo) cx] #:when (match xinfo [(list 'fs _) #t] [_ #f]))
            x))
        ;; TODO: do I really need to ensure that cx has no fs-vars, or can I
        ;; just make sure that body doesn't close over any of them and report
        ;; that we use (ie support) none of them?
        ;;
        ;; find an example use-case. think about typing rules/semantics.
        (unless (null? fs-vars)
          (error 'elab "cannot close over these fs vars in pointed lambda: ~a"
                 fs-vars))
        (define-values (body-type body-uses body-deno)
          (elab body Q (hash-set cx param (list 'point P))))
        (unless (set-member? body-uses param)
          (error 'elab "lambda does not preserve nil in parameter: ~a" param))
        (values `(-o ,P ,body-type)
                (set-remove body-uses param)
                (λ (env)
                  (hash (hash)
                        (λ (x)
                          (hash-ref (body-deno (hash-set env param x))
                                    (hash))))))]

       [`(-> ,A ,B) (todo)]             ; SET LAMBDA

       [_ (error 'elab "bad type for lambda: ~a" want)])]

    ;; POLYMORPHIC/PARAMETRIC OPERATOR special cases:
    ;; equality, when, exists, sum, minimum
    [`(= ,a ,b)                         ; EQUALITY
     ;; `a` is a set argument: hide pointed/fs vars like elab-set-app does.
     (define-values (a-type a-uses a-deno) (elab a #f (cx-hide cx)))
     (unless (first-order? a-type)
       (error 'elab "equality is only supported at first-order types; got: ~a" a-type))
     (define (eq-a-deno env)
       (define a-table (a-deno env))
       (for/hash ([(k a-val) a-table]) (values k (hash a-val #t))))
     (elab-finite-app a-type (inferred 'bool) a-uses eq-a-deno b)]

    [`(when ,a ,b)
     (define-values (a-type a-uses a-deno) (elab a 'bool cx))
     (define-values (b-type b-uses b-deno) (elab b want (cx-grounding cx a-uses)))
     (values b-type
             (set-union a-uses b-uses)
             (λ (env)
               ;; this replicates logic from pointed application, slightly optimized.
               (for*/hash ([(a-row a-val) (a-deno env)]
                           #:when a-val
                           [(b-row b-val) (b-deno (hash-union env a-row))])
                 (values (hash-union a-row b-row) b-val))))]

    ;; AGGREGATIONS
    [`(exists (,(? symbol? var) ,var-type) ,body)
     (elab-aggregation 'exists 'bool #f (λ (x y) (or x y)) var var-type body)]
    [`(sum (,(? symbol? var) ,var-type) ,body)
     (elab-aggregation 'sum 'natz 0 + var var-type body)]
    [`(minimum (,(? symbol? var) ,var-type) ,body)
     (elab-aggregation 'minimum 'natinf +inf.0 exact-min var var-type body)]
    [`(maximum (,(? symbol? var) ,var-type) ,body)
     (elab-aggregation 'maximum 'natz 0 max var var-type body)]

    [`(app ,fun ,arg)                       ; FUNCTION APPLICATION
     (define-values (fun-type fun-uses fun-deno) (elab fun #f cx))
     (match fun-type
       [`(=> ,A ,P) (elab-finite-app A (inferred P) fun-uses fun-deno arg)]
       [`(-o ,P ,Q) (elab-pointed-app P (inferred Q) fun-uses fun-deno arg)]
       [`(-> ,A ,B) (elab-set-app A (inferred B) fun-uses fun-deno arg)]
       [_ (error 'elab "cannot apply non-function of type: ~a" fun-type)])]

    ;; SUGAR: "or" expressions get elaborated into calling "or" on with-pairs.
    [`(or)            (elab 'nil (inferred 'bool) cx)]
    [`(or ,x)         (elab x    (inferred 'bool) cx)]
    [`(or ,x ,y ,@ys) (elab `(or (app or (cons ,x ,y)) ,@ys) want cx)]

    ;; SUGAR: Any other list with two or more elements gets elaborated into
    ;; function application, nested/curried as necessary.
    [(and fun-app (list* _ _))
     (define curried-term
       (for/fold ([fun (car fun-app)])
                 ([arg (cdr fun-app)])
         `(app ,fun ,arg)))
     (elab curried-term want cx)]

    ))


;;; Read eval print loop. WIP.

;; TODO: I *really* need parametric operators to make working at the repl
;; tolerable. maybe hardcode a few of them in?
;; NEED PARAMETRIC: equality, and, when, exists, sum
(define default-repl-env-list
  `([and    (-o bool (-o bool bool))   ,(λ (x) (λ (y) (and x y)))]
    [when   (-o bool (-o any any))     ,(λ (x) (λ (y) (and x y)))]
    [or     (-o (& bool bool) bool)    ,(match-λ [`(,x ,y) (or x y)])]
    [exists (-o (=> any bool) bool)    ,(λ (table) (for/or ([(_ v) table]) v))]
    [sum    (-o (=> any natz) natz)    ,(λ (table) (for/sum ([(_ v) table]) v))]
    ))

(define repl-env? (hash/c symbol? (list/c type? value?) #:flat? #t))
(define/contract default-repl-env repl-env?
  (for/hash ([x default-repl-env-list])
    (match-define `(,name ,type ,value) x)
    (values name (list type value))))

(define/contract (evaluate term [repl-env default-repl-env])
  (-> term? repl-env? value?)           ;TODO: allow optional argument!
  (define cx  (for/hash ([(x info) repl-env]) (values x (list 'set (first info)))))
  (define env (for/hash ([(x info) repl-env]) (values x (second info))))
  (define-values (type used deno) (elab term #f cx))
  (printf "term: ~a\n" term)
  (printf "type: ~a\n" type)
  (printf "uses: ~a\n" (set->list used))
  #;
  (for ([(x xinfo) cx])
    (match (get-area xinfo)
      ['fs #:when (not (set-member? used x))
       (error 'repl "Variable not finitely supported: ~a" x)]
      ['point #:when (not (set-member? used x))
       (error 'repl "Variable not used in a point preserving way: ~a" x)]
      [(or 'set 'point)
       #:when (and (set-member? used x)
                   (not (hash-has-key? env x)))
       (error 'repl "Runtime environment missing variable: ~a" x)]
      [_ (void)]))                      ;otherwise ok.
  (define term-map (deno env))
  (define value (hash-ref term-map (hash) (λ () (make-nil type))))
  value)

;; Process one repl form. (def NAME TYPE EXPR) extends repl-env with a new
;; set-area binding; any other form is evaluated and its value printed.
;; Returns the (possibly extended) repl-env.
(define/contract (repl-step form repl-env)
  (-> term? repl-env? repl-env?)
  (match form
    [`(def ,(? symbol? name) ,type ,expr)
     (unless (type? type)
       (error 'repl "not a valid type in (def ~a ...): ~a" name type))
     (define cx  (for/hash ([(x info) repl-env]) (values x (list 'set (first info)))))
     (define env (for/hash ([(x info) repl-env]) (values x (second info))))
     (define-values (got-type _uses deno) (elab expr type cx))
     (define value (hash-ref (deno env) (hash) (λ () (make-nil got-type))))
     (printf "~a : ~a\n" name got-type)
     (hash-set repl-env name (list got-type value))]
    [_
     ;; TODO: decent pretty printing.
     (printf "~a\n" (evaluate form repl-env))
     repl-env]))

;; Interactive read-eval-print loop. Exits on EOF or `:q`.
(define (repl [repl-env default-repl-env])
  (printf "fslang repl. type :q or ctrl-D to quit.\n")
  (let loop ([repl-env repl-env])
    (printf "> ")
    (flush-output)
    (define form (read))
    (cond
      [(eof-object? form) (newline)]
      [(eq? form ':q) (void)]
      [else
       (define next-env
         (with-handlers ([exn:fail?
                          (λ (e)
                            (printf "error: ~a\n" (exn-message e))
                            repl-env)])
           (repl-step form repl-env)))
       (loop next-env)])))

(module+ main (repl))


;; TODO: more failure tests for ill-typed terms.
;; TODO: test variable hiding in set-function application.
(module+ test
  (require rackunit)

  (define stdlib
    (hash
     'and    (λ (x) (λ (y) (and x y)))
     'or     (match-λ [`(,x ,y) (or x y)])
     ;; NB. these are redundant with the built-in parametric versions in elab.
     ;; I should probably remove these and the tests for them at some point.
     'when   (λ (x) (λ (y) (and x y)))
     'exists (λ (table) (for/or ([(_ v) table]) v))
     'sum    (λ (table) (for/sum ([(_ v) table]) v))
     ))

  (define check-subtype?
    (if (eq? subtype? equal?) check-equal?
        (curry check subtype?)))

  (define expect-val-default (gensym 'expect-val-default))
  (define (test-elab term want vartypes
                     #:name   [name #f]
                     #:fail   [exn-predicate #f]
                     #:type   [expect-type #f]
                     #:uses   [expect-uses #f]
                     #:eval   [eval-env #f]
                     #:to-map [expect-map any/c]
                     #:to     [expect-val expect-val-default])
    (test-case (or name (format "~a" term))
      (let/ec exit-early
        (define cx (for/hash ([vartype vartypes])
                     (match-define (list var area type) vartype)
                     (values var (list area type))))
        (define-values (term-type term-uses term-deno)
          (if exn-predicate
              (exit-early (check-exn exn-predicate (λ () (elab term want cx))))
              (elab term want cx)))
        ;; The used variables should be a subset of all variables.
        (check subset? term-uses (list->set (hash-keys cx)))
        ;; The inferred type should be a subtype of the `want' type.
        (when want
          (check-subtype? term-type want))
        ;; The inferred type should equal the expected type.
        (when expect-type
          (check-equal? term-type expect-type))
        ;; The used variables should equal the expected used variables.
        (when expect-uses
          (check-equal? term-uses (list->set expect-uses)))
        ;; evaluate if requested
        (when eval-env
          (define term-map (term-deno eval-env))
          (if (procedure? expect-map)
              (check-pred expect-map term-map)
              (check-equal? term-map expect-map))
          (unless (eq? expect-val expect-val-default)
            (define term-val
              (if (hash-empty? term-map)
                  (make-nil term-type)
                  (hash-ref term-map (hash))))
            (if (procedure? expect-val)
                (check-pred expect-val term-val)
                (check-equal? term-val expect-val)))))))

  (test-elab 'x #f '([x point bool])
             #:type 'bool #:uses '(x)
             #:eval (hash 'x #t) #:to #t)

  (test-elab '(f x) #f '([f point (-o bool bool)]
                         [x point bool])
             #:type 'bool #:uses '(f x)
             #:eval (hash 'f (λ (x) x) 'x #t) #:to #t)

  (test-elab '(f x) #f '([f set (=> nat bool)]
                         [x fs nat])
             #:type 'bool
             #:uses '(f x)
             #:eval (hash 'f (hash 17 #t 23 #t))
             #:to-map (hash (hash 'x 23) #t (hash 'x 17) #t))

  (test-elab '(f x) #f '([f set (=> nat bool)]
                         [x set nat])
             #:type 'bool
             #:uses '(f x)
             #:eval (hash 'f (hash 17 #t 23 #t) 'x 17)
             #:to #t)

  (test-elab 'nil 'bool '([x fs bool] [y point bool])
             #:type 'bool #:uses '(x y)
             #:eval (hash 'y #t) #:to-map (hash))

  (test-elab 'x #f '([x point bool] [y point bool] [z fs bool])
             #:type 'bool #:uses '(x)
             #:eval (hash 'x #f 'y #t) #:to-map (hash (hash) #f))

  (test-elab '(f nil)
             #f
             '([f point (-o bool bool)] [x point bool])
             #:type 'bool #:uses '(f x)
             #:eval (hash 'f (λ (x) x) 'x #t) #:to-map (hash))

  (test-elab '((as (-o bool bool) nil) x)
             #f
             '([x point bool])
             #:type 'bool #:uses '(x)
             #:eval (hash 'x #t) #:to-map (hash))

  (test-elab '(λ (x) nil)
             '(=> nat bool)
             '()
             #:type '(=> nat bool)
             #:eval (hash) #:to-map (hash))

  (test-elab '(λ (x) x)
             '(-o bool bool)
             '()
             #:type '(-o bool bool)
             #:eval (hash)
             #:to-map (match-lambda [(hash (hash) (? procedure?)) #t] [_ #f]))

  (test-elab '(λ (x) (λ (y) (x y)))
             '(-o (-o bool bool) (-o bool bool))
             '()
             #:eval (hash)
             #:to-map (match-lambda [(hash (hash) (? procedure?)) #t] [_ #f]))

  #; ;; fails b/c don't support set lambdas yet
  (test-elab '(λ (f) (λ (x) (f x)))
             '(-o (=> nat bool) (-> nat bool))
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
             #:to #t)

  (test-elab '(f x x) #f '([f set (=> nat (=> nat nat))]
                           [x set nat])
             #:type 'nat
             #:uses '(f x)
             #:eval (hash 'x 23
                          'f (hash 17 (hash 17 1717 23 1723)
                                   23 (hash 23 2323 17 2317)))
             #:to 2323)

  (test-elab '(f x y) #f '([f set (=> nat (=> nat bool))]
                           [x fs nat]
                           [y fs nat])
             #:type 'bool
             #:uses '(f x y)
             #:eval (hash 'f (hash 17 (hash 17 1717 23 1723)
                                   23 (hash 23 2323 17 2317)))
             #:to-map (hash (hash 'x 17 'y 17) 1717
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
             #:to-map (hash (hash 'x 17) #t (hash 'x 23) #f)
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
             #:to-map (hash (hash 'x 23) #t))

  ;; cross product
  (test-elab '(and (f x) (g y))
             #f
             '([and set (-o bool (-o bool bool))]
               [x fs a]
               [y fs b]
               [f set   (=> a bool)]
               [g point (=> b bool)]
               )
             #:type 'bool
             #:uses '(and f g x y)
             #:eval (hash 'and (λ (x) (λ (y) (and x y)))
                          'f (hash 'ada #t 'bob #t)
                          'g (hash 17 #t 23 #t))
             #:to-map (hash (hash 'x 'ada 'y 17) #t
                            (hash 'x 'ada 'y 23) #t
                            (hash 'x 'bob 'y 17) #t
                            (hash 'x 'bob 'y 23) #t))

  ;; FINITE LAMBDAS
  (test-elab '(λ (x) (f x))
             '(=> nat bool)
             '([f point (=> nat bool)])
             #:eval (hash 'f (hash 17 #t))
             #:to   (hash 17 #t))

  (test-elab '(λ (x) (f x)) '(=> nat bool) '([f point (=> nat bool)])
             #:eval (hash 'f (hash)) #:to-map (hash))

  (test-elab '(λ (x) (and (f x) (g x)))
             '(=> nat bool)
             '([and set (-o bool (-o bool bool))]
               [f point (=> nat bool)]
               [g point (=> nat bool)])
             #:uses '(and f g)
             #:eval (hash 'and (λ (x) (λ (y) (and x y)))
                          'f (hash 17 #t 23 #t)
                          'g (hash 23 #t 54 #t))
             #:to (hash 23 #t))

  (test-elab '(λ (y) (and (f x) (g y)))
             '(=> b bool)
             '([and set (-o bool (-o bool bool))]
               [f point (=> a bool)]
               [g point (=> b bool)]
               [x fs a])
             #:uses '(and f g x)
             #:eval (hash 'and (λ (x) (λ (y) (and x y)))
                          'f (hash 'ada #t 'bob #t)
                          'g (hash 17 #t 23 #t))
             #:to-map (hash (hash 'x 'ada) (hash 17 #t 23 #t)
                            (hash 'x 'bob) (hash 17 #t 23 #t)))

  ;; WITH TUPLES. TODO: use #:eval argument once implemented.
  (test-elab '(cons) #f '([x point bool] [y fs nat])
             #:type '(&)
             #:uses '(x y)
             #:eval (hash)
             #:to-map (hash)            ;TODO: why? why not (hash (hash) '())?
             )

  (test-elab '(cons (f x y))
             #f
             '([f point (-o p (=> nat bool))]
               [x point p]
               [y fs nat])
             #:type '(& bool)
             #:uses '(f x y)
             #:eval (hash 'f (λ (x) (if (eq? x 'IAMX) (hash 17 #t 23 #t) (hash)))
                          'x 'IAMX)
             #:to-map (hash (hash 'y 17) '(#t)
                            (hash 'y 23) '(#t)))

  (test-elab '(cons x x) #f '([x point bool])
             #:type '(& bool bool)
             #:uses '(x)
             #:eval (hash 'x 'yes) #:to '(yes yes))

  (test-elab '(cons x y) #f '([x point bool] [y set nat])
             #:type '(& bool nat)
             #:uses '(y) ;; depends on y, but does not preserve point wrt x
             #:eval (hash 'x #t 'y 17)
             #:to   '(#t 17))

  ;; our first real outer join
  (test-elab '(cons (f x) (g x))
             #f
             '([x fs nat]
               [f set (=> nat bool)]
               [g point (=> nat bool)])
             #:type '(& bool bool)
             #:uses '(x f)
             #:eval (hash 'f (hash 17 #t 23 #t)
                          'g (hash 23 #t 54 #t))
             #:to-map (hash (hash 'x 17) '(#t #f)
                            (hash 'x 23) '(#t #t)
                            (hash 'x 54) '(#f #t)))

  (test-elab '(cons x (cons (f x y) x))
             #f
             '([x point p]
               [y point q]
               [f point (-o p (-o q bool))])
             #:type '(& p (& bool p))
             #:uses '(x)
             #:eval (hash 'x 'x 'y 'y
                          'f (λ (x) (λ (y) (and (eq? x 'x) (eq? y 'y)))))
             #:to '(x (#t x)))

  (test-elab '(cons x (f y))
             '(& p q)
             '([x point p]
               [f point (=> nat q)]
               [y fs nat])
             #:fail #rx"variable y is ground by some but not all with-pair components")

  (test-elab '(cons (f x) (g x y))
             '(& p q)
             '([f point (=> nat p)]
               [g point (=> nat (=> nat q))]
               [x fs nat]
               [y fs nat])
             #:fail #rx"variable y is ground by some but not all with-pair components")

  ;; OR EXPRESSIONS
  (test-elab '(or) #f '([x point p] [y fs q])
             #:type 'bool #:uses '(x y)
             #:eval (hash 'x 'x) #:to-map (hash))

  (test-elab '(or x) #f '([x point bool] [y fs q])
             #:type 'bool #:uses '(x)
             #:eval (hash 'x #t) #:to #t)

  (test-elab '(or x y) #f '([x point bool]
                            [y point bool]
                            [or set (-o (& bool bool) bool)])
             #:type 'bool #:uses '(or)
             #:eval (hash 'x #f 'y #t 'or (match-λ [`(,x ,y) (or x y)]))
             #:to #t)

  ;; costars x y = ∃λfilm. stars film x AND stars film y
  (define film-stars
    (hash 'casablanca '(bogart bergman)
          'the-big-sleep '(bogart bacall)))
  (define film-stars-trie
    (for/hash ([(film actors) film-stars])
      (values film (for/hash ([actor actors]) (values actor #t)))))
  (define costars (make-hash))
  (for* ([(_ actors) film-stars] [actor1 actors] [actor2 actors])
    (hash-update! costars actor1 (λ (s) (set-add s actor2)) (λ () (set))))

  (test-elab
   '(exists (λ (film) (and (stars film x) (stars film y))))
   'bool
   '([x      fs     person]
     [y      fs     person]
     [exists set    (-o (=> film bool) bool)]
     [and    set    (-o bool (-o bool bool))]
     [stars  point  (=> film (=> person bool))])
   #:eval (hash-set stdlib 'stars film-stars-trie)
   #:to-map (for*/hash ([(x actors) costars] [y actors])
              (values (hash 'x x 'y y) #t)))

  (test-elab
   '(λ (x) (λ (y) (exists (λ (film) (and (stars film x) (stars film y))))))
   '(=> person (=> person bool))
   '([exists set    (-o (=> film bool) bool)]
     [and    set    (-o bool (-o bool bool))]
     [stars  point  (=> film (=> person bool))])
   #:eval (hash-set stdlib 'stars film-stars-trie)
   #:to (for/hash ([(x actors) costars])
          (values x (for/hash ([y actors]) (values y #t)))))

  ;; test the built-in polymorphic exists
  (test-elab
   '(exists (film _) (and (stars film x) (stars film y)))
   'bool
   '([x      fs     person]
     [y      fs     person]
     [and    set    (-o bool (-o bool bool))]
     [stars  point  (=> _ (=> person bool))])
   #:eval (hash-set stdlib 'stars film-stars-trie)
   #:to-map (for*/hash ([(x actors) costars] [y actors])
              (values (hash 'x x 'y y) #t)))

  (test-elab
   '(λ (x) (λ (y) (exists (film _) (and (stars film x) (stars film y)))))
   '(=> person (=> person bool))
   '([and    set    (-o bool (-o bool bool))]
     [stars  point  (=> _ (=> person bool))])
   #:eval (hash-set stdlib 'stars film-stars-trie)
   #:to (for/hash ([(x actors) costars])
          (values x (for/hash ([y actors]) (values y #t)))))

  ;; filmCount x = sum λfilm. 1 when stars film x
  (define film-counts (make-hash))
  (for* ([(_ actors) film-stars] [actor actors])
    (hash-update! film-counts actor add1 0))

  (test-elab
   '(sum (film _) (when (stars film actor) 1))
   'natz
   '([actor  fs     person]
     [stars  point  (=> _ (=> person bool))])
   #:eval (hash-set stdlib 'stars film-stars-trie)
   #:to-map (for/hash ([(actor n) film-counts])
              (values (hash 'actor actor) n)))

  ;; TODO: a better test for minimum.
  (test-elab
   '(minimum (film _) (when (stars film actor) 1))
   'natinf
   '([actor  fs     person]
     [stars  point  (=> _ (=> person bool))])
   #:eval (hash-set stdlib 'stars film-stars-trie)
   #:to-map (for/hash ([(actor n) film-counts])
              (values (hash 'actor actor) 1)))

  ;; maximum
  (test-elab
   '(maximum (actor person) (sum (film _) (when (stars film actor) 1)))
   'natz
   '([stars  point  (=> _ (=> person bool))])
   #:eval (hash-set stdlib 'stars film-stars-trie)
   #:to (apply max 0 (hash-values film-counts)))

  #;
  (check-equal? #t #f))
