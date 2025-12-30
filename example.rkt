;; This is an example of a typechecker & interpreter for a simply typed lambda
;; calculus written in an unusual style. I wandered into this style after
;; writing the compiler for Datafun in tagless-final style using OCaml modules;
;; more recently I began writing an interpreter for a related language (see
;; fslang.rkt), initially in the same style, but later decided to just
;; inline/fuse all the phases/passes together. This puts all information about a
;; particular language construct in one place - one branch of a gigantic "match"
;; over the input syntax. This is probably not a great way to structure a large
;; compiler but it's pretty good for fast prototyping.
#lang racket

(define term? any/c)
(define value? any/c)
(define type?
  (flat-rec-contract type?
     symbol?                            ; base type
     (list/c '-> type? type?)           ; functions
     (cons/c '* (listof type?))         ; tuples
     ))
;; A context maps variables to types.
(define cx? (hash/c symbol? type? #:immutable #t #:flat? #t))
;; An environment maps variables to values.
(define env? (hash/c symbol? value? #:immutable #t #:flat? #t))
;; A term denotes a function from environments to values.
(define deno/c (-> env? value?))

(define subtype? equal?)

;; Bidirectional elaborator/evaluator that, given a term, optional expected
;; type, and typing context, returns the term's type and denotation.
(define/contract (elab term expect cx)
  (-> term? (or/c #f type?) cx?
      (values type? deno/c))

  (define (cannot-infer name)
    (unless expect (error 'elab "cannot infer type of ~a" name))
    expect)

  (define (inferred got)
    (cond [(not expect) got]
          [(subtype? got expect) got]
          [else (error 'elab "expected ~a, but inferred ~a" expect got)]))

  (match term
    [`(is ,anno ,body)                    ; TYPE ANNOTATION
     (unless (type? anno) (error 'elab "invalid type in type annotation: ~a" anno))
     (when (and expect (not (subtype? anno expect)))
       (error 'elab "expected ~a, but annotated ~a" expect anno))
     (elab body anno cx)]

    [`(tuple ,@args)                    ;TUPLE
     (define n (length args))
     (define arg-expects
       (match expect
         [#f (make-list n #f)]
         [`(* ,@types)
          (define n-expect (length types))
          (if (= n n-expect)
              types
              (error 'elab "tuple has wrong length; expected ~a, got ~a"
                     n-expect n))]
         [_ (error 'elab "expected ~a, but got a tuple expression" expect)]))
     (define-values (arg-types arg-denos)
      (for/lists (_1 _2)
                 ([arg args]
                  [arg-expect arg-expects])
        (elab arg arg-expect cx)))
     (values `(* ,@arg-types)
             (λ (env) (for/list ([d arg-denos]) (d env))))]

    [`(nth ,(? exact-nonnegative-integer? n) ,e) ;PROJECTION
     (define-values (etp edeno) (elab e #f cx))
     (values
      (match etp
        [`(* ,@tps)
         (unless (< n (length tps))
           (error 'elab "expected tuple with at least ~a parts, got ~a" (+ 1 n) etp))
         (list-ref tps n)]
        [_ (error 'elab "cannot project from non-tuple type: ~a" etp)])
      (λ (env) (list-ref (edeno env) n)))]

    [`(,(or 'λ 'lambda) (,(? symbol? param)) ,body) ;LAMBDA
     (define-values (A B)
       (match (cannot-infer "lambda")
        [`(-> ,A ,B) (values A B)]
        [tp (error 'elab "lambda cannot have type: ~a" tp)]))
     (define-values (body-tp body-deno)
       (elab body B (hash-set cx param A)))
     (values
      `(-> ,A ,body-tp)
      (lambda (env) (λ (x) (body-deno (hash-set env param x)))))]

    [`(,e1 ,e2)                         ;APPLICATION
     (define-values (tp1 deno1) (elab e1 #f cx))
     (define-values (A B)
       (match tp1
         [`(-> ,A ,B) (values A B)]
         [_ (error 'elab "cannot apply a non-function of type: ~a" tp1)]))
     (define-values (tp2 deno2) (elab e2 A cx))
     (values
      (inferred B)
      (λ (env) ((deno1 env) (deno2 env))))]

    [(? number? n) (values (inferred 'num) (λ (_) n))] ;NUMBER LITERAL

    [(? symbol? x)                      ;VARIABLE
     (values (inferred (hash-ref cx x))
             (λ (env) (hash-ref env x)))]))


(module+ test
  (require rackunit)
  (define no-check-value (gensym))
  (define (test-elab term expect [cx (hash)]
                     #:type [check-type #f]
                     #:eval [env #f]
                     #:to   [check-value no-check-value]
                     )
    (define-values (type deno) (elab term expect cx))
    (when expect
      (check subtype? expect type))
    (when check-type
     (check-equal? type check-type))
    ;; TODO: check the denotation
    (when (or env (not (eq? check-value no-check-value)))
      (define value (deno (or env (hash))))
      (unless (eq? check-value no-check-value)
        (check-equal? value check-value))))

  (test-elab 2 #f #:type 'num #:eval (hash) #:to 2)
  (test-elab 'x #f (hash 'x 'bool) #:type 'bool #:eval (hash 'x #t) #:to #t)
  (test-elab '(tuple 2 x) #f (hash 'x 'bool)
             #:type '(* num bool)
             #:eval (hash 'x #t) #:to '(2 #t))
  (test-elab '(nth 0 (tuple 2 x)) #f (hash 'x 'bool)
             #:type 'num
             #:eval (hash 'x #t) #:to 2)
  (test-elab '(nth 1 (tuple 2 x)) #f (hash 'x 'bool)
             #:type 'bool
             #:eval (hash 'x #t) #:to #t)

  (test-elab '(λ (x) x) '(-> a a))
  (test-elab '(f 2) #f (hash 'f '(-> num bool))
             #:type 'bool
             #:eval (hash 'f (λ (x) (> x 0))) #:to #t)
  )
