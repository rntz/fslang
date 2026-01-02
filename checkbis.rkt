#lang racket

(define-syntax-rule (todo)
  (error "todo"))

(define term? any/c)
(define type?
  (flat-rec-contract type?
     #t                                 ; #f = bottom, #t = top type
     symbol?                            ; base type
     (list/c '-> type? type?)           ; functions
     (list/c '* type? type?)            ; pairs
     ))

;; A context maps variables to types.
(define cx? (hash/c symbol? type? #:immutable #t #:flat? #t))

(define/match (subtype? a b)
  ; [(#f _) #t]
  [(_ #t) #t]
  [(x y) #:when (eq? x y) #t]
  [(`(-> ,a1 ,a2) `(-> ,b1 ,b2)) (and (subtype? b1 a1) (subtype? a2 b2))]
  [(`(* ,a1 ,a2)  `(* ,b1 ,b2)) (and (subtype? a1 a2) (subtype? b1 b2))]
  [(_ _) #f])

;; Do we check function first or argument first? Function-first is the
;; traditional, theoretically grounded bidirectional approach. However, it seems
;; awkward here for reasons explained below. Instead we can try to synthesize
;; the argument first. This seems to fit better with our "unidirectional but
;; with partial type information" approach.
(define FUNCTION-FIRST #f)

(define (check term want cx)
  (define (inferred got)
    (unless (subtype? got want) (error 'check "want ~a, got ~a" want got))
    got)
  (match term
    [(? boolean? x) (inferred 'bool)]
    [(? number? x) (inferred 'num)]

    [(? symbol? x) (inferred (hash-ref cx x))]

    [`(is ,anno ,body)
     (unless (type? anno) (error 'check "invalid type in annotation: ~a" anno))
     (unless (subtype? anno want)
       (error 'check "want ~a, annotated ~a" want anno))
     (check body anno cx)]

    [`(cons ,t ,u)
     (define-values (want-a want-b)
       ;; ***** POTENTIAL PROBLEM *****
       ;;
       ;; I worry that this match may become unwieldy if we add more interesting
       ;; subtyping relationships to our language, in particular, if we add
       ;; supertypes of the pair type.
       (match want
         [#t (values #t #t)]
         [`(* ,a ,b) (values a b)]
         [_ (error 'elab "tuple cannot have type ~a" want)]))
     `(* ,(check t want-a cx) ,(check u want-b cx))]

    [`(fst ,t)
     (match-define `(* ,a ,_) (check t `(* ,want #t) cx))
     a]

    [`(snd ,t)
     (match-define `(* ,_ ,b) (check t `(* #t ,want) cx))
     b]

    [`(lambda (,(? symbol? x)) ,body)
     ;; ***** POTENTIAL PROBLEM *****
     ;; Another possibly unwieldy match, if we add supertypes of functions.
     (define-values (a b)
       (match want
         [`(-> ,a ,b) (values a b)]
         [#t (error 'check "cannot infer lambda")]
         [_ (error 'check "lambda cannot have type ~a" want)]))
     `(-> ,a ,(check body b (hash-set cx x a)))]

    [`(,t ,u)
     ;; Do we check function-first or argument-first?
     (cond
       [FUNCTION-FIRST
        ;; You might think I could do (check t `(-> #f ,want) cx), where #f is
        ;; bottom type. The problem is that if t = (lambda (x) body) then this
        ;; will usually succeed, but provide no information about the argument
        ;; type (the type of x/u), so we will check u at type #f and (almost
        ;; always) fail.
        (match-define `(-> ,a ,b)
          (check t #t cx)
          #;(check t `(-> #f ,want) cx)
          )
        (check u a cx)
        (inferred b)]
       [else
        ;; 2. Argument-first. This is less traditional, although I have seen
        ;; papers suggesting it [1] (which I have not yet read in detail).
        ;;
        ;; [1] https://xnning.github.io/papers/let-arguments-go-first.pdf
        (define u-type (check u #t cx))
        (match-define `(-> ,_ ,result) (check t `(-> ,u-type ,want) cx))
        result])]
    ))
