#lang racket
;;; fucking around with syntax to figure out how to report errors nicely.

(define (read-string name source-string)
  (define p (open-input-string source-string))
  (port-count-lines! p)
  (read-syntax name p))

(define foo-src "{x . -> . y}")
(define foo-stx (read-string "foo" foo-src))

(define (show-location str stx)
  (define lines (string-split str "\n"))
  (define the-line (list-ref lines (- (syntax-line stx) 1)))
  (displayln the-line)
  (display (make-string (syntax-column stx) #\space))
  (define n (syntax-span stx))
  (if (and n (> n 0))
      (displayln (make-string n #\^))
   (displayln "^")))
