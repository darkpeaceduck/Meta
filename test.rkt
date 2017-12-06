#lang racket

(require "auxiliary_functions.rkt")
(require "int.rkt")

(define check (lambda (a b)
  (if (equal? (list->set a) (list->set b)) (println 'OK) (println 'Failed))))

(define ARGS (list 1 1 0 1 0 1))
(define Q '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))
(define DIV1 '(prog1 div1 pp1 bb1 cmd1))
(define DIV2 '(prog2 div2 pp2 bb2 cmd2))
(define MARGS '(Q Qtail Instruction Operator Nextlabel Symbol))
(define SUF '('() '() '() '() '() '()))
(define REQUIRED_RESULT (list 1 1 0 1))


(define runm
  (lambda ret
    (int (car ret) `(,ARGS))))

(define run2
  (lambda ret
    (runm (intp (car ret) `((',Q ,SUF))))))

(define run3
  (lambda ret
    (run2 (intp (car ret) `((',int_machine ',MARGS ,SUF))))))


(define proj1 (intp mix_L `(,int_machine ,MARGS (',Q ,SUF))))

(define proj2 (intp mix_L `(,mix_L1 ,DIV1 (',int_machine ',MARGS ,SUF))))

(define proj3 (intp mix_L `(,mix_L1 ,DIV1 (',mix_L2 ',DIV2 '() '() '() '() '() '()))))

(check (runm proj1) REQUIRED_RESULT)
(check (run2 proj2) REQUIRED_RESULT)
(check (run3 proj3) REQUIRED_RESULT)

