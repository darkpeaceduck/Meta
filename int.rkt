#lang racket

(require "auxiliary_functions.rkt")
(provide (all-defined-out))
(provide int)

(define int
  (lambda (p d)
    (let ([prog (initial-prog p)]
          [st (initial-st (cdar p) d)])
      (int-bb prog st (cdadr p)))))

(define int-bb
  (lambda (prog st bb)
    (match bb
      ['() (error "int: empty basic_block list")]
      [`(,h) (int-jump prog st h)]
      [`(,h . ,t) (int-bb prog (int-assn st h) t)]
      )))

(define int-jump
  (lambda (prog st jump)
    (match jump
      [`(goto ,l) (int-bb prog st (bb-lookup prog l))]
      [`(if ,e ,l1 ,l2) (int-bb prog st (bb-lookup prog (if (eval-exp st e) l1 l2)))]
      [`(return ,e) (eval-exp st e)]
      )))

(define int-assn
  (lambda (st assn)
    (match assn
      [`(:= ,x ,exp)  (let ([nv (eval-exp st exp)]) (st-set st x nv))]
      [_ (error "int: assignment expected")]
      )))

(define find_name
  '((read name namelist valuelist)
   (search (if (equal? name (car namelist)) found cont))
   (cont (:= valuelist (cdr valuelist))
         (:= namelist (cdr namelist))
         (goto search))
   (found (return (car valuelist)))
   ))

(define mix_L
'(
 (read prog div vs0)
 (init  (:= pending (make-pending-list prog (make-list-st div vs0)))
       (:= marked '())
       (:= residual (initial-residual (cdar prog) div))
       (goto outer-loop))

 (outer-loop (if (empty? pending) stop init-pp))
 (outer-loop-body-end (:= residual (extend residual (list code)))
                    (:= cmd '()) (goto outer-loop))
 (init-pp (:= pp prog) (goto init-pp-1))
 (init-pp-1 (:= pp (cdr pp))  (if (empty? pp) error init-pp-2))
 (init-pp-2 (if (eq? (caar pending) (caar pp)) outer-loop-body init-pp-1))
 (outer-loop-body
       (:= pp (caar pp))
       (:= st (cadar pending))
       (:= pending (cdr pending))
       (:= marked (set-marked pp st marked))
       (:= bb (st-lookup prog pp))
       (:= code (list (make-st-label pp st)))
       (:= pp '())
       (goto inner-loop))
   (inner-loop (if (empty? bb) outer-loop-body-end inner-loop-body))
   (inner-loop-body (:= cmd (car bb))
               (:= bb (cdr bb))
               (goto switch-cmd-ass))
   (switch-cmd-ass (if (eq? ':=     (car cmd)) do-ass-cmd switch-cmd-goto))
   (switch-cmd-goto (if (eq? 'goto   (car cmd)) do-goto-cmd   switch-cmd-if))
   (switch-cmd-if   (if (eq? 'if     (car cmd)) do-if-cmd     switch-cmd-return))
   (switch-cmd-return  (if (eq? 'return (car cmd)) do-return-cmd    error))

   (do-ass-cmd (if (is_exp_static_by_division (cadr cmd) div)
                  do-ass-cmd-static do-ass-cmd-dynamic))

   (do-ass-cmd-static (:= st (list-st-set st (cadr cmd) (reduce (caddr cmd) st)))
                     (goto inner-loop))
   
   (do-ass-cmd-dynamic (:= code (extend code (list
                          (make-ass (cadr cmd) (reduce (caddr cmd) st)))))
                      (goto inner-loop))

   (do-goto-cmd (:= bb (st-lookup prog (cadr cmd))) (goto inner-loop))

   (do-if-cmd (if (is_exp_static_by_division (cadr cmd) div)
              do-if-cmd-static do-if-cmd-dynamic))

   (do-if-cmd-dynamic  (if (is-marked (caddr cmd) st marked)
                       do-if-cmd-dynamic-1 do-if-cmd-dynamic-2))
   (do-if-cmd-dynamic-1 (if (is-marked (cadddr cmd) st marked)
                        do-if-cmd-dynamic-fin do-if-cmd-dynamic-3))

   (do-if-cmd-dynamic-2 (:= pending (pending-append (caddr cmd) st pending))
                    (goto do-if-cmd-dynamic-1))
   (do-if-cmd-dynamic-3 (:= pending (pending-append (cadddr cmd) st pending))
                    (goto do-if-cmd-dynamic-fin))


   (do-if-cmd-dynamic-fin (:= code (extend code (list
                        (make-if (reduce (cadr cmd) st)
                             (make-st-label (caddr cmd) st)
                             (make-st-label (cadddr cmd) st)))))
                   (goto inner-loop))

   (do-if-cmd-static (if (my-eval (reduce (cadr cmd) st))
                     do-if-cmd-static-1 do-if-cmd-static-2))
   (do-if-cmd-static-1 (:= bb (st-lookup prog (caddr cmd)))
                   (goto inner-loop))
   (do-if-cmd-static-2 (:= bb (st-lookup prog (cadddr cmd)))
                   (goto inner-loop))

   (do-return-cmd (:= code (extend code
                    (list (make-return (reduce (cadr cmd) st)))))
           (goto inner-loop))

  (error (return 'mix-errored))
   (stop (return residual))
))



(define mix_L1
'(
 (read prog1 div1 vs01)
 (init  (:= pending1 (make-pending-list prog1 (make-list-st div1 vs01)))
       (:= marked1 '())
       (:= residual1 (initial-residual (cdar prog1) div1))
       (goto outer-loop))

 (outer-loop (if (empty? pending1) st1op init-pp1))
 (outer-loop-body-end (:= residual1 (extend residual1 (list code1)))
                    (:= cmd1 '()) (goto outer-loop))
 (init-pp1 (:= pp1 prog1) (goto init-pp1-1))
 (init-pp1-1 (:= pp1 (cdr pp1))  (if (empty? pp1) error init-pp1-2))
 (init-pp1-2 (if (eq? (caar pending1) (caar pp1)) outer-loop-body init-pp1-1))
 (outer-loop-body
       (:= pp1 (caar pp1))
       (:= st1 (cadar pending1))
       (:= pending1 (cdr pending1))
       (:= marked1 (set-marked pp1 st1 marked1))
       (:= bb1 (st-lookup prog1 pp1))
       (:= code1 (list (make-st-label pp1 st1)))
       (:= pp1 '())
       (goto inner-loop))
   (inner-loop (if (empty? bb1) outer-loop-body-end inner-loop-body))
   (inner-loop-body (:= cmd1 (car bb1))
               (:= bb1 (cdr bb1))
               (goto switch-cmd-ass))
   (switch-cmd-ass (if (eq? ':=     (car cmd1)) do-ass-cmd switch-cmd-goto))
   (switch-cmd-goto (if (eq? 'goto   (car cmd1)) do-goto-cmd   switch-cmd-if))
   (switch-cmd-if   (if (eq? 'if     (car cmd1)) do-if-cmd     switch-cmd-return))
   (switch-cmd-return  (if (eq? 'return (car cmd1)) do-return-cmd   error))

   (do-ass-cmd (if (is_exp_static_by_division (cadr cmd1) div1)
                  do-ass-cmd-st1atic do-ass-cmd-dynamic))

   (do-ass-cmd-st1atic (:= st1 (list-st-set st1 (cadr cmd1) (reduce (caddr cmd1) st1)))
                     (goto inner-loop))
   
   (do-ass-cmd-dynamic (:= code1 (extend code1 (list
                          (make-ass (cadr cmd1) (reduce (caddr cmd1) st1)))))
                      (goto inner-loop))

   (do-goto-cmd (:= bb1 (st-lookup prog1 (cadr cmd1))) (goto inner-loop))

   (do-if-cmd (if (is_exp_static_by_division (cadr cmd1) div1)
              do-if-cmd-st1atic do-if-cmd-dynamic))

   (do-if-cmd-dynamic  (if (is-marked (caddr cmd1) st1 marked1)
                       do-if-cmd-dynamic-1 do-if-cmd-dynamic-2))
   (do-if-cmd-dynamic-1 (if (is-marked (cadddr cmd1) st1 marked1)
                        do-if-cmd-dynamic-fin do-if-cmd-dynamic-3))

   (do-if-cmd-dynamic-2 (:= pending1 (pending-append (caddr cmd1) st1 pending1))
                    (goto do-if-cmd-dynamic-1))
   (do-if-cmd-dynamic-3 (:= pending1 (pending-append (cadddr cmd1) st1 pending1))
                    (goto do-if-cmd-dynamic-fin))


   (do-if-cmd-dynamic-fin (:= code1 (extend code1 (list
                        (make-if (reduce (cadr cmd1) st1)
                             (make-st-label (caddr cmd1) st1)
                             (make-st-label (cadddr cmd1) st1)))))
                   (goto inner-loop))

   (do-if-cmd-st1atic (if (my-eval (reduce (cadr cmd1) st1))
                     do-if-cmd-st1atic-1 do-if-cmd-st1atic-2))
   (do-if-cmd-st1atic-1 (:= bb1 (st-lookup prog1 (caddr cmd1)))
                   (goto inner-loop))
   (do-if-cmd-st1atic-2 (:= bb1 (st-lookup prog1 (cadddr cmd1)))
                   (goto inner-loop))

   (do-return-cmd (:= code1 (extend code1
                    (list (make-return (reduce (cadr cmd1) st1)))))
           (goto inner-loop))

  (error (return 'mix-errored))
   (st1op (return residual1))
))


(define mix_L2
'(
 (read prog2 div2 vs02)
 (init  (:= pending2 (make-pending-list prog2 (make-list-st div2 vs02)))
       (:= marked2 '())
       (:= residual2 (initial-residual (cdar prog2) div2))
       (goto outer-loop))

 (outer-loop (if (empty? pending2) st2op init-pp2))
 (outer-loop-body-end (:= residual2 (extend residual2 (list code2)))
                    (:= cmd2 '()) (goto outer-loop))
 (init-pp2 (:= pp2 prog2) (goto init-pp2-2))
 (init-pp2-2 (:= pp2 (cdr pp2))  (if (empty? pp2) error init-pp2-3))
 (init-pp2-3 (if (eq? (caar pending2) (caar pp2)) outer-loop-body init-pp2-2))
 (outer-loop-body
       (:= pp2 (caar pp2))
       (:= st2 (cadar pending2))
       (:= pending2 (cdr pending2))
       (:= marked2 (set-marked pp2 st2 marked2))
       (:= bb2 (st-lookup prog2 pp2))
       (:= code2 (list (make-st-label pp2 st2)))
       (:= pp2 '())
       (goto inner-loop))
   (inner-loop (if (empty? bb2) outer-loop-body-end inner-loop-body))
   (inner-loop-body (:= cmd2 (car bb2))
               (:= bb2 (cdr bb2))
               (goto switch-cmd-ass))
   (switch-cmd-ass (if (eq? ':=     (car cmd2)) do-ass-cmd switch-cmd-goto))
   (switch-cmd-goto (if (eq? 'goto   (car cmd2)) do-goto-cmd   switch-cmd-if))
   (switch-cmd-if   (if (eq? 'if     (car cmd2)) do-if-cmd     switch-cmd-return))
   (switch-cmd-return  (if (eq? 'return (car cmd2)) do-return-cmd    error))
  

   (do-ass-cmd (if (is_exp_static_by_division (cadr cmd2) div2)
                  do-ass-cmd-st2atic do-ass-cmd-dynamic))

   (do-ass-cmd-st2atic (:= st2 (list-st-set st2 (cadr cmd2) (reduce (caddr cmd2) st2)))
                     (goto inner-loop))
   
   (do-ass-cmd-dynamic (:= code2 (extend code2 (list
                          (make-ass (cadr cmd2) (reduce (caddr cmd2) st2)))))
                      (goto inner-loop))

   (do-goto-cmd (:= bb2 (st-lookup prog2 (cadr cmd2))) (goto inner-loop))

   (do-if-cmd (if (is_exp_static_by_division (cadr cmd2) div2)
              do-if-cmd-st2atic do-if-cmd-dynamic))

   (do-if-cmd-dynamic  (if (is-marked (caddr cmd2) st2 marked2)
                       do-if-cmd-dynamic-2 do-if-cmd-dynamic-3))
   (do-if-cmd-dynamic-2 (if (is-marked (cadddr cmd2) st2 marked2)
                        do-if-cmd-dynamic-fin do-if-cmd-dynamic-4))

   (do-if-cmd-dynamic-3 (:= pending2 (pending-append (caddr cmd2) st2 pending2))
                    (goto do-if-cmd-dynamic-2))
   (do-if-cmd-dynamic-4 (:= pending2 (pending-append (cadddr cmd2) st2 pending2))
                    (goto do-if-cmd-dynamic-fin))


   (do-if-cmd-dynamic-fin (:= code2 (extend code2 (list
                        (make-if (reduce (cadr cmd2) st2)
                             (make-st-label (caddr cmd2) st2)
                             (make-st-label (cadddr cmd2) st2)))))
                   (goto inner-loop))

   (do-if-cmd-st2atic (if (my-eval (reduce (cadr cmd2) st2))
                     do-if-cmd-st2atic-2 do-if-cmd-st2atic-3))
   (do-if-cmd-st2atic-2 (:= bb2 (st-lookup prog2 (caddr cmd2)))
                   (goto inner-loop))
   (do-if-cmd-st2atic-3 (:= bb2 (st-lookup prog2 (cadddr cmd2)))
                   (goto inner-loop))

   (do-return-cmd (:= code2 (extend code2
                    (list (make-return (reduce (cadr cmd2) st2)))))
           (goto inner-loop))

  (error (return 'mix-errored))
   (st2op (return residual2))
))

(define int_machine
  '(
    (read Q Right)
    (int_init (:= Qtail Q)
          (:= Left '())
          (goto int_loop))
    (int_loop (if (empty? Qtail) int_stop int_cont))
    
    (int_cont (:= Instruction (car Qtail)) (:= Qtail (cdr Qtail)) (:= Operator (cadr Instruction))
          (if (eq? Operator 'right) do-right cont1))
    (cont1 (if (eq? Operator 'left)  do-left  cont2))
    (cont2 (if (eq? Operator 'write) do-write cont3))
    (cont3 (if (eq? Operator 'goto)  do-goto  cont4))
    (cont4 (if (eq? Operator 'if)    do-if    int_error))
    
    (do-right (:= Left (cons (car Right) Left))         (:= Right (cdr Right))                           (goto int_loop))
    (do-left  (:= Left (cdr Left))                      (:= Right (cons (car Left) Right))               (goto int_loop))
    (do-write (:= Symbol (caddr Instruction))           (:= Right (cons Symbol (cdr Right)))             (goto int_loop))
    (do-goto  (:= Nextlabel (caddr Instruction))        (:= Qtail (list-tail Q Nextlabel))               (goto int_loop))
    (do-if    (:= Symbol (caddr Instruction))           (:= Nextlabel (caddr (cddr Instruction)))        (if (eq? Symbol (car Right)) int_jump int_loop))
    
    (int_jump     (:= Qtail (list-tail Q Nextlabel))        (goto int_loop))
    
    (int_error    (return ('syntax-error: Instruction)))
    
    (int_stop     (return Right))
    ))

(define intp
  (lambda (p d)
     (pretty (int p d))))