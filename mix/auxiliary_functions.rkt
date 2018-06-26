#lang racket

(provide (all-defined-out))

; for environment
(define st-lookup dict-ref)
(define st-bound? dict-has-key?)
(define st-set
  (lambda (st x e)
    (dict-set st x (cons 'quote (list e)))))


(define st-empty  #hash())
(define initial-st
  (lambda (vars d)
    (if (equal? (length vars) (length d))
        (for/fold ([st st-empty])
                  ([i vars]
                   [j d])
          (st-set st i j))
        (error "initial-st error: program arity mismatch"))))

; for basic_blocks
(define bb-lookup dict-ref)
(define bb-set    dict-set)
(define bb-empty  #hash())
(define initial-prog
  (lambda (p)
    (for/fold ([bbs bb-empty])
              ([i (cdr p)])
      (bb-set bbs (car i) (cdr i)))))

; eval
(define-namespace-anchor abracadabra)
(define ns (namespace-anchor->namespace abracadabra))
(define my-eval
  (lambda (e)
    (eval e ns)))

; eval expression in current environment
(define subst
  (lambda (st e)
    (match e
      [`(,x . ,y) `(,(subst st x) . ,(subst st y))]
      [`,x (if (st-bound? st x) (st-lookup st x) x)]
      )))
(define eval-exp
  (lambda (st e)
    (let ([ee (subst st e)])
      (my-eval ee))))

; mix
(define initial-residual
  (lambda (read-data division)
    (let ([init (set-subtract read-data division)])
      (list (append '(read) init)))))

(define initial-code
  (lambda (pp vs)
    ;`((,pp . ,vs) . ())))
    `(,pp . ())))

(define extend append)
(define first_command car)
(define rest_bb cdr)

(define pending-set
  (lambda (pending pair)
    (if (equal? pair '())
        pending
        (let ([m (member pair pending)])
          (if (not m)
              (append (list pair) pending)
              pending)))))

(define listminus
  (lambda (l1 l2)
    (let ([m (member l1 l2)])
      (if (not m)
          l1
          '()
          ))))

(define pretty
  (lambda (program)
    (let* ([add-block
            (lambda (block acc)
              (match acc
                [`(,num ,used ,blocks)
                 (if (member (car block) used)
                     `(,num ,used ,(append blocks (list (cons (index-of used (car block)) (cdr block)))))
                     `(,(+ num 1) ,(append used (list (car block))) ,(append blocks (list (cons num (cdr block))))))]))]
           [update-instr
            (lambda (instr ids)
              (match (car instr)
                ['goto (list 'goto (index-of ids (cadr instr)))]
                ['if (list 'if (cadr instr) (index-of ids (caddr instr)) (index-of ids (cadddr instr)))]
                [_ instr]))]
           [folded (foldl add-block `(0 () ()) (cdr program))])
      (cons (car program)
            (map (lambda (b) (cons (car b) (map (lambda (i) (update-instr i (cadr folded))) (cdr b))  )) (caddr folded))))))

; division
; ASSUMPTION: division contains only static variables!
(define is_var_static_by_division
  (lambda (x names)
    (if (member x names) #t #f)))
(define is_exp_static_by_division
  (lambda (exp names)
    (match exp
      [`(quote ,c) #t]
      [`(list ,l ...) (= (length (filter (lambda (e) (not (is_exp_static_by_division e names))) l)) 0)]
      [`(,op ,l) (is_exp_static_by_division l names)]
      [`(,op ,e1 ,e2) (and (is_exp_static_by_division e1 names) (is_exp_static_by_division e2 names))]
      [`,x (is_var_static_by_division x names)]
     )))

(define (make_paired_acc acc l1 l2) (if (or (empty? l1) (empty? l2)) acc (make_paired_acc (append acc (list (list (car l1) (car l2)))) (cdr l1) (cdr l2))))
(define (make_paired l1 l2) (make_paired_acc '() l1 l2))
(define (decompose l) (list (map car l) (map cadr l)))


(define _reduce
  (lambda (exp div)
    (match exp
      [`(quote ,c) (cons `',c #t)]

      [`(list ,l ...) (let ([res (map (lambda (e) (_reduce e div)) l)]) (cons (cons 'list (map car res)) (andmap cdr res)))]

      [`(,op ,l)
        (let ([a (_reduce l div)])
          (let ([b (car a)])
            (if (cdr a) (cons `',(my-eval `(,op ,b)) #t) (cons `(,op ,b) #f)) 
          )
        )
      ]
      
      [`(,op ,e1 ,e2)
        (let ([a (_reduce e1 div)] [b (_reduce e2 div)]) (let ([aa (car a)] [bb (car b)])
            (if (and (cdr a) (cdr b))
                (cons `',(my-eval `(,op ,aa ,bb)) #t) (cons `(,op ,aa ,bb) #f)) 
          )
        )
      ]

      [`(,op ,e1 ,e2 ,e3)
        (let ([a (_reduce e1 div)] [b (_reduce e2 div)]  [c (_reduce e3 div)])
          (let ([aa (car a)] [bb (car b)] [cc (car c)])
            (if (and (cdr a) (cdr b)) (cons `',(my-eval `(,op ,aa ,bb ,cc)) #t) (cons `(,op ,aa ,bb ,cc) #f)) 
          )
        )
      ]

      [(? number? n) (cons `',n #t)]
      [`,x (if (is_var_static_by_division x (car (decompose div))) (cons (car (st-lookup div x)) #t) (cons x #f))] 
    )
  )
)

(define reduce
  (lambda (exp div)
    (let ([result (car (_reduce exp div))])
      result
    )
  )
)

(define make-list-st
  (lambda (ks vs)
    (make_paired ks vs)))

(define make-pending-list
  (lambda (prog st)
    (list (list (caadr prog) st))))
  

(define pending-append
  (lambda (p st pending)
    (append pending (list (list p st)))))

(define list-st-set
  (lambda (st k v)
     (let ([names (car (decompose st))]
           [values (cadr (decompose st))])
    (if (member k names)
        (make_paired names (list-set values (index-of names k) v))
        (append st (list (list k v)))))))
    

(define set-marked
  (lambda (pp st marked )
    (cons (list pp st) marked)))

(define is-marked
  (lambda (p st marked)
    (member (list p st) marked)))

(define add-pending-if-not-marked
  (lambda (p st pending marked )
    (if (is-marked p st marked) pending (pending-append p st pending))))

(define make-st-label
  (lambda (p st)
    (list p '@ st)))

(define make-if
  (lambda (arg e1 e2)
    (list 'if arg e1 e2)))

(define make-return
  (lambda (arg)
    (list 'return arg)))

(define make-ass
  (lambda (a b)
     (list ':= a b)))