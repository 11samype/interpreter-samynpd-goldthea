;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+
	
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))
   
 ; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure (params (list-of symbol?))
			(body expression?)
			(env environment?)]
			
  [closure1 (params (list-of symbol?))
			(body expression?)
			(env environment?)]
	)
 
;; Parsed expression datatypes

(define-datatype expression expression?
  [var-exp        ; variable references
   (id symbol?)]
  [lit-exp        ; "Normal" data.  Did I leave out any types?
   (datum
    (lambda (x)
      (ormap 
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? pair? null?))))]
  [app-exp        ; applications
   (rator expression?)
   (rands (list-of expression?))]
  [letrec-exp
	(proc-names (list-of symbol?))
	(idss (list-f (list-of symbol?)))
	(bodies (list-of expression?))
	(letrec-body expression?)]
  [if-exp 
	(test-exp expression?)
	(then-exp expression?)
	(else-exp expression?)]
  [if-2-exp 
	(test-exp expression?)
	(then-exp expression?)]
  [let-exp
	(syms (list-of symbol?))
	(exprs (list-of expression?))
	(bodies (list-of expression?))]
  [lambda-exp
	(params (list-of symbol?))
	(body (list-of expression?))]
  [lambda-exp-parenless
	(params (list-of symbol?))
	(body (list-of expression?))]

  [and-exp
	(body (list-of expression?))]
  [or-exp
    (body (list-of expression?))]

  [lambda-exp-improper
	(params (improper-checker))
	
  [quote-exp
	(arg scheme-value?)]
  )

  (define improper-checker
	(lambda (x)
		(and (not (list? x)) (pair? x))))

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define parse-exp
  (lambda (datum)
    (cond
     [(symbol? datum) (var-exp datum)]
     [(or (number? datum)
          (string? datum)
          (vector? datum)
          (boolean? datum)
          (null? datum)) (lit-exp datum)]
     [(pair? datum)
      (cond
	    [(and (eqv? (car datum) 'let)
			  (validate-let datum))
		   (let-exp ;(car datum)
			 (map car (cadr datum))
			 (map parse-exp (map cadr (cadr datum)))
			 (map parse-exp (cddr datum)))]
		[(eqv? (car datum) 'quote) (if (= (length datum) 2)
                                      (quote-exp (cadr datum))
                                      (eopl:error 'parse-exp "bad quote: ~s" datum))]
		[(and (eqv? (car datum) 'if) (validate-if datum))
	     (if (= (length datum) 4)
		 (if-exp 
		   (parse-exp (cadr datum))
		   (parse-exp (caddr datum))
		   (parse-exp (cadddr datum)))
		 (if-2-exp
		   (parse-exp (cadr datum))
		   (parse-exp (caddr datum))))]

		   ;;;;;;;;;;;;;;;;;;;;;;;;; lambda code
		   
		   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
       ((eqv? (car datum) 'lambda)
			(if (symbol? (cadr datum))
			(lambda-exp-parenless (list (cadr datum))
				(map parse-exp (cddr datum)))
			;;; error check
				(if (null? (cddr datum))
					(eopl:error 'parse-exp "no lambda body ~s" datum)
					

			(if (and (not (list? (cadr datum))) (pair? 	(cadr datum)))
			(lambda-exp-improper (cadr datum)
				(map parse-exp (cddr datum)))
				
				;error check (currently misses the improper list input)
				(if (contains-non-variable (cadr datum))
					(eopl:error 'parse-exp "non-variable input to lambda ~s" datum)	
			
			(lambda-exp (cadr datum)
				(map parse-exp (cddr datum))))))))
		   
		   ;;;;;;;;;;;;;;;;;;;;;;;
		   
		[(eqv? (car datum) 'and)
			(and-exp (map parse-exp (cdr datum)))]
		[(eqv? (car datum) 'or)
			(and-exp (map parse-exp (cdr datum)))]
		[(eqv? (car datum) 'case)
			(and-exp (map parse-exp (cdr datum)))]
		[(eqv? (car datum) 'begin)
			(and-exp (map parse-exp (cdr datum)))]
		[(eqv? (car datum) 'cond)
			(and-exp (map parse-exp (cdr datum)))]
		
       [else (app-exp (parse-exp (1st datum))
		      (map parse-exp (cdr datum)))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))
	 
(define contains-non-variable
	(lambda (list1)
		(if (null? list1)
			#f
		(if (or (number? (car list1)) (boolean? (car list1)))
			#t
		(contains-non-variable (cdr list1)))))) 
	 
	 
(define get-vars
	(lambda (list1)
		(if (null? list1)
			'()
		(if (list? (car list1))
			'()
		(cons (car list1) (get-vars (cdr list1)))))))
		
(define get-body
	(lambda (list1)
		(if (null? list1)
			'()
		(if (list? (car list1))
			list1
		(get-body (cdr list1))))))



(define validate-if
	(lambda (exp)
		(if (and (> (length exp) 2) (< (length exp) 5))
			#t
			(eopl:error 'parse-exp "if-expression ~s does not have (only) test, then, and else" exp))))

(define validate-let
	(lambda (exp)
		(if (> (length exp) 2) ; cant get to proper list check because of this?!?!?!
			(if (and (list? (cadr exp)) (first-symbols? (cadr exp)) (lists-length-2? (cadr exp)) (proper-list-2-lists? (cadr exp)))
				#t
				(eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" exp))
			(eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" exp))))

(define first-symbols?
	(lambda (x)
		(cond [(null? x) #t]
			[else (and (symbol? (caar x)) (first-symbols? (cdr x)))])))
			
(define lists-length-2?
	(lambda (ls)
		(cond [(null? ls) #t]
			[else (and (= (length (car ls)) 2) (lists-length-2? (cdr ls)))])))
			
(define proper-2-list?
	(lambda (ls)
		(list? (cdr ls))))
		
(define proper-list-2-lists?
	(lambda (ls)
		(cond [(null? ls) #t]
			[else (and (proper-2-list? (car ls)) (proper-list-2-lists? (cdr ls)))])))

;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+

; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
      [empty-env-record ()
        (fail)]
      [extended-env-record (syms vals env)
		(let ([pos (list-find-position sym syms)])
      	  (if (number? pos)
	      (succeed (list-ref vals pos))
	      (apply-env env sym succeed fail)))])))

;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

; needs:
; and
; or
; begin
; let*
; case
(define syntax-expand
  (lambda (exp)
  
	(cases expression exp
		
	)
    ;(cond
	
	 ;[(equal? (car datum) 'cond) (cond-expand datum)]
	 
	 ;[(and (equal? (caar datum) 'lambda) (symbol? (cadar datum))) (lambda-paren-expand datum)]
	
	 [else datum]));)
	 
(define cond-test-getter
	(lambda (expression)
		(if (null? expression)
			'()
		(cons (caar expression) (cond-test-getter (cdr expression))))))
		
(define cond-body-getter
	(lambda (expression)
		(if (null? expression)
			'()
		(cons (cadar expression) (cond-body-getter (cdr expression))))))
		
(define cond-expand
	(lambda (cond-expression)
		(cond-expand-helper (cond-test-getter (cdr cond-expression)) (cond-body-getter (cdr cond-expression)))))
		
(define cond-expand-helper
	(lambda (test-list body-list)
		(if (null? (cdr test-list))
			(if (eqv? (car test-list) 'else)
				(car body-list)
		(list 'if (car test-list) (car body-list)))
		(list 'if (car test-list) (car body-list)
				  (cond-expand-helper (cdr test-list) (cdr body-list)))
		)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form init-env)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (let ([identity-proc (lambda (x) x)])
  (lambda (exp env)
	(cases expression exp
		[lit-exp (datum) datum]
		[var-exp (id) ; look up its value.
			(apply-env env id
				identity-proc ; procedure to call if var is in env
;					(lambda () ; procedure to call if var is not in env
;						(apply-env global-env ; was init-env
;							id
;							identity-proc
							(lambda () 
								(error 'apply-env
										"variable ~s is not bound" 
										id)))]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
	  [let-exp (syms exprs bodies)
		(let ([extended-env
			(extend-env syms
				(map (lambda (e) (eval-exp e env)) 
					exprs) 
				env)])
		(let loop ([bodies bodies]) 
			(if (null? (cdr bodies))
				(eval-exp (car bodies) extended-env)
				(begin (eval-exp (car bodies) extended-env) 
					(loop (cdr bodies))))))]
	  [if-exp (test-exp then-exp else-exp)
		(if (eval-exp test-exp env)
			(eval-exp then-exp env)
			(eval-exp else-exp env))]
	  [if-2-exp (test-exp then-exp)
		(if (eval-exp test-exp env)
			(eval-exp then-exp env))]
	  [lambda-exp (params bodys)
		(run-multiple-lambda-bodys closure params bodys env)]
	  [lambda-exp-parenless (params bodys)
	    (run-multiple-lambda-bodys closure1 params bodys env)]
	  [lambda-exp-improper (params bodys)
		(run-multiple-lambda-bodys closure params bodys env)]
;	  [letrec-exp 
;		(proc-names idss bodies letrec-body)
;		(eval-exp letrec-body
;			(extend-env-recursively 
;				proc-names idss bodies env))]
	  [quote-exp (arg)
		arg]
	  
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))
	  
(define run-multiple-lambda-bodys
	(lambda (closure1 params bodys env)
		(if (null? (cdr bodys))
			(closure1 params (car bodys) env)
			(begin
			(closure1 params (car bodys) env)
			(run-multiple-lambda-bodys closure1 params (cdr bodys) env)))))


(define eval-rands
  (lambda (rands env)
    (map (lambda (e)
		(eval-exp e env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
	  
	  [closure (params body env)
		(let ([extended-env (extend-env params  args env)])
			(eval-exp body extended-env))]
			
	  [closure1 (params body env)
		(let ([extended-env (extend-env params  (list args) env)])
			(eval-exp body extended-env))]
	
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))
					
(trace apply-proc)

(define *prim-proc-names* '(+ - * / add1 sub1 set-car! set-cdr! not car cdr caar cadr cadar symbol? list list? list->vector vector->list vector? vector vector-ref number? length pair? cons >= = > < <= zero? null? eq? equal? procedure? map apply))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))
	 
(define global-env init-env)

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc [(+) (apply + args)]  [(-) (apply - args)]
 [(*) (apply * args)]  [(/) (apply / args)]  [(add1) (+ (1st args) 1)]
 [(sub1) (- (1st args) 1)]  [(not) (not (1st args))]  [(cons) (cons (1st args) (2nd args))]
 [(car) (car (1st args))]  [(cdr) (cdr (1st args))] [(list) args]
 [(list?) (list? (1st args))]  [(list->vector) (list->vector (1st args))]
 [(vector->list) (vector->list (1st args))]  [(vector?) (vector? (1st args))]
 [(vector) (list->vector args)]  [(vector-ref) (vector-ref (1st args) (2nd args))]
 [(number?) (number? (1st args))]  [(symbol?) (symbol? (1st args))]
 [(caar) (caar (1st args))]  [(cadr) (cadr (1st args))]  [(cadar) (cadar (1st args))]
 [(length) (length (1st args))]  [(pair?) (pair? (1st args))]  [(<) (apply < args)]
 [(>) (apply > args)]  [(<=) (or (apply < args) (apply = args))]
 [(>=) (or (apply > args) (apply = args))]  [(=) (= (1st args) (2nd args))]
 [(zero?) (= (1st args) 0)] [(null?) (null? (1st args))]
 [(eq?) (eq? (1st args) (2nd args))]  [(equal?) (equal? (1st args) (2nd args))]
 [(set-car!) (set-car! (1st args) (2nd args))]
 [(set-cdr!) (set-cdr! (1st args) (2nd args))]
 [(procedure?) (proc-val? (1st args))]
	  [(map) (cases proc-val (1st args)
				[prim-proc (op)
					(if (null? (cadr args))
						'()
						(cons (apply-prim-proc op (list (caadr args)))
							 (apply-prim-proc 'map (list (1st args) (cdadr args)))))]
				[closure (params body env)
					(if (null? (cadr args))
						'()
						(cons (apply-prim-proc (1st args) (list (caadr args)))
							 (apply-prim-proc 'map (list (1st args) (cdadr args)))))])]
	  [(apply) (cases proc-val (1st args)
				[prim-proc (op)
					(apply-prim-proc op (apply-helper-all-list (cdr args)))]
					[else +])]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))
			
(define apply-helper-all-list
	(lambda (args)
		(cond [(null? args) '()]
			[(list? (car args)) (append (car args) (apply-helper-all-list (cdr args)))]
			[else (cons (car args) (apply-helper-all-list (cdr args)))])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "ヽ༼ຈل͜ຈ༽ﾉ ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp (syntax-expand x)))))

