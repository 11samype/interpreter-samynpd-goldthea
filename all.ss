;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+
	
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms improper-or-regular)
   (vals (list-of box?))
   (env environment?)]
  [recursively-extended-env-record
   (procnames (list-of symbol?))
   (idss (list-of (list-of symbol?)))
   (bodies  (list-of expression?))
   (old-env environment?)])
   
  
  (define improper-checker
	(lambda (x)
		(and (not (list? x)) (pair? x))))
		
  (define improper-or-regular
	(lambda (x)
		(or ((list-of symbol?) x) (improper-checker x))))

 ; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure (params symbol-or-list?)
			(body expression-or-list)
			(env environment?)]
	)
 
 (define symbol-or-list?
	(lambda (x)
		(or (symbol? x) (list-of symbol? x))))

 (define expression-or-list
	(lambda (x)
		(or (expression? x) ((list-of expression?) x)))) 
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
	(proc-args (list-of (list-of symbol?)))
	(proc-bodies (list-of expression?))
	(letrec-body (list-of expression?))]
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
	(params symbol?)
	(body (list-of expression?))]
  [cond-exp
	(tests (list-of expression?))
	(bodies (list-of expression?))]
  [begin-exp
	(bodies (list-of expression?))]
  [and-exp
	(bodies (list-of expression?))]
  [or-exp
	(bodies (list-of expression?))]
  [case-exp
	(test (lambda (x) (or (symbol? x) (number? x) (pair? x))))
	(lists (lambda (x) (or (symbol? x) (number? x) (pair? x))))
	(bodies (list-of expression?))]
  [while-exp
	(test expression?)
	(body (list-of expression?))]
  [lambda-exp-improper
	(params improper-checker)
	(body (list-of expression?))]
  [quote-exp
	(arg scheme-value?)]
 [set!-exp
	(variable symbol?)
	(new-value expression?)]
	
  [named-let-exp
	(proc-name symbol?)
	(arg-names (list-of symbol?))
	(internal-bodies (list-of expression?))
	(external-body (list-of expression?))]
  )
;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
; for letrec
	; 1st after letrec = proc name
	; 2nd after letrec = proc args
	; 3rd after letrec = inside the lambdas
	; expand proc bodies and arg bodies
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
		[(and (eqv? (car datum) 'let) (symbol? (cadr datum)))
		; named let
		(named-let-exp
			(cadr datum)
			(map car (caddr datum))
			(map parse-exp (map cadr (caddr datum)))
			(list (parse-exp (cadddr datum))))]
		
		
	    [(and (eqv? (car datum) 'let)
			  (validate-let datum))
		   (let-exp ;(car datum)
			 (map car (cadr datum))
			 (map parse-exp (map cadr (cadr datum)))
			 (map parse-exp (cddr datum)))]
		[(eqv? (car datum) 'letrec)
			(letrec-exp ;(car datum)
			 (map car (cadr datum)) ; proc-names
			 (map cadr (map cadr (cadr datum))) ; proc-args
			 (map parse-exp (map caddr (map cadr (cadr datum)))) ; proc-bodies
			 (map parse-exp (cddr datum))) ; letrec-body
			 ]
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
       ((eqv? (car datum) 'lambda)
			(if (symbol? (cadr datum))
			(lambda-exp-parenless (cadr datum)
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
			(or-exp (map parse-exp (cdr datum)))]
;		[(eqv? (car datum) 'case)
;			(case-exp (cadr datum) (map car (cddr datum)) (map parse-exp (map cadr (cddr datum))))]
		[(eqv? (car datum) 'set!)
			(set!-exp (cadr datum) (parse-exp (caddr datum)))]
		[(eqv? (car datum) 'begin)
			(begin-exp (map parse-exp (cdr datum)))]
		[(eqv? (car datum) 'cond)
			(cond-exp (map parse-exp (map car (cdr datum))) (map parse-exp (map cadr (cdr datum))))]
		[(eqv? (car datum) 'while)
			(while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))]
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
    (extended-env-record syms (map box vals) env)))

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

;(define apply-env
;  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
;    (cases environment env
;      [empty-env-record ()
;       (fail)]
;      [extended-env-record (syms vals env)
;		(let ([pos (list-find-position sym syms)])
 ;     	  (if (number? pos)
;	      (succeed (list-ref vals pos))
;	      (apply-env env sym succeed fail)))]
;	  [recursively-extended-env-record
;		(procnames idss bodies old-env)
;		(let ([pos
;			(list-find-position sym procnames)])
;		 (if (number? pos)
;			(closure (list-ref idss pos)
;						(list (list-ref bodies pos))
;						env)
;			(apply-env old-env sym succeed fail)))])))
			
			
(define apply-env-ref
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
      [empty-env-record ()
        (fail)]
      [extended-env-record (syms vals env)
		(let ([pos (list-find-position sym syms)])
      	  (if (number? pos)
	      (succeed (list-ref vals pos))
	      (apply-env-ref env sym succeed fail)))]
	  [recursively-extended-env-record
		(procnames idss bodies old-env)
		(let ([pos
			(list-find-position sym procnames)])
		 (if (number? pos)
			(closure (list-ref idss pos)
						(list (list-ref bodies pos))
						env)
			(apply-env-ref old-env sym succeed fail)))])))

(define apply-env
	(lambda (env sym succeed fail)
		(unbox (apply-env-ref env sym succeed fail))))

; still have to deal with recursive extend-env
(define extend-env-recursively
	(lambda (proc-names idss bodies old-env)
		(recursively-extended-env-record 
			proc-names idss bodies old-env)))

;(define extend-env-recursively
;	(lambda (proc-names idss bodies old-env)
;		(let ([len (langth proc-names)])
;			(let ([vec (make-vector len)])
;				(let ([env (extended-env-record
;							proc-name vec old-env)])
;					(for-each
;						(lambda (pos ids body)
;							(vector-set! vec
;										pos
;										(closure ids body env)))
;						(iota len)
;						idss
;						bodies
;						)
;					env)))))

(define iota
	(lambda (len)
		(reverse (iota-helper len))))

(define iota-helper
	(lambda (len)
		(cond [(zero? len) '()]
			[else (cons (- len 1) (iota-helper (- len 1)))])))

;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+

(define syntax-expand
  (lambda (exp)
	(cases expression exp
		[lit-exp (datum) exp]
		[var-exp (id) exp]
		[app-exp (rator rands)
			(app-exp (syntax-expand rator) (map syntax-expand rands))]
		;[let-exp (syms exprs bodies)
		;	(let-exp syms (map syntax-expand exprs) (map syntax-expand bodies))]
			
		[let-exp (syms exprs bodies)
			(app-exp (lambda-exp syms (map syntax-expand bodies)) (map syntax-expand exprs))]
			
		[letrec-exp (procnames proc-args proc-bodies letrec-body) 
			(let ([syms procnames] [vals (make-lambda proc-args proc-bodies)] [body letrec-body])
				   (syntax-expand (let-exp syms vals (list (letrec-to-set syms vals (map syntax-expand body))))))]
			   
		[if-exp (test-exp then-exp else-exp)
			(if-exp (syntax-expand test-exp)
					(syntax-expand then-exp)
					(syntax-expand else-exp))]
		[if-2-exp (test-exp then-exp)
			(if-2-exp (syntax-expand test-exp)
					(syntax-expand then-exp))]
		[lambda-exp (params bodies)
			(lambda-exp params (map syntax-expand bodies))]
		[lambda-exp-parenless (params bodies)
			(lambda-exp-parenless params (map syntax-expand bodies))]
		[lambda-exp-improper (params bodies)
			(lambda-exp-improper params (map syntax-expand bodies))]
		[quote-exp (arg) exp]
		[cond-exp (tests bodies)
			(cond-expand tests bodies)]
		[begin-exp (bodies)
			(app-exp (lambda-exp '() (map syntax-expand bodies)) '())]
		[and-exp (bodies)
			(and-expand (map syntax-expand bodies))]
		[or-exp (bodies)
			(or-expand (map syntax-expand bodies))]
		[case-exp (test lists bodies)
			(case-expand test lists bodies (empty-env))]
		[while-exp (test body)
                 (while-exp (syntax-expand test)
                            (map syntax-expand body))]
		[named-let-exp (proc-name arg-names internal-bodies external-body)
		(named-let-expand proc-name arg-names internal-bodies external-body)]
		[set!-exp (variable new-value)	
		(set!-exp variable (syntax-expand new-value))]
		[else (eopl:error 'syntax-expand "Bad abstract syntax: ~a" exp)]
	)))
	
(define letrec-to-set
  (lambda (names vals body)
    (if (null? names) (let-exp '() '()  body)
    (let ((l (letrec-to-set (cdr names) (cdr vals) body)))
      (let-exp '(temp) (list (car vals)) (list (set!-exp (car names) (var-exp 'temp)) l))))))
	
(define set!-h
	(lambda (ids vals)
		(cond 	[(null? ids) '()]
				[else (cons (set!-exp (car ids) (car vals)) (set!-h (cdr ids) (cdr vals)))])))

;(define make-t-list
;	(lambda (proc-args t-list count)
;			(cond [(null? (cdr proc-args)) (make-string
	
(define make-set!
	(lambda (variables new-values)
		(cond [(null? (cdr variables)) (set!-exp (car variables) (car new-values))]
			[else (cons (set!-exp (car variables) (car new-values)) (make-set! (cdr variables) (cdr new-values)))])))
	
(define make-lambda
	(lambda (params-ls bodies-ls)
		(cond [(null? (cdr params-ls)) (list (lambda-exp (car params-ls) (list (car bodies-ls))))]
			[else (cons (lambda-exp (car params-ls) (list (car bodies-ls))) (make-lambda (cdr params-ls) (cdr bodies-ls)))])))
	
(define named-let-expand
	(lambda (proc-name arg-names internal-bodies external-body)
		(letrec-exp (list proc-name)
		
					(list arg-names) 
					
					external-body
					
					 (list (app-exp (var-exp proc-name) internal-bodies)))))

;(define case-expand
;	(lambda (test lists bodies)
;		(let-exp '(x) test (lists-bodies->if lists bodies))))
		
;(define lists-bodies->if
;	(lambda (lists bodies)
;		(if (null? (cdr lists))
;			(let loop ([ls (car lists)] [body (car bodies)])
;				(if-exp (
;			(list-body->if (car lists) (car bodies))
;			(list-body->if (car lists) (car bodies)))))
			
(define case-expand
  (lambda (test lists bodies env)
    (cond [(null? lists) '()]
          [(equal? 'else (car lists))
           (car bodies)]
          [(contains? (eval-exp (parse-exp test) env) (car lists)) (car bodies)]
          [else (case-expand test (cdr lists) (cdr bodies) env)])))
	
(define or-expand
	(lambda (bodies)
	 (if (null? bodies) (lit-exp #f)
		(if (null? (cdr bodies))
			(if-exp (syntax-expand (car bodies)) (syntax-expand (car bodies)) (lit-exp '#f))
			(if-exp (syntax-expand (car bodies)) (syntax-expand (car bodies)) (or-expand (cdr bodies)))))))

(define and-expand
	(lambda (bodies)
	 (if (null? bodies) (lit-exp #t)
		(if (null? (cdr bodies))
			(if-exp (syntax-expand (car bodies)) (syntax-expand (car bodies)) (lit-exp '#f))
			(if-exp (syntax-expand (car bodies)) (and-expand (cdr bodies)) (lit-exp '#f))))))

(define cond-expand
	(lambda (tests bodies)
		(if (null? (cdr tests))
			(if (equal? (car tests) (var-exp 'else))
				(syntax-expand (car bodies))
				(if-2-exp (syntax-expand (car tests)) (syntax-expand (car bodies))))
			(if-exp (syntax-expand (car tests)) (syntax-expand (car bodies)) (cond-expand (cdr tests) (cdr bodies))))))
			
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
							(lambda () 
								(error 'apply-env
										"variable ~s is not bound" 
										id)))]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
;	  [let-exp (syms exprs bodies)
;		(let ([extended-env
;			(extend-env syms
;				(map (lambda (e) (eval-exp e env)) 
;					exprs) 
;				env)])
;		(let loop ([bodies bodies]) 
;			(if (null? (cdr bodies))
;				(eval-exp (car bodies) extended-env)
;				(begin (eval-exp (car bodies) extended-env) 
;					(loop (cdr bodies))))))]
	  [if-exp (test-exp then-exp else-exp)
		(if (eval-exp test-exp env)
			(eval-exp then-exp env)
			(eval-exp else-exp env))]
	  [if-2-exp (test-exp then-exp)
		(if (eval-exp test-exp env)
			(eval-exp then-exp env))]
	  [lambda-exp (params bodys)
		(closure params bodys env)]
	  [lambda-exp-parenless (params bodys)
	    (closure params bodys env)]
	  [lambda-exp-improper (params bodys)
	    (closure params bodys env)]

	  [letrec-exp 
		(proc-names proc-args proc-bodies letrec-body)
		(car (map (lambda (e) (eval-exp e 
			(extend-env-recursively 
				proc-names proc-args proc-bodies env))) letrec-body))]
	  [quote-exp (arg) arg]
	  [while-exp (test body)
		(let loop ([cond (eval-exp test env)])
				   (if cond
                       (let loop2 ((bodies body))
						 (if (null? bodies)
                             (loop (eval-exp test env))
                             (begin (eval-exp (car bodies) env)
                                    (loop2 (cdr bodies)))))))]
	  [set!-exp (variable new-value)
		(set-box! 
			(apply-env-ref env variable (lambda (x) x) (lambda () (eopl:error "set! unfound input variable")))
			(eval-exp new-value env))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))

(define eval-rands
  (lambda (rands env)
    (map (lambda (e)
		(eval-exp e env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define eval-begin
	(lambda (ls env)
		(if (null? (cdr ls))
			(begin (eval-exp (car ls) env))
			(begin
				(eval-exp (car ls) env)
				(eval-begin (cdr ls) env)))))

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
	  
	  [closure (params bodies env)

		(eval-begin bodies (extend-env params args env))

	  ]

      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
           		   proc-value)])))
				   
(define improper-list-remover
	(lambda (list1)
		(if (symbol? list1)
			(cons list1 '())
		(cons (car list1) (improper-list-remover (cdr list1))))))
			
(define extend-n
	(lambda (length1 value)
		(if (zero? length1)
		'()
	(cons value (extend-n (- length1 1) value)))))

(define *prim-proc-names* '(+ - * / add1 sub1 set-car! set-cdr! not car cdr caar cadr cadar symbol? list list? list->vector vector->list vector? vector vector-ref number? length pair? cons >= = > < <= zero? null? eq? equal? procedure? map apply quotient vector-set! eqv? list-tail append))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))
	 
(define global-env init-env)
	
	
(define reset-global-env
  (lambda ()
    (set! global-env (extend-env
                      *prim-proc-names*
                      (map prim-proc
                           *prim-proc-names*)
                      (empty-env)))))

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
 [(quotient) (quotient (1st args) (1st args))]
 [(set-car!) (set-car! (1st args) (2nd args))]
 [(set-cdr!) (set-cdr! (1st args) (2nd args))]
 [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
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
						(cons (apply-proc (1st args) (list (caadr args)))
							 (apply-prim-proc 'map (list (1st args) (cdadr args)))))
							 ])]
	  [(apply) (cases proc-val (1st args)
				[prim-proc (op)
					(apply-prim-proc op (apply-helper-all-list (cdr args)))]
					[else +])]
	  [(append) (append (1st args) (2nd args))]
	  [(eqv?) (eqv? (1st args) (2nd args))]
	  [(list-tail) (list-tail (1st args) (2nd args))]
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
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))

; set! stuff

	; box stuff
;http://docs.racket-lang.org/reference/boxes.html

; use boxes
;(cell value) = (box value)
;(cell? obj) = (box? obj)
;(cell-ref cell) = (unbox cell)
;(cell-set! cell value) (set-box! cell value)


;;; todo list
; 1, do define stuff
; 2, test global set!
; 3, syntax exapand letrec