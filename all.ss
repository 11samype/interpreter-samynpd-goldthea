;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

;(load "chez-init.ss") 



;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

;; Parsed expression datatypes

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure (params (list-of symbol?))
			(body expression?)
			(env environment?)])
	 
	 
	 
	
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))
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
	(params (lambda (x) (or (symbol? x) (pair? x) (null? x))))
	(body expression?)]
  [quote-exp
	(arg scheme-value?)]
  )


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
       [else (app-exp (parse-exp (1st datum))
		      (map parse-exp (cdr datum)))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

(define validate-if
	(lambda (exp)
		(if (and (> (length exp) 2) (< (length exp) 5))
			#t
			(eopl:error 'parse-exp "if-expression ~s does not have (only) test, then, and else" exp))))






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



; To be added later









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
				(map (lambda (e)(eval-exp e env)) 
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
	  [lambda-exp (params body)
		(closure params body env)]
	  [letrec-exp 
		(proc-names idss bodies letrec-body)
		(eval-exp letrec-body
			(extend-env-recursively 
				proc-names idss bodies env))]
	  [quote-exp (arg)
		arg]
	  
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))

; evaluate the list of operands, putting results into a list

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
		(let ([extended-env (extended-env params args env)])
			(eval-exp body extended-env))]
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(+ - * add1 sub1 cons =))

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
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
	  [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
	  [(car) (car (args))]
	  [(>=) (or (apply > args) (apply = args))]
      [(=) (= (1st args) (2nd args))]
	  [(zero?) (= (1st args) 0)]
	  [(null?) (= (1st args) '())]
	  [(eq?) (eq? (1st args) (2nd args))]
	  [(equal?) (equal? (1st args) (2nd args))]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "ヽ༼ຈل͜ຈ༽ﾉ ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))









