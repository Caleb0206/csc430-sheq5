#lang typed/racket
(require typed/rackunit)

;; SHEQ5
;; Fully finished SHEQ5 assignment with game, too.

;; Data definitions

;; Value - Numbers, Booleans, String, CloV, PrimV
(define-type Value (U Real Boolean String CloV PrimV))

;; CloV - Closures contain list of symbol params, body of ExprC, Env
(struct CloV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)

;; PrimV - Represents a primitive operator by its symbol
(struct PrimV ([op : Symbol]) #:transparent)

;; LamC - Lambdas contain a list of symbol args, and a body of ExprC
(struct LamC ([args : (Listof Symbol)] [body : ExprC]) #:transparent)

;; Binding : pair of a Symbol and a Value
(struct Binding ([name : Symbol] [val : Value]) #:transparent)

;; Env : a list of Bindings
(define-type Env (Listof Binding))

;; ExprC type : NumC, IfC, IdC, AppC, LamC, StringC
(define-type ExprC (U NumC IfC IdC AppC LamC StringC))

;; NumC : a Real
(struct NumC ([n : Real]) #:transparent)

;; StringC : a String
(struct StringC ([s : String]) #:transparent)

;; IdC : a symbol representing an ID
(struct IdC ([name : Symbol]) #:transparent)

;; IfC : an if statement of ExprC, and ExprC's to act on if true or false
(struct IfC ([v : ExprC] [iftrue : ExprC] [iffalse : ExprC]) #:transparent)

;; AppC : Represents a function application.function ExprC with a list of arg ExprC's
(struct AppC ([expr : ExprC] [args : (Listof ExprC)]) #:transparent)

;; Top level environment
(: top-env Env)
(define top-env (list
                 (Binding 'true #t)
                 (Binding 'false #f)
                 (Binding '+ (PrimV '+))
                 (Binding '- (PrimV '-))
                 (Binding '* (PrimV '*))
                 (Binding '/ (PrimV '/))
                 (Binding '<= (PrimV '<=))
                 (Binding 'equal? (PrimV 'equal?))
                 (Binding 'substring (PrimV 'substring))
                 (Binding 'strlen (PrimV 'strlen))
                 (Binding 'error (PrimV 'error))
                 (Binding 'println (PrimV 'println))
                 (Binding 'read-num (PrimV 'read-num))
                 (Binding 'read-str (PrimV 'read-str))
                 (Binding '++ (PrimV '++))
                 (Binding 'rnd (PrimV 'rnd))
                 (Binding 'round (PrimV 'round))
                 (Binding 'ceil (PrimV 'ceil))
                 (Binding 'floor (PrimV 'floor))))

;; reserved-keywords - a list of key-words
(define reserved-keywords '(if lambda let = in end : else))

;; ---- Interpreters ----

;; top-interp - Parse and evaluate the S-exp, return a serialized String result
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

;; interp - takes the complete AST (ExprC) with an Env, returning a Value
(define (interp [e : ExprC] [env : Env]) : Value
  ; template
  #;(match e
      [numc -> number]
      [stringc -> s]
      [ifc -> eval if expr]
      [LamC -> CloV params body env]
      [AppC -> interp CloV or PrimV]
      [Idc -> get binding])

  ; body
  (match e
    [(NumC n) n]
    [(StringC s) s]
    [(IfC v if-t if-f)
     (define test-val (interp v env))
     (cond
       [(boolean? test-val)
        (if test-val
            (interp if-t env)
            (interp if-f env))]
       [else (error 'interp "SHEQ: If expected boolean test, got ~a" test-val)])]
    [(LamC params body) (CloV params body env)]
    [(AppC (IdC 'seq) exprs)
     (interp-seq exprs env)]
    [(AppC lam args)
     (define f-val (interp lam env))
     (define arg-vals
       (for/list : (Listof Value) ([a args])
         (interp a env)))
     (cond
       [(CloV? f-val)
        (if (equal? (length arg-vals) (length (CloV-params f-val)))
            (interp (CloV-body f-val)
                    (append (map Binding (CloV-params f-val) arg-vals)
                            (CloV-env f-val)))
            (error 'interp "SHEQ: Incorrect number of arguments for CloV, got ~a expected ~a"
                   (length (CloV-params f-val))
                   (length arg-vals)))]
        
       [(PrimV? f-val)
        (interp-prim f-val arg-vals)]
       [else
        (error 'interp "SHEQ: Attempted to apply non function value ~a" f-val)])]         
    [(IdC id) (get-binding-val id env)]))

;; interp-seq - takes a list of ExprC's to interpret them sequentially, returns the last expression's Value
(define (interp-seq [exprs : (Listof ExprC)] [env : Env]) : Value
  (match exprs
    ['() (error 'interp "SHEQ: seq needs at least 1 expression.")]
    [(list f) (interp f env)]
    [(cons f rest) (begin (interp f env) (interp-seq rest env))]))

;; interp-prim - takes a PrimV and a list of Values, returns a Value
(define (interp-prim [p : PrimV] [args : (Listof Value)]) : Value
  (match (PrimV-op p)
    ['+
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (+ a b)]
          [else (error 'interp-prim "SHEQ: PrimV + expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['*
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (* a b)]
          [else (error 'interp-prim "SHEQ: PrimV * expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['-
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (- a b)]
          [else (error 'interp-prim "SHEQ: PrimV - expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['/
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b) (not (equal? b 0))) (/ a b)]
          [(and (real? a) (real? b) (equal? b 0))
           (error 'interp-prim "SHEQ: Divide by zero error")]
          [else (error 'interp-prim "SHEQ: PrimV / expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['<=
     (match args
       [(list a b)
        (cond
          [(and (real? a) (real? b)) (<= a b)]
          [else (error 'interp-prim "SHEQ: PrimV <= expected 2 numbers, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['equal?
     (match args
       [(list a b)
        (cond [(or (CloV? a) (CloV? b) (PrimV? a) (PrimV? b)) #f]
           
              [else (equal? a b)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments")])]
    ['substring
     (match args
       [(list s start stop)
        (cond
          [(and (string? s)
                (natural? start)
                (natural? stop)
                (>= start 0)
                (< start (string-length s))
                (>= stop 0)
                (< stop (string-length s)))
           (substring s (inexact->exact start) (inexact->exact stop))]
          [else
           (error 'interp-prim "SHEQ: Substring needs string and 2 valid natural indices, got ~a" args)])]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 3, got ~a" (length args))])]
    ['strlen
     (match args
       [(list s)
        (if (string? s)
            (string-length s)
            (error 'interp-prim "SHEQ: Syntax error, ~a is not a string" s))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 1, got ~a" (length args))])]
    ['error
     (match args
       [(list v)
        (error 'interp-prim "SHEQ: user-error ~a" (serialize v))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 1, got ~a" (length args))])]
    ['println
     (match args
       [(list s)
        (if (string? s)
            (begin
              (displayln s)
              #t)
            (error 'interp-prim "SHEQ: Attempted to print a non-string value, got ~a" s))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 1, got ~a" (length args))])]
    ['read-num
     (match args
       ['()
        (begin
          (display "> ")
          ;; (flush-output)
          (define input (read-line))
          (cond
            [(eof-object? input)
             (error 'interp-prim "SHEQ: read-num read EOF")]
            [else
             (define num (string->number input))
             (if (real? num)
                 num
                 (error 'interp-prim "SHEQ: read-num expected a Number, got ~a" input))]))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 0, got ~a" (length args))])]
    ['read-str
     (match args
       ['()
        (begin
          (display "> ")
          ;; (flush-output)
          (define input (read-line))
          (if (eof-object? input)
              (error 'interp-prim "SHEQ: read-str read EOF")
              input))]
       [_ (error 'interp-prim "SHEQ: Incorrect number of arguments, expected 0, got ~a" (length args))])]
    ['++
     (match args
       ['() ""]
       [_ (apply string-append (map val->string args))])]
    ['rnd (random)]
    ['round (match args
              [(list (? real? n)) (round n)]
              [_ (error 'interp-prim
                        "SHEQ: Incorrect number or type of arguments for round procedure, expected 1 real, got ~a"
                        args)])]
    ['ceil (match args
             [(list (? real? n)) (ceiling n)]
             [_ (error 'interp-prim
                       "SHEQ: Incorrect number or type of arguments for ceil procedure, expected 1 real, got ~a"
                       args)])]
    ['floor (match args
              [(list (? real? n)) (floor n)]
              [_ (error 'interp-prim
                        "SHEQ: Incorrect number or type of arguments for floor procedure, expected 1 real, got ~a"
                        args)])]
    [_
     (error 'interp-prim "SHEQ: Invalid PrimV op, got ~a" args)]))


;; ---- Parser ---- 
;; parse - takes a S-exp and returns concrete syntax in ExprC AST
(define (parse [e : Sexp]) : ExprC
  ; template
  #;(match e
      [number -> NumC]
      [string -> StringC]
      [not reserved symbol -> idc]
      [list 'let ... -> AppC(LamC)]
      [list 'if ... -> IfC]
      [list 'lambda ... -> LamC]
      [list f args -> AppC]
      [else -> throw unknown error])
  ; body
  (match e
    ;; Match Real
    [(? real? n) (NumC n)]
    ;; Match String
    [(? string? s) (StringC s)]
    ;; Match Id
    [(? symbol? name)
     (if (reserved-symbol? name)
         (error 'parse "SHEQ: Syntax error, unexpected reserved keyword, got ~e" name)
         (IdC name))]
    ;; Match Let
    [(list 'let 
           (list (list (? symbol? args) '= vals) ...) 
           'in
           in-body
           'end)
     (define args-list (cast args (Listof Symbol)))
     (cond
       [(not (distinct-args? args-list))
        (error 'parse "SHEQ: Let binding list is invalid, duplicate variables ~a" args-list)]
       [(ormap reserved-symbol? args-list)
        (error 'parse "SHEQ: let binding list is invalid, reserved symbol was used ~a" args-list)]
       [else (AppC 
              (LamC args-list (parse in-body)) 
              (for/list : (Listof ExprC) ([v vals]) 
                (parse (cast v Sexp))))])]
    ;; Match If
    [(list 'if v iftrue iffalse)
     (IfC (parse v) (parse iftrue) (parse  iffalse))]
    ;; Match Lambda
    [(list 'lambda (list (? symbol? args) ...) ': body)
     (define args-list (cast args (Listof Symbol)))
     (if (distinct-args? args-list)
         (LamC args-list (parse body))
         (error 'parse "SHEQ: Lambda args list is invalid, duplicate parameters found, ~a" args-list))]
    ;; Match Application
    [(list f args ...)
     (AppC (parse f) (for/list : (Listof ExprC) ([a args]) (parse a)))]
    [other (error 'parse "SHEQ: Syntax error, got ~e" other)]))

;; val->string - converts a Value to a string
(define (val->string [v : Value]) : String
  (match v
    [(? real? r) (~a r)]
    [(? boolean? b) (if b
                        "true"
                        "false")]
    [(? string? s) (~a s)]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]))

;; serialize - takes a Value and returns a serialized String
(define (serialize [v : Value]) : String
  (match v
    [(? real? r) (~v r)]
    [(? boolean? b) (if b
                        "true"
                        "false")]
    [(? string? s) (~v s)]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]))

;; ---- Helper functions ----

;; get-binding-val takes a symbol and enviornment, performs a lookup and returns an ExprC if found
(define (get-binding-val [s : Symbol] [env : Env]) : Value
  (match env
    ['() (error 'get-binding "SHEQ: An unbound identifier ~a" s)]
    [(cons (Binding name val) r)
     (if (equal? s name)
         val
         (get-binding-val s r))]))

;; distinct-args? - returns true if every symbol in args is distinct 
(define (distinct-args? [args : (Listof Symbol)]) : Boolean
  (not (check-duplicates args)))

;; reserved-symbol? - Determines if a given symbol is in the reserved keywords
(define (reserved-symbol? [s : Symbol]) : Boolean
  (if (memq s reserved-keywords)
      #t
      #f))

;; create-env - takes Listof Symbol, Listof Value, an Env, and returns a new Env
(define (create-env [args : (Listof Symbol)] [vals : (Listof Value)] [env : Env]) : Env
  (match* (args vals)
    [('() '()) env]
    [('() _) (error 'create-env "SHEQ: too many values were passed in application ~a ~a" args vals)]
    [(_ '()) (error 'create-env "SHEQ: too few values were passed in application ~a ~a" args vals)]
    [((cons fa ra) (cons fv rv))
     (create-env ra rv (cons (Binding fa fv) env))]))


;; ---- Tests ----

;; Large test
; The program calculates two areas using two different functions, and then compares them.
;; The result is the result of the comparison
(define prog '{
               let
                  {[square = {lambda (x) : {* x x}}]
                   [area = {lambda (w h) : {* w h}}]
                   [gt = {lambda (v1 v2 t f) : {if {<= v1 v2} 1 0}}]}
                in
                {gt {square 4} {area 4 3} 0 1}
                end})
(check-equal? (top-interp prog) "0")

;; ---- top-interp Tests ----
(check-equal? (top-interp '{+ 3 2}) "5")
(check-equal? (top-interp '{if {<= 5 10} "less than" "not less than"}) "\"less than\"")

(check-equal? (top-interp 
               '{let {[x = 5]
                      [y = {+ 8 9}]}
                  in
                  {+ x {* y {let {[x = 3]}
                              in
                              {+ x x}
                              end}}}
                  end
                  }) "107")

(check-equal? (top-interp '{seq
                            {let ([n = 5])
                              in
                              {+ 1 n}
                              end}
                            {let ([x = 2])
                              in
                              {* 2 x}
                              end}}) "4")

;; incorect num of arguments (from handin)
(check-exn #rx"SHEQ: Incorrect number of arguments for CloV"
           (lambda () (top-interp '{{lambda () : 19} 17})))

;; divide by zero error test case (from handin)
(check-exn #rx"SHEQ: Divide by zero error"
           (lambda () (top-interp
                       '{{lambda (ignoreit) : {ignoreit {/ 52 {+ 0 0}}}} {lambda (x) : {+ 7 x}}})))

;; ---- interp tests ----
(check-equal? (interp (IdC 'true) top-env) #t)

(check-equal? (interp (NumC 89) top-env) 89)

(check-equal? (interp (AppC (IdC '+) (list (NumC 8)
                                           (AppC (IdC '*) (list (NumC 2) (NumC 3))))) top-env)  14)

(check-equal? (interp (AppC (IdC 'main) '()) (list (Binding 'main (CloV '() (NumC 5) '())))) 5)

(check-equal? (interp (AppC (IdC 'someFunction) (list (NumC 3)))
                      (list (Binding 'someFunction
                                     (CloV '(x)
                                           (AppC (IdC '*) (list (NumC 10) (IdC 'x)))
                                           top-env)))) 30)

(check-equal? (interp (AppC (IdC '<=) (list (NumC 9) (NumC 10))) top-env) #t)

(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 9) (NumC 10))) top-env) #f)

(check-equal? (interp (AppC (IdC 'equal?) (list (NumC 9) (NumC 10))) top-env) #f)

(check-equal? (interp (IfC (AppC (IdC '<=) (list (NumC 5) (NumC 2))) (NumC 1) (NumC -1)) top-env) -1)

(check-equal? (interp (AppC (LamC '(x) (AppC (IdC '+) (list (IdC 'x) (NumC 1))))
                            (list (NumC 5))) top-env) 6)

(check-equal? (interp (IfC (AppC (IdC 'equal?) (list (NumC 81) (NumC 81)))
                           (IdC 'true) (IdC 'false)) top-env) #t)

;; interp with seq
(check-exn #rx"SHEQ: seq needs at least 1 expression."
           (lambda () (interp (AppC (IdC 'seq) '()) top-env)))


;; ---- interp error check ---- 
(check-exn #rx"SHEQ: An unbound identifier" (lambda () (interp (IdC 'x) '())))

(check-exn #rx"SHEQ: PrimV \\+ expected 2 numbers"
           (lambda () (interp (AppC (IdC '+) (list (IdC '-) (NumC 4))) top-env)))

(check-exn #rx"SHEQ: Divide by zero error"
           (lambda () (interp (AppC (IdC '/) (list (NumC 5) (NumC 0))) top-env)))

(check-exn #rx"SHEQ: If expected boolean test"
           (lambda () (interp (parse '{if 32 23 32}) top-env)))

(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda ()
             (interp (AppC (LamC '(x)
                                 (AppC (IdC '+) (list (IdC 'x) (NumC 1) (NumC 2))))
                           (list (NumC 5))) top-env)))

(check-exn #rx"SHEQ: Attempted to apply non function value"
           (lambda ()
             (interp (AppC (NumC 9) (list (NumC 12))) top-env)))



;; ---- serialize tests ----
(check-equal? (serialize '32) "32")
(check-equal? (serialize #f) "false")
(check-equal? (serialize #t) "true")
(check-equal? (serialize (CloV '(x) (NumC 34) top-env)) "#<procedure>")
(check-equal? (serialize (PrimV '<=)) "#<primop>")

(check-exn #rx"SHEQ: user-error true" (lambda () (interp-prim (PrimV 'error) (list #t))))



;; ---- parse Tests ----

(check-equal? (parse '{(lambda (x) : {+ x 1}) 5})
              (AppC (LamC '(x) (AppC (IdC '+) (list (IdC 'x) (NumC 1)))) (list (NumC 5))))

(check-equal? (parse '{+ 5 12}) (AppC (IdC '+) (list (NumC 5) (NumC 12))))

(check-equal? (parse '{applyThis 5 12}) (AppC (IdC 'applyThis) (list (NumC 5) (NumC 12))))

(check-equal? (parse 'double) (IdC 'double))

(check-equal? (parse '{double x 2}) (AppC (IdC 'double) (list (IdC 'x) (NumC 2))))

(check-equal? (parse '{ifleq0? 5 x y}) (AppC (IdC 'ifleq0?) (list (NumC 5) (IdC 'x) (IdC 'y))))

(check-equal? (parse '{let {[x = 5] [y = {* 7 8}]} in {+ x y} end}) 
              (AppC 
               (LamC (list 'x 'y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))) 
               (list (NumC 5) 
                     (AppC (IdC '*) (list (NumC 7) (NumC 8))))))

(check-equal? (parse '{if {<= 3 90} 3 90})
              (IfC (AppC (IdC '<=) (list (NumC 3) (NumC 90))) (NumC 3) (NumC 90)))


;; parse errors
(check-exn #rx"SHEQ: Lambda args list is invalid, duplicate parameters found"
           (lambda () (parse '(lambda (x y x) : 33))))
(check-exn #rx"SHEQ: Let binding list is invalid, duplicate variables"
           (lambda () (parse '(let {[bo = {lambda () : 33}] [bo = "Twenty"]} in {bo} end))))
(check-exn #rx"SHEQ: let binding list is invalid, reserved symbol was used"
           (lambda () (parse '(let {[if = {lambda () : 0}]} in {if 3} end))))

(check-exn #rx"SHEQ: Syntax error, got"
           (lambda () (parse '{})))

(check-exn #rx"SHEQ: Syntax error, unexpected reserved keyword, got"
           (lambda () (parse '{let 2})))

(check-exn #rx"SHEQ: Syntax error, unexpected reserved keyword, got"
           (lambda () (parse '{end 3 4 3 2})))

(check-exn #rx"SHEQ: Syntax error, unexpected reserved keyword, got" (lambda () (parse '=)))


;; ---- intperp-prim Tests ----
;; PrimV '+ tests
(check-equal? (interp-prim (PrimV '+) (list 8 9)) 17)
(check-exn #rx"SHEQ: PrimV \\+ expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '+) (list 8 #t))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '+) (list 8 23 3 2))))

;; PrimV '* tests
(check-equal? (interp-prim (PrimV '*) (list 8 4)) 32)
(check-exn #rx"SHEQ: PrimV \\* expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '*) (list #f #t))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '*) (list 2))))

;; PrimV '/ tests
(check-equal? (interp-prim (PrimV '/) (list 33 11)) 3)
(check-exn #rx"SHEQ: PrimV \\/ expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '/) (list #f #t))))
(check-exn #rx"SHEQ: Divide by zero error"
           (lambda () (interp-prim (PrimV '/) (list 3 0)))) 
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '/) (list 21 2 3))))

;; PrimV '- tests
(check-equal? (interp-prim (PrimV '-) (list 33 11)) 22)
(check-exn #rx"SHEQ: PrimV \\- expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '-) (list #f #t))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '-) (list 9 3 2 1 3))))

;; PrimV '<= tests
(check-equal? (interp-prim (PrimV '<=) (list 3 11)) #t)
(check-equal? (interp-prim (PrimV '<=) (list 3 -11)) #f)
(check-exn #rx"SHEQ: PrimV \\<= expected 2 numbers, got"
           (lambda () (interp-prim (PrimV '<=) (list #f #t))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV '<=) (list 3))))

;; PrimV 'equal? tests
(check-equal? (interp-prim (PrimV 'equal?) (list 9 9)) #t)
(check-equal? (interp-prim (PrimV 'equal?) (list #f #f)) #t)
(check-equal? (interp-prim (PrimV 'equal?) (list "hi" "hi")) #t)
(check-equal? (interp-prim (PrimV 'equal?) (list 3 #f)) #f)
(check-equal? (interp-prim (PrimV 'equal?)
                           (list (CloV '(x) (NumC 1) '()) (CloV '(x) (NumC 1) '()))) #f)
(check-equal? (interp-prim (PrimV 'equal?)
                           (list (PrimV '-) (PrimV '-))) #f)
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV 'equal?) (list 3))))

;; PrimV 'substring tests
(check-equal? (interp-prim (PrimV 'substring) (list "hello world!" 0 5)) "hello")
(check-exn #rx"SHEQ: Substring needs string and 2 valid natural indices"
           (lambda () (interp-prim (PrimV 'substring) (list "hello" 99 1))))
(check-exn #rx"SHEQ: Incorrect number of arguments, expected 3"
           (lambda () (interp-prim (PrimV 'substring) (list "bib" 0 1 23 3))))

;; PrimV 'strlen tests
(check-equal? (interp-prim (PrimV 'strlen) (list "hello world!")) 12)
(check-exn #rx"SHEQ: Syntax error" (lambda () (interp-prim (PrimV 'strlen) (list 3))))
(check-exn #rx"SHEQ: Incorrect number of arguments, expected 1"
           (lambda () (interp-prim (PrimV 'strlen) (list "bib" "five" 3))))

;; PrimV 'error test
(check-exn #rx"SHEQ: Incorrect number of arguments, expected 1"
           (lambda () (interp-prim (PrimV 'error) (list "This" "too many"))))

;; PrimV invalid PrimV test
(check-exn #rx"SHEQ: Invalid PrimV op"
           (lambda () (interp-prim (PrimV 'dothis) (list 9))))

;; PrimV 'println tests
(check-equal? (interp-prim (PrimV 'println) (list "test: Hello World from interp")) #t)

(check-exn #rx"SHEQ: Attempted to print a non-string value"
           (lambda ()
             (interp-prim (PrimV 'println) (list 5))))
(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda ()
             (interp-prim (PrimV 'println) (list "a" "c"))))


;; PrimV 'read-num test
(check-equal? (with-input-from-string "52\n"
                (lambda () (interp-prim (PrimV 'read-num) '()))) 52)

(check-exn #rx"SHEQ: read-num expected a Number"
           (lambda () 
             (with-input-from-string "five"
               (lambda () (interp-prim (PrimV 'read-num) '())))))

(check-exn #rx"SHEQ: read-num read EOF"
           (lambda () 
             (with-input-from-string ""
               (lambda () (interp-prim (PrimV 'read-num) '())))))

(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV 'read-num) (list 4 2 1))))

;; PrimV 'read-str tests
(check-equal? (with-input-from-string "hello\n"
                (lambda () (interp-prim (PrimV 'read-str) '()))) "hello")

(check-exn #rx"SHEQ: Incorrect number of arguments"
           (lambda () (interp-prim (PrimV 'read-str) (list "s" "b" "c"))))

(check-exn #rx"SHEQ: read-str read EOF"
           (lambda () 
             (with-input-from-string ""
               (lambda () (interp-prim (PrimV 'read-str) '())))))

;; PrimV '++ tests
(check-equal? (interp-prim (PrimV '++) (list 4 "hello" #f)) "4hellofalse")
(check-equal? (interp-prim (PrimV '++) '()) "")

;; ---- Helper Tests ----

;; distinct-args? tests
(check-equal? (distinct-args? '(x y z)) #t)
(check-equal? (distinct-args? '(x y x)) #f)

;; reserved-symbol tests
(check-equal? (reserved-symbol? 'lambda) #t)
(check-equal? (reserved-symbol? '+++) #f)

;; create-env tests
(check-equal? (create-env (list 'a) (list 5) (list (Binding 'random 314)))
              (list (Binding 'a 5) (Binding 'random 314)))
(check-exn #rx"SHEQ: too many values were passed in application"
           (lambda () (create-env (list 'a) (list 5 3 4) (list (Binding 'random 314)))))
(check-exn #rx"SHEQ: too few values were passed in application"
           (lambda () (create-env (list 'a 'x) (list 4) (list (Binding 'random 314)))))

;; get-binding tests
(check-equal? (get-binding-val 'sym (list (Binding 'sym 5))) 5)
(check-exn #rx"SHEQ: An unbound identifier" (lambda () (get-binding-val 'sym '())))



;; tests for SHEQ5 Game

;; value->string tests
(check-equal? (val->string 3) "3")
(check-equal? (val->string #t) "true")
(check-equal? (val->string #f) "false")
(check-equal? (val->string "s") "s")
(check-equal? (val->string (CloV '(x) (NumC 4) top-env)) "#<procedure>")
(check-equal? (val->string (PrimV '+)) "#<primop>")

;; PrimV 'rnd test
(check-equal? (real? (interp-prim (PrimV 'rnd) '())) #t)


;; PrimV 'round tests
(check-equal? (interp-prim (PrimV 'round) (list 3.1)) 3.0)

(check-exn #rx"SHEQ: Incorrect number or type of arguments for round procedure"
           (lambda ()
             (interp-prim (PrimV 'round) (list 32.1 23))))

;; PrimV 'ceil tests
(check-equal? (interp-prim (PrimV 'ceil) (list 3.1)) 4.0)

(check-exn #rx"SHEQ: Incorrect number or type of arguments for ceil procedure"
           (lambda ()
             (interp-prim (PrimV 'ceil) (list 32.1 23))))

;; PrimV 'floor tests
(check-equal? (interp-prim (PrimV 'floor) (list 3.99)) 3.0)

(check-exn #rx"SHEQ: Incorrect number or type of arguments for floor procedure"
           (lambda ()
             (interp-prim (PrimV 'floor) (list 32.1 23))))


;; ---- SHEQ5 GAME ----

;; Main let block
;; - String definitions
;; - Data structures (player data)
;; - Basic for-loops (encounter input loops)
;;
;; Main let block body -> Secondary Let block
;; - Gameplay functions (encounters)
;;
;; Secondary Let block body -> Gameplay loop

(define dungeon-game : Sexp 
  '{let
       ;; ---- CONSTS & STRUCTS ----
       ([welcome-string = "
Welcome to the
      ______            _        _______  _______  _______  _       
     (  __  \\ |\\     /|( (    /|(  ____ \\(  ____ \\(  ___  )( (    /|
     | (  \\  )| )   ( ||  \\  ( || (    \\/| (    \\/| (   ) ||  \\  ( |
     | |   ) || |   | ||   \\ | || |      | (__    | |   | ||   \\ | |
     | |   | || |   | || (\\ \\) || | ____ |  __)   | |   | || (\\ \\) |
     | |   ) || |   | || | \\   || | \\_  )| (      | |   | || | \\   |
     | (__/  )| (___) || )  \\  || (___) || (____/\\| (___) || )  \\  |
     (______/ (_______)|/    )_)(_______)(_______/(_______)|/    )_)

                                  .  .   ~~//====......          __--~ ~~
                  -.            \\_|//     |||\\\\  ~~~~~~::::... /~
               ___-==_       _-~o~  \\/    |||  \\            _/~~-
       __---~~~.==~||\\=_    -_--~/_-~|-   |\\   \\        _/~
   _-~~     .=~    |  \\-_    '-~7  /-   /  ||    \\      /
 .~       .~       |   \\ -_    /  /-   /   ||      \\   /
/  ____  /         |     \\ ~-_/  /|- _/   .||       \\ /
|~~    ~~|--~~~~--_ \\     ~==-/   | \\~--===~~        .\\
         '         ~-|      /|    |-~\\~~       __--~~
                     |-~~-_/ |    |   ~\\_   _-~            /\\
                          /  \\     \\__   \\/~                \\__
                      _--~ _/ | .-~~____--~-/                  ~~==.
                     ((->/~   '.|||' -_|    ~~-/ ,              . _||
                                -_     ~\\      ~~---l__i__i__i--~~_/
                                _-~-__   ~)  \\--______________--~~
                              //.-~~~-~_--~- |-------~~~~~~~~
                                     //.-~~~--\\"]
        [game-over-string = "Game Over"]
        ;; Rounds n to a given decimal place dec
        ;; Example: n = 3.14159, dec = 0.001, result = 3.142
        [round-to-place = {lambda (n dec) : {* dec {round {/ n dec}}}}]
        [|| = {lambda (a b) : {if a true {if b true false}}}]
        [create-player =
                       {lambda (name hp atk rolls def acc) :
                         {lambda (key) : 
                           {if {equal? key "name"} 
                               name 
                               {if {equal? key "hp"}
                                   {round hp}
                                   {if {equal? key "atk"}
                                       atk
                                       {if {equal? key "rolls"}
                                           rolls
                                           {if {equal? key "def"}
                                               def
                                               {if {equal? key "acc"}
                                                   acc
                                                   {if {equal? key "get-dmg"}
                                                       {let ([get-dmg =
                                                                      {lambda (self atk rolls total) : 
                                                                        {if {<= rolls 0} 
                                                                            total 
                                                         ;; If rolls left, do (TOTAL + round(RND * ATK))                   
                                                                            {self self atk
                                                                                  {- rolls 1}
                                                                                  {+ total {ceil {* {rnd} atk}}}}}}]) 
                                                         in {get-dmg get-dmg atk rolls 0} end}
                                                       {error "DGNError: Invalid player key"}}}}}}}}}}]
        ;; create-monster - Creates a monster object. The monster has a 
        ;;	  name
        ;;	  ascii art 
        ;;	  3 different intros (intro1-3) - for display on intro to a fight
        ;;	  2 different attacks (dmg, proc, atktxt) - 
        ;;		dmg is the damage dealt, 
        ;;		proc is the how likely the attack is to hit (0-1), 
        ;;		atktxt is the flavor text
        [create-monster =
                        {lambda (name art intro1 intro2 intro3 dmg1 proc1 atktxt1 dmg2 proc2 atktxt2 hp) :
                          {lambda (key) :
                            {if {equal? key "name"}
                                name
                                {if {equal? key "art"}
                                    art
                                    {if {equal? key "intro"}
                                        ; Get random intro
                                        {if {<= {rnd} 0.3} intro1 {if {<= {rnd} 0.5} intro2 intro3}}
                                        {if {equal? key "atk"}
                                            ; Get random attack
                                            {if {<= {rnd} 0.5}
                                                {seq 
                                                 {println atktxt1}
                                                 {if {<= {rnd} proc1} dmg1 0}}
                                                {seq 
                                                 {println atktxt2}
                                                 {if {<= {rnd} proc2} dmg2 0}}}
                                            {if {equal? key "hp"}
                                                hp
                                                {error "DGNError: Invalid monster key"}}}}}}}}]
        ;; create-encounter - Creates a random encounter. The encounter has
        ;;	  flvrtxt - The flavor text to display when entering the encounter
        ;;	  run-enc - (player-obj -> player-obj) A function whose only argument is a player object,
        ;;		and whose return type is a modified player object
        [create-encounter =
                          {lambda (flvrtxt run-enc) :
                            {lambda (key) : 
                              {if {equal? key "flvrtxt"}
                                  flvrtxt
                                  {if {equal? key "run-enc"}
                                      run-enc
                                      {error "DGNError: Invalid encounter key"}}}}}]
        )
     in
     {seq 
      {println welcome-string}
      {println "What is your name, adventurer?"}
      ;; ---- CHARACTER CREATION & GAMEPLAY FUNCTIONS ----
      {let ([player-obj = {create-player {read-str} 10 6 2 0.1 0.65}]
            [goblin-obj = {create-monster
                           "Sheq" 
                           "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣠⣴⣶⣿⣿⣿⣿⣿⣿⣿⣶⣶⣤⣄⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⣾⣿⡿⠟⠋⠁⠀⠀⠀⠀⠉⠙⠻⣿⣿⣿⣦⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⢠⣿⣿⠏⠀⠀⠀⠀⠀⠀⠀⣀⣀⣀⣀⣀⣙⣻⢿⣿⣆⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⢀⣿⣿⡿⠀⠀⠀⠀⢀⠄⠊⢉⡁⠈⠁⠈⠤⠤⠀⠀⢀⣀⠣⣤⣄⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⢸⣿⣿⠀⠀⠀⠀⢠⠃⢀⠟⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠪⠿⢂⠀⠀⠀⠀⠀⠀⠀
⠀⠀⢀⣠⣤⣶⣶⣿⣿⡏⠀⠀⠀⠀⠇⠀⡅⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢓⢀⡀⠀⠀⠀⠀⠀⠀
⠀⢰⣿⡿⠿⠛⠻⣿⣿⡇⠀⠀⠀⠀⡄⡀⡇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠠⡇⠀⠀⠀⠀⠀⠀
⠀⣾⣿⢃⠀⠀⢰⣿⣿⠃⠀⠀⠀⠀⢠⢧⠐⠄⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣀⡶⠀⠀⠀⠀⠀⠀⠀
⠀⣿⣿⠀⠀⠀⢸⣿⣿⠀⠀⠀⠀⠀⠀⠪⡣⠀⠀⠀⠄⠀⠀⠀⠀⠠⠤⡐⠀⠇⢑⡒⠀⠀⠀⠀⠀⠀⠀⠀
⠀⣿⣿⠀⠀⠀⢸⣿⣿⡇⠀⠀⠀⠀⠀⠀⠈⠐⠢⠤⠀⣀⡀⣀⣀⠀⠦⠦⠓⢲⣿⡇⠀⠀⠀⠀⠀⠀⠀⠀
⢰⣿⣿⠀⠀⠀⢸⣿⣿⡆⠠⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢸⣿⡇⠀⠀⠀⠀⠀⠀⠀⠀
⢸⣿⣿⠀⠀⠀⢸⣿⣿⡀⠀⠄⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢸⣿⡇⠀⠀⠀⠀⠀⠀⠀⠀
⢸⣿⣿⠀⠀⠀⢸⣿⣿⠄⠀⠐⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠘⢸⣿⡇⠄⠀⠀⠀⠀⠀⠀⠀
⠸⣿⣿⠀⠀⠀⢸⣿⣿⡇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠄⠀⣿⣿⡧⠂⡢⡀⠀⠀⠀⠀⠀
⠀⣿⣿⡀⠀⠀⢸⣿⣿⡇⠀⠀⠀⠀⠀⠐⠂⠠⠀⠀⢀⣀⠀⠠⠄⠂⠁⠀⠀⣿⣿⠃⠂⠀⠀⠀⠀⠀⠀⠀
⠀⢻⣿⣧⡀⠀⢸⣿⣿⡇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⣀⡄⠀⠀⢸⣿⣿⡉⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠈⠻⣿⣿⣶⣾⣿⣿⡇⠀⠀⠀⠀⠀⠀⢠⣶⣶⣶⣶⣶⣿⣿⠟⠀⠀⠀⢸⣿⣿⠁⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠉⠉⠉⣿⣿⣇⣀⠀⠀⠀⠀⠀⢸⣿⡟⢻⣿⣿⠉⠀⠀⠀⠀⠀⠘⢿⣿⣷⣦⣄⣀⣀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⢰⣿⣿⣿⣿⠀⠀⠀⠀⠀⠘⣿⣿⣾⣿⡟⠀⠀⠀⠀⠁⠀⠀⡰⠉⠛⠿⢿⣿⣿⣿⣷⣦⡀
⠀⠀⠀⠀⠀⢠⣿⣿⡟⠈⠿⠀⠀⢀⠀⠀⠀⠈⠛⢿⣿⣿⣶⣦⣤⣄⠀⠀⠀⢅⣤⣄⡀⠀⣀⠀⣬⣉⣿⣿
⠀⠀⠀⠀⠀⢸⣿⣿⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠙⠻⠿⢿⣿⣷⠀⠀⠛⠙⢿⣿⣆⣻⣇⣽⣿⣾⣿
⠀⠀⠀⠀⠀⠘⢿⣿⣿⣷⣦⣤⣀⠀⠀⠀⣦⣄⢀⣶⡄⢐⣿⣾⣥⣿⣿⣿⣿⣶⣶⣿⣿⣿⡿⠿⠛⠙⠉⠁
⠀⠀⠀⠀⠀⠀⠀⠙⠛⠛⠿⣿⣿⣿⣿⣶⣿⣿⣿⡿⣿⣿⡿⠟⠛⠛⠉⠉⠉⠛⠛⠉⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠉⠉⠁⠈⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀"
"With a shriek of rusted metal and glee,the sheq scuttles into view, eyes glinting with wicked anticipation!" 
"The stench of oil and rot hits first. Then the sheq appears, grinning, clutching a blade that hums with mischief." 
"Cackling from the shadows, the sheq tumbles forward, crooked teeth bared. ‘Heh! Fresh meat for my collection!"
1 0.75 "The sheq lunges with manic speed, slashing wildly and laughing as sparks fly!"
3 0.7 "It hurls a crude bomb made from scrap and rocks — the explosion fills the air with smoke and cruel laughter."
                           5}]
            [skeleton-obj = {create-monster
                             "Skeleton"
                             "              .7
            .'/
           / /
          / /
         / /
        / /
       / /                             
          / /
     / /         
    / /          
  __|/
,-\\__\\
|f-\"Y\\|
\\()7L/
 cgD                            __ _
 |\\(                          .'  Y '>,
  \\ \\                        / _   _   \\
   \\\\\\                       )(_) (_)(|}
    \\\\\\                      {  4A   } /
     \\\\\\                      \\uLuJJ/\\l
      \\\\\\                     |3    p)/
       \\\\\\___ __________      /nnm_n//
       c7___-__,__-)\\,__)(\".  \\_>-<_/D
                  //V     \\_\"-._.__G G_c__.-__<\"/ ( \\
                         <\"-._>__-,G_.___)\\   \\7\\
                        (\"-.__.| \\\"<.__.-\" )   \\ \\
                        |\"-.__\"\\  |\"-.__.-\".\\   \\ \\
                        (\"-.__\"\". \\\"-.__.-\".|    \\_\\
                        \\\"-.__\"\"|!|\"-.__.-\".)     \\ \\
                         \"-.__\"\"\\_|\"-.__.-\"./      \\ l
                          \".__\"\"\">G>-.__.-\">       .--,_"
"Bones rattle in the dark — the skeleton rises, clutching a chipped sword that remembers war long past."
"A hollow clatter echoes through the corridor as a skeleton lurches into view, eye sockets glowing faintly."
"Dust swirls and bones knit together — a forgotten warrior stands once more, silent but relentless."
2 0.95 "The skeleton swings its rusted blade with mechanical precision, heedless of pain or mercy."
3 0.8 "With a dry hiss, the skeleton lunges forward, jabbing its rusted blade toward your chest."
10}]
            [rat-obj =
                     {create-monster
                      "Giant Rat"
                      "               _     __,..---\"\"-._                 ';-,
        ,    _/_),-\"`             '-.                `\\
       \\|.-\"`    -_)                 '.                ||
       /`   a   ,                      \\              .'/
       '.___,__/                 .-'    \\_        _.-'.'
          |\\  \\      \\         /`        _`\"\"\"\"\"\"`_.-'
             _/;--._, >        |   --.__/ `\"\"\"\"\"\"`
           (((-'  __//`'-......-;\\      )
                (((-'       __//  '--. /
                          (((-'    __//
                                 (((-'"
                      "A massive rat scurries from the shadows, fur slick with filth and eyes burning with hunger."
                      "You hear squeaks and skittering — then a rat the size of a dog lurches forward, teeth gnashing."
                      "The stench of rot fills the air as a swollen, twitching rat crawls into view, tail lashing."
                      1 0.75 "The rat leaps up, biting and clawing in a frenzy of hunger and panic."
                      1 0.8 "It lunges again and again, its squeals echoing through the dungeon walls."
                      3}]
            [wolf-obj =
                      {create-monster
                       "Wolf"
                       "                              __
                            .d$$b
                          .' TO$;\\
                         /  : TP._;
                        / _.;  :Tb|
                       /   /   ;j$j
                   _.-\"       d$$$$
                 .' ..       d$$$$;
                /  /P'      d$$$$P. |\\
               /   \"      .d$$$P' |\\^\"l
             .'           `T$P^\"\"\"\"\"  :
         ._.'      _.'                ;
      `-.-\".-'-' ._.       _.-\"    .-\"
    `.-\" _____  ._              .-\"
   -(.g$$$$$$$b.              .'
     \"\"^^T$$$P^)            .(:
       _/  -\"  /.'         /:/;
    ._.'-'`-'  \")/         /;/;
 `-.-\"..--\"\"   \" /         /  ;
.-\" ..--\"\"        -'          :
..--\"\"--.-\"         (\\      .-(\\
  ..--\"\"              `-\\(\\/;`
    _.                      :
                            ;`-
                           :\\
                           ;"
                       "A low growl cuts through the silence — a hungry wolf circles, eyes gleaming in the dark."
                       "From the shadows leaps a gaunt wolf, fur bristling and teeth bared in a snarl of fury."
                       "The sound of claws on stone — then a flash of grey fur as the wolf lunges into the light."
                       2 0.9 "The wolf snaps its jaws shut with a vicious bite, saliva and fury flying!"
                       1 0.98 "It darts in and slices with its claws before leaping back, ready to strike again."
                       9}]                             			
            ;; handle-battle - Returns the player's object after a battle with monster has been concluded
            [handle-battle =
                           {lambda (player monster mod) :
                             {let ([get-action =
                                               {lambda (self) :
                                                 {seq
                                                  {println "What will you do? [attack / defend]"}
                                                  {let ([input = {read-str}]) 
                                                    in 
                                                    {if {|| {equal? input "attack"}
                                                            {equal? input "defend"}}
                                                        input
                                                        {seq
                                                         {println {++
                                                                   "Hmmmm... I don't understand \""
                                                                   input
                                                                   "\"... Please try something else!"}}
                                                         {self self}}} 
                                                    end}}}])
                               in
                               {seq
                                {println {monster "art"}}
                                {println {++ {monster "intro"} "\n"}}
                                {println {++ "Prepare to fight: "
                                             {monster "name"}
                                             " ("
                                             {round {* {monster "hp"} mod}} "♥)!"}}
                                {let ([monster-hp = {round {* {monster "hp" } mod}}]
                                      [player-dmg = {player "get-dmg"}]
                                      [action = {get-action get-action}]
                                      [damage-player = {lambda (damage) :
                                                         {seq 
                                                          {if {<= damage 0}
                                                              {println {++ "The "
                                                                           {monster "name"}
                                                                           " missed! You took "
                                                                           damage
                                                                           " damage."}}
                                                              {println {++
                                                                        "You took "
                                                                        damage
                                                                        " damage."}}}
                                                          {create-player {player "name"}
                                                                         {- {player "hp"} damage}
                                                                         {player "atk"}
                                                                         {player "rolls"}
                                                                         {player "def"}
                                                                         {player "acc"}}}}])
                                  in
                                  {if {equal? action "attack"}
                                      ;; And now I realize I need enemy health :D
									  
                                      ; Attack monster
                                      {if {<= {rnd} {player "acc"}}
                                          ; Successfully hit monster
                                          {if {<= monster-hp player-dmg}
                                              {seq
                                               {println {++ "Your swing connects, killing the "
                                                            {monster "name"}
                                                            " in a single, swift blow ("
															player-dmg
															"✶)!!"}}
                                               player}
                                              {seq
                                               {println {++ "Your attack wasn't enough kill "
                                                            {monster "name"}
                                                            " ("
                                                            player-dmg
                                                            "✶ -> "
                                                            monster-hp
                                                            "♥)"
                                                            "!"}}
                                               {damage-player {round-to-place {* {monster "atk"} mod} 0.01}}}}
                                          ; Missed monster
                                          {seq
                                           {println "Your attack missed!"}
                                           {damage-player {round-to-place {* {monster "atk"} mod} 0.01}}}}
									  
                                      ; Defend from monster - Return player with (HP - (DMG TAKEN * (1 - DEF)))
                                      {damage-player {round-to-place {* {* {monster "atk"} mod} {- 1 {player "def"}}} 0.01}}}
                                  end}}                              
                               end}}])
        in
        {seq 
         {println {++ "Your player name is: "
                      {player-obj "name"}
                      " and your lucky number is "
                      {round-to-place {rnd} 0.001}}}
         ;; ---- MAIN GAMEPLAY LOOP ----
         {let ([chest-enc =
                          {create-encounter 
                           "The air grows still as you enter
                              — at the center of the chamber rests a lone chest, bathed in a thin shaft of light."
                           {lambda (player) :
                             {seq
                              {println "Open chest? [Y/N]"}
                              {if {equal? {read-str} "Y"}
                                  ;; Opens chest
                                  {if {<= {rnd} 0.9}
                                      ;; Tool
                                      {if {<= {rnd} 0.6}
                                          ;; Weapon
                                          {if {<= {rnd} 0.5}
                                              ;; Basic sword
                                              {seq
                                               {println "The lid creaks open, the sound echoing through the chamber."}
                                               {println "You found a Rusted Iron Sword (2D8✶ 0.7→)! Equip? [Y/N]"}
                                               {if {equal? {read-str} "Y"}
                                                   {create-player
                                                    {player "name"}
                                                    {player "hp"}
                                                    8
                                                    2
                                                    {player "def"}
                                                    0.7}
                                                   player}}
                                              ;; Better sword
                                              {if {<= {rnd} 0.6}
                                                  ;; Uncommon sword
                                                  {seq
                                                   {println "The lid creaks open,
                                                            the sound echoing through the chamber."}
                                                   {println "You found a Steel Longword (3D6✶ 0.75→)! Equip? [Y/N]"}
                                                   {if {equal? {read-str} "Y"}
                                                       {create-player
                                                        {player "name"}
                                                        {player "hp"}
                                                        6
                                                        3
                                                        {player "def"}
                                                        0.75}
                                                       player}}
                                                  ;; Super rare swords
                                                  {if {<= {rnd} 0.7}
                                                      {seq
                                                       {println
                                                        "The lid creaks open, the sound echoes through the chamber."}
                                                       {println
                                                        "You found an Emberfang Blade (3D8✶ 0.8→)! Equip? [Y/N]"}
                                                       {if {equal? {read-str} "Y"}
                                                           {create-player
                                                            {player "name"}
                                                            {player "hp"}
                                                            8
                                                            3
                                                            {player "def"}
                                                            0.8}
                                                           player}}
                                                      {seq
                                                       {println
                                                        "The lid creaks open, the sound echoing through the chamber."}
                                                       {println
                                                        "You found Astral Edge (5D6✶ 0.8→)! Equip? [Y/N]"}
                                                       {if {equal? {read-str} "Y"}
                                                           {create-player
                                                            {player "name"}
                                                            {player "hp"}
                                                            6
                                                            5
                                                            {player "def"}
                                                            0.8}
                                                           player}}}}}
                                          ;; Armor
                                          {seq
                                           {println "You found armor (DEF ❖)!"}
                                           ; Increases at a rate of ((1 + DEF) / 2.25)
                                           {create-player {player "name"}
                                                          {player "hp"}
                                                          {player "atk"}
                                                          {player "rolls"}
                                                          {round-to-place {/ {+ 1 {player "def"}} 2.25} 0.001}
                                                          {player "acc"}}}}
                                      {seq 
                                       {println
                                        "It's filled with... gold coins, precious jewels, and heirlooms? How useless!"}
                                       player}}
                                  ;; Walks away
                                  {seq
                                   {println "You walk away, leaving the mysteries of the chest behind."}
                                   player}}}}}]
               [spring-enc = {create-encounter 
                              "Fresh water trickles between smooth rocks,feeding a patch of green life in the dungeon."
                              {lambda (player) :
                                {let ([new-health = {round-to-place
                                                     {+ {player "hp"}
                                                        {+ {/ {- 10 {player "hp"}} 2} 1}}
                                                     0.01}])
                                  in
                                  {seq 
                                   {println {++ "You are healed to "
                                                {if
                                                 {<= new-health 10}
                                                 new-health
                                                 10}
                                                " HP (♥)!"}} 
                                   {create-player {player "name"}
                                                  {if {<= new-health 10}
                                                      new-health
                                                      10}
                                                  {player "atk"}
                                                  {player "rolls"}
                                                  {player "def"}
                                                  {player "acc"}}} 
                                  end}}}]
               ;; handle-encounter - Returns the player's object after a random encounter
               [handle-encounter =
                                 {lambda (player encounter) :
                                   {seq
                                    {println {encounter "flvrtxt"}}
                                    {{encounter "run-enc"} player}}}])
           in
           {let
               ;; main-loop - handles the main gameplay loop
               ([main-loop =
                           {lambda (self floor# player) : 
                             {if {<= {player "hp"} 0}
                                 ;; Game over
                                 {seq 
                                  {println "\n╭────────────────────────────────────────────────────────────╮\n"}
                                  {println game-over-string}
                                  {println {++ "Floors encountered: " {- floor# 1}}}
                                  {println {++ "Great adventuring, " {player "name"} "!"}}
                                  {println "\n╰────────────────────────────────────────────────────────────╯"}}
                                 ;; Explore floor
                                 {let ([monster =
                                                {if {<= {rnd} 0.35}
                                                    {if {<= {rnd} 0.45}
                                                        skeleton-obj
                                                        wolf-obj}
                                                    {if {<= {rnd} 0.4}
                                                        goblin-obj
                                                        rat-obj}}]
                                       [encounter = {if {<= {rnd} 0.65}
                                                        chest-enc
                                                        spring-enc}]
                                       [floor-mod = {+ 1 {* floor# 0.03}}])
                                   in
                                   {seq 
                                    {println {++ "\n╭──────────────────────────────  Floor #: "
                                                 floor#
                                                 "  ──────────────────────────────╮"}}
                                    {println {++ {player "hp"} " HP (♥)  |  " 
                                                 {player "rolls"} "D" {player "atk"} " ATTACK (✶)  |  "
                                                 {player "acc"} " ACCURACY (→)  |  "
                                                 {player "def"} " DEF (❖)" "\n"}}
                                    {self self {+ floor# 1}
                                      {if {<= {rnd} 0.7} 
										{handle-battle player monster floor-mod} 
										{handle-encounter player encounter}}}}    
                                   end}}}]) 
             in 
             {main-loop main-loop 1 player-obj} 
             end}
           end}}
        end}}
     end})

(top-interp dungeon-game)







