#lang plai
;;;;
;; CFAER stuff
(define-type CFAER
    (numI (n number?))
    (binopI (op symbol?) (lhs CFAER?) (rhs CFAER?))
    (appI (fun-expr CFAER?) (arg-expr CFAER?))
    (funI (param symbol?) (body CFAER?))
    (if0I (test CFAER?) (iftrue CFAER?) (iffalse CFAER?))
    (recI (name symbol?) (named-expr CFAER?) (body CFAER?))
    (idI (name symbol?)))

(define interp-cfaer
    (lambda (a-cfaer env)
        (type-case CFAER a-cfaer
            (numI (x) (numV x))
            (binopI (op l r)
                (numV ((lookup op ops)
                    (numV-n (interp-cfaer l env))
                    (numV-n (interp-cfaer r env)))))
            (appI (fun-expr arg-expr) 
                (local ((define fun-val (interp-cfaer fun-expr env)))
                    (interp-cfaer (closureV-body fun-val)
                        (aSub (closureV-param fun-val)
                            (interp-cfaer arg-expr env)
                            (closureV-env fun-val)))))
            (funI (bound-id bound-body) (closureV bound-id bound-body env))
            (if0I (test iftrue iffalse)
                (if (zero? (numV-n (interp-cfaer test env)))
                    (interp-cfaer iftrue env)
                    (interp-cfaer iffalse env)))
            (recI (bound-id named-expr bound-body)
                (interp-cfaer bound-body
                    (rec-bind-interp bound-id named-expr env)))
            (idI (v) (envlookup v env)))))

(define rec-bind-interp
    (lambda (bound-id named-expr env)
        (local
            ((define value-holder (box (numV 9999)))
                (define new-env (aRecSub bound-id value-holder env))
                (define named-expr-val (interp-cfaer named-expr new-env)))
            (begin
                (set-box! value-holder named-expr-val) new-env))))

(define-type CFAER-value
    (numV (n number?))
    (closureV (param symbol?) (body CFAER?) (env Env?)))

(define (boxed-CFAER-value? v)
    (and (box? v) (CFAER-value? (unbox v))))

;;;;
;; CFWAER stuff
;; The define-type and parser are (mostly) the versions given with the assignment
;;
(define-type CFWAER
    (num (n number?))
    (binop (op symbol?) (lhs CFWAER?) (rhs CFWAER?))
    (app (fun-expr CFWAER?) (arg-expr CFWAER?))
    (fun (param symbol?) (body CFWAER?))
    (with (name symbol?) (named-expr CFWAER?) (body CFWAER?))
    (if0 (test CFWAER?) (iftrue CFWAER?) (iffalse CFWAER?))
    (rec (name symbol?) (named-expr CFWAER?) (body CFWAER?))
    (id (name symbol?)))

(define elab-cfwaer
    (lambda (a-cfwaer)
        (type-case CFWAER a-cfwaer
            (num (x) (numI x))
            (binop (op l r) (binopI op (elab-cfwaer l) (elab-cfwaer r)))
            (app (fun-expr arg-expr) (appI (elab-cfwaer fun-expr) (elab-cfwaer arg-expr)))
            (fun (param body) (funI param (elab-cfwaer body)))
            (with (name named-expr body) (appI (funI name (elab-cfwaer body)) (elab-cfwaer named-expr)))
            (if0 (test iftrue iffalse) (if0I (elab-cfwaer test) (elab-cfwaer iftrue) (elab-cfwaer iffalse)))
            (rec (name named-expr body) (recI name (elab-cfwaer named-expr) (elab-cfwaer body)))
            (id (name) (idI name)))))

(define parse-cfwaer
    (lambda (expr)
        (cond ((symbol? expr) (id expr))
            ((number? expr) (num expr))
            ((list? expr)
                (case (car expr)
                    ((-) (binop 'sub (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
                    ((+) (binop 'add (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
                    ((*) (binop 'mul (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
                    ((/) (binop 'div (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
                    ((with) (with (car (cadr expr)) 
                        (parse-cfwaer (cadr (cadr expr))) 
                        (parse-cfwaer (caddr expr))))
                    ((rec) (rec (car (cadr expr)) 
                        (parse-cfwaer (cadr (cadr expr))) 
                        (parse-cfwaer (caddr expr))))
                    ((if0) (if0 (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))
                        (parse-cfwaer (cadddr expr))))
                    ((fun) (fun (caadr expr) (parse-cfwaer (caddr expr))))
                (else (app (parse-cfwaer (car expr)) (parse-cfwaer (cadr expr))))))
            (else 'parse-cfwaer "Unexpected token"))))

; Since I am using an elaborator to eliminate the (with) part of the language,
; the interpreter is in the CFAER section of the code. This function serves as a
; wrapper for elaborating the CFWAER into a CFAER, then interpreting it
(define interp-cfwaer (lambda (expr env) (interp-cfaer (elab-cfwaer expr) env)))

; Parse the expression, then pass it to the CFAER interpreter via the CFWAER
; interpreter/elaborator
(define eval-cfwaer (lambda (expr) (interp-cfwaer (parse-cfwaer expr) (mtSub))))

;;;;
;; Deferred substitution stuff
;;
(define-type Env
    (mtSub)
    (aSub (name symbol?) (value CFAER-value?) (env Env?))
    (aRecSub (name symbol?) (value boxed-CFAER-value?) (env Env?)))

(define (envlookup name env)
    (type-case Env env
        (mtSub () (error 'envlookup "Unbound identifier"))
        (aSub (bound-name bound-value rest-env)
            (if (symbol=? bound-name name)
                bound-value
                (envlookup name rest-env)))
        (aRecSub (bound-name boxed-bound-value rest-env)
            (if (symbol=? bound-name name)
                (unbox boxed-bound-value)
                (envlookup name rest-env)))))

;;;;
;; Binop stuff
;;
(define-type Binop
    (bop (name symbol?) (op procedure?)))

(define lookup
    (lambda (op-name op-table)
        (cond ((empty? op-table) (error 'lookup (string-append "Operator not found: " (symbol->string op-name))))
            (else
                (if (symbol=? (bop-name (car op-table)) op-name)
                    (bop-op (car op-table))
                    (lookup op-name (cdr op-table)))))))

(define ops (list
    (bop 'add +)
    (bop 'sub -)
    (bop 'mul *)
    (bop 'div /)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;
;; Tests
;;

;;;; Testing the op table
(lookup 'add ops)
(lookup 'sub ops)
(lookup 'mul ops)
(lookup 'div ops)

;;;; Testing the complete evaluator for CFWAER
(eval-cfwaer `{rec {fac {fun {n} {if0 n 1 {* n {fac {+ n -1}}}}}} {fac 5}})
(eval-cfwaer `{+ 5 {- 3 2}})
(eval-cfwaer `{+ 1 2})
(eval-cfwaer `{+ {- {- 4 3} 15} {+ {+ {- 10 5} {- 3 2}} {- 15 42}}})
(eval-cfwaer `{/ 50 5})
(eval-cfwaer `{+ 1 2})
(eval-cfwaer `{* 2 2})
(eval-cfwaer `{if0 0 1 2})
(eval-cfwaer `{with {x 5} x})
(eval-cfwaer `{with {x 1} {+ x 1}})
(eval-cfwaer `{if0 {with {x 3} {- x 2}} {with {x 10} {* x 2}} {with {x 8} {/ x 2}}})
(eval-cfwaer `{with {x 2} {with {y 3} {+ x y}}})
(eval-cfwaer `{fun {x} {+ x 1}})
(eval-cfwaer `{fun {x} x})

;;;; Testing the parser for CFWAER
(parse-cfwaer `{rec {fac {fun {n} {if0 n 1 {* n {fac {+ n -1}}}}}} {fac 5}})
(parse-cfwaer `{+ 5 {- 3 2}})
(parse-cfwaer `{+ 1 2})
(parse-cfwaer `{+ {- {- 4 3} 15} {+ {+ {- 10 5} {- 3 2}} {- 15 42}}})
(parse-cfwaer `{/ 50 5})
(parse-cfwaer `{+ 1 2})
(parse-cfwaer `{* 2 2})
(parse-cfwaer `{if0 0 1 2})
(parse-cfwaer `{with {x 5} x})
(parse-cfwaer `{with {x 1} {+ x 1}})
(parse-cfwaer `{if0 {with {x 3} {- x 2}} {with {x 10} {* x 2}} {with {x 8} {/ x 2}}})
(parse-cfwaer `{with {x 2} {with {y 3} {+ x y}}})
(parse-cfwaer `{fun {x} {+ x 1}})
(parse-cfwaer `{fun {x} x})

;;;; Testing the elaborator from CFWAER to CFAER
(elab-cfwaer (binop 'add (num 1) (num 2)))
(elab-cfwaer (binop 'add (binop 'sub (binop 'sub (num 4) (num 3)) (num 15)) (binop 'add (binop 'add (binop 'sub (num 10) (num 5)) (binop 'sub (num 3) (num 2))) (binop 'sub (num 15) (num 42)))))
(elab-cfwaer (binop 'div (num 50) (num 5)))
(elab-cfwaer (binop 'add (num 1) (num 2)))
(elab-cfwaer (binop 'mul (num 2) (num 2)))
(elab-cfwaer (if0 (num 0) (num 1) (num 2)))
(elab-cfwaer (app (fun 'x (id 'x)) (num 5)))
(elab-cfwaer (app (fun 'x (binop 'add (id 'x) (num 1))) (num 1)))
(elab-cfwaer (if0 (app (fun 'x (binop 'sub (id 'x) (num 2))) (num 3)) (app (fun 'x (binop 'mul (id 'x) (num 2))) (num 10)) (app (fun 'x (binop 'div (id 'x) (num 2))) (num 8))))
(elab-cfwaer (app (if0 (num 0) (fun 'x (binop 'add (id 'x) (num 1))) (fun 'x (binop 'add (id 'x) (num 2)))) (num 0)))
(elab-cfwaer (app (fun 'x (app (fun 'y (binop 'add (id 'x) (id 'y))) (num 3))) (num 2)))
(elab-cfwaer (fun 'x (binop 'add (id 'x) (num 1))))
(elab-cfwaer (fun 'x (id 'x)))

;;;; Testing the interpreter for CFAER
; (((4 - 3) - 15) + (((10 - 5) + (3 - 2)) + (15 - 42))) = (1 - 15) + (6 + (-27)) = -14 + (-21) = -35
(interp-cfaer (binopI 'add (binopI 'sub (binopI 'sub (numI 4) (numI 3)) (numI 15)) (binopI 'add (binopI 'add (binopI 'sub (numI 10) (numI 5)) (binopI 'sub (numI 3) (numI 2))) (binopI 'sub (numI 15) (numI 42)))) (mtSub))

; 50 / 5 = 10
(interp-cfaer (binopI 'div (numI 50) (numI 5)) (mtSub))

; 1 + 2 = 3
(interp-cfaer (binopI 'add (numI 1) (numI 2)) (mtSub))

; 2 + 2 = 4
(interp-cfaer (binopI 'mul (numI 2) (numI 2)) (mtSub))

; 0 == 0 => 1
(interp-cfaer (if0I (numI 0) (numI 1) (numI 2)) (mtSub))

; fun(x=5){x} => 5
(interp-cfaer (appI (funI 'x (idI 'x)) (numI 5)) (mtSub))

; fun(x=1){x+1} => 2
(interp-cfaer (appI (funI 'x (binopI 'add (idI 'x) (numI 1))) (numI 1)) (mtSub))

; (3 - 2) != 0 => with x=8, x/2 = 8 / 2 = 4
(interp-cfaer (if0I (appI (funI 'x (binopI 'sub (idI 'x) (numI 2))) (numI 3)) (appI (funI 'x (binopI 'mul (idI 'x) (numI 2))) (numI 10)) (appI (funI 'x (binopI 'div (idI 'x) (numI 2))) (numI 8))) (mtSub))

; 0 == 0 => fun(x=0){x+1} = 1
(interp-cfaer (appI (if0I (numI 0) (funI 'x (binopI 'add (idI 'x) (numI 1))) (funI 'x (binopI 'add (idI 'x) (numI 2)))) (numI 0)) (mtSub))

; x = 2, y = 3; x + y = 5
(interp-cfaer (appI (funI 'x (appI (funI 'y (binopI 'add (idI 'x) (idI 'y))) (numI 3))) (numI 2)) (mtSub))

; Defining the "add one" function
; (closureV 'x (binopI 'add (idI 'x) (numI 1)) (mtSub))
(interp-cfaer (funI 'x (binopI 'add (idI 'x) (numI 1))) (mtSub))

; Defining the identity function
; (closureV 'x (idI 'x) (mtSub))
(interp-cfaer (funI 'x (idI 'x)) (mtSub))