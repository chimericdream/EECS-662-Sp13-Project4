#lang plai
;;;;
;; CFAES stuff
(define-type CFAES
    (numI (n number?))
    (binopI (op symbol?) (lhs CFAES?) (rhs CFAES?))
    (appI (fun-expr CFAES?) (arg-expr CFAES?))
    (funI (param symbol?) (body CFAES?))
    (if0I (test CFAES?) (iftrue CFAES?) (iffalse CFAES?))
    (idI (name symbol?)))

(define interp-cfaes
    (lambda (a-cfaes env sto)
        (type-case CFAES a-cfaes
            (numI (x) (numV x))
            (binopI (op l r)
                (numV ((lookup op ops)
                    (numV-n (interp-cfaes l env sto))
                    (numV-n (interp-cfaes r env sto)))))
            (appI (fun-expr arg-expr) 
                (local ((define fun-val (interp-cfaes fun-expr env sto)))
                    (interp-cfaes
                        (closureV-body fun-val)
                        (aSub (closureV-param fun-val)
                            (interp-cfaes arg-expr env sto)
                            (closureV-env fun-val))
                        sto)))
            (funI (bound-id bound-body) (closureV bound-id bound-body env sto))
            (if0I (test iftrue iffalse)
                (if (zero? (numV-n (interp-cfaes test env sto)))
                    (interp-cfaes iftrue env sto)
                    (interp-cfaes iffalse env sto)))
            (idI (v) (envlookup v env)))))

(define-type CFAES-value
    (numV (n number?))
    (closureV (param symbol?) (body CFAES?) (env Env?) (sto Store?)))

;;;;
;; CFWAES stuff
;; The define-type and parser are (mostly) the versions given with the assignment
;;
(define-type CFWAES
    (num (n number?))
    (binop (op symbol?) (lhs CFWAES?) (rhs CFWAES?))
    (app (fun-expr CFWAES?) (arg-expr CFWAES?))
    (fun (param symbol?) (body CFWAES?))
    (with (name symbol?) (named-expr CFWAES?) (body CFWAES?))
    (if0 (test CFWAES?) (iftrue CFWAES?) (iffalse CFWAES?))
    (id (name symbol?)))

(define elab-cfwaes
    (lambda (a-cfwaes)
        (type-case CFWAES a-cfwaes
            (num (x) (numI x))
            (binop (op l r) (binopI op (elab-cfwaes l) (elab-cfwaes r)))
            (app (fun-expr arg-expr) (appI (elab-cfwaes fun-expr) (elab-cfwaes arg-expr)))
            (fun (param body) (funI param (elab-cfwaes body)))
            (with (name named-expr body) (appI (funI name (elab-cfwaes body)) (elab-cfwaes named-expr)))
            (if0 (test iftrue iffalse) (if0I (elab-cfwaes test) (elab-cfwaes iftrue) (elab-cfwaes iffalse)))
            (id (name) (idI name)))))

(define parse-cfwaes
    (lambda (expr)
        (cond ((symbol? expr) (id expr))
            ((number? expr) (num expr))
            ((list? expr)
                (case (car expr)
                    ((-) (binop 'sub (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
                    ((+) (binop 'add (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
                    ((*) (binop 'mul (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
                    ((/) (binop 'div (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
                    ((with) (with (car (cadr expr)) 
                        (parse-cfwaes (cadr (cadr expr))) 
                        (parse-cfwaes (caddr expr))))
                    ((if0) (if0 (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))
                        (parse-cfwaes (cadddr expr))))
                    ((fun) (fun (caadr expr) (parse-cfwaes (caddr expr))))
                (else (app (parse-cfwaes (car expr)) (parse-cfwaes (cadr expr))))))
            (else 'parse-cfwaes "Unexpected token"))))

; Since I am using an elaborator to eliminate the (with) part of the language,
; the interpreter is in the CFAES section of the code. This function serves as a
; wrapper for elaborating the CFWAES into a CFAES, then interpreting it
(define interp-cfwaes (lambda (expr env sto) (interp-cfaes (elab-cfwaes expr) env sto)))

; Parse the expression, then pass it to the CFAES interpreter via the CFWAES
; interpreter/elaborator
(define eval-cfwaes (lambda (expr) (interp-cfwaes (parse-cfwaes expr) (mtSub) (mtSto))))

;;;;
;; The data store
;;
(define-type Store
    (mtSto)
    (aSto (name symbol?) (value CFAES-value?) (sto Store?)))

(define (stolookup name sto)
    (type-case Store sto
        (mtSto () (error 'stolookup "Unbound identifier"))
        (aSto (bound-name bound-value rest-sto)
            (if (symbol=? bound-name name)
                bound-value
                (stolookup name rest-sto)))))

;;;;
;; Deferred substitution stuff
;;
(define-type Env
    (mtSub)
    (aSub (name symbol?) (value CFAES-value?) (env Env?)))

(define (envlookup name env)
    (type-case Env env
        (mtSub () (error 'envlookup "Unbound identifier"))
        (aSub (bound-name bound-value rest-env)
            (if (symbol=? bound-name name)
                bound-value
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

;;;; Testing the complete evaluator for CFWAES
(eval-cfwaes `{+ 5 {- 3 2}})
(eval-cfwaes `{+ 1 2})
(eval-cfwaes `{+ {- {- 4 3} 15} {+ {+ {- 10 5} {- 3 2}} {- 15 42}}})
(eval-cfwaes `{/ 50 5})
(eval-cfwaes `{+ 1 2})
(eval-cfwaes `{* 2 2})
(eval-cfwaes `{if0 0 1 2})
(eval-cfwaes `{with {x 5} x})
(eval-cfwaes `{with {x 1} {+ x 1}})
(eval-cfwaes `{if0 {with {x 3} {- x 2}} {with {x 10} {* x 2}} {with {x 8} {/ x 2}}})
(eval-cfwaes `{with {x 2} {with {y 3} {+ x y}}})
(eval-cfwaes `{fun {x} {+ x 1}})
(eval-cfwaes `{fun {x} x})

;;;; Testing the parser for CFWAES
(parse-cfwaes `{+ 5 {- 3 2}})
(parse-cfwaes `{+ 1 2})
(parse-cfwaes `{+ {- {- 4 3} 15} {+ {+ {- 10 5} {- 3 2}} {- 15 42}}})
(parse-cfwaes `{/ 50 5})
(parse-cfwaes `{+ 1 2})
(parse-cfwaes `{* 2 2})
(parse-cfwaes `{if0 0 1 2})
(parse-cfwaes `{with {x 5} x})
(parse-cfwaes `{with {x 1} {+ x 1}})
(parse-cfwaes `{if0 {with {x 3} {- x 2}} {with {x 10} {* x 2}} {with {x 8} {/ x 2}}})
(parse-cfwaes `{with {x 2} {with {y 3} {+ x y}}})
(parse-cfwaes `{fun {x} {+ x 1}})
(parse-cfwaes `{fun {x} x})

;;;; Testing the elaborator from CFWAES to CFAES
(elab-cfwaes (binop 'add (num 1) (num 2)))
(elab-cfwaes (binop 'add (binop 'sub (binop 'sub (num 4) (num 3)) (num 15)) (binop 'add (binop 'add (binop 'sub (num 10) (num 5)) (binop 'sub (num 3) (num 2))) (binop 'sub (num 15) (num 42)))))
(elab-cfwaes (binop 'div (num 50) (num 5)))
(elab-cfwaes (binop 'add (num 1) (num 2)))
(elab-cfwaes (binop 'mul (num 2) (num 2)))
(elab-cfwaes (if0 (num 0) (num 1) (num 2)))
(elab-cfwaes (app (fun 'x (id 'x)) (num 5)))
(elab-cfwaes (app (fun 'x (binop 'add (id 'x) (num 1))) (num 1)))
(elab-cfwaes (if0 (app (fun 'x (binop 'sub (id 'x) (num 2))) (num 3)) (app (fun 'x (binop 'mul (id 'x) (num 2))) (num 10)) (app (fun 'x (binop 'div (id 'x) (num 2))) (num 8))))
(elab-cfwaes (app (if0 (num 0) (fun 'x (binop 'add (id 'x) (num 1))) (fun 'x (binop 'add (id 'x) (num 2)))) (num 0)))
(elab-cfwaes (app (fun 'x (app (fun 'y (binop 'add (id 'x) (id 'y))) (num 3))) (num 2)))
(elab-cfwaes (fun 'x (binop 'add (id 'x) (num 1))))
(elab-cfwaes (fun 'x (id 'x)))

;;;; Testing the interpreter for CFAES
; (((4 - 3) - 15) + (((10 - 5) + (3 - 2)) + (15 - 42))) = (1 - 15) + (6 + (-27)) = -14 + (-21) = -35
(interp-cfaes (binopI 'add (binopI 'sub (binopI 'sub (numI 4) (numI 3)) (numI 15)) (binopI 'add (binopI 'add (binopI 'sub (numI 10) (numI 5)) (binopI 'sub (numI 3) (numI 2))) (binopI 'sub (numI 15) (numI 42)))) (mtSub) (mtSto))

; 50 / 5 = 10
(interp-cfaes (binopI 'div (numI 50) (numI 5)) (mtSub) (mtSto))

; 1 + 2 = 3
(interp-cfaes (binopI 'add (numI 1) (numI 2)) (mtSub) (mtSto))

; 2 + 2 = 4
(interp-cfaes (binopI 'mul (numI 2) (numI 2)) (mtSub) (mtSto))

; 0 == 0 => 1
(interp-cfaes (if0I (numI 0) (numI 1) (numI 2)) (mtSub) (mtSto))

; fun(x=5){x} => 5
(interp-cfaes (appI (funI 'x (idI 'x)) (numI 5)) (mtSub) (mtSto))

; fun(x=1){x+1} => 2
(interp-cfaes (appI (funI 'x (binopI 'add (idI 'x) (numI 1))) (numI 1)) (mtSub) (mtSto))

; (3 - 2) != 0 => with x=8, x/2 = 8 / 2 = 4
(interp-cfaes (if0I (appI (funI 'x (binopI 'sub (idI 'x) (numI 2))) (numI 3)) (appI (funI 'x (binopI 'mul (idI 'x) (numI 2))) (numI 10)) (appI (funI 'x (binopI 'div (idI 'x) (numI 2))) (numI 8))) (mtSub) (mtSto))

; 0 == 0 => fun(x=0){x+1} = 1
(interp-cfaes (appI (if0I (numI 0) (funI 'x (binopI 'add (idI 'x) (numI 1))) (funI 'x (binopI 'add (idI 'x) (numI 2)))) (numI 0)) (mtSub) (mtSto))

; x = 2, y = 3; x + y = 5
(interp-cfaes (appI (funI 'x (appI (funI 'y (binopI 'add (idI 'x) (idI 'y))) (numI 3))) (numI 2)) (mtSub) (mtSto))

; Defining the "add one" function
; (closureV 'x (binopI 'add (idI 'x) (numI 1)) (mtSub) (mtSto))
(interp-cfaes (funI 'x (binopI 'add (idI 'x) (numI 1))) (mtSub) (mtSto))

; Defining the identity function
; (closureV 'x (idI 'x) (mtSub) (mtSto))
(interp-cfaes (funI 'x (idI 'x)) (mtSub) (mtSto))