#lang plai
;;;;
;; CFAE stuff
(define-type CFAE
    (numI (n number?))
    (binopI (op symbol?) (lhs CFAE?) (rhs CFAE?))
    (appI (fun-expr CFAE?) (arg-expr CFAE?))
    (funI (param symbol?) (body CFAE?))
    (if0I (test CFAE?) (iftrue CFAE?) (iffalse CFAE?))
    (idI (name symbol?)))

(define interp-cfae
    (lambda (a-cfae ds)
        (type-case CFAE a-cfae
            (numI (x) (numV x))
            (binopI (op l r)
                (numV ((lookup op ops)
                    (numV-n (interp-cfae l ds))
                    (numV-n (interp-cfae r ds)))))
            (idI (v) (dslookup v ds))
            (if0I (test iftrue iffalse)
                (if (zero? (numV-n (interp-cfae test ds)))
                    (interp-cfae iftrue ds)
                    (interp-cfae iffalse ds)))
            (funI (bound-id bound-body) (closureV bound-id bound-body ds))
            (appI (fun-expr arg-expr) 
                (local ((define fun-val (interp-cfae fun-expr ds)))
                    (interp-cfae (closureV-body fun-val)
                        (aSub (closureV-param fun-val)
                            (interp-cfae arg-expr ds)
                            (closureV-ds fun-val))))))))

(define-type CFAE-value
    (numV (n number?))
    (closureV (param symbol?) (body CFAE?) (ds DefSub?)))

;;;;
;; CFWAE stuff
;;
(define-type CFWAE
    (num (n number?))
    (binop (op symbol?) (lhs CFWAE?) (rhs CFWAE?))
    (app (fun-expr CFWAE?) (arg-expr CFWAE?))
    (fun (param symbol?) (body CFWAE?))
    (with (name symbol?) (named-expr CFWAE?) (body CFWAE?))
    (if0 (test CFWAE?) (iftrue CFWAE?) (iffalse CFWAE?))
    (id (name symbol?)))

(define elab-cfwae
    (lambda (a-cfwae)
        (type-case CFWAE a-cfwae
            (num (x) (numI x))
            (binop (op l r) (binopI op (elab-cfwae l) (elab-cfwae r)))
            (app (fun-expr arg-expr) (appI (elab-cfwae fun-expr) (elab-cfwae arg-expr)))
            (fun (param body) (funI param (elab-cfwae body)))
            (with (name named-expr body) (appI (funI name (elab-cfwae body)) (elab-cfwae named-expr)))
            (if0 (test iftrue iffalse) (if0I (elab-cfwae test) (elab-cfwae iftrue) (elab-cfwae iffalse)))
            (id (name) (idI name)))))

; The CFWAE parser is basically identical to the parser for CFWAER given in the
; assignment. The only exception is the lack of the (rec) case.
(define parse-cfwae
    (lambda (expr)
        (cond ((symbol? expr) (id expr))
            ((number? expr) (num expr))
            ((list? expr)
                (case (car expr)
                    ((-) (binop 'sub (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))
                    ((+) (binop 'add (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))
                    ((*) (binop 'mul (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))
                    ((/) (binop 'div (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))
                    ((with) (with (car (cadr expr)) 
                        (parse-cfwae (cadr (cadr expr))) 
                        (parse-cfwae (caddr expr))))
                    ((if0) (if0 (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))
                        (parse-cfwae (cadddr expr))))
                    ((fun) (fun (caadr expr) (parse-cfwae (caddr expr))))
                (else (app (parse-cfwae (car expr)) (parse-cfwae (cadr expr))))))
            (else 'parse-cfwae "Unexpected token"))))

; Since I am using an elaborator to eliminate the (with) part of the language,
; the interpreter is in the CFAE section of the code. This function serves as a
; wrapper for elaborating the CFWAE into a CFAE, then interpreting it
(define interp-cfwae (lambda (expr env) (interp-cfae (elab-cfwae expr) env)))

; Parse the expression, then pass it to the CFAE interpreter via the CFWAE
; interpreter/elaborator
(define eval-cfwae (lambda (expr) (interp-cfwae (parse-cfwae expr) (mtSub))))

;;;;
;; Deferred substitution stuff
;;
(define-type DefSub
    (mtSub)
    (aSub (name symbol?) (value CFAE-value?) (ds DefSub?)))

(define (dslookup name ds)
    (type-case DefSub ds
        (mtSub () (error 'dslookup "Unbound identifier"))
        (aSub (bound-name bound-value rest-ds)
            (if (symbol=? bound-name name)
                bound-value
                (dslookup name rest-ds)))))

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

;;;; Testing the complete evaluator for CFWAE
(eval-cfwae `{+ 5 {- 3 2}})

;;;; Testing the parser for CFWAE
(parse-cfwae `{+ 5 {- 3 2}})
(parse-cfwae `{+ 1 2})
(parse-cfwae `{+ {- {- 4 3} 15} {+ {+ {- 10 5} {- 3 2}} {- 15 42}}})
(parse-cfwae `{/ 50 5})
(parse-cfwae `{+ 1 2})
(parse-cfwae `{* 2 2})
(parse-cfwae `{if0 0 1 2})
(parse-cfwae `{with {x 5} x})
(parse-cfwae `{with {x 1} {+ x 1}})
(parse-cfwae `{if0 {with {x 3} {- x 2}} {with {x 10} {* x 2}} {with {x 8} {/ x 2}}})
(parse-cfwae `{with {x 2} {with {y 3} {+ x y}}})
(parse-cfwae `{fun {x} {+ x 1}})
(parse-cfwae `{fun {x} x})

;;;; Testing the elaborator from CFWAE to CFAE
(elab-cfwae (binop 'add (num 1) (num 2)))
(elab-cfwae (binop 'add (binop 'sub (binop 'sub (num 4) (num 3)) (num 15)) (binop 'add (binop 'add (binop 'sub (num 10) (num 5)) (binop 'sub (num 3) (num 2))) (binop 'sub (num 15) (num 42)))))
(elab-cfwae (binop 'div (num 50) (num 5)))
(elab-cfwae (binop 'add (num 1) (num 2)))
(elab-cfwae (binop 'mul (num 2) (num 2)))
(elab-cfwae (if0 (num 0) (num 1) (num 2)))
(elab-cfwae (app (fun 'x (id 'x)) (num 5)))
(elab-cfwae (app (fun 'x (binop 'add (id 'x) (num 1))) (num 1)))
(elab-cfwae (if0 (app (fun 'x (binop 'sub (id 'x) (num 2))) (num 3)) (app (fun 'x (binop 'mul (id 'x) (num 2))) (num 10)) (app (fun 'x (binop 'div (id 'x) (num 2))) (num 8))))
(elab-cfwae (app (if0 (num 0) (fun 'x (binop 'add (id 'x) (num 1))) (fun 'x (binop 'add (id 'x) (num 2)))) (num 0)))
(elab-cfwae (app (fun 'x (app (fun 'y (binop 'add (id 'x) (id 'y))) (num 3))) (num 2)))
(elab-cfwae (fun 'x (binop 'add (id 'x) (num 1))))
(elab-cfwae (fun 'x (id 'x)))

;;;; Testing the interpreter for CFAE
; (((4 - 3) - 15) + (((10 - 5) + (3 - 2)) + (15 - 42))) = (1 - 15) + (6 + (-27)) = -14 + (-21) = -35
(interp-cfae (binopI 'add (binopI 'sub (binopI 'sub (numI 4) (numI 3)) (numI 15)) (binopI 'add (binopI 'add (binopI 'sub (numI 10) (numI 5)) (binopI 'sub (numI 3) (numI 2))) (binopI 'sub (numI 15) (numI 42)))) (mtSub))

; 50 / 5 = 10
(interp-cfae (binopI 'div (numI 50) (numI 5)) (mtSub))

; 1 + 2 = 3
(interp-cfae (binopI 'add (numI 1) (numI 2)) (mtSub))

; 2 + 2 = 4
(interp-cfae (binopI 'mul (numI 2) (numI 2)) (mtSub))

; 0 == 0 => 1
(interp-cfae (if0I (numI 0) (numI 1) (numI 2)) (mtSub))

; fun(x=5){x} => 5
(interp-cfae (appI (funI 'x (idI 'x)) (numI 5)) (mtSub))

; fun(x=1){x+1} => 2
(interp-cfae (appI (funI 'x (binopI 'add (idI 'x) (numI 1))) (numI 1)) (mtSub))

; (3 - 2) != 0 => with x=8, x/2 = 8 / 2 = 4
(interp-cfae (if0I (appI (funI 'x (binopI 'sub (idI 'x) (numI 2))) (numI 3)) (appI (funI 'x (binopI 'mul (idI 'x) (numI 2))) (numI 10)) (appI (funI 'x (binopI 'div (idI 'x) (numI 2))) (numI 8))) (mtSub))

; 0 == 0 => fun(x=0){x+1} = 1
(interp-cfae (appI (if0I (numI 0) (funI 'x (binopI 'add (idI 'x) (numI 1))) (funI 'x (binopI 'add (idI 'x) (numI 2)))) (numI 0)) (mtSub))

; x = 2, y = 3; x + y = 5
(interp-cfae (appI (funI 'x (appI (funI 'y (binopI 'add (idI 'x) (idI 'y))) (numI 3))) (numI 2)) (mtSub))

; Defining the "add one" function
; (closureV 'x (binopI 'add (idI 'x) (numI 1)) (mtSub))
(interp-cfae (funI 'x (binopI 'add (idI 'x) (numI 1))) (mtSub))

; Defining the identity function
; (closureV 'x (idI 'x) (mtSub))
(interp-cfae (funI 'x (idI 'x)) (mtSub))