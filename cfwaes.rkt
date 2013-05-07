#lang plai
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
    (seqn (expr1 CFWAES?) (expr2 CFWAES?))
    (assign (id symbol?) (expr CFWAES?))
    (id (name symbol?)))

(define-type CFWAES-value
    (numV (n number?))
    (closureV (param symbol?) (body CFWAES?) (env Env?) (sto Store?))
    (boxV (location number?)))

(define-type ValueXStore
    (vxs (value CFWAES-value?) (store Store?)))

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
                    ((seqn) (seqn (parse-cfwaes (cadr expr)) (parse-cfwaes (caddr expr))))
                    ((assign) (assign (cadr expr) (parse-cfwaes (caddr expr))))
                (else (app (parse-cfwaes (car expr)) (parse-cfwaes (cadr expr))))))
            (else 'parse-cfwaes "Unexpected token"))))

(define interp-cfwaes
    (lambda (expr env sto)
        (type-case CFWAES expr
            (num (n) (vxs (numV n) sto))
            (binop (op l r)
                (type-case ValueXStore (interp-cfwaes l env sto)
                    (vxs (v1 s1)
                        (type-case ValueXStore (interp-cfwaes r env s1)
                            (vxs (v2 s2)
                                (vxs (numV ((lookup op ops) (numV-n v1) (numV-n v2))) s2))))))
            (app (fun-expr arg-expr)
                (type-case ValueXStore (interp-cfwaes fun-expr env sto)
                    (vxs (fun-val s1)
                        (type-case ValueXStore (interp-cfwaes arg-expr env s1)
                            (vxs (arg-val s2)
                                (local ((define new-loc (next-location)))
                                    (interp-cfwaes
                                        (closureV-body fun-val)
                                        (aSub (closureV-param fun-val) (boxV new-loc) (closureV-env fun-val))
                                        (aSto new-loc arg-val s2))))))))
            (fun (bound-id bound-body)
                (vxs (closureV bound-id bound-body env sto) sto))
            (with (bound-id bound-expr body)
                (type-case ValueXStore (interp-cfwaes bound-expr env sto)
                    (vxs (expr-val expr-store)
                        (local ((define loc (next-location)))
                            (interp-cfwaes body
                                (aSub bound-id (boxV loc) env)
                                (aSto loc expr-val expr-store))))))
            (if0 (test iftrue iffalse)
                (type-case ValueXStore (interp-cfwaes test env sto)
                    (vxs (if-value s1)
                        (if (zero? (numV-n if-value))
                            (interp-cfwaes iftrue env s1)
                            (interp-cfwaes iffalse env s1)))))
            (seqn (expr1 expr2)
                (type-case ValueXStore (interp-cfwaes expr1 env sto)
                    (vxs (expr1-value expr1-store)
                        (interp-cfwaes expr2 env expr1-store))))
            (assign (lval rval)
                (type-case ValueXStore (interp-cfwaes rval env sto)
                    (vxs (rval-value rval-store)
                        (vxs rval-value
                            (aSto (boxV-location (envlookup lval env)) rval-value rval-store)))))
            (id (v) (vxs (stolookup (envlookup v env) sto) sto)))))

; Parse the expression, then pass it to the CFAES interpreter via the CFWAES
; interpreter/elaborator
(define eval-cfwaes (lambda (expr) (vxs-value (interp-cfwaes (parse-cfwaes expr) (mtSub) (mtSto)))))

;;;;
;; The data store
;;
(define-type Store
    (mtSto)
    (aSto (location number?) (value CFWAES-value?) (sto Store?)))

(define (stolookup loc sto)
    (type-case Store sto
        (mtSto () (error 'stolookup (string-append "Unknown location in store: " (number->string (boxV-location loc)))))
        (aSto (location value rest-sto)
            (if (eq? location (boxV-location loc))
                value
                (stolookup loc rest-sto)))))

(define next-location
    (local ((define loc (box 0)))
        (lambda ()
            (begin (set-box! loc (+ 1 (unbox loc)))
                (unbox loc)))))

;;;;
;; Deferred substitution stuff
;;
(define-type Env
    (mtSub)
    (aSub (name symbol?) (location CFWAES-value?) (env Env?)))

(define (envlookup name env)
    (type-case Env env
        (mtSub () (error 'envlookup (string-append "Unbound identifier: " (symbol->string name))))
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

;;;; Testing the evaluator for CFWAES
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
(eval-cfwaes `{with {x 5} {with {y 10} {with {f {fun {x} {assign y x}}} {with {g {fun {z} {+ z 5}}} {+ {f x} {g y}}}}}})
(eval-cfwaes `{with {x 5} {seqn {with {y 5} {assign x 4}} {+ x 5}}})