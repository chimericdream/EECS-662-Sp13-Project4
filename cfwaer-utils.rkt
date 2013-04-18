#lang plai
;;; EECS 662 - Miniproject 3 Support Functions
;;;
;;; Author: Perry Alexander
;;; Date: 4/10/13
;;;
;;; Description:
;;; CFWAER - The abstract data type for representing CFWAER ASTs
;;; parse-cfwaer - Parser translating concrete CFWAER syntax into CFWAER AST
;;; fac5 - Concrete syntax for the example from class
;;;

;;; Define an AST type for CFWAER constructs.
(define-type CFWAER
  (num (n number?))
  (add (lhs CFWAER?) (rhs CFWAER?))
  (sub (lhs CFWAER?) (rhs CFWAER?))
  (mul (lhs CFWAER?) (rhs CFWAER?))
  (div (lhs CFWAER?) (rhs CFWAER?))
  (id (name symbol?))
  (with (name symbol?) (named-expr CFWAER?) (body CFWAER?))
  (rec (name symbol?) (named-expr CFWAER?) (body CFWAER?))
  (if0 (cond CFWAER?) (tarm CFWAER?) (farm CFWAER?))
  (fun (arg-name symbol?) (body CFWAER?))
  (app (fun-expr CFWAER?)(arg CFWAER?)))

;;; Define a parser for CFWAER constructs.  This parser does no error checking at all. Simply converts
;;; concrete syntax to AST.
(define parse-cfwaer
  (lambda (expr)
    (cond ((symbol? expr) (id expr))
          ((number? expr) (num expr))
          ((list? expr)
           (case (car expr)
             ((-) (sub (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
             ((+) (add (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
             ((*) (mul (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
             ((/) (div (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
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

;;; Factorial example from class.  Try (parse-cfwaer fac5) to see the parser produce an AST
;;; for the example.

(define fac5
  `{rec {fac {fun {n} {if0 n 1 {* n {fac {+ n -1}}}}}}{fac 5}}
  )
