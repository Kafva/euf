;; Lets say we want to check if the lhs and rhs are equivlanent for:
;;	( a && b || c ) == ( a && c || b )
;; Variables are declared as 'functions' in SMT
;; The types in SMT are reffered to as 'Sorts' (in simplified terms)
;;
;; The language itself is essentially LISP

;; Required for using (get-proof)
(set-option :produce-proofs true)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)

;; The (assert) command passes constraints to the SMT solver
;; we can techincally invoke it several times to add mutliple expressions with a logical (and)
;;(assert  (= (or (and a b) c)  (or (and a c) b) ) )

;; Check if satisfiable
;;(check-sat)
;;
;;
;;;; Check if the negation is satisifiable
;;;; Unsat => the expressions are equivlanent
;;(reset-assertions)
;;(assert  (not (= (or (and a b) c)  (or (and a c) b) ) ))
;;(check-sat)


;; Equivlanent example
;;	(a && b) || (a && b || c)  == (a && b) || c

;; def ex(a,b,c):
;;    return [ (a and b) or (a and b and c), (a and b) or c  ]


(reset-assertions)
(assert  (not (= 
	(or (and a b) (or (and a b) c))  
	(or (and a b) c)  
)))
(check-sat)
(get-proof)
