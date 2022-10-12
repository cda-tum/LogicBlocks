;; activate unsat core computation
(set-option :produce-unsat-cores true)

(declare-fun x () Int)
(declare-fun y1 () Int)
(declare-fun y2 () Int)
(declare-fun z () Int)

(define-fun A1 () Bool (= x y1))
(define-fun A2 () Bool (not (< z 0)))
(define-fun A3 () Bool (= y1 z))
(define-fun B () Bool (and (= x y2) (not (= y2 z))))

;; use annotation :named to give a name to toplevel formulas. The
;; unsatisfiable core will be a subset of the named formulas. If a toplevel
;; formula doesn't have a name, it will not be part of the unsat core
(assert (! A1 :named First))
(assert (! A2 :named Second))
(assert (! A3 :named Third))
(assert B)

(check-sat)
(get-unsat-core)

(exit)
