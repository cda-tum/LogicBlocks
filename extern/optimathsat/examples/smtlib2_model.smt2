;; activate model generation
(set-option :produce-models true)

(declare-fun x () Int)
(declare-fun y1 () Int)
(declare-fun y2 () Int)
(declare-fun z () Int)

(assert (= x y1))
(assert (not (= y1 z)))
(assert (= x y2))
(assert (and (> y2 0) (< y2 5)))

(check-sat)

;; ask for the model value of some of the constants
(get-value (x z))

(exit)
