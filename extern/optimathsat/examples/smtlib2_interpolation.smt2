;; activate interpolation
(set-option :produce-interpolants true)

(declare-sort U 0)
(declare-fun x () U)
(declare-fun y1 () U)
(declare-fun y2 () U)
(declare-fun z () U)

(define-fun A1 () Bool (= x y1))
(define-fun A2 () Bool (= y1 z))
(define-fun B () Bool (and (= x y2) (not (= y2 z))))

;; use annotation :interpolation-group to partition the input problem into
;; several groups
(assert (! A1 :interpolation-group g1))
(assert (! A2 :interpolation-group g2))
(assert (! B :interpolation-group g3))

(check-sat)

;; compute an interpolant for the given partition: the argument to
;; get-interpolant is a list of groups forming the A-part of the interpolation
;; problem
(get-interpolant (g1 g2))

(exit)
