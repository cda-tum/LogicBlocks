; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; OMT(FP) REDUCTION TO OMT(BV):
;     This file contains an example of how OMT(FP) can be
;     reduced to OMT(BV) using OptiMathSAT. This encoding
;     is quite general, and should be applicable with any
;     other OMT(BV) solver out there.
;
;     Please note that OptiMathSAT has native OMT(FP) procedures
;     that are much easier to use.
;
;     In this example, the minimization of an FP goal 'fp_term'
;     is reduced to the minimization of a BV goal 'minimization_goal',
;     and the maximization of an FP goal 'fp_term' is reduced to
;     the maximization of a BV goal 'maximization_goal'.
;
;     The encoding for the OMT(FP) to OMT(BV) reduction is
;     completed with a couple of usage examples that
;     demonstrate the desired functionality.
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :produce-models true)

;
; ORIGINAL PROBLEM
;

(declare-fun fp_term () (_ FloatingPoint 3 5))


;
; OMT(FP) to OMT(BV) REDUCTION
;

(define-fun _bv_zero () (_ BitVec 8) #b00000000)

(define-fun _bv_min_neg_mask () (_ BitVec 8) #b11111111)
(define-fun _bv_min_pos_mask () (_ BitVec 8) #b00000000)
(define-fun _bv_max_pos_mask () (_ BitVec 8) #b01111111)
(define-fun _bv_max_neg_mask () (_ BitVec 8) #b10000000)

; support functions

(define-fun _bv_xor ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    (bvor (bvand x (bvnot y)) (bvand (bvnot x) y))
)
(define-fun _bv_nxor ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    (bvor (bvand x y) (bvand (bvnot x) (bvnot y)))
)

; support variables

(declare-fun bv_term () (_ BitVec 8))
(declare-fun minimization_goal () (_ BitVec 10))
(declare-fun maximization_goal () (_ BitVec 10))

; constraints

(assert (= ((_ to_fp 3 5) bv_term) fp_term))

(assert (=> (= #b0 ((_ extract 9 9) minimization_goal)) (not (fp.isNaN fp_term))))
(assert (=> (= #b0 ((_ extract 8 8) minimization_goal)) (fp.isNegative fp_term))))
(assert (=  ((_ extract 7 0) minimization_goal)
            (_bv_xor bv_term
                     (ite (= #b00 ((_ extract 9 8) minimization_goal)) _bv_min_neg_mask
                     (ite (= #b01 ((_ extract 9 8) minimization_goal)) _bv_min_pos_mask
                                                                       _bv_zero
            )))
))

(assert (=> (= #b1 ((_ extract 9 9) maximization_goal)) (not (fp.isNaN fp_term))))
(assert (=> (= #b1 ((_ extract 8 8) maximization_goal)) (fp.isPositive fp_term))))
(assert (=  ((_ extract 7 0) maximization_goal)
            (_bv_nxor bv_term
                     (ite (= #b11 ((_ extract 9 8) maximization_goal)) _bv_max_pos_mask
                     (ite (= #b10 ((_ extract 9 8) maximization_goal)) _bv_max_neg_mask
                                                                       _bv_zero
            )))
))


;
; USAGE EXAMPLE(s)
;

; Maximization
(push 1)
    (maximize maximization_goal)    ; maximize fp_term

    (check-sat)
    (get-value (fp_term))

    (push 1)
        ; goal forced in the negative domain
        (assert (fp.leq fp_term (fp #b1 #b001 #b0100)))

        (check-sat)
        (get-value (fp_term))
    (pop 1)
(pop 1)

; Minimizaiton
(push 1)
    (minimize minimization_goal)    ; minimize fp_term

    (check-sat)
    (get-value (fp_term))

    (push 1)
        ; goal forced in the positive domain
        (assert (fp.leq (fp #b0 #b001 #b0100) fp_term))

        (check-sat)
        (get-value (fp_term))
    (pop 1)
(pop 1)

; Goal can only be equal NaN,
; for some binary encoding of NaN
(push 1)
    (assert (fp.isNaN fp_term))

    (minimize minimization_goal)

    (check-sat)
    (get-value (fp_term))
(pop 1)

(exit)
