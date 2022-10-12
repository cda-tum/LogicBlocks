; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; MINMAX/MAXMIN:
;     This file contains a variety of syntax examples which
;     depict minmax/maxmin usage with OptiMathSAT, focusing
;     in particular on how to combine terms of different
;     theories together.
;
;     Rules:
;     - all terms of a minmax/maxmin objective must have
;       the same type.
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :opt.priority box)
(set-option :produce-models true)

;
; PROBLEM
;
(declare-fun r () Real)
(declare-fun i () Int)
(declare-fun b8 () (_ BitVec 8))
(declare-fun b4 () (_ BitVec 4))
(declare-fun f8 () (_ FloatingPoint 3 5))
(declare-fun f16 () (_ FloatingPoint 6 10))

(assert (< r 14))
(assert (< i 13))
(assert (bvule b8 #b00001100))
(assert (bvsle b4 #b0001))
(assert (fp.leq f8 (fp #b0 #b010 #b0010)))

(assert (not (fp.isNaN f8)))
(assert (not (fp.isInfinite f8)))
(assert (not (fp.isNaN f16)))
(assert (not (fp.isInfinite f16)))


;
; REAL
;
(minmax r
        (to_real i)
        (ubv_to_int b8)
)

;
; INT
;
(minmax (to_int r)
        i
        (sbv_to_int b8)
)


;
; BV
;
(minmax ((_ extract 3 0) b8)
        b4
)
(minmax ((_ to_bv 8) (to_int r))
        ((_ to_bv 8) i)
        b8
        ((_ fp.to_ubv 8) RNE f8)
        ((_ zero_extend 4) b4)
)
(minmax ((_ to_bv 8) (to_int r))
        ((_ to_bv 8) i)
        b8
        ((_ fp.to_sbv 8) RNE f8)
        ((_ sign_extend 4) b4)
        :signed
)


;
; FP
;
(minmax 
        ((_ to_fp 3 5) RNE b8)
        ((_ to_fp_unsigned 3 5) RNE b4)
        f8
        ((_ to_fp 3 5) RNE f16)
)


;
; OPTIMIZATION + GET VALUES
;
(check-sat)
(get-objectives)

(exit)
