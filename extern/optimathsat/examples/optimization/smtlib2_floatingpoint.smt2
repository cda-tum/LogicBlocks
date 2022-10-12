; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; FLOATING-POINT OPTIMIZATION:
;     OptiMathSAT supports Floating-Point optimization.
;
;     A solution to a FP problem wherein the cost
;     function is NaN is considered optimal only if
;     it is not possible to assign it with any other
;     FP value.
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :produce-models true)
(set-option :config opt.priority=box)
(set-option :config opt.verbose=true)

;
; PROBLEM
;
(define-fun _m_inf () (_ FloatingPoint 8 24) (fp #b1 #b11111111 #b00000000000000000000000))
(define-fun _m_ten () (_ FloatingPoint 8 24) (fp #b1 #b10000010 #b01000000000000000000000))
(define-fun _zero  () (_ FloatingPoint 8 24) (fp #b0 #b00000000 #b00000000000000000000000))
(define-fun _p_ten () (_ FloatingPoint 8 24) (fp #b0 #b10000010 #b01000000000000000000000))
(define-fun _p_inf () (_ FloatingPoint 8 24) (fp #b0 #b11111111 #b00000000000000000000000))
(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
(declare-fun x3 () (_ FloatingPoint 8 24))
(assert (and
        (fp.leq _m_ten x0)
        (fp.leq x0 _p_ten)
))
(assert (= x1 _zero))
(assert (= x2 (_ NaN 8 24)))
(assert (and
        (fp.leq _m_inf x3)
        (fp.leq x3 _p_inf)
))

;
; GOALS
;
(minimize x0)
(maximize x0)
(minimize x1)
(minimize x2)
(minimize x3)
(maximize x3)

;
;  OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)

; FLOATING POINT OPTIMIZATION OPTIONS
;
; -opt.theory.fp.engine=STR
;          Sets the solving engine for dealing FP objectives:
;           - omt    : standard OMT techniques
;           - ofpbs  : FP optimization with binary search over the bits (default)
;           - ofpbls : FP optimization with binary search with linear cuts
; -opt.theory.fp.branch_preference=BOOL
;          If true, it sets a branching preference on the FP objective. 
;          (default: false) 
; -opt.theory.fp.polarity=BOOL
;          If true, sets the initial polarity of any FP objective towards the 
;          maximum gain direction. (default: true) 
; -opt.theory.fp.safe_bits_only=BOOL
;          If true, polarity and branch_preference are only set for those bits 
;          for which the maximum gain direction is certain. (default: true)
;
; ENGINES LIMITATIONS:
;       - OFPBS: requires -theory.fp.mode=1
;       - OMT/OFPBLS: if -theory.fp.mode=0,
;                     then requires -theory.fp.bv_combination_enabled=False
;
; -theory.fp.mode=INT
;          Select which FP solver to use. Possible values are:
;          - 0 : BV encoding with lazy bit-blasting
;          - 1 : BV encoding with eager bit-blasting
;          - 2 : ACDCL with interval domain.
;

