; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; BITVECTOR OPTIMIZATION:
;     Both OptiMathSAT and Z3 support Bit-Vector optimization.
;     OptiMathSAT allows the user to specify whether a BV
;     objective is intended as signed or not by means of
;     an additional (optional) parameter ':signed', e.g.
;
;         (minimize <bv_term> :signed)
;         (maximize <bv_term>)
;
;     When ':signed' is not specified, OptiMathSAT interprets
;     the BV goal as an unsigned term.
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
(declare-fun x () (_ BitVec 8))
(assert (or
    (and (bvsle ((_ to_bv 8) 120) x)
         (bvsle x ((_ to_bv 8) 120))
    )
    (and (bvsle ((_ to_bv 8) 97) x)
         (bvsle x ((_ to_bv 8) 97))
    )
    (and (bvsle ((_ to_bv 8) 54) x)
         (bvsle x ((_ to_bv 8) 54))
    )
    (and (bvsle ((_ to_bv 8) 32) x)
         (bvsle x ((_ to_bv 8) 32))
    )
    (and (bvsle ((_ to_bv 8) 22) x)
         (bvsle x ((_ to_bv 8) 22))
    )
    (and (bvsle ((_ to_bv 8) 11) x)
         (bvsle x ((_ to_bv 8) 11))
    )
    (and (bvsle ((_ to_bv 8) 8) x)
         (bvsle x ((_ to_bv 8) 8))
    )
    (and (bvsle ((_ to_bv 8) (- 7)) x)
         (bvsle x ((_ to_bv 8) (- 7)))
    )
    (and (bvsle ((_ to_bv 8) (- 16)) x)
         (bvsle x ((_ to_bv 8) (- 16)))
    )
    (and (bvsle ((_ to_bv 8) (- 105)) x)
         (bvsle x ((_ to_bv 8) (- 105)))
    )
))

;
; GOALS
;
(minimize x)
(minimize x :signed)

;
; OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

;
; BITVECTOR OPTIMIZATION OPTIONS
;
; -theory.bv.eager=BOOL
;          If true, BV atoms will be bit-blasted into the main DPLL solver.
; -opt.theory.bv.engine=STR
;          Sets the solving engine for dealing BitVector objectives:
;           - omt   : standard OMT techniques
;           - obvwa : bit-vector optimization with weak assumptions
;           - obvbs : bit-vector optimization with binary search (default)
; -opt.theory.bv.branch_preference=BOOL
;          If true, it sets a branching preference on the BV objective. 
;          (default: true) 
; -opt.theory.bv.polarity=BOOL
;          If true, sets the initial polarity of any BV objective towards the 
;          maximum gain direction. (default: true) 
;
