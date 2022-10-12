; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; WARNING:
;     OptiMathSAT and Z3 have different default behaviours
;     when multiple objectives are optimized in the same
;     formula. Z3 handles them lexicographically, whereas
;     OptiMathSAT handles them in boxed (multi-independent) mode.
;     Therefore, the following option should be correctly
;     set on any boxed/multi-independent formula:
;
;         (set-option :opt.priority box)
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
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (and
        (<= 42 x)
        (<= y x)
        (<= z 24)
))

;
; GOALS
;
(minimize x)
(maximize y)
(maximize z)

;
; OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)

;
; BOXED OPTIMIZATION OPTIONS
;
; -opt.box.branch_preference=BOOL
;          Prefer branching on optimization search cuts. (default: true)
; -opt.box.engine=STR
;          Configures the engine for Multiple-Independent/Boxed optimization. 
;          Possible values are:  
;          - dpll: dpll-based boxed optimization (default)
;          - full: incremental optimization, one objective at a time
;          - partial: incremental optimization, all objectives at the same time
; -opt.box.shuffle=BOOL
;          Optimize objectives in random order. (default: true)
;
