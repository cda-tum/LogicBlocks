; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; MINMAX/MAXMIN:
;     These smtlib2 extensions are only supported by OptiMathSAT.
;     These are syntactic-sugar functions that make it easier
;     to define minmax/maxmin objectives.
;     The syntax is:
;
;         (minmax <term_1> ... <term_n>)
;         (maxmin <term_1> ... <term_n>)
;
; MINMAX:
;     Minimize the maximum possible loss for a worst-case scenario.
;
; MAXMIN:
;     Maximize the minimum possible gain for a worst-case scenario.
;

;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :produce-models true)
(set-option :opt.priority box)

;
; PROBLEM
;
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (and
    (<= 10 x) (<= x 100)
    (<=  0 y) (<= y  50)
    (<= 17 z) (<= z  42)
))

;
; GOAL:
;
(minmax x y z)
(maxmin x y z)

;
; OPTIMIZATION
;
(check-sat)
(get-objectives)
(get-model)
(exit)
