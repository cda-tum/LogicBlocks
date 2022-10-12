; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; ASSERT-SOFT:
;     This file contains a variety syntax examples which
;     depict assert-soft usage in OptiMathSAT.
;
;     For more details about assert-soft semantics and
;     handling, please consult:
;
;         smtlib2_maxsmt.smt2
;
;     The general syntax of assert-soft in OptiMathSAT is:
;
;         (assert-soft <term> :weight <term> :id <string>)
;
;     Syntax Rules:
;     - if :id is missing, it is assumed equal to "I"
;     - if :weight is missing, it is assumed equal to 1
;     - a :weight <term> must be or rational or integer type
;     - a :weight <term> must be a constant value
;     - the soft-clause <term> must be of Boolean type
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :produce-models true)
(set-option :opt.priority box)

;
; PROBLEM
;
(define-fun w1 () Int 5)
(declare-fun x () Real)

;
; CORRECT SYNTAX EXAMPLES
;
(assert-soft false                       :id goal) ; weight assumed to be equal 1
(assert-soft false :weight 0             :id goal)
(assert-soft false :weight 5             :id goal)
(assert-soft false :weight 0.5           :id goal)
(assert-soft false :weight (+ 3 (/ 4 2)) :id goal) ; unsupported by Z3 4.6.0
(assert-soft false :weight w1            :id goal) ; unsupported by Z3 4.6.0
(assert-soft false :weight (/ 2 4)       :id goal) ; unsupported by Z3 4.6.0
(assert-soft false :weight (- 16)        :id goal) ; unsupported by Z3 4.6.0
(assert-soft false :weight (- (/ 2 4))   :id goal) ; unsupported by Z3 4.6.0
(assert-soft false :weight (- 0.5)       :id goal) ; unsupported by Z3 4.6.0

;
; INCORRECT SYNTAX EXAMPLES
;
(assert-soft false :weight #b0010 :id goal) ; type error
(assert-soft false :weight x      :id goal) ; non-constant weight
(assert-soft false :weight -5     :id goal) ; unsupported by OptiMathSAT
(assert-soft false :weight -0.5   :id goal) ; unsupported by OptiMathSAT

;
; MaxSMT GOAL
;
(minimize goal)

;
; OPTIMIZATION + OPTIMUM VALUE
;
(check-sat)
(get-objectives)

(exit)
