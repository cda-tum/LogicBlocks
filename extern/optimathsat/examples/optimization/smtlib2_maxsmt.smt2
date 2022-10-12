; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; ASSERT-SOFT:
;     Both OptiMathSAT and Z3 support the command
;
;         (assert-soft <term> :weight <term> :id <string>)
;
;     but they handle it differently. Z3 minimizes by
;     default the objective function identified by <string>,
;     whereas OptiMathSAT does not. To emulate Z3's behaviour,
;     append the following line before the next (check-sat)
;     in the formula:
;
;         (minimize <string>)
;
;     In OptiMathSAT, (assert-soft ...) can be used to define
;     arbitrary Pseudo-Boolean objectives, which can be either
;     minimized or maximized. To that extent, the weight of
;     a soft-clause is allowed to have zero or negative value.
;     The corresponding goal <string> can be used inside other
;     constraints (e.g. to express a cardinality constraint over
;     a PB sum) or combined with other expressions to form more
;     complex objectives. 
;
; WARNING:
;     OptiMathSAT and Z3 handle the :weight argument differently.
;     Its argument is a <term> for OptiMathSAT, whereas it is a 
;     <numeral> constant for Z3.
;     (for more details about syntax,
;                       see: smtlib2_assert_soft.smt2)
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

;
; MaxSMT Engine:
; - omt:    use OMT-based encoding & engine
; - maxres: use Maximum Resolution engine
; - ext:    use external MaxSAT solver (only via API)
;
(set-option :produce-models true)
(set-option :opt.maxsmt_engine maxres)

;
; MaxSMT PROBLEM
;
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x (- y)))
(assert-soft (< x 0) :weight 1 :id goal)
(assert-soft (< x y) :weight 1 :id goal)
(assert-soft (< y 0) :weight 1 :id goal)

;
; GOAL
;
(minimize goal)

;
; OPTIMIZATION + OPTIMUM VALUE
;
(check-sat)
(get-objectives)

(exit)

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

;
; OTHER ASSERT-SOFT OPTIONS
;     The following options are meaningful only when OptiMathSAT
;     is configured to use OMT-based engine to solve MaxSMT/PB
;     problems. They are also only effective if the corresponding
;     MaxSMT/PB problem is encoded using the command:
;         (assert-soft <term> :id <string> :weight <term>)
; 
;
; -opt.asoft.circuit_limit=INT
;          If greater than zero, pb/maxsmt terms involving more than the 
;          selected number of soft-clauses are split into smaller chunks. 
;          (default: 20) 
; -opt.asoft.encoding=STR
;          Sets the encoding of pb/maxsmt terms defined with soft-clauses:
;           - la  : linear arithmetic encoding
;           - seq : sequential counter encoding
;           - car : cardinality network encoding (default)
; -opt.asoft.no_bidirection=BOOL
;          If true, the pb/maxsmt encoding is not bidirectional and is 
;          guaranteed to yield a correct value only if the corresponding 
;          objective function is minimized. (default: false) 
; -opt.asoft.prefer_pbterms=BOOL
;          If true, Boolean labels associated with soft-clauses are added to the 
;          list of preferred Boolean variables for branching. Has no effect if 
;          'opt.asoft.reduce_vars' is true. (default: true) 
; -opt.asoft.reduce_vars=BOOL
;          If true, no Boolean label is associated with soft-clauses. (default: 
;          false) 
; -opt.maxsmt_engine=STR
;          Sets the solving engine for dealing with pb/maxsmt objectives:
;           - omt    : standard OMT techniques (default)
;           - maxres : Maximum Resolution engine
;           - ext    : external maxsat engine (ex lemma-lifting approach)
;          The option 'unsat_core_generation' is required by maxres.
