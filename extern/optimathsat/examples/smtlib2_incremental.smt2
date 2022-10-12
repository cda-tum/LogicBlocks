;; setting the :global-declarations option to true will turn off the scoping of
;; declarations and definitions. According to the SMT-LIBv2 standard, in the
;; scoped option, declarations and definitions should be scoped wrt. the current
;; assertion stack. However, sometimes this behaviour is not desirable. MathSAT
;; support both scoped and global declarations (with scoped declarations being
;; the default)
(set-option :global-declarations true)

(set-option :produce-models true)
            
(declare-fun x () Int)
(declare-fun y () Int)

(assert (> x 0)) ;; a permanent constraint
(push 1) ;; push a backtracking point
(assert (< x 0))
(check-sat)

(declare-fun z () Int)
(pop 1)

;; with global declarations, z is still in scope
(assert (= z (+ x 3)))
(push 1)
(assert (< y x))

(declare-fun A () Bool)
(assert (= A (= z (+ y 3))))
(declare-fun B () Bool)
(assert (= B (= x (- 5))))

;; MathSAT supports the (non-standard) command check-sat-assumptions, for
;; checking satisfiability under the given assumptions. At the moment,
;; assumptions can only be Boolean constants. However, arbitrary constraints
;; can be used as assumptions by simply "labeling" them with Boolean
;; constants, as done here
(check-sat-assumptions (A B))

;; for unsatisfiable problems, it is possible to get the set of assumptions
;; responsible for the unsatisfiability, with the get-unsat-assumptions
;; command
(get-unsat-assumptions)


;; the reset-assertions command can be used to remove ALL the assertions (and
;; backtracking points), even those added before any push command
(reset-assertions)
;; the global (> x 0) constraint has been removed, so adding (< x 0) does not
;; lead to unsatisfiability
(assert (< x 0))
(check-sat)

;; compute the model value for x
(get-value (x))

(exit)
