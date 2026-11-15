(set-logic QF_FP)
(declare-const a (_ FloatingPoint 8 24))
(assert (not (= (fp.neg (fp.neg a)) a)))
(check-sat)
