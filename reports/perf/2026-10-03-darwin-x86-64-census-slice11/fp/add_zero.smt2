(set-logic QF_FP)
(declare-const a (_ FloatingPoint 11 53))
(assert (not (or (fp.isNaN a) (= (fp.add RNE a (_ -zero 11 53)) a))))
(check-sat)
