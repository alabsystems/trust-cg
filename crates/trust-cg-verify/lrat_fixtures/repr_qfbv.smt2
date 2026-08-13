(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x #x01) x))
(check-sat)
