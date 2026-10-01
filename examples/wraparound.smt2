; Addition wraps modulo 16: reachable loop-head values are 14, 15, and 0.
; The least ordinary unsigned interval containing them is the top interval.
(set-logic HORN)
(declare-fun inv ((_ BitVec 4)) Bool)
(assert (inv #xe))
(assert (forall ((x (_ BitVec 4)))
  (=> (and (inv x) (distinct x #x0)) (inv (bvadd x #x1)))))
(assert (forall ((x (_ BitVec 4)))
  (=> (inv x) true)))
(check-sat)
