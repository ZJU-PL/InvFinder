(set-logic HORN)
(declare-fun inv ((_ BitVec 4)) Bool)
(assert (forall ((x (_ BitVec 4))) (=> (= x #x0) (inv x))))
(assert (forall ((x (_ BitVec 4)) (xp (_ BitVec 4)))
    (=> (and (inv x)
         (= xp (ite (bvuge x #xc) #x1
               (ite (= (bvand x #x1) #x1) #xf
                 (ite (bvult x #xa) (bvadd x #x2) x)))))
        (inv xp))))
(assert (forall ((x (_ BitVec 4)))
    (=> (inv x) (and (bvule x #xa) (= (bvand x #x1) #x0)))))
(check-sat)
