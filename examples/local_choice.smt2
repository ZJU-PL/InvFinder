; The universally quantified Horn local becomes an existential transition
; choice when the relation predicate is removed. It must not remain free.
(set-logic HORN)
(declare-fun inv ((_ BitVec 4)) Bool)
(assert (inv #x0))
(assert (forall ((x (_ BitVec 4)) (next (_ BitVec 4)) (choice (_ BitVec 4)))
  (=> (and (inv x) (bvult x #x3) (bvule choice #x1)
           (= next (bvadd x choice)))
      (inv next))))
(assert (forall ((x (_ BitVec 4)))
  (=> (and (inv x) (bvugt x #x3)) false)))
(check-sat)
