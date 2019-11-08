(declare-const PC!68 (_ BitVec 64))
(declare-const PC!67 (_ BitVec 64))
(assert 
   (= PC!68 PC!67))
(check-sat)
(get-value (
  PC!68
  PC!67
  ))
(get-model)
(exit)
