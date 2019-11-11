(declare-const PC!126 (_ BitVec 64))
(declare-const PC!127 (_ BitVec 64))
(assert 
   (= PC!127 PC!126))
(check-sat)
(get-value (
  PC!126
  PC!127
  ))
(get-model)
(exit)
