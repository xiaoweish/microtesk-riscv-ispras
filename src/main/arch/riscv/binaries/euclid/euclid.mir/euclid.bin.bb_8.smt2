(declare-const %61 (_ BitVec 64))
(declare-const %62 (_ BitVec 64))
(declare-const prev_pc!20 (_ BitVec 64))
(declare-const XREG!25 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!23 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!66 (_ BitVec 64))
(declare-const XREG!24 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!64 (_ BitVec 64))
(declare-const PC!65 (_ BitVec 64))
(declare-const PC!62 (_ BitVec 64))
(declare-const PC!61 (_ BitVec 64))
(assert 
   (=
     XREG!24
     (store XREG!23 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!20 PC!61))
(assert 
   (=
     %61
     (bvadd PC!61 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!25
     (store XREG!24 #b00000 %61)))
(assert 
   (=
     %62
     (bvadd PC!61 #b1111111111111111111111111111111111111111111111111111111111110100)))
(assert 
   (= PC!62 %62))
(assert 
   (= PC!64 %62))
(assert 
   (= PC!65 PC!64))
(assert 
   (= PC!66 PC!64))
(check-sat)
(get-value (
  %61
  %62
  prev_pc!20
  XREG!25
  XREG!23
  PC!66
  XREG!24
  PC!64
  PC!65
  PC!62
  PC!61
  ))
(get-model)
(exit)
