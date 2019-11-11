(declare-const PC!80 (_ BitVec 64))
(declare-const %501 (_ BitVec 64))
(declare-const PC!81 (_ BitVec 64))
(declare-const %500 (_ BitVec 64))
(declare-const prev_pc!27 (_ BitVec 64))
(declare-const PC!78 (_ BitVec 64))
(declare-const PC!84 (_ BitVec 64))
(declare-const prev_pc!28 (_ BitVec 64))
(declare-const PC!85 (_ BitVec 64))
(declare-const PC!82 (_ BitVec 64))
(declare-const PC!83 (_ BitVec 64))
(declare-const PC!79 (_ BitVec 64))
(declare-const %495 (_ BitVec 64))
(declare-const XREG!43 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!44 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!41 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %497 (_ BitVec 64))
(declare-const %496 (_ BitVec 64))
(declare-const XREG!42 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %499 (_ BitVec 64))
(declare-const XREG!40 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %498 (_ BitVec 64))
(assert 
   (=
     XREG!41
     (store XREG!40 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!27 PC!78))
(assert 
   (=
     %497
     (select XREG!41 #b01101)))
(assert 
   (=
     %496
     (bvshl %497 #b000011)))
(assert 
   (=
     XREG!42
     (store XREG!41 #b01111 %496)))
(assert 
   (=
     %495
     (bvadd PC!78 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!79 %495))
(assert 
   (= PC!80 %495))
(assert 
   (= PC!81 PC!80))
(assert 
   (=
     XREG!43
     (store XREG!42 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!28 PC!80))
(assert 
   (=
     %500
     (select XREG!43 #b01010)))
(assert 
   (=
     %501
     (select XREG!43 #b01111)))
(assert 
   (=
     %499
     (bvadd %500 %501)))
(assert 
   (=
     XREG!44
     (store XREG!43 #b01111 %499)))
(assert 
   (=
     %498
     (bvadd PC!80 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!85 %498))
(assert 
   (= PC!82 %498))
(assert 
   (= PC!83 PC!82))
(assert 
   (= PC!84 PC!82))
(check-sat)
(get-value (
  PC!80
  %501
  PC!81
  %500
  prev_pc!27
  PC!78
  PC!84
  prev_pc!28
  PC!85
  PC!82
  PC!83
  PC!79
  %495
  XREG!43
  XREG!44
  XREG!41
  %497
  %496
  XREG!42
  %499
  XREG!40
  %498
  ))
(get-model)
(exit)
