(declare-const %721 (_ BitVec 64))
(declare-const PC!122 (_ BitVec 64))
(declare-const %720 (_ BitVec 64))
(declare-const PC!121 (_ BitVec 64))
(declare-const %723 (_ BitVec 64))
(declare-const PC!120 (_ BitVec 64))
(declare-const %722 (_ BitVec 64))
(declare-const PC!125 (_ BitVec 64))
(declare-const PC!123 (_ BitVec 64))
(declare-const PC!119 (_ BitVec 64))
(declare-const PC!118 (_ BitVec 64))
(declare-const PC!117 (_ BitVec 64))
(declare-const %719 (_ BitVec 64))
(declare-const prev_pc!41 (_ BitVec 64))
(declare-const XREG!65 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const prev_pc!40 (_ BitVec 64))
(declare-const XREG!63 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!64 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!61 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!62 (Array (_ BitVec 5) (_ BitVec 64)))
(assert 
   (=
     XREG!62
     (store XREG!61 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!40 PC!117))
(assert 
   (=
     %721
     (select XREG!62 #b00000)))
(assert 
   (=
     %720
     (bvadd %721 #b0000000000000000000000000000000000000000000000000000000000000010)))
(assert 
   (=
     XREG!63
     (store XREG!62 #b01101 %720)))
(assert 
   (=
     %719
     (bvadd PC!117 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!125 %719))
(assert 
   (= PC!118 %719))
(assert 
   (= PC!119 PC!118))
(assert 
   (=
     XREG!64
     (store XREG!63 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!41 PC!118))
(assert 
   (=
     %722
     (bvadd PC!118 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!65
     (store XREG!64 #b00000 %722)))
(assert 
   (=
     %723
     (bvadd PC!118 #b1111111111111111111111111111111111111111111111111111111111010100)))
(assert 
   (= PC!120 %723))
(assert 
   (= PC!121 %723))
(assert 
   (= PC!122 PC!121))
(assert 
   (= PC!123 PC!121))
(check-sat)
(get-value (
  %721
  PC!122
  %720
  PC!121
  %723
  PC!120
  %722
  PC!125
  PC!123
  PC!119
  PC!118
  PC!117
  %719
  prev_pc!41
  XREG!65
  prev_pc!40
  XREG!63
  XREG!64
  XREG!61
  XREG!62
  ))
(get-model)
(exit)
