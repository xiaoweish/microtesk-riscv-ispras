(declare-const %77 (_ BitVec 1))
(declare-const %78 (_ BitVec 64))
(declare-const %79 (_ BitVec 64))
(declare-const PC!51 (_ BitVec 64))
(declare-const prev_pc!17 (_ BitVec 64))
(declare-const PC!52 (_ BitVec 64))
(declare-const PC!50 (_ BitVec 64))
(declare-const XREG!27 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!48 (_ BitVec 64))
(declare-const XREG!28 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!49 (_ BitVec 64))
(declare-const XREG!26 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!47 (_ BitVec 64))
(declare-const %80 (_ BitVec 64))
(declare-const %81 (_ BitVec 64))
(assert 
   (=
     XREG!27
     (store XREG!26 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!17 PC!47))
(assert 
   (=
     %79
     (bvadd PC!47 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!28
     (store XREG!27 #b00000 %79)))
(assert 
   (=
     %81
     (select XREG!28 #b00001)))
(assert 
   (=
     %80
     (bvadd %81 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= PC!48 %80))
(assert 
   (=
     %77
     (ite
       (= %80 PC!47)
       #b1
       #b0)))
(assert 
   (=
     %78
     (bvadd %80 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!52 %78))
(assert 
   (=
     PC!49
     (ite
       (= %77 #b1)
       %78
       %80)))
(assert 
   (= PC!50 PC!49))
(assert 
   (= PC!51 PC!49))
(check-sat)
(get-value (
  %77
  %78
  %79
  PC!51
  prev_pc!17
  PC!52
  PC!50
  XREG!27
  PC!48
  XREG!28
  PC!49
  XREG!26
  PC!47
  %80
  %81
  ))
(get-model)
(exit)
