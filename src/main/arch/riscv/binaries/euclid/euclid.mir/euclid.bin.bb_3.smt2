(declare-const prev_pc!8 (_ BitVec 64))
(declare-const %20 (_ BitVec 64))
(declare-const %21 (_ BitVec 1))
(declare-const %22 (_ BitVec 64))
(declare-const %23 (_ BitVec 64))
(declare-const %24 (_ BitVec 64))
(declare-const PC!22 (_ BitVec 64))
(declare-const PC!23 (_ BitVec 64))
(declare-const %19 (_ BitVec 1))
(declare-const PC!28 (_ BitVec 64))
(declare-const PC!26 (_ BitVec 64))
(declare-const PC!27 (_ BitVec 64))
(declare-const PC!24 (_ BitVec 64))
(declare-const PC!25 (_ BitVec 64))
(declare-const XREG!7 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!8 (Array (_ BitVec 5) (_ BitVec 64)))
(assert 
   (=
     XREG!8
     (store XREG!7 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!8 PC!22))
(assert 
   (=
     %23
     (select XREG!8 #b01011)))
(assert 
   (=
     %24
     (select XREG!8 #b01010)))
(assert 
   (=
     %21
     (ite
       (bvsge %23 %24)
       #b1
       #b0)))
(assert 
   (=
     %22
     (bvadd PC!22 #b0000000000000000000000000000000000000000000000000000000000010100)))
(assert 
   (= PC!28 %22))
(assert 
   (=
     PC!23
     (ite
       (= %21 #b1)
       %22
       PC!22)))
(assert 
   (=
     %19
     (ite
       (= PC!23 PC!22)
       #b1
       #b0)))
(assert 
   (=
     %20
     (bvadd PC!23 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!27 %20))
(assert 
   (=
     PC!24
     (ite
       (= %21 #b1)
       %22
       %20)))
(assert 
   (= PC!25 PC!24))
(assert 
   (= PC!26 PC!24))
(check-sat)
(get-value (
  prev_pc!8
  %20
  %21
  %22
  %23
  %24
  PC!22
  PC!23
  %19
  PC!28
  PC!26
  PC!27
  PC!24
  PC!25
  XREG!7
  XREG!8
  ))
(get-model)
(exit)
