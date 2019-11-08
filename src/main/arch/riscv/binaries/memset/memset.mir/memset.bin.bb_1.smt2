(declare-const prev_pc!8 (_ BitVec 64))
(declare-const prev_pc!9 (_ BitVec 64))
(declare-const %229 (_ BitVec 64))
(declare-const PC!22 (_ BitVec 64))
(declare-const PC!23 (_ BitVec 64))
(declare-const PC!20 (_ BitVec 64))
(declare-const PC!21 (_ BitVec 64))
(declare-const PC!28 (_ BitVec 64))
(declare-const PC!26 (_ BitVec 64))
(declare-const PC!27 (_ BitVec 64))
(declare-const PC!24 (_ BitVec 64))
(declare-const XREG!12 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!13 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!10 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!9 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %231 (_ BitVec 64))
(declare-const %230 (_ BitVec 64))
(declare-const XREG!11 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %233 (_ BitVec 64))
(declare-const %232 (_ BitVec 64))
(assert 
   (=
     XREG!10
     (store XREG!9 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!8 PC!20))
(assert 
   (=
     %231
     (select XREG!10 #b01011)))
(assert 
   (=
     %230
     (bvand %231 #b0000000000000000000000000000000000000000000000000000000011111111)))
(assert 
   (=
     XREG!11
     (store XREG!10 #b01011 %230)))
(assert 
   (=
     %229
     (bvadd PC!20 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!21 %229))
(assert 
   (= PC!22 %229))
(assert 
   (= PC!23 PC!22))
(assert 
   (=
     XREG!12
     (store XREG!11 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!9 PC!22))
(assert 
   (=
     %232
     (bvadd PC!22 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!13
     (store XREG!12 #b00001 %232)))
(assert 
   (=
     %233
     (bvadd PC!22 #b1111111111111111111111111111111111111111111111111111111111101000)))
(assert 
   (= PC!24 %233))
(assert 
   (= PC!26 %233))
(assert 
   (= PC!27 PC!26))
(assert 
   (= PC!28 PC!26))
(check-sat)
(get-value (
  prev_pc!8
  prev_pc!9
  %229
  PC!22
  PC!23
  PC!20
  PC!21
  PC!28
  PC!26
  PC!27
  PC!24
  XREG!12
  XREG!13
  XREG!10
  XREG!9
  %231
  %230
  XREG!11
  %233
  %232
  ))
(get-model)
(exit)
