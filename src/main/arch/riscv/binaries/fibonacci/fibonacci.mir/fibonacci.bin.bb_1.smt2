(declare-const %237 (_ BitVec 64))
(declare-const %236 (_ BitVec 64))
(declare-const PC!22 (_ BitVec 64))
(declare-const PC!23 (_ BitVec 64))
(declare-const PC!20 (_ BitVec 64))
(declare-const PC!21 (_ BitVec 64))
(declare-const PC!28 (_ BitVec 64))
(declare-const PC!29 (_ BitVec 64))
(declare-const PC!26 (_ BitVec 64))
(declare-const PC!27 (_ BitVec 64))
(declare-const PC!24 (_ BitVec 64))
(declare-const PC!25 (_ BitVec 64))
(declare-const XREG!12 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!10 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!9 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %231 (_ BitVec 64))
(declare-const %230 (_ BitVec 64))
(declare-const XREG!11 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %233 (_ BitVec 64))
(declare-const %232 (_ BitVec 1))
(declare-const %235 (_ BitVec 64))
(declare-const %234 (_ BitVec 1))
(declare-const prev_pc!8 (_ BitVec 64))
(declare-const prev_pc!9 (_ BitVec 64))
(declare-const %229 (_ BitVec 64))
(assert 
   (=
     XREG!10
     (store XREG!9 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!8 PC!20))
(assert 
   (=
     %231
     (select XREG!10 #b00000)))
(assert 
   (=
     %230
     (bvadd %231 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!11
     (store XREG!10 #b01111 %230)))
(assert 
   (=
     %229
     (bvadd PC!20 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!29 %229))
(assert 
   (= PC!21 %229))
(assert 
   (= PC!22 PC!21))
(assert 
   (=
     XREG!12
     (store XREG!11 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!9 PC!21))
(assert 
   (=
     %236
     (select XREG!12 #b01111)))
(assert 
   (=
     %237
     (select XREG!12 #b01011)))
(assert 
   (=
     %234
     (ite
       (bvuge %236 %237)
       #b1
       #b0)))
(assert 
   (=
     %235
     (bvadd PC!21 #b0000000000000000000000000000000000000000000000000000000001100100)))
(assert 
   (= PC!23 %235))
(assert 
   (=
     PC!24
     (ite
       (= %234 #b1)
       %235
       PC!21)))
(assert 
   (=
     %232
     (ite
       (= PC!24 PC!21)
       #b1
       #b0)))
(assert 
   (=
     %233
     (bvadd PC!24 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!25 %233))
(assert 
   (=
     PC!26
     (ite
       (= %234 #b1)
       %235
       %233)))
(assert 
   (= PC!27 PC!26))
(assert 
   (= PC!28 PC!26))
(check-sat)
(get-value (
  %237
  %236
  PC!22
  PC!23
  PC!20
  PC!21
  PC!28
  PC!29
  PC!26
  PC!27
  PC!24
  PC!25
  XREG!12
  XREG!10
  XREG!9
  %231
  %230
  XREG!11
  %233
  %232
  %235
  %234
  prev_pc!8
  prev_pc!9
  %229
  ))
(get-model)
(exit)
