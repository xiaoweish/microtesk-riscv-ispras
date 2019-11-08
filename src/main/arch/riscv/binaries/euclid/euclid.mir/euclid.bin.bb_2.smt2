(declare-const prev_pc!6 (_ BitVec 64))
(declare-const %13 (_ BitVec 1))
(declare-const %14 (_ BitVec 64))
(declare-const %15 (_ BitVec 1))
(declare-const %16 (_ BitVec 64))
(declare-const PC!20 (_ BitVec 64))
(declare-const %17 (_ BitVec 64))
(declare-const PC!21 (_ BitVec 64))
(declare-const %18 (_ BitVec 64))
(declare-const PC!19 (_ BitVec 64))
(declare-const PC!17 (_ BitVec 64))
(declare-const PC!18 (_ BitVec 64))
(declare-const PC!15 (_ BitVec 64))
(declare-const PC!16 (_ BitVec 64))
(declare-const XREG!5 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!6 (Array (_ BitVec 5) (_ BitVec 64)))
(assert 
   (=
     XREG!6
     (store XREG!5 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!6 PC!15))
(assert 
   (=
     %17
     (select XREG!6 #b01011)))
(assert 
   (=
     %18
     (select XREG!6 #b01010)))
(assert 
   (=
     %15
     (ite
       (bvsge %17 %18)
       #b1
       #b0)))
(assert 
   (=
     %16
     (bvadd PC!15 #b0000000000000000000000000000000000000000000000000000000000010100)))
(assert 
   (= PC!21 %16))
(assert 
   (=
     PC!16
     (ite
       (= %15 #b1)
       %16
       PC!15)))
(assert 
   (=
     %13
     (ite
       (= PC!16 PC!15)
       #b1
       #b0)))
(assert 
   (=
     %14
     (bvadd PC!16 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!20 %14))
(assert 
   (=
     PC!17
     (ite
       (= %15 #b1)
       %16
       %14)))
(assert 
   (= PC!18 PC!17))
(assert 
   (= PC!19 PC!17))
(check-sat)
(get-value (
  prev_pc!6
  %13
  %14
  %15
  %16
  PC!20
  %17
  PC!21
  %18
  PC!19
  PC!17
  PC!18
  PC!15
  PC!16
  XREG!5
  XREG!6
  ))
(get-model)
(exit)
