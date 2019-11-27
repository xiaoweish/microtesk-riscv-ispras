(declare-const %20 (_ BitVec 64))
(declare-const %21 (_ BitVec 64))
(declare-const PC!15 (_ BitVec 64))
(declare-const prev_pc!5 (_ BitVec 64))
(declare-const PC!13 (_ BitVec 64))
(declare-const PC!14 (_ BitVec 64))
(declare-const PC!11 (_ BitVec 64))
(declare-const PC!12 (_ BitVec 64))
(declare-const XREG!7 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %19 (_ BitVec 64))
(declare-const XREG!5 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!6 (Array (_ BitVec 5) (_ BitVec 64)))
(assert 
   (=
     XREG!6
     (store XREG!5 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!5 PC!11))
(assert 
   (=
     %21
     (select XREG!6 #b01010)))
(assert 
   (=
     %20
     (bvadd %21 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (=
     XREG!7
     (store XREG!6 #b01111 %20)))
(assert 
   (=
     %19
     (bvadd PC!11 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!12 %19))
(assert 
   (= PC!13 %19))
(assert 
   (= PC!14 PC!13))
(assert 
   (= PC!15 PC!13))
(check-sat)
(get-value (
  %20
  %21
  PC!15
  prev_pc!5
  PC!13
  PC!14
  PC!11
  PC!12
  XREG!7
  %19
  XREG!5
  XREG!6
  ))
(get-model)
(exit)
