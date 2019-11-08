(declare-const XREG!3 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!4 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const prev_pc!4 (_ BitVec 64))
(declare-const %10 (_ BitVec 64))
(declare-const %11 (_ BitVec 64))
(declare-const %12 (_ BitVec 64))
(declare-const PC!11 (_ BitVec 64))
(declare-const PC!12 (_ BitVec 64))
(declare-const PC!10 (_ BitVec 64))
(declare-const PC!9 (_ BitVec 64))
(declare-const PC!8 (_ BitVec 64))
(declare-const %7 (_ BitVec 1))
(declare-const %8 (_ BitVec 64))
(declare-const %9 (_ BitVec 1))
(declare-const PC!13 (_ BitVec 64))
(declare-const PC!14 (_ BitVec 64))
(assert 
   (=
     XREG!4
     (store XREG!3 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!4 PC!8))
(assert 
   (=
     %11
     (select XREG!4 #b01011)))
(assert 
   (=
     %12
     (select XREG!4 #b01010)))
(assert 
   (=
     %9
     (ite
       (bvsge %11 %12)
       #b1
       #b0)))
(assert 
   (=
     %10
     (bvadd PC!8 #b0000000000000000000000000000000000000000000000000000000000010100)))
(assert 
   (= PC!14 %10))
(assert 
   (=
     PC!9
     (ite
       (= %9 #b1)
       %10
       PC!8)))
(assert 
   (=
     %7
     (ite
       (= PC!9 PC!8)
       #b1
       #b0)))
(assert 
   (=
     %8
     (bvadd PC!9 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!13 %8))
(assert 
   (=
     PC!10
     (ite
       (= %9 #b1)
       %10
       %8)))
(assert 
   (= PC!11 PC!10))
(assert 
   (= PC!12 PC!10))
(check-sat)
(get-value (
  XREG!3
  XREG!4
  prev_pc!4
  %10
  %11
  %12
  PC!11
  PC!12
  PC!10
  PC!9
  PC!8
  %7
  %8
  %9
  PC!13
  PC!14
  ))
(get-model)
(exit)
