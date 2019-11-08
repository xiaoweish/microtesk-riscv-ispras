(declare-const PC!3 (_ BitVec 64))
(declare-const PC!2 (_ BitVec 64))
(declare-const XREG!1 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!5 (_ BitVec 64))
(declare-const XREG!2 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!4 (_ BitVec 64))
(declare-const prev_pc!2 (_ BitVec 64))
(declare-const PC!1 (_ BitVec 64))
(declare-const %1 (_ BitVec 1))
(declare-const PC!7 (_ BitVec 64))
(declare-const %2 (_ BitVec 64))
(declare-const PC!6 (_ BitVec 64))
(declare-const %3 (_ BitVec 1))
(declare-const %4 (_ BitVec 64))
(declare-const %5 (_ BitVec 64))
(declare-const %6 (_ BitVec 64))
(assert 
   (=
     XREG!2
     (store XREG!1 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!2 PC!1))
(assert 
   (=
     %5
     (select XREG!2 #b00000)))
(assert 
   (=
     %6
     (select XREG!2 #b01011)))
(assert 
   (=
     %3
     (ite
       (bvsge %5 %6)
       #b1
       #b0)))
(assert 
   (=
     %4
     (bvadd PC!1 #b0000000000000000000000000000000000000000000000000000000000110100)))
(assert 
   (= PC!2 %4))
(assert 
   (=
     PC!3
     (ite
       (= %3 #b1)
       %4
       PC!1)))
(assert 
   (=
     %1
     (ite
       (= PC!3 PC!1)
       #b1
       #b0)))
(assert 
   (=
     %2
     (bvadd PC!3 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!4 %2))
(assert 
   (=
     PC!5
     (ite
       (= %3 #b1)
       %4
       %2)))
(assert 
   (= PC!6 PC!5))
(assert 
   (= PC!7 PC!5))
(check-sat)
(get-value (
  PC!3
  PC!2
  XREG!1
  PC!5
  XREG!2
  PC!4
  prev_pc!2
  PC!1
  %1
  PC!7
  %2
  PC!6
  %3
  %4
  %5
  %6
  ))
(get-model)
(exit)
