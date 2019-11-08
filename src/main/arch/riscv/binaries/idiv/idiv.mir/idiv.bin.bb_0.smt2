(declare-const XREG!3 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!3 (_ BitVec 64))
(declare-const PC!2 (_ BitVec 64))
(declare-const XREG!4 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!1 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!5 (_ BitVec 64))
(declare-const XREG!2 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!4 (_ BitVec 64))
(declare-const %10 (_ BitVec 64))
(declare-const %11 (_ BitVec 64))
(declare-const PC!1 (_ BitVec 64))
(declare-const %12 (_ BitVec 64))
(declare-const PC!7 (_ BitVec 64))
(declare-const PC!6 (_ BitVec 64))
(declare-const PC!9 (_ BitVec 64))
(declare-const PC!8 (_ BitVec 64))
(declare-const XREG!5 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!6 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const prev_pc!4 (_ BitVec 64))
(declare-const prev_pc!2 (_ BitVec 64))
(declare-const prev_pc!3 (_ BitVec 64))
(declare-const PC!11 (_ BitVec 64))
(declare-const PC!12 (_ BitVec 64))
(declare-const PC!10 (_ BitVec 64))
(declare-const %1 (_ BitVec 64))
(declare-const %2 (_ BitVec 64))
(declare-const %3 (_ BitVec 64))
(declare-const %4 (_ BitVec 64))
(declare-const %5 (_ BitVec 64))
(declare-const %6 (_ BitVec 64))
(declare-const %7 (_ BitVec 1))
(declare-const %8 (_ BitVec 64))
(declare-const %9 (_ BitVec 1))
(declare-const PC!13 (_ BitVec 64))
(assert 
   (=
     XREG!2
     (store XREG!1 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!2 PC!1))
(assert 
   (=
     %3
     (select XREG!2 #b01010)))
(assert 
   (=
     %2
     (bvadd %3 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (=
     XREG!3
     (store XREG!2 #b01111 %2)))
(assert 
   (=
     %1
     (bvadd PC!1 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!2 %1))
(assert 
   (= PC!3 %1))
(assert 
   (= PC!4 PC!3))
(assert 
   (=
     XREG!4
     (store XREG!3 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!3 PC!3))
(assert 
   (=
     %6
     (select XREG!4 #b00000)))
(assert 
   (=
     %5
     (bvadd %6 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (=
     XREG!5
     (store XREG!4 #b01010 %5)))
(assert 
   (=
     %4
     (bvadd PC!3 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!5 %4))
(assert 
   (= PC!6 %4))
(assert 
   (= PC!7 PC!6))
(assert 
   (=
     XREG!6
     (store XREG!5 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!4 PC!6))
(assert 
   (=
     %11
     (select XREG!6 #b01111)))
(assert 
   (=
     %12
     (select XREG!6 #b01011)))
(assert 
   (=
     %9
     (ite
       (bvslt %11 %12)
       #b1
       #b0)))
(assert 
   (=
     %10
     (bvadd PC!6 #b0000000000000000000000000000000000000000000000000000000000010000)))
(assert 
   (= PC!13 %10))
(assert 
   (=
     PC!8
     (ite
       (= %9 #b1)
       %10
       PC!6)))
(assert 
   (=
     %7
     (ite
       (= PC!8 PC!6)
       #b1
       #b0)))
(assert 
   (=
     %8
     (bvadd PC!8 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!12 %8))
(assert 
   (=
     PC!9
     (ite
       (= %9 #b1)
       %10
       %8)))
(assert 
   (= PC!10 PC!9))
(assert 
   (= PC!11 PC!9))
(check-sat)
(get-value (
  XREG!3
  PC!3
  PC!2
  XREG!4
  XREG!1
  PC!5
  XREG!2
  PC!4
  %10
  %11
  PC!1
  %12
  PC!7
  PC!6
  PC!9
  PC!8
  XREG!5
  XREG!6
  prev_pc!4
  prev_pc!2
  prev_pc!3
  PC!11
  PC!12
  PC!10
  %1
  %2
  %3
  %4
  %5
  %6
  %7
  %8
  %9
  PC!13
  ))
(get-model)
(exit)
