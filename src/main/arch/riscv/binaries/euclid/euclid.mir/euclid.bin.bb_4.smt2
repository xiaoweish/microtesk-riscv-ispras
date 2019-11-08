(declare-const %30 (_ BitVec 64))
(declare-const %31 (_ BitVec 64))
(declare-const %32 (_ BitVec 1))
(declare-const %33 (_ BitVec 64))
(declare-const %34 (_ BitVec 1))
(declare-const %35 (_ BitVec 64))
(declare-const %36 (_ BitVec 64))
(declare-const %37 (_ BitVec 64))
(declare-const PC!29 (_ BitVec 64))
(declare-const XREG!12 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!10 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!9 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!11 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const prev_pc!10 (_ BitVec 64))
(declare-const prev_pc!11 (_ BitVec 64))
(declare-const %25 (_ BitVec 64))
(declare-const PC!33 (_ BitVec 64))
(declare-const %26 (_ BitVec 32))
(declare-const PC!34 (_ BitVec 64))
(declare-const %27 (_ BitVec 32))
(declare-const PC!31 (_ BitVec 64))
(declare-const %28 (_ BitVec 32))
(declare-const PC!32 (_ BitVec 64))
(declare-const %29 (_ BitVec 64))
(declare-const PC!30 (_ BitVec 64))
(declare-const PC!37 (_ BitVec 64))
(declare-const PC!38 (_ BitVec 64))
(declare-const PC!35 (_ BitVec 64))
(declare-const PC!36 (_ BitVec 64))
(assert 
   (=
     XREG!10
     (store XREG!9 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!10 PC!29))
(assert 
   (=
     %30
     (select XREG!10 #b01010)))
(assert 
   (=
     %26
     ((_ extract 31 0) %30)))
(assert 
   (=
     %31
     (select XREG!10 #b01011)))
(assert 
   (=
     %28
     ((_ extract 31 0) %31)))
(assert 
   (=
     %27
     (bvsub %26 %28)))
(assert 
   (=
     %29
     ((_ sign_extend 32) %27)))
(assert 
   (=
     XREG!11
     (store XREG!10 #b01010 %29)))
(assert 
   (=
     %25
     (bvadd PC!29 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!38 %25))
(assert 
   (= PC!30 %25))
(assert 
   (= PC!31 PC!30))
(assert 
   (=
     XREG!12
     (store XREG!11 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!11 PC!30))
(assert 
   (=
     %36
     (select XREG!12 #b01011)))
(assert 
   (=
     %37
     (select XREG!12 #b01010)))
(assert 
   (=
     %34
     (ite
       (distinct %36 %37)
       #b1
       #b0)))
(assert 
   (=
     %35
     (bvadd PC!30 #b1111111111111111111111111111111111111111111111111111111111111000)))
(assert 
   (= PC!32 %35))
(assert 
   (=
     PC!33
     (ite
       (= %34 #b1)
       %35
       PC!30)))
(assert 
   (=
     %32
     (ite
       (= PC!33 PC!30)
       #b1
       #b0)))
(assert 
   (=
     %33
     (bvadd PC!33 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!34 %33))
(assert 
   (=
     PC!35
     (ite
       (= %34 #b1)
       %35
       %33)))
(assert 
   (= PC!36 PC!35))
(assert 
   (= PC!37 PC!35))
(check-sat)
(get-value (
  %30
  %31
  %32
  %33
  %34
  %35
  %36
  %37
  PC!29
  XREG!12
  XREG!10
  XREG!9
  XREG!11
  prev_pc!10
  prev_pc!11
  %25
  PC!33
  %26
  PC!34
  %27
  PC!31
  %28
  PC!32
  %29
  PC!30
  PC!37
  PC!38
  PC!35
  PC!36
  ))
(get-model)
(exit)
