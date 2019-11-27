(declare-const %50 (_ BitVec 64))
(declare-const %51 (_ BitVec 64))
(declare-const XREG!18 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!29 (_ BitVec 64))
(declare-const XREG!16 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!17 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!14 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!15 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %43 (_ BitVec 64))
(declare-const %44 (_ BitVec 64))
(declare-const %45 (_ BitVec 64))
(declare-const prev_pc!12 (_ BitVec 64))
(declare-const prev_pc!11 (_ BitVec 64))
(declare-const %46 (_ BitVec 64))
(declare-const %47 (_ BitVec 1))
(declare-const PC!33 (_ BitVec 64))
(declare-const %48 (_ BitVec 64))
(declare-const PC!34 (_ BitVec 64))
(declare-const PC!31 (_ BitVec 64))
(declare-const %49 (_ BitVec 64))
(declare-const PC!32 (_ BitVec 64))
(declare-const PC!30 (_ BitVec 64))
(declare-const PC!37 (_ BitVec 64))
(declare-const PC!35 (_ BitVec 64))
(declare-const PC!36 (_ BitVec 64))
(assert 
   (=
     XREG!15
     (store XREG!14 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!11 PC!29))
(assert 
   (=
     %45
     (select XREG!15 #b01111)))
(assert 
   (=
     %46
     (select XREG!15 #b01010)))
(assert 
   (=
     %44
     (bvsub %45 %46)))
(assert 
   (=
     XREG!16
     (store XREG!15 #b01010 %44)))
(assert 
   (=
     %43
     (bvadd PC!29 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!37 %43))
(assert 
   (= PC!30 %43))
(assert 
   (= PC!31 PC!30))
(assert 
   (=
     XREG!17
     (store XREG!16 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!12 PC!30))
(assert 
   (=
     %49
     (bvadd PC!30 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!18
     (store XREG!17 #b00000 %49)))
(assert 
   (=
     %51
     (select XREG!18 #b00001)))
(assert 
   (=
     %50
     (bvadd %51 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= PC!32 %50))
(assert 
   (=
     %47
     (ite
       (= %50 PC!30)
       #b1
       #b0)))
(assert 
   (=
     %48
     (bvadd %50 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!33 %48))
(assert 
   (=
     PC!34
     (ite
       (= %47 #b1)
       %48
       %50)))
(assert 
   (= PC!35 PC!34))
(assert 
   (= PC!36 PC!34))
(check-sat)
(get-value (
  %50
  %51
  XREG!18
  PC!29
  XREG!16
  XREG!17
  XREG!14
  XREG!15
  %43
  %44
  %45
  prev_pc!12
  prev_pc!11
  %46
  %47
  PC!33
  %48
  PC!34
  PC!31
  %49
  PC!32
  PC!30
  PC!37
  PC!35
  PC!36
  ))
(get-model)
(exit)
