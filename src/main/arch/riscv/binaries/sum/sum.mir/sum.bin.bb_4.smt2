(declare-const %83 (_ BitVec 64))
(declare-const %84 (_ BitVec 64))
(declare-const %85 (_ BitVec 1))
(declare-const %86 (_ BitVec 64))
(declare-const %87 (_ BitVec 64))
(declare-const prev_pc!20 (_ BitVec 64))
(declare-const %88 (_ BitVec 64))
(declare-const %89 (_ BitVec 64))
(declare-const PC!55 (_ BitVec 64))
(declare-const PC!56 (_ BitVec 64))
(declare-const PC!53 (_ BitVec 64))
(declare-const PC!54 (_ BitVec 64))
(declare-const PC!60 (_ BitVec 64))
(declare-const prev_pc!19 (_ BitVec 64))
(declare-const PC!61 (_ BitVec 64))
(declare-const XREG!29 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!59 (_ BitVec 64))
(declare-const PC!57 (_ BitVec 64))
(declare-const PC!58 (_ BitVec 64))
(declare-const XREG!32 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!33 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!30 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!31 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %82 (_ BitVec 64))
(assert 
   (=
     XREG!30
     (store XREG!29 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!19 PC!53))
(assert 
   (=
     %84
     (select XREG!30 #b00000)))
(assert 
   (=
     %83
     (bvadd %84 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (=
     XREG!31
     (store XREG!30 #b01010 %83)))
(assert 
   (=
     %82
     (bvadd PC!53 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!54 %82))
(assert 
   (= PC!55 %82))
(assert 
   (= PC!56 PC!55))
(assert 
   (=
     XREG!32
     (store XREG!31 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!20 PC!55))
(assert 
   (=
     %87
     (bvadd PC!55 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!33
     (store XREG!32 #b00000 %87)))
(assert 
   (=
     %89
     (select XREG!33 #b00001)))
(assert 
   (=
     %88
     (bvadd %89 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= PC!57 %88))
(assert 
   (=
     %85
     (ite
       (= %88 PC!55)
       #b1
       #b0)))
(assert 
   (=
     %86
     (bvadd %88 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!58 %86))
(assert 
   (=
     PC!59
     (ite
       (= %85 #b1)
       %86
       %88)))
(assert 
   (= PC!60 PC!59))
(assert 
   (= PC!61 PC!59))
(check-sat)
(get-value (
  %83
  %84
  %85
  %86
  %87
  prev_pc!20
  %88
  %89
  PC!55
  PC!56
  PC!53
  PC!54
  PC!60
  prev_pc!19
  PC!61
  XREG!29
  PC!59
  PC!57
  PC!58
  XREG!32
  XREG!33
  XREG!30
  XREG!31
  %82
  ))
(get-model)
(exit)
