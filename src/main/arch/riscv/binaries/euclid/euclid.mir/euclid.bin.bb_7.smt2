(declare-const %50 (_ BitVec 32))
(declare-const %51 (_ BitVec 32))
(declare-const %52 (_ BitVec 64))
(declare-const %53 (_ BitVec 64))
(declare-const %54 (_ BitVec 64))
(declare-const %55 (_ BitVec 1))
(declare-const %56 (_ BitVec 64))
(declare-const %57 (_ BitVec 1))
(declare-const %58 (_ BitVec 64))
(declare-const %59 (_ BitVec 64))
(declare-const PC!60 (_ BitVec 64))
(declare-const XREG!19 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %60 (_ BitVec 64))
(declare-const PC!55 (_ BitVec 64))
(declare-const %48 (_ BitVec 64))
(declare-const PC!56 (_ BitVec 64))
(declare-const %49 (_ BitVec 32))
(declare-const PC!53 (_ BitVec 64))
(declare-const PC!54 (_ BitVec 64))
(declare-const PC!51 (_ BitVec 64))
(declare-const prev_pc!18 (_ BitVec 64))
(declare-const prev_pc!17 (_ BitVec 64))
(declare-const PC!52 (_ BitVec 64))
(declare-const PC!59 (_ BitVec 64))
(declare-const PC!57 (_ BitVec 64))
(declare-const PC!58 (_ BitVec 64))
(declare-const XREG!21 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!22 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!20 (Array (_ BitVec 5) (_ BitVec 64)))
(assert 
   (=
     XREG!20
     (store XREG!19 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!17 PC!51))
(assert 
   (=
     %53
     (select XREG!20 #b01011)))
(assert 
   (=
     %49
     ((_ extract 31 0) %53)))
(assert 
   (=
     %54
     (select XREG!20 #b01010)))
(assert 
   (=
     %51
     ((_ extract 31 0) %54)))
(assert 
   (=
     %50
     (bvsub %49 %51)))
(assert 
   (=
     %52
     ((_ sign_extend 32) %50)))
(assert 
   (=
     XREG!21
     (store XREG!20 #b01011 %52)))
(assert 
   (=
     %48
     (bvadd PC!51 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!60 %48))
(assert 
   (= PC!52 %48))
(assert 
   (= PC!53 PC!52))
(assert 
   (=
     XREG!22
     (store XREG!21 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!18 PC!52))
(assert 
   (=
     %59
     (select XREG!22 #b01010)))
(assert 
   (=
     %60
     (select XREG!22 #b01011)))
(assert 
   (=
     %57
     (ite
       (distinct %59 %60)
       #b1
       #b0)))
(assert 
   (=
     %58
     (bvadd PC!52 #b1111111111111111111111111111111111111111111111111111111111101000)))
(assert 
   (= PC!59 %58))
(assert 
   (=
     PC!54
     (ite
       (= %57 #b1)
       %58
       PC!52)))
(assert 
   (=
     %55
     (ite
       (= PC!54 PC!52)
       #b1
       #b0)))
(assert 
   (=
     %56
     (bvadd PC!54 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!55 %56))
(assert 
   (=
     PC!56
     (ite
       (= %57 #b1)
       %58
       %56)))
(assert 
   (= PC!57 PC!56))
(assert 
   (= PC!58 PC!56))
(check-sat)
(get-value (
  %50
  %51
  %52
  %53
  %54
  %55
  %56
  %57
  %58
  %59
  PC!60
  XREG!19
  %60
  PC!55
  %48
  PC!56
  %49
  PC!53
  PC!54
  PC!51
  prev_pc!18
  prev_pc!17
  PC!52
  PC!59
  PC!57
  PC!58
  XREG!21
  XREG!22
  XREG!20
  ))
(get-model)
(exit)
