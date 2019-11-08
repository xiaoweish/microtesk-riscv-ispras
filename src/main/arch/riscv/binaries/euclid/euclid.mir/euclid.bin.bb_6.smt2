(declare-const prev_pc!15 (_ BitVec 64))
(declare-const %43 (_ BitVec 1))
(declare-const %44 (_ BitVec 64))
(declare-const %45 (_ BitVec 64))
(declare-const %46 (_ BitVec 64))
(declare-const %47 (_ BitVec 64))
(declare-const PC!45 (_ BitVec 64))
(declare-const PC!50 (_ BitVec 64))
(declare-const XREG!18 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!16 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!48 (_ BitVec 64))
(declare-const XREG!17 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!49 (_ BitVec 64))
(declare-const PC!46 (_ BitVec 64))
(declare-const PC!47 (_ BitVec 64))
(assert 
   (=
     XREG!17
     (store XREG!16 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!15 PC!45))
(assert 
   (=
     %45
     (bvadd PC!45 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!18
     (store XREG!17 #b00000 %45)))
(assert 
   (=
     %47
     (select XREG!18 #b00001)))
(assert 
   (=
     %46
     (bvadd %47 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= PC!46 %46))
(assert 
   (=
     %43
     (ite
       (= %46 PC!45)
       #b1
       #b0)))
(assert 
   (=
     %44
     (bvadd %46 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!50 %44))
(assert 
   (=
     PC!47
     (ite
       (= %43 #b1)
       %44
       %46)))
(assert 
   (= PC!48 PC!47))
(assert 
   (= PC!49 PC!47))
(check-sat)
(get-value (
  prev_pc!15
  %43
  %44
  %45
  %46
  %47
  PC!45
  PC!50
  XREG!18
  XREG!16
  PC!48
  XREG!17
  PC!49
  PC!46
  PC!47
  ))
(get-model)
(exit)
