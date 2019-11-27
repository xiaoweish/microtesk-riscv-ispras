(declare-const prev_pc!14 (_ BitVec 64))
(declare-const %52 (_ BitVec 64))
(declare-const %53 (_ BitVec 64))
(declare-const prev_pc!15 (_ BitVec 64))
(declare-const %54 (_ BitVec 64))
(declare-const %55 (_ BitVec 1))
(declare-const %56 (_ BitVec 64))
(declare-const %57 (_ BitVec 64))
(declare-const %58 (_ BitVec 64))
(declare-const PC!44 (_ BitVec 64))
(declare-const %59 (_ BitVec 64))
(declare-const PC!45 (_ BitVec 64))
(declare-const PC!42 (_ BitVec 64))
(declare-const PC!43 (_ BitVec 64))
(declare-const PC!40 (_ BitVec 64))
(declare-const PC!41 (_ BitVec 64))
(declare-const PC!39 (_ BitVec 64))
(declare-const XREG!19 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!38 (_ BitVec 64))
(declare-const PC!46 (_ BitVec 64))
(declare-const XREG!23 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!21 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!22 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!20 (Array (_ BitVec 5) (_ BitVec 64)))
(assert 
   (=
     XREG!20
     (store XREG!19 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!14 PC!38))
(assert 
   (=
     %54
     (select XREG!20 #b00000)))
(assert 
   (=
     %53
     (bvadd %54 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (=
     XREG!21
     (store XREG!20 #b01010 %53)))
(assert 
   (=
     %52
     (bvadd PC!38 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!46 %52))
(assert 
   (= PC!39 %52))
(assert 
   (= PC!40 PC!39))
(assert 
   (=
     XREG!22
     (store XREG!21 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!15 PC!39))
(assert 
   (=
     %57
     (bvadd PC!39 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!23
     (store XREG!22 #b00000 %57)))
(assert 
   (=
     %59
     (select XREG!23 #b00001)))
(assert 
   (=
     %58
     (bvadd %59 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= PC!41 %58))
(assert 
   (=
     %55
     (ite
       (= %58 PC!39)
       #b1
       #b0)))
(assert 
   (=
     %56
     (bvadd %58 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!42 %56))
(assert 
   (=
     PC!43
     (ite
       (= %55 #b1)
       %56
       %58)))
(assert 
   (= PC!44 PC!43))
(assert 
   (= PC!45 PC!43))
(check-sat)
(get-value (
  prev_pc!14
  %52
  %53
  prev_pc!15
  %54
  %55
  %56
  %57
  %58
  PC!44
  %59
  PC!45
  PC!42
  PC!43
  PC!40
  PC!41
  PC!39
  XREG!19
  PC!38
  PC!46
  XREG!23
  XREG!21
  XREG!22
  XREG!20
  ))
(get-model)
(exit)
