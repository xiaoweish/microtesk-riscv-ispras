(declare-const prev_pc!13 (_ BitVec 64))
(declare-const %40 (_ BitVec 64))
(declare-const %41 (_ BitVec 64))
(declare-const %42 (_ BitVec 64))
(declare-const PC!44 (_ BitVec 64))
(declare-const %38 (_ BitVec 1))
(declare-const PC!42 (_ BitVec 64))
(declare-const %39 (_ BitVec 64))
(declare-const PC!43 (_ BitVec 64))
(declare-const PC!40 (_ BitVec 64))
(declare-const PC!41 (_ BitVec 64))
(declare-const PC!39 (_ BitVec 64))
(declare-const XREG!14 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!15 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!13 (Array (_ BitVec 5) (_ BitVec 64)))
(assert 
   (=
     XREG!14
     (store XREG!13 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!13 PC!39))
(assert 
   (=
     %40
     (bvadd PC!39 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!15
     (store XREG!14 #b00000 %40)))
(assert 
   (=
     %42
     (select XREG!15 #b00001)))
(assert 
   (=
     %41
     (bvadd %42 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= PC!40 %41))
(assert 
   (=
     %38
     (ite
       (= %41 PC!39)
       #b1
       #b0)))
(assert 
   (=
     %39
     (bvadd %41 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!44 %39))
(assert 
   (=
     PC!41
     (ite
       (= %38 #b1)
       %39
       %41)))
(assert 
   (= PC!42 PC!41))
(assert 
   (= PC!43 PC!41))
(check-sat)
(get-value (
  prev_pc!13
  %40
  %41
  %42
  PC!44
  %38
  PC!42
  %39
  PC!43
  PC!40
  PC!41
  PC!39
  XREG!14
  XREG!15
  XREG!13
  ))
(get-model)
(exit)
