(declare-const PC!111 (_ BitVec 64))
(declare-const XREG!60 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const prev_pc!38 (_ BitVec 64))
(declare-const %714 (_ BitVec 1))
(declare-const PC!115 (_ BitVec 64))
(declare-const PC!114 (_ BitVec 64))
(declare-const %716 (_ BitVec 64))
(declare-const PC!113 (_ BitVec 64))
(declare-const PC!112 (_ BitVec 64))
(declare-const %715 (_ BitVec 64))
(declare-const %718 (_ BitVec 64))
(declare-const %717 (_ BitVec 64))
(declare-const PC!116 (_ BitVec 64))
(declare-const XREG!58 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!59 (Array (_ BitVec 5) (_ BitVec 64)))
(assert 
   (=
     XREG!59
     (store XREG!58 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!38 PC!111))
(assert 
   (=
     %716
     (bvadd PC!111 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!60
     (store XREG!59 #b00000 %716)))
(assert 
   (=
     %718
     (select XREG!60 #b00001)))
(assert 
   (=
     %717
     (bvadd %718 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= PC!112 %717))
(assert 
   (=
     %714
     (ite
       (= %717 PC!111)
       #b1
       #b0)))
(assert 
   (=
     %715
     (bvadd %717 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!116 %715))
(assert 
   (=
     PC!113
     (ite
       (= %714 #b1)
       %715
       %717)))
(assert 
   (= PC!114 PC!113))
(assert 
   (= PC!115 PC!113))
(check-sat)
(get-value (
  PC!111
  XREG!60
  prev_pc!38
  %714
  PC!115
  PC!114
  %716
  PC!113
  PC!112
  %715
  %718
  %717
  PC!116
  XREG!58
  XREG!59
  ))
(get-model)
(exit)
