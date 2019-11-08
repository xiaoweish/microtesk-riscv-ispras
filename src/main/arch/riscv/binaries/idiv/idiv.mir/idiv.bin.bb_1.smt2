(declare-const %30 (_ BitVec 64))
(declare-const %13 (_ BitVec 64))
(declare-const %14 (_ BitVec 32))
(declare-const PC!22 (_ BitVec 64))
(declare-const %15 (_ BitVec 32))
(declare-const PC!23 (_ BitVec 64))
(declare-const %16 (_ BitVec 32))
(declare-const PC!20 (_ BitVec 64))
(declare-const %17 (_ BitVec 64))
(declare-const PC!21 (_ BitVec 64))
(declare-const %18 (_ BitVec 64))
(declare-const %19 (_ BitVec 64))
(declare-const PC!26 (_ BitVec 64))
(declare-const PC!24 (_ BitVec 64))
(declare-const PC!25 (_ BitVec 64))
(declare-const XREG!12 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!9 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!10 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!11 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!7 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!8 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const prev_pc!8 (_ BitVec 64))
(declare-const prev_pc!6 (_ BitVec 64))
(declare-const prev_pc!7 (_ BitVec 64))
(declare-const %20 (_ BitVec 64))
(declare-const %21 (_ BitVec 32))
(declare-const %22 (_ BitVec 32))
(declare-const %23 (_ BitVec 64))
(declare-const %24 (_ BitVec 64))
(declare-const %25 (_ BitVec 1))
(declare-const %26 (_ BitVec 64))
(declare-const %27 (_ BitVec 1))
(declare-const %28 (_ BitVec 64))
(declare-const %29 (_ BitVec 64))
(declare-const PC!19 (_ BitVec 64))
(declare-const PC!17 (_ BitVec 64))
(declare-const PC!18 (_ BitVec 64))
(declare-const PC!15 (_ BitVec 64))
(declare-const PC!16 (_ BitVec 64))
(declare-const PC!14 (_ BitVec 64))
(assert 
   (=
     XREG!8
     (store XREG!7 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!6 PC!14))
(assert 
   (=
     %18
     (select XREG!8 #b01111)))
(assert 
   (=
     %14
     ((_ extract 31 0) %18)))
(assert 
   (=
     %19
     (select XREG!8 #b01011)))
(assert 
   (=
     %16
     ((_ extract 31 0) %19)))
(assert 
   (=
     %15
     (bvsub %14 %16)))
(assert 
   (=
     %17
     ((_ sign_extend 32) %15)))
(assert 
   (=
     XREG!9
     (store XREG!8 #b01111 %17)))
(assert 
   (=
     %13
     (bvadd PC!14 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!26 %13))
(assert 
   (= PC!15 %13))
(assert 
   (= PC!16 PC!15))
(assert 
   (=
     XREG!10
     (store XREG!9 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!7 PC!15))
(assert 
   (=
     %24
     (select XREG!10 #b01010)))
(assert 
   (=
     %21
     ((_ extract 31 0) %24)))
(assert 
   (=
     %22
     (bvadd %21 #b00000000000000000000000000000001)))
(assert 
   (=
     %23
     ((_ sign_extend 32) %22)))
(assert 
   (=
     XREG!11
     (store XREG!10 #b01010 %23)))
(assert 
   (=
     %20
     (bvadd PC!15 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!25 %20))
(assert 
   (= PC!17 %20))
(assert 
   (= PC!18 PC!17))
(assert 
   (=
     XREG!12
     (store XREG!11 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!8 PC!17))
(assert 
   (=
     %29
     (select XREG!12 #b01111)))
(assert 
   (=
     %30
     (select XREG!12 #b01011)))
(assert 
   (=
     %27
     (ite
       (bvsge %29 %30)
       #b1
       #b0)))
(assert 
   (=
     %28
     (bvadd PC!17 #b1111111111111111111111111111111111111111111111111111111111111000)))
(assert 
   (= PC!24 %28))
(assert 
   (=
     PC!19
     (ite
       (= %27 #b1)
       %28
       PC!17)))
(assert 
   (=
     %25
     (ite
       (= PC!19 PC!17)
       #b1
       #b0)))
(assert 
   (=
     %26
     (bvadd PC!19 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!20 %26))
(assert 
   (=
     PC!21
     (ite
       (= %27 #b1)
       %28
       %26)))
(assert 
   (= PC!22 PC!21))
(assert 
   (= PC!23 PC!21))
(check-sat)
(get-value (
  %30
  %13
  %14
  PC!22
  %15
  PC!23
  %16
  PC!20
  %17
  PC!21
  %18
  %19
  PC!26
  PC!24
  PC!25
  XREG!12
  XREG!9
  XREG!10
  XREG!11
  XREG!7
  XREG!8
  prev_pc!8
  prev_pc!6
  prev_pc!7
  %20
  %21
  %22
  %23
  %24
  %25
  %26
  %27
  %28
  %29
  PC!19
  PC!17
  PC!18
  PC!15
  PC!16
  PC!14
  ))
(get-model)
(exit)
