(declare-const XREG!3 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!4 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %10 (_ BitVec 64))
(declare-const %11 (_ BitVec 64))
(declare-const %12 (_ BitVec 64))
(declare-const %13 (_ BitVec 64))
(declare-const %14 (_ BitVec 64))
(declare-const %15 (_ BitVec 64))
(declare-const %16 (_ BitVec 64))
(declare-const %17 (_ BitVec 64))
(declare-const %18 (_ BitVec 64))
(declare-const %19 (_ BitVec 64))
(declare-const XREG!16 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!17 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!14 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!15 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!12 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!13 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!9 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!10 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!11 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!7 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!8 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!5 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!6 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const prev_pc!8 (_ BitVec 64))
(declare-const prev_pc!9 (_ BitVec 64))
(declare-const prev_pc!6 (_ BitVec 64))
(declare-const prev_pc!7 (_ BitVec 64))
(declare-const %20 (_ BitVec 64))
(declare-const prev_pc!4 (_ BitVec 64))
(declare-const %21 (_ BitVec 64))
(declare-const prev_pc!10 (_ BitVec 64))
(declare-const prev_pc!5 (_ BitVec 64))
(declare-const %22 (_ BitVec 64))
(declare-const %23 (_ BitVec 64))
(declare-const %24 (_ BitVec 64))
(declare-const PC!11 (_ BitVec 64))
(declare-const %25 (_ BitVec 64))
(declare-const PC!12 (_ BitVec 64))
(declare-const %26 (_ BitVec 64))
(declare-const %27 (_ BitVec 64))
(declare-const PC!10 (_ BitVec 64))
(declare-const %28 (_ BitVec 64))
(declare-const %29 (_ BitVec 64))
(declare-const PC!19 (_ BitVec 64))
(declare-const %7 (_ BitVec 64))
(declare-const PC!17 (_ BitVec 64))
(declare-const %8 (_ BitVec 32))
(declare-const PC!18 (_ BitVec 64))
(declare-const %9 (_ BitVec 32))
(declare-const PC!15 (_ BitVec 64))
(declare-const PC!16 (_ BitVec 64))
(declare-const PC!13 (_ BitVec 64))
(declare-const PC!14 (_ BitVec 64))
(declare-const %30 (_ BitVec 64))
(declare-const PC!22 (_ BitVec 64))
(declare-const PC!23 (_ BitVec 64))
(declare-const PC!20 (_ BitVec 64))
(declare-const PC!21 (_ BitVec 64))
(declare-const PC!9 (_ BitVec 64))
(declare-const PC!8 (_ BitVec 64))
(declare-const PC!28 (_ BitVec 64))
(declare-const PC!29 (_ BitVec 64))
(declare-const PC!26 (_ BitVec 64))
(declare-const PC!27 (_ BitVec 64))
(declare-const PC!24 (_ BitVec 64))
(declare-const PC!25 (_ BitVec 64))
(declare-const PC!30 (_ BitVec 64))
(assert 
   (=
     XREG!4
     (store XREG!3 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!4 PC!8))
(assert 
   (=
     %11
     (select XREG!4 #b01011)))
(assert 
   (=
     %8
     ((_ extract 31 0) %11)))
(assert 
   (=
     %9
     (bvadd %8 #b11111111111111111111111111111111)))
(assert 
   (=
     %10
     ((_ sign_extend 32) %9)))
(assert 
   (=
     XREG!5
     (store XREG!4 #b01110 %10)))
(assert 
   (=
     %7
     (bvadd PC!8 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!30 %7))
(assert 
   (= PC!9 %7))
(assert 
   (= PC!10 PC!9))
(assert 
   (=
     XREG!6
     (store XREG!5 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!5 PC!9))
(assert 
   (=
     %14
     (select XREG!6 #b01110)))
(assert 
   (=
     %13
     (bvshl %14 #b100000)))
(assert 
   (=
     XREG!7
     (store XREG!6 #b01110 %13)))
(assert 
   (=
     %12
     (bvadd PC!9 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!11 %12))
(assert 
   (= PC!12 %12))
(assert 
   (= PC!13 PC!12))
(assert 
   (=
     XREG!8
     (store XREG!7 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!6 PC!12))
(assert 
   (=
     %17
     (select XREG!8 #b01010)))
(assert 
   (=
     %16
     (bvadd %17 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!9
     (store XREG!8 #b01101 %16)))
(assert 
   (=
     %15
     (bvadd PC!12 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!29 %15))
(assert 
   (= PC!14 %15))
(assert 
   (= PC!15 PC!14))
(assert 
   (=
     XREG!10
     (store XREG!9 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!7 PC!14))
(assert 
   (=
     %20
     (select XREG!10 #b01110)))
(assert 
   (=
     %19
     (bvlshr %20 #b011110)))
(assert 
   (=
     XREG!11
     (store XREG!10 #b01110 %19)))
(assert 
   (=
     %18
     (bvadd PC!14 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!16 %18))
(assert 
   (= PC!17 %18))
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
     %23
     (select XREG!12 #b01010)))
(assert 
   (=
     %22
     (bvadd %23 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (=
     XREG!13
     (store XREG!12 #b01111 %22)))
(assert 
   (=
     %21
     (bvadd PC!17 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!28 %21))
(assert 
   (= PC!19 %21))
(assert 
   (= PC!20 PC!19))
(assert 
   (=
     XREG!14
     (store XREG!13 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!9 PC!19))
(assert 
   (=
     %26
     (select XREG!14 #b01110)))
(assert 
   (=
     %27
     (select XREG!14 #b01101)))
(assert 
   (=
     %25
     (bvadd %26 %27)))
(assert 
   (=
     XREG!15
     (store XREG!14 #b01110 %25)))
(assert 
   (=
     %24
     (bvadd PC!19 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!27 %24))
(assert 
   (= PC!21 %24))
(assert 
   (= PC!22 PC!21))
(assert 
   (=
     XREG!16
     (store XREG!15 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!10 PC!21))
(assert 
   (=
     %30
     (select XREG!16 #b00000)))
(assert 
   (=
     %29
     (bvadd %30 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (=
     XREG!17
     (store XREG!16 #b01010 %29)))
(assert 
   (=
     %28
     (bvadd PC!21 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!23 %28))
(assert 
   (= PC!24 %28))
(assert 
   (= PC!25 PC!24))
(assert 
   (= PC!26 PC!24))
(check-sat)
(get-value (
  XREG!3
  XREG!4
  %10
  %11
  %12
  %13
  %14
  %15
  %16
  %17
  %18
  %19
  XREG!16
  XREG!17
  XREG!14
  XREG!15
  XREG!12
  XREG!13
  XREG!9
  XREG!10
  XREG!11
  XREG!7
  XREG!8
  XREG!5
  XREG!6
  prev_pc!8
  prev_pc!9
  prev_pc!6
  prev_pc!7
  %20
  prev_pc!4
  %21
  prev_pc!10
  prev_pc!5
  %22
  %23
  %24
  PC!11
  %25
  PC!12
  %26
  %27
  PC!10
  %28
  %29
  PC!19
  %7
  PC!17
  %8
  PC!18
  %9
  PC!15
  PC!16
  PC!13
  PC!14
  %30
  PC!22
  PC!23
  PC!20
  PC!21
  PC!9
  PC!8
  PC!28
  PC!29
  PC!26
  PC!27
  PC!24
  PC!25
  PC!30
  ))
(get-model)
(exit)
