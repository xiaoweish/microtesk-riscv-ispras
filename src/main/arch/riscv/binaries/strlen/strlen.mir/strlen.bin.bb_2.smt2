(declare-const tmp_address!4 (_ BitVec 64))
(declare-const XREG!12 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!13 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!9 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!10 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const tmp_byte!4 (_ BitVec 8))
(declare-const XREG!11 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!8 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const prev_pc!8 (_ BitVec 64))
(declare-const prev_pc!9 (_ BitVec 64))
(declare-const prev_pc!7 (_ BitVec 64))
(declare-const %22 (_ BitVec 64))
(declare-const %23 (_ BitVec 64))
(declare-const %24 (_ BitVec 64))
(declare-const %25 (_ BitVec 64))
(declare-const %26 (_ BitVec 53))
(declare-const %27 (_ BitVec 3))
(declare-const %28 (_ BitVec 6))
(declare-const %29 (_ BitVec 6))
(declare-const PC!19 (_ BitVec 64))
(declare-const PC!17 (_ BitVec 64))
(declare-const rd_var!4 (_ BitVec 64))
(declare-const PC!18 (_ BitVec 64))
(declare-const PC!16 (_ BitVec 64))
(declare-const tmp_bit_offset!4 (_ BitVec 6))
(declare-const %30 (_ BitVec 6))
(declare-const %31 (_ BitVec 64))
(declare-const %32 (_ BitVec 8))
(declare-const %33 (_ BitVec 64))
(declare-const %34 (_ BitVec 64))
(declare-const %35 (_ BitVec 64))
(declare-const %36 (_ BitVec 64))
(declare-const PC!22 (_ BitVec 64))
(declare-const %37 (_ BitVec 1))
(declare-const PC!23 (_ BitVec 64))
(declare-const PC!20 (_ BitVec 64))
(declare-const %38 (_ BitVec 64))
(declare-const PC!21 (_ BitVec 64))
(declare-const %39 (_ BitVec 1))
(declare-const PC!28 (_ BitVec 64))
(declare-const PC!26 (_ BitVec 64))
(declare-const PC!27 (_ BitVec 64))
(declare-const PC!24 (_ BitVec 64))
(declare-const PC!25 (_ BitVec 64))
(declare-const %40 (_ BitVec 64))
(declare-const %41 (_ BitVec 64))
(declare-const %42 (_ BitVec 64))
(declare-const mem_index!4 (_ BitVec 53))
(declare-const MEM!2 (Array (_ BitVec 53) (_ BitVec 64)))
(assert 
   (=
     XREG!9
     (store XREG!8 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!7 PC!16))
(assert 
   (=
     %24
     (select XREG!9 #b01111)))
(assert 
   (=
     %23
     (bvadd %24 #b0000000000000000000000000000000000000000000000000000000000000001)))
(assert 
   (= tmp_address!4 %23))
(assert 
   (=
     %25
     (bvlshr %23 #b0000000000000000000000000000000000000000000000000000000000000011)))
(assert 
   (=
     %26
     ((_ extract 52 0) %25)))
(assert 
   (= mem_index!4 %26))
(assert 
   (=
     %27
     ((_ extract 2 0) %23)))
(assert 
   (=
     %28
     ((_ zero_extend 3) %27)))
(assert 
   (=
     %29
     (bvmul %28 #b001000)))
(assert 
   (= tmp_bit_offset!4 %29))
(assert 
   (=
     %30
     (bvadd %29 #b000111)))
(assert 
   (=
     %31
     (select MEM!2 %26)))
(assert 
   (=
     %32
     ((_ extract
       7
       0)
       (bvlshr
         %31
         ((_ zero_extend 58) %29)))))
(assert 
   (= tmp_byte!4 %32))
(assert 
   (=
     %33
     ((_ zero_extend 56) %32)))
(assert 
   (= rd_var!4 %33))
(assert 
   (=
     XREG!10
     (store XREG!9 #b01110 %33)))
(assert 
   (=
     %22
     (bvadd PC!16 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!17 %22))
(assert 
   (= PC!18 %22))
(assert 
   (= PC!19 PC!18))
(assert 
   (=
     XREG!11
     (store XREG!10 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!8 PC!18))
(assert 
   (=
     %36
     (select XREG!11 #b01111)))
(assert 
   (=
     %35
     (bvadd %36 #b0000000000000000000000000000000000000000000000000000000000000001)))
(assert 
   (=
     XREG!12
     (store XREG!11 #b01111 %35)))
(assert 
   (=
     %34
     (bvadd PC!18 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!28 %34))
(assert 
   (= PC!20 %34))
(assert 
   (= PC!21 PC!20))
(assert 
   (=
     XREG!13
     (store XREG!12 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!9 PC!20))
(assert 
   (=
     %41
     (select XREG!13 #b01110)))
(assert 
   (=
     %42
     (select XREG!13 #b00000)))
(assert 
   (=
     %39
     (ite
       (distinct %41 %42)
       #b1
       #b0)))
(assert 
   (=
     %40
     (bvadd PC!20 #b1111111111111111111111111111111111111111111111111111111111111000)))
(assert 
   (= PC!27 %40))
(assert 
   (=
     PC!22
     (ite
       (= %39 #b1)
       %40
       PC!20)))
(assert 
   (=
     %37
     (ite
       (= PC!22 PC!20)
       #b1
       #b0)))
(assert 
   (=
     %38
     (bvadd PC!22 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!23 %38))
(assert 
   (=
     PC!24
     (ite
       (= %39 #b1)
       %40
       %38)))
(assert 
   (= PC!25 PC!24))
(assert 
   (= PC!26 PC!24))
(check-sat)
(get-value (
  tmp_address!4
  XREG!12
  XREG!13
  XREG!9
  XREG!10
  tmp_byte!4
  XREG!11
  XREG!8
  prev_pc!8
  prev_pc!9
  prev_pc!7
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
  rd_var!4
  PC!18
  PC!16
  tmp_bit_offset!4
  %30
  %31
  %32
  %33
  %34
  %35
  %36
  PC!22
  %37
  PC!23
  PC!20
  %38
  PC!21
  %39
  PC!28
  PC!26
  PC!27
  PC!24
  PC!25
  %40
  %41
  %42
  mem_index!4
  MEM!2
  ))
(get-model)
(exit)
