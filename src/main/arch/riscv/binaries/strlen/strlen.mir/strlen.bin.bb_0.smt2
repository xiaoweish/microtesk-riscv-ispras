(declare-const XREG!3 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!3 (_ BitVec 64))
(declare-const PC!2 (_ BitVec 64))
(declare-const XREG!4 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!1 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!5 (_ BitVec 64))
(declare-const XREG!2 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!4 (_ BitVec 64))
(declare-const %10 (_ BitVec 64))
(declare-const %11 (_ BitVec 8))
(declare-const PC!1 (_ BitVec 64))
(declare-const tmp_bit_offset!2 (_ BitVec 6))
(declare-const %12 (_ BitVec 64))
(declare-const %13 (_ BitVec 1))
(declare-const %14 (_ BitVec 64))
(declare-const %15 (_ BitVec 1))
(declare-const %16 (_ BitVec 64))
(declare-const %17 (_ BitVec 64))
(declare-const tmp_address!2 (_ BitVec 64))
(declare-const %18 (_ BitVec 64))
(declare-const PC!7 (_ BitVec 64))
(declare-const PC!6 (_ BitVec 64))
(declare-const PC!9 (_ BitVec 64))
(declare-const PC!8 (_ BitVec 64))
(declare-const tmp_byte!2 (_ BitVec 8))
(declare-const prev_pc!2 (_ BitVec 64))
(declare-const prev_pc!3 (_ BitVec 64))
(declare-const PC!10 (_ BitVec 64))
(declare-const %1 (_ BitVec 64))
(declare-const %2 (_ BitVec 64))
(declare-const %3 (_ BitVec 64))
(declare-const %4 (_ BitVec 64))
(declare-const %5 (_ BitVec 53))
(declare-const %6 (_ BitVec 3))
(declare-const %7 (_ BitVec 6))
(declare-const %8 (_ BitVec 6))
(declare-const %9 (_ BitVec 6))
(declare-const rd_var!2 (_ BitVec 64))
(declare-const MEM!1 (Array (_ BitVec 53) (_ BitVec 64)))
(declare-const mem_index!2 (_ BitVec 53))
(assert 
   (=
     XREG!2
     (store XREG!1 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!2 PC!1))
(assert 
   (=
     %3
     (select XREG!2 #b01010)))
(assert 
   (=
     %2
     (bvadd %3 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= tmp_address!2 %2))
(assert 
   (=
     %4
     (bvlshr %2 #b0000000000000000000000000000000000000000000000000000000000000011)))
(assert 
   (=
     %5
     ((_ extract 52 0) %4)))
(assert 
   (= mem_index!2 %5))
(assert 
   (=
     %6
     ((_ extract 2 0) %2)))
(assert 
   (=
     %7
     ((_ zero_extend 3) %6)))
(assert 
   (=
     %8
     (bvmul %7 #b001000)))
(assert 
   (= tmp_bit_offset!2 %8))
(assert 
   (=
     %9
     (bvadd %8 #b000111)))
(assert 
   (=
     %10
     (select MEM!1 %5)))
(assert 
   (=
     %11
     ((_ extract
       7
       0)
       (bvlshr
         %10
         ((_ zero_extend 58) %8)))))
(assert 
   (= tmp_byte!2 %11))
(assert 
   (=
     %12
     ((_ zero_extend 56) %11)))
(assert 
   (= rd_var!2 %12))
(assert 
   (=
     XREG!3
     (store XREG!2 #b01111 %12)))
(assert 
   (=
     %1
     (bvadd PC!1 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!10 %1))
(assert 
   (= PC!2 %1))
(assert 
   (= PC!3 PC!2))
(assert 
   (=
     XREG!4
     (store XREG!3 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!3 PC!2))
(assert 
   (=
     %17
     (select XREG!4 #b01111)))
(assert 
   (=
     %18
     (select XREG!4 #b00000)))
(assert 
   (=
     %15
     (ite
       (= %17 %18)
       #b1
       #b0)))
(assert 
   (=
     %16
     (bvadd PC!2 #b0000000000000000000000000000000000000000000000000000000000011100)))
(assert 
   (= PC!9 %16))
(assert 
   (=
     PC!4
     (ite
       (= %15 #b1)
       %16
       PC!2)))
(assert 
   (=
     %13
     (ite
       (= PC!4 PC!2)
       #b1
       #b0)))
(assert 
   (=
     %14
     (bvadd PC!4 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!5 %14))
(assert 
   (=
     PC!6
     (ite
       (= %15 #b1)
       %16
       %14)))
(assert 
   (= PC!7 PC!6))
(assert 
   (= PC!8 PC!6))
(check-sat)
(get-value (
  XREG!3
  PC!3
  PC!2
  XREG!4
  XREG!1
  PC!5
  XREG!2
  PC!4
  %10
  %11
  PC!1
  tmp_bit_offset!2
  %12
  %13
  %14
  %15
  %16
  %17
  tmp_address!2
  %18
  PC!7
  PC!6
  PC!9
  PC!8
  tmp_byte!2
  prev_pc!2
  prev_pc!3
  PC!10
  %1
  %2
  %3
  %4
  %5
  %6
  %7
  %8
  %9
  rd_var!2
  MEM!1
  mem_index!2
  ))
(get-model)
(exit)
