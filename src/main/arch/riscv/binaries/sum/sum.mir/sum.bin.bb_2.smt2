(declare-const %50 (_ BitVec 8))
(declare-const %51 (_ BitVec 24))
(declare-const %52 (_ BitVec 2))
(declare-const %53 (_ BitVec 1))
(declare-const %54 (_ BitVec 32))
(declare-const %55 (_ BitVec 16))
(declare-const tmp_bit_offset!2 (_ BitVec 6))
(declare-const %56 (_ BitVec 16))
(declare-const %57 (_ BitVec 32))
(declare-const %58 (_ BitVec 24))
(declare-const PC!44 (_ BitVec 64))
(declare-const PC!45 (_ BitVec 64))
(declare-const %59 (_ BitVec 8))
(declare-const PC!42 (_ BitVec 64))
(declare-const PC!43 (_ BitVec 64))
(declare-const tmp_address!2 (_ BitVec 64))
(declare-const PC!40 (_ BitVec 64))
(declare-const PC!41 (_ BitVec 64))
(declare-const XREG!18 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!19 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!46 (_ BitVec 64))
(declare-const %60 (_ BitVec 64))
(declare-const %61 (_ BitVec 64))
(declare-const prev_pc!14 (_ BitVec 64))
(declare-const prev_pc!13 (_ BitVec 64))
(declare-const %62 (_ BitVec 64))
(declare-const tmp_dword1!3 (_ BitVec 64))
(declare-const %63 (_ BitVec 64))
(declare-const tmp_dword1!2 (_ BitVec 64))
(declare-const %64 (_ BitVec 64))
(declare-const prev_pc!15 (_ BitVec 64))
(declare-const tmp_word!2 (_ BitVec 32))
(declare-const tmp_dword1!1 (_ BitVec 64))
(declare-const %65 (_ BitVec 32))
(declare-const tmp_word!3 (_ BitVec 32))
(declare-const %66 (_ BitVec 32))
(declare-const tmp_word!4 (_ BitVec 32))
(declare-const prev_pc!12 (_ BitVec 64))
(declare-const tmp_word!5 (_ BitVec 32))
(declare-const %67 (_ BitVec 32))
(declare-const tmp_word!6 (_ BitVec 32))
(declare-const %68 (_ BitVec 64))
(declare-const %69 (_ BitVec 64))
(declare-const rd_var!2 (_ BitVec 64))
(declare-const %70 (_ BitVec 64))
(declare-const %71 (_ BitVec 1))
(declare-const %72 (_ BitVec 64))
(declare-const %73 (_ BitVec 1))
(declare-const %74 (_ BitVec 64))
(declare-const %31 (_ BitVec 64))
(declare-const %75 (_ BitVec 64))
(declare-const %32 (_ BitVec 64))
(declare-const %76 (_ BitVec 64))
(declare-const %33 (_ BitVec 64))
(declare-const %34 (_ BitVec 64))
(declare-const %35 (_ BitVec 53))
(declare-const %36 (_ BitVec 3))
(declare-const %37 (_ BitVec 6))
(declare-const %38 (_ BitVec 6))
(declare-const %39 (_ BitVec 3))
(declare-const %40 (_ BitVec 1))
(declare-const tmp_dword2!3 (_ BitVec 64))
(declare-const %41 (_ BitVec 6))
(declare-const tmp_dword2!2 (_ BitVec 64))
(declare-const %42 (_ BitVec 64))
(declare-const tmp_dword2!1 (_ BitVec 64))
(declare-const %43 (_ BitVec 32))
(declare-const %44 (_ BitVec 53))
(declare-const %45 (_ BitVec 64))
(declare-const %46 (_ BitVec 64))
(declare-const %47 (_ BitVec 2))
(declare-const PC!33 (_ BitVec 64))
(declare-const %48 (_ BitVec 1))
(declare-const PC!34 (_ BitVec 64))
(declare-const PC!31 (_ BitVec 64))
(declare-const %49 (_ BitVec 32))
(declare-const PC!32 (_ BitVec 64))
(declare-const PC!39 (_ BitVec 64))
(declare-const PC!37 (_ BitVec 64))
(declare-const PC!38 (_ BitVec 64))
(declare-const PC!35 (_ BitVec 64))
(declare-const XREG!25 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!36 (_ BitVec 64))
(declare-const MEM!1 (Array (_ BitVec 53) (_ BitVec 64)))
(declare-const XREG!23 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const mem_index!2 (_ BitVec 53))
(declare-const XREG!24 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!21 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!22 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!20 (Array (_ BitVec 5) (_ BitVec 64)))
(assert 
   (=
     XREG!19
     (store XREG!18 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!12 PC!31))
(assert 
   (=
     %33
     (select XREG!19 #b01111)))
(assert 
   (=
     %32
     (bvadd %33 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= tmp_address!2 %32))
(assert 
   (=
     %34
     (bvlshr %32 #b0000000000000000000000000000000000000000000000000000000000000011)))
(assert 
   (=
     %35
     ((_ extract 52 0) %34)))
(assert 
   (= mem_index!2 %35))
(assert 
   (=
     %36
     ((_ extract 2 0) %32)))
(assert 
   (=
     %37
     ((_ zero_extend 3) %36)))
(assert 
   (=
     %38
     (bvmul %37 #b001000)))
(assert 
   (= tmp_bit_offset!2 %38))
(assert 
   (=
     %39
     ((_ extract 2 0) %32)))
(assert 
   (=
     %40
     (ite
       (bvult %39 #b101)
       #b1
       #b0)))
(assert 
   (=
     %41
     (bvadd %38 #b011111)))
(assert 
   (=
     %42
     (select MEM!1 %35)))
(assert 
   (=
     %43
     ((_ extract
       31
       0)
       (bvlshr
         %42
         ((_ zero_extend 58) %38)))))
(assert 
   (= tmp_word!5 %43))
(assert 
   (=
     %44
     (bvadd %35 #b00000000000000000000000000000000000000000000000000001)))
(assert 
   (=
     %45
     (select MEM!1 %44)))
(assert 
   (= tmp_dword1!2 %45))
(assert 
   (=
     %46
     (select MEM!1 %35)))
(assert 
   (= tmp_dword2!2 %46))
(assert 
   (=
     %47
     ((_ extract 1 0) %32)))
(assert 
   (=
     %48
     (ite
       (= %47 #b01)
       #b1
       #b0)))
(assert 
   (=
     tmp_word!6
     (ite
       (= %40 #b1)
       %43
       (ite
         (= %48 #b1)
         %49
         (ite
           (= %53 #b1)
           %54
           %57)))))
(assert 
   (=
     tmp_dword2!3
     (ite
       (= %40 #b1)
       tmp_dword2!1
       %46)))
(assert 
   (=
     tmp_dword1!3
     (ite
       (= %40 #b1)
       tmp_dword1!1
       %45)))
(assert 
   (=
     %60
     ((_ sign_extend 32) tmp_word!6)))
(assert 
   (= rd_var!2 %60))
(assert 
   (=
     XREG!20
     (store XREG!19 #b01101 %60)))
(assert 
   (=
     %31
     (bvadd PC!31 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!46 %31))
(assert 
   (= PC!32 %31))
(assert 
   (= PC!33 PC!32))
(assert 
   (=
     XREG!21
     (store XREG!20 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!13 PC!32))
(assert 
   (=
     %63
     (select XREG!21 #b01111)))
(assert 
   (=
     %62
     (bvadd %63 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!22
     (store XREG!21 #b01111 %62)))
(assert 
   (=
     %61
     (bvadd PC!32 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!34 %61))
(assert 
   (= PC!35 %61))
(assert 
   (= PC!36 PC!35))
(assert 
   (=
     XREG!23
     (store XREG!22 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!14 PC!35))
(assert 
   (=
     %69
     (select XREG!23 #b01101)))
(assert 
   (=
     %65
     ((_ extract 31 0) %69)))
(assert 
   (=
     %70
     (select XREG!23 #b01010)))
(assert 
   (=
     %67
     ((_ extract 31 0) %70)))
(assert 
   (=
     %66
     (bvadd %65 %67)))
(assert 
   (=
     %68
     ((_ sign_extend 32) %66)))
(assert 
   (=
     XREG!24
     (store XREG!23 #b01010 %68)))
(assert 
   (=
     %64
     (bvadd PC!35 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!45 %64))
(assert 
   (= PC!37 %64))
(assert 
   (= PC!38 PC!37))
(assert 
   (=
     XREG!25
     (store XREG!24 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!15 PC!37))
(assert 
   (=
     %75
     (select XREG!25 #b01110)))
(assert 
   (=
     %76
     (select XREG!25 #b01111)))
(assert 
   (=
     %73
     (ite
       (distinct %75 %76)
       #b1
       #b0)))
(assert 
   (=
     %50
     ((_ extract 7 0) %45)))
(assert 
   (=
     %51
     ((_ extract 63 40) %46)))
(assert 
   (=
     %49
     (concat %50 %51)))
(assert 
   (= tmp_word!4 %49))
(assert 
   (=
     %52
     ((_ extract 1 0) %32)))
(assert 
   (=
     %53
     (ite
       (= %52 #b10)
       #b1
       #b0)))
(assert 
   (=
     %55
     ((_ extract 15 0) %45)))
(assert 
   (=
     %56
     ((_ extract 63 48) %46)))
(assert 
   (=
     %54
     (concat %55 %56)))
(assert 
   (= tmp_word!3 %54))
(assert 
   (=
     %58
     ((_ extract 23 0) %45)))
(assert 
   (=
     %59
     ((_ extract 63 56) %46)))
(assert 
   (=
     %57
     (concat %58 %59)))
(assert 
   (= tmp_word!2 %57))
(assert 
   (=
     %74
     (bvadd PC!37 #b1111111111111111111111111111111111111111111111111111111111110100)))
(assert 
   (= PC!39 %74))
(assert 
   (=
     PC!40
     (ite
       (= %73 #b1)
       %74
       PC!37)))
(assert 
   (=
     %71
     (ite
       (= PC!40 PC!37)
       #b1
       #b0)))
(assert 
   (=
     %72
     (bvadd PC!40 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!44 %72))
(assert 
   (=
     PC!41
     (ite
       (= %73 #b1)
       %74
       %72)))
(assert 
   (= PC!42 PC!41))
(assert 
   (= PC!43 PC!41))
(check-sat)
(get-value (
  %50
  %51
  %52
  %53
  %54
  %55
  tmp_bit_offset!2
  %56
  %57
  %58
  PC!44
  PC!45
  %59
  PC!42
  PC!43
  tmp_address!2
  PC!40
  PC!41
  XREG!18
  XREG!19
  PC!46
  %60
  %61
  prev_pc!14
  prev_pc!13
  %62
  tmp_dword1!3
  %63
  tmp_dword1!2
  %64
  prev_pc!15
  tmp_word!2
  tmp_dword1!1
  %65
  tmp_word!3
  %66
  tmp_word!4
  prev_pc!12
  tmp_word!5
  %67
  tmp_word!6
  %68
  %69
  rd_var!2
  %70
  %71
  %72
  %73
  %74
  %31
  %75
  %32
  %76
  %33
  %34
  %35
  %36
  %37
  %38
  %39
  %40
  tmp_dword2!3
  %41
  tmp_dword2!2
  %42
  tmp_dword2!1
  %43
  %44
  %45
  %46
  %47
  PC!33
  %48
  PC!34
  PC!31
  %49
  PC!32
  PC!39
  PC!37
  PC!38
  PC!35
  XREG!25
  PC!36
  MEM!1
  XREG!23
  mem_index!2
  XREG!24
  XREG!21
  XREG!22
  XREG!20
  ))
(get-model)
(exit)
