(declare-const %258 (_ BitVec 64))
(declare-const PC!44 (_ BitVec 64))
(declare-const PC!45 (_ BitVec 64))
(declare-const PC!42 (_ BitVec 64))
(declare-const PC!43 (_ BitVec 64))
(declare-const PC!40 (_ BitVec 64))
(declare-const PC!41 (_ BitVec 64))
(declare-const XREG!18 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!19 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!16 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!48 (_ BitVec 64))
(declare-const XREG!17 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!49 (_ BitVec 64))
(declare-const XREG!14 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!46 (_ BitVec 64))
(declare-const XREG!15 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!47 (_ BitVec 64))
(declare-const %251 (_ BitVec 64))
(declare-const XREG!13 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %250 (_ BitVec 64))
(declare-const %253 (_ BitVec 64))
(declare-const %252 (_ BitVec 64))
(declare-const %255 (_ BitVec 64))
(declare-const %254 (_ BitVec 64))
(declare-const %257 (_ BitVec 64))
(declare-const %256 (_ BitVec 64))
(declare-const prev_pc!14 (_ BitVec 64))
(declare-const prev_pc!13 (_ BitVec 64))
(declare-const prev_pc!16 (_ BitVec 64))
(declare-const prev_pc!15 (_ BitVec 64))
(declare-const prev_pc!12 (_ BitVec 64))
(declare-const prev_pc!11 (_ BitVec 64))
(declare-const PC!51 (_ BitVec 64))
(declare-const PC!52 (_ BitVec 64))
(declare-const prev_pc!17 (_ BitVec 64))
(declare-const PC!50 (_ BitVec 64))
(declare-const %239 (_ BitVec 64))
(declare-const %238 (_ BitVec 64))
(declare-const %248 (_ BitVec 64))
(declare-const %247 (_ BitVec 64))
(declare-const %249 (_ BitVec 64))
(declare-const PC!33 (_ BitVec 64))
(declare-const PC!34 (_ BitVec 64))
(declare-const PC!31 (_ BitVec 64))
(declare-const PC!32 (_ BitVec 64))
(declare-const PC!30 (_ BitVec 64))
(declare-const PC!39 (_ BitVec 64))
(declare-const PC!37 (_ BitVec 64))
(declare-const XREG!27 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!38 (_ BitVec 64))
(declare-const PC!35 (_ BitVec 64))
(declare-const XREG!25 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const PC!36 (_ BitVec 64))
(declare-const XREG!26 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %240 (_ BitVec 64))
(declare-const XREG!23 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const XREG!24 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %242 (_ BitVec 64))
(declare-const XREG!21 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %241 (_ BitVec 64))
(declare-const XREG!22 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %244 (_ BitVec 64))
(declare-const %243 (_ BitVec 64))
(declare-const XREG!20 (Array (_ BitVec 5) (_ BitVec 64)))
(declare-const %246 (_ BitVec 64))
(declare-const %245 (_ BitVec 64))
(assert 
   (=
     XREG!14
     (store XREG!13 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!11 PC!30))
(assert 
   (=
     %240
     (select XREG!14 #b01011)))
(assert 
   (=
     %239
     (bvadd %240 #b1111111111111111111111111111111111111111111111111111111111111011)))
(assert 
   (=
     XREG!15
     (store XREG!14 #b01101 %239)))
(assert 
   (=
     %238
     (bvadd PC!30 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!31 %238))
(assert 
   (= PC!32 %238))
(assert 
   (= PC!33 PC!32))
(assert 
   (=
     XREG!16
     (store XREG!15 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!12 PC!32))
(assert 
   (=
     %243
     (select XREG!16 #b01101)))
(assert 
   (=
     %242
     (bvand %243 #b1111111111111111111111111111111111111111111111111111111111111110)))
(assert 
   (=
     XREG!17
     (store XREG!16 #b01101 %242)))
(assert 
   (=
     %241
     (bvadd PC!32 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!52 %241))
(assert 
   (= PC!34 %241))
(assert 
   (= PC!35 PC!34))
(assert 
   (=
     XREG!18
     (store XREG!17 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!13 PC!34))
(assert 
   (=
     %246
     (select XREG!18 #b01010)))
(assert 
   (=
     %245
     (bvadd %246 #b0000000000000000000000000000000000000000000000000000000000010000)))
(assert 
   (=
     XREG!19
     (store XREG!18 #b01100 %245)))
(assert 
   (=
     %244
     (bvadd PC!34 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!36 %244))
(assert 
   (= PC!37 %244))
(assert 
   (= PC!38 PC!37))
(assert 
   (=
     XREG!20
     (store XREG!19 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!14 PC!37))
(assert 
   (=
     %249
     (select XREG!20 #b01101)))
(assert 
   (=
     %248
     (bvadd %249 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (=
     XREG!21
     (store XREG!20 #b01101 %248)))
(assert 
   (=
     %247
     (bvadd PC!37 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!51 %247))
(assert 
   (= PC!39 %247))
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
     %252
     (select XREG!22 #b00000)))
(assert 
   (=
     %251
     (bvadd %252 #b0000000000000000000000000000000000000000000000000000000000000001)))
(assert 
   (=
     XREG!23
     (store XREG!22 #b01110 %251)))
(assert 
   (=
     %250
     (bvadd PC!39 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!41 %250))
(assert 
   (= PC!42 %250))
(assert 
   (= PC!43 PC!42))
(assert 
   (=
     XREG!24
     (store XREG!23 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!16 PC!42))
(assert 
   (=
     %255
     (select XREG!24 #b00000)))
(assert 
   (=
     %254
     (bvadd %255 #b0000000000000000000000000000000000000000000000000000000000000001)))
(assert 
   (=
     XREG!25
     (store XREG!24 #b01111 %254)))
(assert 
   (=
     %253
     (bvadd PC!42 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!50 %253))
(assert 
   (= PC!44 %253))
(assert 
   (= PC!45 PC!44))
(assert 
   (=
     XREG!26
     (store XREG!25 #b00000 #b0000000000000000000000000000000000000000000000000000000000000000)))
(assert 
   (= prev_pc!17 PC!44))
(assert 
   (=
     %258
     (select XREG!26 #b00000)))
(assert 
   (=
     %257
     (bvadd %258 #b0000000000000000000000000000000000000000000000000000000000000010)))
(assert 
   (=
     XREG!27
     (store XREG!26 #b10000 %257)))
(assert 
   (=
     %256
     (bvadd PC!44 #b0000000000000000000000000000000000000000000000000000000000000100)))
(assert 
   (= PC!49 %256))
(assert 
   (= PC!46 %256))
(assert 
   (= PC!47 PC!46))
(assert 
   (= PC!48 PC!46))
(check-sat)
(get-value (
  %258
  PC!44
  PC!45
  PC!42
  PC!43
  PC!40
  PC!41
  XREG!18
  XREG!19
  XREG!16
  PC!48
  XREG!17
  PC!49
  XREG!14
  PC!46
  XREG!15
  PC!47
  %251
  XREG!13
  %250
  %253
  %252
  %255
  %254
  %257
  %256
  prev_pc!14
  prev_pc!13
  prev_pc!16
  prev_pc!15
  prev_pc!12
  prev_pc!11
  PC!51
  PC!52
  prev_pc!17
  PC!50
  %239
  %238
  %248
  %247
  %249
  PC!33
  PC!34
  PC!31
  PC!32
  PC!30
  PC!39
  PC!37
  XREG!27
  PC!38
  PC!35
  XREG!25
  PC!36
  XREG!26
  %240
  XREG!23
  XREG!24
  %242
  XREG!21
  %241
  XREG!22
  %244
  %243
  XREG!20
  %246
  %245
  ))
(get-model)
(exit)
