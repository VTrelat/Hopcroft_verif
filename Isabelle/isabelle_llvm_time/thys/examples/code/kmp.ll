; Generated by Isabelle/LLVM-shallow
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"



declare void @isabelle_llvm_free(i8*)
declare i8* @isabelle_llvm_calloc(i64, i64)


define i64 @kmp({ i64, i8* } %x, { i64, i8* } %x1) {

  start:
    %a1 = extractvalue { i64, i8* } %x, 0
    %a2 = extractvalue { i64, i8* } %x, 1
    %xa = icmp eq i64 %a1, 0
    br i1 %xa, label %then, label %else

  then:
    br label %ctd_if

  else:
    %xaa = call { i64, i64* } @KMP_compute_butlast_ff_s_impl ({ i64, i8* } %x)
    %xb = insertvalue { i64, i64 } zeroinitializer, i64 0, 0
    %tmpaa = insertvalue { i64, i64 } %xb, i64 -1, 1
    %xc = insertvalue { i64, { i64, i64 } } zeroinitializer, i64 0, 0
    %xd = insertvalue { i64, { i64, i64 } } %xc, { i64, i64 } %tmpaa, 1
    br label %while_start

  while_start:
    %xba = phi { i64, { i64, i64 } } [ %r1, %ctd_iff ], [ %xd, %else ]
    %a1a = extractvalue { i64, { i64, i64 } } %xba, 0
    %xca = extractvalue { i64, { i64, i64 } } %xba, 1
    %a1aa = extractvalue { i64, i64 } %xca, 0
    %a2a = extractvalue { i64, i64 } %xca, 1
    %a1b = extractvalue { i64, i8* } %x, 0
    %a2b = extractvalue { i64, i8* } %x, 1
    %xe = add i64 %a1a, %a1b
    %a1c = extractvalue { i64, i8* } %x1, 0
    %a2c = extractvalue { i64, i8* } %x1, 1
    %xg = icmp sle i64 %xe, %a1c
    %x2 = icmp eq i64 -1, %a2a
    %x3 = and i1 %xg, %x2
    br i1 %x3, label %while_body, label %while_end

  while_body:
    %a1a1 = extractvalue { i64, { i64, i64 } } %xba, 0
    %xca1 = extractvalue { i64, { i64, i64 } } %xba, 1
    %a1aa1 = extractvalue { i64, i64 } %xca1, 0
    %a2a1 = extractvalue { i64, i64 } %xca1, 1
    %xe1 = insertvalue { i64, i64 } zeroinitializer, i64 %a1aa1, 0
    %xf = insertvalue { i64, i64 } %xe1, i64 %a2a1, 1
    br label %while_starta

  while_starta:
    %s = phi { i64, i64 } [ %r, %ctd_ifc ], [ %xf, %while_body ]
    %a1b1 = extractvalue { i64, i64 } %s, 0
    %a2b1 = extractvalue { i64, i64 } %s, 1
    %xea = icmp eq i64 -1, %a2b1
    br i1 %xea, label %thena, label %elsea

  thena:
    %xfa = add i64 %a1a1, %a1b1
    %a1c1 = extractvalue { i64, i8* } %x1, 0
    %a2c1 = extractvalue { i64, i8* } %x1, 1
    %xg1 = getelementptr i8, i8* %a2c1, i64 %xfa
    %xh = load i8, i8* %xg1
    %a1d = extractvalue { i64, i8* } %x, 0
    %a2d = extractvalue { i64, i8* } %x, 1
    %xi = getelementptr i8, i8* %a2d, i64 %a1b1
    %x4 = load i8, i8* %xi
    %x5 = icmp eq i8 %xh, %x4
    br label %ctd_ifa

  elsea:
    br label %ctd_ifa

  ctd_ifa:
    %x6 = phi i1 [ 0, %elsea ], [ %x5, %thena ]
    br i1 %x6, label %while_bodya, label %while_enda

  while_bodya:
    %a1b2 = extractvalue { i64, i64 } %s, 0
    %a2b2 = extractvalue { i64, i64 } %s, 1
    %xda = add i64 %a1b2, 1
    %a1c2 = extractvalue { i64, i8* } %x, 0
    %a2c2 = extractvalue { i64, i8* } %x, 1
    %xfa1 = icmp eq i64 %xda, %a1c2
    br i1 %xfa1, label %thenb, label %elseb

  thenb:
    %xga = insertvalue { i64, i64 } zeroinitializer, i64 %xda, 0
    %x7 = insertvalue { i64, i64 } %xga, i64 %a1a1, 1
    br label %ctd_ifb

  elseb:
    %xga1 = insertvalue { i64, i64 } zeroinitializer, i64 %xda, 0
    %x8 = insertvalue { i64, i64 } %xga1, i64 -1, 1
    br label %ctd_ifb

  ctd_ifb:
    %r = phi { i64, i64 } [ %x8, %elseb ], [ %x7, %thenb ]
    %c_1 = extractvalue { i64, i64 } %s, 0
    %b = extractvalue { i64, i64 } %s, 1
    %d = icmp eq i64 -1, %b
    br i1 %d, label %thenc, label %elsec

  thenc:
    br label %ctd_ifc

  elsec:
    br label %ctd_ifc

  ctd_ifc:
    br label %while_starta

  while_enda:
    %a1b3 = extractvalue { i64, i64 } %s, 0
    %a2b3 = extractvalue { i64, i64 } %s, 1
    %xea1 = icmp eq i64 -1, %a2b3
    br i1 %xea1, label %thend, label %elsed

  thend:
    %a1c3 = extractvalue { i64, i64* } %xaa, 0
    %a2c3 = extractvalue { i64, i64* } %xaa, 1
    %xfa2 = getelementptr i64, i64* %a2c3, i64 %a1b3
    %xg2 = load i64, i64* %xfa2
    %xh1 = sub i64 %a1b3, %xg2
    %xia = add i64 %xh1, 1
    %xj = add i64 %a1a1, %xia
    %a1d1 = extractvalue { i64, i64* } %xaa, 0
    %a2d1 = extractvalue { i64, i64* } %xaa, 1
    %xk = getelementptr i64, i64* %a2d1, i64 %a1b3
    %xl = load i64, i64* %xk
    %xma = icmp sle i64 %xl, 1
    br i1 %xma, label %thene, label %elsee

  thene:
    br label %ctd_ife

  elsee:
    %x9 = sub i64 %xl, 1
    br label %ctd_ife

  ctd_ife:
    %xn = phi i64 [ %x9, %elsee ], [ 0, %thene ]
    %xo = insertvalue { i64, { i64, i64 } } zeroinitializer, i64 %xj, 0
    %xp = insertvalue { i64, i64 } zeroinitializer, i64 %xn, 0
    %x10 = insertvalue { i64, i64 } %xp, i64 -1, 1
    %x11 = insertvalue { i64, { i64, i64 } } %xo, { i64, i64 } %x10, 1
    br label %ctd_ifd

  elsed:
    %xfa3 = insertvalue { i64, { i64, i64 } } zeroinitializer, i64 %a1a1, 0
    %xg3 = insertvalue { i64, i64 } zeroinitializer, i64 %a1b3, 0
    %x12 = insertvalue { i64, i64 } %xg3, i64 %a1a1, 1
    %x13 = insertvalue { i64, { i64, i64 } } %xfa3, { i64, i64 } %x12, 1
    br label %ctd_ifd

  ctd_ifd:
    %r1 = phi { i64, { i64, i64 } } [ %x13, %elsed ], [ %x11, %ctd_ife ]
    %c_11 = extractvalue { i64, i64 } %s, 0
    %b1 = extractvalue { i64, i64 } %s, 1
    %d1 = icmp eq i64 -1, %b1
    br i1 %d1, label %thenf, label %elsef

  thenf:
    br label %ctd_iff

  elsef:
    br label %ctd_iff

  ctd_iff:
    br label %while_start

  while_end:
    %a1a2 = extractvalue { i64, i64* } %xaa, 0
    %xca2 = extractvalue { i64, i64* } %xaa, 1
    call void @LLVM_DS_NArray_narray_free (i64* %xca2)
    %a1b4 = extractvalue { i64, { i64, i64 } } %xba, 0
    %b2 = extractvalue { i64, { i64, i64 } } %xba, 1
    %a1aa2 = extractvalue { i64, i64 } %b2, 0
    %x14 = extractvalue { i64, i64 } %b2, 1
    br label %ctd_if

  ctd_if:
    %x15 = phi i64 [ %x14, %while_end ], [ 0, %then ]
    ret i64 %x15
}

define void @LLVM_DS_NArray_narray_free(i64* %p) {

  start:
    %a = ptrtoint i64* %p to i64
    %b = ptrtoint i64* null to i64
    %tmp = icmp eq i64 %a, %b
    br i1 %tmp, label %then, label %else

  then:
    br label %ctd_if

  else:
    %c = bitcast i64* %p to i8*
    call void @isabelle_llvm_free (i8* %c)
    br label %ctd_if

  ctd_if:
    ret void
}

define { i64, i64* } @KMP_compute_butlast_ff_s_impl({ i64, i8* } %x) {

  start:
    %a1 = extractvalue { i64, i8* } %x, 0
    %a2 = extractvalue { i64, i8* } %x, 1
    %tmp = icmp eq i64 %a1, 0
    br i1 %tmp, label %then, label %else

  then:
    br label %ctd_if

  else:
    %t = getelementptr i64, i64* null, i64 1
    %a = ptrtoint i64* %t to i64
    %b = call i8* @isabelle_llvm_calloc (i64 %a1, i64 %a)
    %x1 = bitcast i8* %b to i64*
    br label %ctd_if

  ctd_if:
    %xaa = phi i64* [ %x1, %else ], [ null, %then ]
    %xb = insertvalue { i64, i64* } zeroinitializer, i64 %a1, 0
    %xc = insertvalue { i64, i64* } %xb, i64* %xaa, 1
    %xd = insertvalue { i64, i64 } zeroinitializer, i64 0, 0
    %tmpca = insertvalue { i64, i64 } %xd, i64 1, 1
    %xe = insertvalue { { i64, i64* }, { i64, i64 } } zeroinitializer, { i64, i64* } %xc, 0
    %xf = insertvalue { { i64, i64* }, { i64, i64 } } %xe, { i64, i64 } %tmpca, 1
    br label %while_start

  while_start:
    %xda = phi { { i64, i64* }, { i64, i64 } } [ %x9, %while_enda ], [ %xf, %ctd_if ]
    %a1a = extractvalue { { i64, i64* }, { i64, i64 } } %xda, 0
    %xea = extractvalue { { i64, i64* }, { i64, i64 } } %xda, 1
    %a1aa = extractvalue { i64, i64 } %xea, 0
    %a2a = extractvalue { i64, i64 } %xea, 1
    %a1b = extractvalue { i64, i64* } %a1a, 0
    %a2b = extractvalue { i64, i64* } %a1a, 1
    %x2 = icmp slt i64 %a2a, %a1b
    br i1 %x2, label %while_body, label %while_end

  while_body:
    %a1a1 = extractvalue { { i64, i64* }, { i64, i64 } } %xda, 0
    %xea1 = extractvalue { { i64, i64* }, { i64, i64 } } %xda, 1
    %a1aa1 = extractvalue { i64, i64 } %xea1, 0
    %a2a1 = extractvalue { i64, i64 } %xea1, 1
    br label %while_starta

  while_starta:
    %s = phi i64 [ %x7, %while_bodya ], [ %a1aa1, %while_body ]
    %xfa = icmp slt i64 0, %s
    br i1 %xfa, label %thena, label %elsea

  thena:
    %xga = sub i64 %s, 1
    %a1b1 = extractvalue { i64, i8* } %x, 0
    %a2b1 = extractvalue { i64, i8* } %x, 1
    %xh = getelementptr i8, i8* %a2b1, i64 %xga
    %xj = load i8, i8* %xh
    %xka = sub i64 %a2a1, 1
    %a1c = extractvalue { i64, i8* } %x, 0
    %a2c = extractvalue { i64, i8* } %x, 1
    %xl = getelementptr i8, i8* %a2c, i64 %xka
    %x3 = load i8, i8* %xl
    %x4 = icmp ne i8 %xj, %x3
    br label %ctd_ifa

  elsea:
    br label %ctd_ifa

  ctd_ifa:
    %x5 = phi i1 [ 0, %elsea ], [ %x4, %thena ]
    br i1 %x5, label %while_bodya, label %while_enda

  while_bodya:
    %bi = sub i64 %s, 1
    %a1b2 = extractvalue { i64, i64* } %a1a1, 0
    %a2b2 = extractvalue { i64, i64* } %a1a1, 1
    %x6 = getelementptr i64, i64* %a2b2, i64 %bi
    %x7 = load i64, i64* %x6
    br label %while_starta

  while_enda:
    %xga1 = add i64 %s, 1
    %a1b3 = extractvalue { i64, i64* } %a1a1, 0
    %a2b3 = extractvalue { i64, i64* } %a1a1, 1
    %p = getelementptr i64, i64* %a2b3, i64 %a2a1
    store i64 %xga1, i64* %p
    %xj1 = insertvalue { i64, i64* } zeroinitializer, i64 %a1b3, 0
    %xk = insertvalue { i64, i64* } %xj1, i64* %a2b3, 1
    %xla = add i64 %a2a1, 1
    %xm = insertvalue { { i64, i64* }, { i64, i64 } } zeroinitializer, { i64, i64* } %xk, 0
    %xn = insertvalue { i64, i64 } zeroinitializer, i64 %xga1, 0
    %x8 = insertvalue { i64, i64 } %xn, i64 %xla, 1
    %x9 = insertvalue { { i64, i64* }, { i64, i64 } } %xm, { i64, i64 } %x8, 1
    br label %while_start

  while_end:
    %a1a2 = extractvalue { { i64, i64* }, { i64, i64 } } %xda, 0
    %xea2 = extractvalue { { i64, i64* }, { i64, i64 } } %xda, 1
    %a1aa2 = extractvalue { i64, i64 } %xea2, 0
    %a2a2 = extractvalue { i64, i64 } %xea2, 1
    ret { i64, i64* } %a1a2
}
