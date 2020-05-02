From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "dlinklist.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 17%positive.
Definition ___builtin_annot_intval : ident := 18%positive.
Definition ___builtin_bswap : ident := 10%positive.
Definition ___builtin_bswap16 : ident := 12%positive.
Definition ___builtin_bswap32 : ident := 11%positive.
Definition ___builtin_bswap64 : ident := 9%positive.
Definition ___builtin_clz : ident := 43%positive.
Definition ___builtin_clzl : ident := 44%positive.
Definition ___builtin_clzll : ident := 45%positive.
Definition ___builtin_ctz : ident := 46%positive.
Definition ___builtin_ctzl : ident := 47%positive.
Definition ___builtin_ctzll : ident := 48%positive.
Definition ___builtin_debug : ident := 60%positive.
Definition ___builtin_fabs : ident := 13%positive.
Definition ___builtin_fmadd : ident := 51%positive.
Definition ___builtin_fmax : ident := 49%positive.
Definition ___builtin_fmin : ident := 50%positive.
Definition ___builtin_fmsub : ident := 52%positive.
Definition ___builtin_fnmadd : ident := 53%positive.
Definition ___builtin_fnmsub : ident := 54%positive.
Definition ___builtin_fsqrt : ident := 14%positive.
Definition ___builtin_membar : ident := 19%positive.
Definition ___builtin_memcpy_aligned : ident := 15%positive.
Definition ___builtin_nop : ident := 59%positive.
Definition ___builtin_read16_reversed : ident := 55%positive.
Definition ___builtin_read32_reversed : ident := 56%positive.
Definition ___builtin_sel : ident := 16%positive.
Definition ___builtin_va_arg : ident := 21%positive.
Definition ___builtin_va_copy : ident := 22%positive.
Definition ___builtin_va_end : ident := 23%positive.
Definition ___builtin_va_start : ident := 20%positive.
Definition ___builtin_write16_reversed : ident := 57%positive.
Definition ___builtin_write32_reversed : ident := 58%positive.
Definition ___compcert_i64_dtos : ident := 28%positive.
Definition ___compcert_i64_dtou : ident := 29%positive.
Definition ___compcert_i64_sar : ident := 40%positive.
Definition ___compcert_i64_sdiv : ident := 34%positive.
Definition ___compcert_i64_shl : ident := 38%positive.
Definition ___compcert_i64_shr : ident := 39%positive.
Definition ___compcert_i64_smod : ident := 36%positive.
Definition ___compcert_i64_smulh : ident := 41%positive.
Definition ___compcert_i64_stod : ident := 30%positive.
Definition ___compcert_i64_stof : ident := 32%positive.
Definition ___compcert_i64_udiv : ident := 35%positive.
Definition ___compcert_i64_umod : ident := 37%positive.
Definition ___compcert_i64_umulh : ident := 42%positive.
Definition ___compcert_i64_utod : ident := 31%positive.
Definition ___compcert_i64_utof : ident := 33%positive.
Definition ___compcert_va_composite : ident := 27%positive.
Definition ___compcert_va_float64 : ident := 26%positive.
Definition ___compcert_va_int32 : ident := 24%positive.
Definition ___compcert_va_int64 : ident := 25%positive.
Definition _begin : ident := 67%positive.
Definition _delete : ident := 82%positive.
Definition _end : ident := 68%positive.
Definition _freeN : ident := 62%positive.
Definition _get_size : ident := 71%positive.
Definition _head : ident := 6%positive.
Definition _insert : ident := 81%positive.
Definition _k : ident := 86%positive.
Definition _l : ident := 63%positive.
Definition _l1 : ident := 83%positive.
Definition _l2 : ident := 84%positive.
Definition _list : ident := 8%positive.
Definition _list_free : ident := 66%positive.
Definition _list_new : ident := 64%positive.
Definition _main : ident := 88%positive.
Definition _mallocN : ident := 61%positive.
Definition _merge : ident := 85%positive.
Definition _move : ident := 80%positive.
Definition _nd : ident := 73%positive.
Definition _next : ident := 4%positive.
Definition _node : ident := 2%positive.
Definition _pop_back : ident := 76%positive.
Definition _pop_front : ident := 78%positive.
Definition _pos : ident := 79%positive.
Definition _prev : ident := 3%positive.
Definition _push_back : ident := 74%positive.
Definition _push_front : ident := 77%positive.
Definition _rbegin : ident := 69%positive.
Definition _rend : ident := 70%positive.
Definition _res : ident := 75%positive.
Definition _size : ident := 5%positive.
Definition _split_K : ident := 87%positive.
Definition _tail : ident := 7%positive.
Definition _tmp : ident := 65%positive.
Definition _v : ident := 72%positive.
Definition _val : ident := 1%positive.
Definition _t'1 : ident := 89%positive.
Definition _t'10 : ident := 98%positive.
Definition _t'2 : ident := 90%positive.
Definition _t'3 : ident := 91%positive.
Definition _t'4 : ident := 92%positive.
Definition _t'5 : ident := 93%positive.
Definition _t'6 : ident := 94%positive.
Definition _t'7 : ident := 95%positive.
Definition _t'8 : ident := 96%positive.
Definition _t'9 : ident := 97%positive.

Definition f_list_new := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_l, (tptr (Tstruct _list noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _list noattr) tuint) :: nil))
    (Sset _l
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _list noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _size tuint)
          (Econst_int (Int.repr 0) tint))
        (Sreturn (Some (Etempvar _l (tptr (Tstruct _list noattr)))))))))
|}.

Definition f_list_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tmp, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
        (Sifthenelse (Ebinop One
                       (Etempvar _t'3 (tptr (Tstruct _node noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          Sskip
          Sbreak))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
          (Sset _tmp
            (Efield
              (Ederef (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _head
                (tptr (Tstruct _node noattr))))
            (Scall None
              (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil))
                             tvoid cc_default))
              ((Etempvar _t'1 (tptr (Tstruct _node noattr))) ::
               (Esizeof (Tstruct _node noattr) tuint) :: nil)))
          (Sassign
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr)))
            (Etempvar _tmp (tptr (Tstruct _node noattr)))))))
    Sskip)
  (Scall None
    (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid
                   cc_default))
    ((Etempvar _l (tptr (Tstruct _list noattr))) ::
     (Esizeof (Tstruct _list noattr) tuint) :: nil)))
|}.

Definition f_begin := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
        (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _node noattr))))))
|}.

Definition f_end := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
        (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _node noattr))))))
|}.

Definition f_rbegin := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
        (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _node noattr))))))
|}.

Definition f_rend := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
        (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _node noattr))))))
|}.

Definition f_get_size := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
        (Tstruct _list noattr)) _size tuint))
  (Sreturn (Some (Etempvar _t'1 tuint))))
|}.

Definition f_push_back := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nd, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'5, (tptr (Tstruct _node noattr))) :: (_t'4, tuint) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _node noattr) tuint) :: nil))
    (Sset _nd
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _node noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _val tuint) (Etempvar _v tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _prev (tptr (Tstruct _node noattr)))
            (Etempvar _t'5 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _size tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _size tuint)
              (Ebinop Oadd (Etempvar _t'4 tuint)
                (Econst_int (Int.repr 1) tint) tuint)))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _node noattr))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sassign
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _head
                  (tptr (Tstruct _node noattr)))
                (Etempvar _nd (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _t'3 (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _next
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _nd (tptr (Tstruct _node noattr))))))))))))
|}.

Definition f_pop_back := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tuint) :: (_tmp, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'6
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'6 (tptr (Tstruct _node noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
      (Sset _res
        (Efield
          (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _val tuint)))
    (Ssequence
      (Sset _tmp
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _tmp (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _prev (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr)))
            (Etempvar _t'4 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Scall None
            (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil))
                           tvoid cc_default))
            ((Etempvar _tmp (tptr (Tstruct _node noattr))) ::
             (Esizeof (Tstruct _node noattr) tuint) :: nil))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _size tuint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _size tuint)
                (Ebinop Osub (Etempvar _t'3 tuint)
                  (Econst_int (Int.repr 1) tint) tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _node noattr))))
                (Sifthenelse (Ebinop Oeq
                               (Etempvar _t'1 (tptr (Tstruct _node noattr)))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _head
                      (tptr (Tstruct _node noattr)))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _tail
                        (tptr (Tstruct _node noattr))))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _next
                        (tptr (Tstruct _node noattr)))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
              (Sreturn (Some (Etempvar _res tuint))))))))))
|}.

Definition f_push_front := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nd, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr tvoid)) ::
               (_t'5, (tptr (Tstruct _node noattr))) :: (_t'4, tuint) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _node noattr) tuint) :: nil))
    (Sset _nd
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _node noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _val tuint) (Etempvar _v tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _prev (tptr (Tstruct _node noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr)))
            (Etempvar _t'5 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _size tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _size tuint)
              (Ebinop Oadd (Etempvar _t'4 tuint)
                (Econst_int (Int.repr 1) tint) tuint)))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _head
                (tptr (Tstruct _node noattr))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sassign
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _tail
                  (tptr (Tstruct _node noattr)))
                (Etempvar _nd (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _head
                    (tptr (Tstruct _node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _t'3 (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _prev
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _nd (tptr (Tstruct _node noattr))))))))))))
|}.

Definition f_pop_front := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tuint) :: (_tmp, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'6
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'6 (tptr (Tstruct _node noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
      (Sset _res
        (Efield
          (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _val tuint)))
    (Ssequence
      (Sset _tmp
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _tmp (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr)))
            (Etempvar _t'4 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Scall None
            (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil))
                           tvoid cc_default))
            ((Etempvar _tmp (tptr (Tstruct _node noattr))) ::
             (Esizeof (Tstruct _node noattr) tuint) :: nil))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _size tuint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _size tuint)
                (Ebinop Osub (Etempvar _t'3 tuint)
                  (Econst_int (Int.repr 1) tint) tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _head
                    (tptr (Tstruct _node noattr))))
                (Sifthenelse (Ebinop Oeq
                               (Etempvar _t'1 (tptr (Tstruct _node noattr)))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _tail
                      (tptr (Tstruct _node noattr)))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _head
                        (tptr (Tstruct _node noattr))))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _prev
                        (tptr (Tstruct _node noattr)))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
              (Sreturn (Some (Etempvar _res tuint))))))))))
|}.

Definition f_move := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: (_pos, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _res
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
        (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
  (Ssequence
    (Swhile
      (Ebinop Ogt (Etempvar _pos tint) (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _res
          (Efield
            (Ederef (Etempvar _res (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr))))
        (Sset _pos
          (Ebinop Osub (Etempvar _pos tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Sreturn (Some (Etempvar _res (tptr (Tstruct _node noattr)))))))
|}.

Definition f_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: (_pos, tint) ::
                (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, (tptr (Tstruct _node noattr))) ::
               (_nd, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) :: (_t'4, tuint) ::
               (_t'3, tuint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _pos tint) (Econst_int (Int.repr 0) tint)
               tint)
  (Scall None
    (Evar _push_front (Tfunction
                        (Tcons (tptr (Tstruct _list noattr))
                          (Tcons tuint Tnil)) tvoid cc_default))
    ((Etempvar _l (tptr (Tstruct _list noattr))) :: (Etempvar _v tuint) ::
     nil))
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _size tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _pos tint) (Etempvar _t'3 tuint) tint)
      (Scall None
        (Evar _push_back (Tfunction
                           (Tcons (tptr (Tstruct _list noattr))
                             (Tcons tuint Tnil)) tvoid cc_default))
        ((Etempvar _l (tptr (Tstruct _list noattr))) ::
         (Etempvar _v tuint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _move (Tfunction
                          (Tcons (tptr (Tstruct _list noattr))
                            (Tcons tint Tnil)) (tptr (Tstruct _node noattr))
                          cc_default))
            ((Etempvar _l (tptr (Tstruct _list noattr))) ::
             (Etempvar _pos tint) :: nil))
          (Sset _res (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)
                               cc_default))
              ((Esizeof (Tstruct _node noattr) tuint) :: nil))
            (Sset _nd
              (Ecast (Etempvar _t'2 (tptr tvoid))
                (tptr (Tstruct _node noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _val tuint) (Etempvar _v tuint))
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef (Etempvar _res (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _prev
                    (tptr (Tstruct _node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _prev
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _t'6 (tptr (Tstruct _node noattr)))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _next
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _res (tptr (Tstruct _node noattr))))
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef (Etempvar _res (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _prev
                        (tptr (Tstruct _node noattr))))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _next
                        (tptr (Tstruct _node noattr)))
                      (Etempvar _nd (tptr (Tstruct _node noattr)))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _res (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _prev
                        (tptr (Tstruct _node noattr)))
                      (Etempvar _nd (tptr (Tstruct _node noattr))))
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _size tuint))
                      (Sassign
                        (Efield
                          (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _size tuint)
                        (Ebinop Oadd (Etempvar _t'4 tuint)
                          (Econst_int (Int.repr 1) tint) tuint)))))))))))))
|}.

Definition f_delete := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: (_pos, tint) ::
                (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) :: (_t'3, tuint) ::
               (_t'2, tuint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _pos tint) (Econst_int (Int.repr 0) tint)
               tint)
  (Scall None
    (Evar _pop_front (Tfunction (Tcons (tptr (Tstruct _list noattr)) Tnil)
                       tuint cc_default))
    ((Etempvar _l (tptr (Tstruct _list noattr))) :: nil))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _size tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _pos tint)
                   (Ebinop Osub (Etempvar _t'2 tuint)
                     (Econst_int (Int.repr 1) tint) tuint) tint)
      (Scall None
        (Evar _pop_back (Tfunction (Tcons (tptr (Tstruct _list noattr)) Tnil)
                          tuint cc_default))
        ((Etempvar _l (tptr (Tstruct _list noattr))) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _move (Tfunction
                          (Tcons (tptr (Tstruct _list noattr))
                            (Tcons tint Tnil)) (tptr (Tstruct _node noattr))
                          cc_default))
            ((Etempvar _l (tptr (Tstruct _list noattr))) ::
             (Etempvar _pos tint) :: nil))
          (Sset _res (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _res (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _prev
                (tptr (Tstruct _node noattr))))
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _res (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _next
                  (tptr (Tstruct _node noattr))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _t'6 (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _next
                  (tptr (Tstruct _node noattr)))
                (Etempvar _t'7 (tptr (Tstruct _node noattr))))))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _res (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _next
                  (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef (Etempvar _res (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _prev
                    (tptr (Tstruct _node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _t'4 (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _prev
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _t'5 (tptr (Tstruct _node noattr))))))
            (Ssequence
              (Scall None
                (Evar _freeN (Tfunction
                               (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid
                               cc_default))
                ((Etempvar _res (tptr (Tstruct _node noattr))) ::
                 (Esizeof (Tstruct _node noattr) tuint) :: nil))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _size tuint))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _size tuint)
                  (Ebinop Osub (Etempvar _t'3 tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))))))))
|}.

Definition f_merge := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l1, (tptr (Tstruct _list noattr))) ::
                (_l2, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'9, (tptr (Tstruct _node noattr))) ::
               (_t'8, (tptr (Tstruct _node noattr))) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr (Tstruct _node noattr))) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'7
      (Efield
        (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
    (Sifthenelse (Ebinop One (Etempvar _t'7 (tptr (Tstruct _node noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _t'8 (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _next (tptr (Tstruct _node noattr)))
            (Etempvar _t'9 (tptr (Tstruct _node noattr))))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
      (Sifthenelse (Ebinop One (Etempvar _t'4 (tptr (Tstruct _node noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _node noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _prev
                (tptr (Tstruct _node noattr)))
              (Etempvar _t'6 (tptr (Tstruct _node noattr))))))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail (tptr (Tstruct _node noattr)))
          (Etempvar _t'3 (tptr (Tstruct _node noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _size tuint))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _l2 (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _size tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _l1 (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _size tuint)
              (Ebinop Oadd (Etempvar _t'1 tuint) (Etempvar _t'2 tuint) tuint))))
        (Scall None
          (Evar _freeN (Tfunction (Tcons (tptr tvoid) (Tcons tint Tnil))
                         tvoid cc_default))
          ((Etempvar _l2 (tptr (Tstruct _list noattr))) ::
           (Esizeof (Tstruct _list noattr) tuint) :: nil))))))
|}.

Definition f_split_K := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _list noattr))) :: (_k, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, (tptr (Tstruct _list noattr))) ::
               (_nd, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) ::
               (_t'10, (tptr (Tstruct _node noattr))) ::
               (_t'9, (tptr (Tstruct _node noattr))) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) :: (_t'4, tuint) ::
               (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _list_new (Tfunction Tnil (tptr (Tstruct _list noattr))
                        cc_default)) nil)
    (Sset _res (Etempvar _t'1 (tptr (Tstruct _list noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _k tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _res (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head (tptr (Tstruct _node noattr)))
            (Etempvar _t'10 (tptr (Tstruct _node noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _node noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _res (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _node noattr)))
              (Etempvar _t'9 (tptr (Tstruct _node noattr)))))
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _size tuint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _res (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _size tuint)
                (Etempvar _t'8 tuint)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _head
                  (tptr (Tstruct _node noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _node noattr)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _size tuint)
                  (Econst_int (Int.repr 0) tint)))))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _size tuint))
        (Sifthenelse (Ebinop Olt (Etempvar _k tuint) (Etempvar _t'3 tuint)
                       tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _move (Tfunction
                              (Tcons (tptr (Tstruct _list noattr))
                                (Tcons tint Tnil))
                              (tptr (Tstruct _node noattr)) cc_default))
                ((Etempvar _l (tptr (Tstruct _list noattr))) ::
                 (Etempvar _k tuint) :: nil))
              (Sset _nd (Etempvar _t'2 (tptr (Tstruct _node noattr)))))
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _res (tptr (Tstruct _list noattr)))
                      (Tstruct _list noattr)) _tail
                    (tptr (Tstruct _node noattr)))
                  (Etempvar _t'7 (tptr (Tstruct _node noattr)))))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef (Etempvar _nd (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _prev
                      (tptr (Tstruct _node noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _l (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _tail
                      (tptr (Tstruct _node noattr)))
                    (Etempvar _t'6 (tptr (Tstruct _node noattr)))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _res (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _head
                      (tptr (Tstruct _node noattr)))
                    (Etempvar _nd (tptr (Tstruct _node noattr))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'5
                        (Efield
                          (Ederef
                            (Etempvar _nd (tptr (Tstruct _node noattr)))
                            (Tstruct _node noattr)) _prev
                          (tptr (Tstruct _node noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _t'5 (tptr (Tstruct _node noattr)))
                            (Tstruct _node noattr)) _next
                          (tptr (Tstruct _node noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _nd (tptr (Tstruct _node noattr)))
                            (Tstruct _node noattr)) _prev
                          (tptr (Tstruct _node noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'4
                            (Efield
                              (Ederef
                                (Etempvar _l (tptr (Tstruct _list noattr)))
                                (Tstruct _list noattr)) _size tuint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _res (tptr (Tstruct _list noattr)))
                                (Tstruct _list noattr)) _size tuint)
                            (Ebinop Osub (Etempvar _t'4 tuint)
                              (Etempvar _k tuint) tuint)))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _l (tptr (Tstruct _list noattr)))
                              (Tstruct _list noattr)) _size tuint)
                          (Etempvar _k tuint)))))))))
          Sskip)))
    (Sreturn (Some (Etempvar _res (tptr (Tstruct _list noattr)))))))
|}.

Definition composites : list composite_definition :=
(Composite _node Struct
   ((_val, tuint) :: (_prev, (tptr (Tstruct _node noattr))) ::
    (_next, (tptr (Tstruct _node noattr))) :: nil)
   noattr ::
 Composite _list Struct
   ((_size, tuint) :: (_head, (tptr (Tstruct _node noattr))) ::
    (_tail, (tptr (Tstruct _node noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_freeN,
   Gfun(External (EF_external "freeN"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tint Tnil))
     tvoid cc_default)) :: (_list_new, Gfun(Internal f_list_new)) ::
 (_list_free, Gfun(Internal f_list_free)) ::
 (_begin, Gfun(Internal f_begin)) :: (_end, Gfun(Internal f_end)) ::
 (_rbegin, Gfun(Internal f_rbegin)) :: (_rend, Gfun(Internal f_rend)) ::
 (_get_size, Gfun(Internal f_get_size)) ::
 (_push_back, Gfun(Internal f_push_back)) ::
 (_pop_back, Gfun(Internal f_pop_back)) ::
 (_push_front, Gfun(Internal f_push_front)) ::
 (_pop_front, Gfun(Internal f_pop_front)) ::
 (_move, Gfun(Internal f_move)) :: (_insert, Gfun(Internal f_insert)) ::
 (_delete, Gfun(Internal f_delete)) :: (_merge, Gfun(Internal f_merge)) ::
 (_split_K, Gfun(Internal f_split_K)) :: nil).

Definition public_idents : list ident :=
(_split_K :: _merge :: _delete :: _insert :: _move :: _pop_front ::
 _push_front :: _pop_back :: _push_back :: _get_size :: _rend :: _rbegin ::
 _end :: _begin :: _list_free :: _list_new :: _freeN :: _mallocN ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


