Require Import VST.floyd.proofauto.
Require Import VST.floyd.Funspec_old_Notation.
Require Import DL.verif.dlinklist.
Require Import DL.verif.verif_dlinklist_def.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

(***********************************************************************
V.Main proofs
***********************************************************************)

(* 
Lemma list_1n_rep_saturate_local_nullprev_tail:
  forall l head tail, 
    list_1n_rep l head tail nullval |-- 
    !! is_pointer_or_null tail.
Proof.
  intros. 
  pose proof (list_1n_rep_saturate_local_tail l head tail nullval
    mapsto_memory_block.is_pointer_or_null_nullval).
  exact H.
Qed.
Hint Resolve list_1n_rep_saturate_local_nullprev_tail: saturate_local.
 *)
Lemma list_head_null : forall l tail prev, 
  list_1n_rep l nullval tail prev |-- !! (l = nil) && emp.
Proof.
  intros.
  destruct l.
  - simpl. entailer!.
  - simpl. Intros old_head. unfold node_rep. 
    entailer!. 
    sfcn.
Qed.

Lemma Z_length_minus_1 : forall a l, Z_length (a :: l) - 1 = Z_length l.
Proof.
  intros.
  unfold Z_length.
  simpl length.
  lia.
Qed.

Lemma Z_length_plus_1 : forall a l, (Z_length l) + 1 = Z_length (a :: l).
Proof.
  intros.
  unfold Z_length.
  simpl length.
  lia.
Qed.

(* proof for next *)
Theorem body_next: 
  semax_body Vprog Gprog f_next next_spec.
Proof.
  start_function.
  unfold node_rep.
  forward.
(* return p->next; *)
(* proof for begin *)
Abort.

Theorem body_begin: 
  semax_body Vprog Gprog f_begin begin_spec.
Proof.
  start_function. 
  unfold list_rep.
  Intros head tail.
  forward.
  forward.                              (* return l->head; *)
  unfold list_single_out.
  destruct (list_nth_out l 0) as [[l1 y] l2] eqn:E.
  destruct y.
  - (* not an empty linklist *)
    destruct l.
    { (* show that l <> [] *)
      rewrite list_nth_nil in E.
      inversion E.
    }
    simpl in E; inversion E; subst.
    simpl list_1n_rep_aux.
    simpl list_1n_rep.
    Intros old_head.
    Exists head head tail nullval nullval old_head tail.
    entailer!.
  - (* an empty linklist *)
    destruct l; [| inversion E].
    destruct H; subst.
    simpl in E; inversion E; subst.
    simpl list_1n_rep.
    Intros; subst.
    Exists nullval nullval nullval.
    entailer!.
    apply TT_right. 
Qed.

(* proof for end *)
Theorem body_end: 
  semax_body Vprog Gprog f_end end_spec.
Proof.
  start_function. 
  unfold list_rep.
  Intros head tail.
  forward.
  { (* TODO: is there some shadowing? *)
    pose proof (list_1n_rep_saturate_local_tail l head tail nullval
    mapsto_memory_block.is_pointer_or_null_nullval).
    sep_apply H.
    entailer!.
  }
  forward.                              (* return l->tail; *)
  unfold list_single_out.
  destruct (list_nth_out l ((length l) - 1)%nat) as [[l1 y] l2] eqn:E.
  destruct y.
  - (* not an empty linklist *)
    destruct l.
    { (* show that l <> [] *)
      rewrite list_nth_nil in E.
      inversion E.
    }
    pose proof (list_cons_app l z0).
    destruct H1 as [l3 [a H1]].
    destruct H1 as [H1 [H2 H3]].
    rewrite H1.
    sep_apply list_1n_split.
    Intros head' tail'.
    simpl list_1n_rep at 1.
    Intros old_head.
    Exists head' head tail.
    Exists head tail' old_head tail.
    pose proof E.
    apply list_nth_tail in E. subst l2.
    simpl_length.
    apply list_nth_split in H6.
    destruct H6 as [H6 H7].
    rewrite <- H3 in H7.
    rewrite <- H2 in H6.
    simpl list_1n_rep.
    inversion H7; subst.
    entailer!.
  - (* empty linklist *)
    Exists nullval head tail.
    destruct l.
    2: {
      simpl_length.
      apply list_nth_split in E.
      destruct E.
      pose proof (list_cons_app l z).
      repeat destruct H3.
      rewrite <- (proj2 H4) in H2.
      discriminate.
    }
    simpl in E; inversion E; subst.
    simpl list_1n_rep.
    Intros; subst.
    entailer!.
    apply TT_right. 
Qed.

(* proof for rend, the same as begin *)
Theorem body_rend: 
  semax_body Vprog Gprog f_rend rend_spec.
Proof.
  start_function. 
  unfold list_rep.
  Intros head tail.
  forward.
  forward.                              (* return l->head; *)
  unfold list_single_out.
  destruct (list_nth_out l 0) as [[l1 y] l2] eqn:E.
  destruct y.
  - (* not an empty linklist *)
    destruct l.
    { (* show that l <> [] *)
      rewrite list_nth_nil in E.
      inversion E.
    }
    simpl in E; inversion E; subst.
    simpl list_1n_rep_aux.
    simpl list_1n_rep.
    Intros old_head.
    Exists head head tail nullval nullval old_head tail.
    entailer!.
  - (* an empty linklist *)
    destruct l; [| inversion E].
    destruct H; subst.
    simpl in E; inversion E; subst.
    simpl list_1n_rep.
    Intros; subst.
    Exists nullval nullval nullval.
    entailer!.
    apply TT_right. 
Qed.

(* proof for rbegin, the same as end *)
Theorem body_rbegin: 
  semax_body Vprog Gprog f_rbegin rbegin_spec.
Proof.
  start_function. 
  unfold list_rep.
  Intros head tail.
  forward.
  { (* TODO: is there some shadowing? *)
    pose proof (list_1n_rep_saturate_local_tail l head tail nullval
    mapsto_memory_block.is_pointer_or_null_nullval).
    sep_apply H.
    entailer!.
  }
  forward.                              (* return l->tail; *)
  unfold list_single_out.
  destruct (list_nth_out l ((length l) - 1)%nat) as [[l1 y] l2] eqn:E.
  destruct y.
  - (* not an empty linklist *)
    destruct l.
    { (* show that l <> [] *)
      rewrite list_nth_nil in E.
      inversion E.
    }
    pose proof (list_cons_app l z0).
    destruct H1 as [l3 [a H1]].
    destruct H1 as [H1 [H2 H3]].
    rewrite H1.
    sep_apply list_1n_split.
    Intros head' tail'.
    simpl list_1n_rep at 1.
    Intros old_head.
    Exists head' head tail.
    Exists head tail' old_head tail.
    pose proof E.
    apply list_nth_tail in E. subst l2.
    simpl_length.
    apply list_nth_split in H6.
    destruct H6 as [H6 H7].
    rewrite <- H3 in H7.
    rewrite <- H2 in H6.
    simpl list_1n_rep.
    inversion H7; subst.
    entailer!.
  - (* empty linklist *)
    Exists nullval head tail.
    destruct l.
    2: {
      simpl_length.
      apply list_nth_split in E.
      destruct E.
      pose proof (list_cons_app l z).
      repeat destruct H3.
      rewrite <- (proj2 H4) in H2.
      discriminate.
    }
    simpl in E; inversion E; subst.
    simpl list_1n_rep.
    Intros; subst.
    entailer!.
    apply TT_right. 
Qed.

(* proof for get_size *)
Theorem body_get_size: 
  semax_body Vprog Gprog f_get_size get_size_spec.
Proof.
  start_function. 
  unfold list_rep.
  Intros head tail.
  forward.
  forward.
  unfold list_rep.
  Exists head tail.
  entailer!.
Qed.
(* 
Definition list_new_spec :=
 DECLARE _list_new
  WITH u : unit
  PRE  [  ]
       PROP() LOCAL() SEP ()
  POST [ tptr t_struct_list ]
    EX v: val,
    PROP ()
    LOCAL (temp ret_temp v)
    SEP (list_rep nil v).
 *)
(* proof for list_new *)
Theorem body_list_new: 
  semax_body Vprog Gprog f_list_new list_new_spec.
Proof.
  start_function.
  forward_call (sizeof t_struct_list).  (* mallocN *)
  { computable. }
  Intros p.
  rewrite memory_block_data_at_ by auto.
  forward.                              (* l->head = NULL;  *)
  forward.                              (* l->tail = NULL;  *)
  forward.                              (* l->size = 0;     *)
  forward.                              (* return;          *)
  Exists p. 
  entailer.
  unfold list_rep. 
  Exists nullval nullval.
  simpl list_1n_rep.
  entailer!.
Qed.

(* proof for list_free *)
Theorem body_list_free: 
  semax_body Vprog Gprog f_list_free list_free_spec.
Proof.
  start_function.
  unfold list_rep.
  Intros head tail.
  forward.                              (* tmp = l->head;   *)
  forward_while
  ( EX l' : list Z, EX head' : val, 
    EX prev' : val, 
    PROP ()
    LOCAL (temp _l p; temp _tmp head')
    SEP (data_at Tsh t_struct_list 
      (Vint (Int.repr (Z_length l')), (head', tail)) p * 
      list_1n_rep l' head' tail prev'))%assert.
  { Exists l head nullval. entailer!. }
  { destruct l'; entailer!. }
  { (* loop body *)
    destruct l'.
    { simpl. Intros. contradiction. }
    simpl. unfold node_rep. Intros old_head.
    forward.
    forward.                            (* l->head = tmp->next; *) 
    forward_call (head', sizeof t_struct_node); [solve_free | ].
                                        (* freeN(tmp, sizeof (struct node)); *)
    forward.
    forward.                            (* l->size -= 1;    *)
    forward.                            (* tmp = l->head;   *)
    Exists (l', old_head, head').
    entailer!.
    rewrite Z_length_minus_1.
    entailer!.
  }
  subst head'.
  sep_apply list_head_null.
  Intros.
  forward_call (p, sizeof t_struct_list); [solve_free | ].
                                        (* freeN(l, sizeof (struct list)); *)
  entailer!.
Qed.


(* 
Definition begin_spec :=
 DECLARE _begin
  WITH p : val, l : list Z
  PRE  [ _l OF (tptr t_struct_list) ]
    PROP () 
    LOCAL (temp _l p) 
    SEP (list_rep l p)
  POST [ tptr t_struct_node ]
    EX res : val, EX head : val, EX tail : val, 
    PROP ()
    LOCAL (temp ret_temp res)
    SEP (data_at Tsh t_struct_list
          (Vint (Int.repr (Z_length l)), (head, tail)) p; 
          list_single_out l 0%nat res).
 *)
Theorem body_begin_ref: 
  semax_body Vprog Gprog f_begin begin_spec.
Proof.
  start_function. 
  unfold list_rep.
  Intros head tail.
  forward.
  forward.                              (* return l->head; *)
  unfold list_single_out. 

  
  destruct (list_nth_out l 0) as [[l1 y] l2] eqn:E.
  destruct y.
  - (* not an empty linklist *)
    destruct l.
    { (* show that l <> [] *)
      rewrite list_nth_nil in E.
      inversion E.
    }
    simpl in E; inversion E; subst.
    simpl list_1n_rep_aux.
    simpl list_1n_rep.
    Intros old_head.
    Exists head head tail nullval nullval old_head tail.
    entailer!.
  - (* an empty linklist *)
    destruct l; [| inversion E].
    destruct H; subst.
    simpl in E; inversion E; subst.
    simpl list_1n_rep.
    Intros; subst.
    Exists nullval nullval nullval.
    entailer!.
    apply TT_right. 
Qed.

