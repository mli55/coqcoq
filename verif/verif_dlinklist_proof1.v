Require Import VST.floyd.proofauto.
Require Import VST.floyd.Funspec_old_Notation.
Require Import DL.verif.dlinklist.
Require Import DL.verif.verif_dlinklist_def.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

(***********************************************************************
Main proofs
***********************************************************************)

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

Lemma Z_length_plus : forall l1 l2, 
  (Z_length l1) + (Z_length l2) = Z_length (l1 ++ l2).
Proof.
  intros.
  unfold Z_length.
  rewrite app_length.
  lia.
Qed.

(* quick unfold *)
(* TODO: maybe not useful *)
Ltac unfold_list_rep := unfold list_rep, list_full_rep.


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
  unfold_list_rep.
  Exists nullval nullval.
  simpl list_1n_rep.
  entailer!.
Qed.

(* proof for list_free *)
Theorem body_list_free: 
  semax_body Vprog Gprog f_list_free list_free_spec.
Proof.
  start_function.
  unfold_list_rep.
  Intros head tail.
  forward.                              (* tmp = l->head;   *)
  forward_while
  ( EX l' : list Z, EX head' : val, 
    EX prev' : val, 
    PROP ()
    LOCAL (temp _l p; temp _tmp head')
    SEP (data_at Tsh t_struct_list 
      (Vint (Int.repr (Z_length l')), (head', tail)) p * 
      list_1n_rep l' head' tail prev' nullval))%assert.
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
  subst; simpl list_1n_rep.
  entailer!.
Qed.

(* proof for get_size *)
Theorem body_get_size: 
  semax_body Vprog Gprog f_get_size get_size_spec.
Proof.
  start_function. 
  unfold_list_rep.
  Intros head tail.
  forward.
  forward.
  unfold_list_rep.
  Exists head tail.
  entailer!.
Qed.

(* proof for next *)
Theorem body_next: 
  semax_body Vprog Gprog f_next next_spec.
Proof.
  start_function.
  unfold node_rep.
  forward.
  forward.                              (* return p->next; *)
Qed.

(* proof for rnext *)
Theorem body_rnext: 
  semax_body Vprog Gprog f_rnext rnext_spec.
Proof.
  start_function.
  unfold node_rep.
  forward.
  { sep_apply list_1n_rep_saturate_local_tail_nullval; entailer!. }
  forward.                              (* return p->prev; *)
Qed.

(* proof for begin *)
Theorem body_begin: 
  semax_body Vprog Gprog f_begin begin_spec.
Proof.
  start_function. 
  unfold_list_rep.
  Intros.
  forward.
  forward.                              (* return l->head; *)
  Exists head.
  entailer.
  sep_apply node_in_list_begin.
  entailer!.
Qed.

(* proof for end *)
Theorem body_end: 
  semax_body Vprog Gprog f_end end_spec.
Proof.
  start_function. 
  unfold_list_rep.
  Intros.
  forward.
  { sep_apply list_1n_rep_saturate_local_tail_nullval; entailer!. }
  forward.                              (* return l->tail; *)
  Exists tail.
  entailer.
  sep_apply node_in_list_end.
  entailer!.
Qed.

(* proof for rbegin, the same as end *)
Theorem body_rbegin: 
  semax_body Vprog Gprog f_rbegin rbegin_spec.
Proof.
  start_function. 
  unfold_list_rep.
  Intros.
  forward.
  { sep_apply list_1n_rep_saturate_local_tail_nullval; entailer!. }
  forward.                              (* return l->tail; *)
  Exists tail.
  entailer.
  sep_apply node_in_list_end.
  entailer!.
Qed.

(* proof for rend, the same as begin *)
Theorem body_rend: 
  semax_body Vprog Gprog f_rend rend_spec.
Proof.
  start_function. 
  unfold_list_rep.
  Intros.
  forward.
  forward.                              (* return l->head; *)
  Exists head.
  entailer.
  sep_apply node_in_list_begin.
  entailer!.
Qed.
(* 
(* proof for move *)
Theorem body_move: 
  semax_body Vprog Gprog f_move move_spec.
Proof.
  start_function.
  unfold_list_rep.
  Intros.
  forward.                              (* res = l->head; *)
  forward_loop
  ( EX pos' : nat, 
    EX dis : nat, 
    EX res' : val, 
    PROP ((0 <= pos')%nat; (pos' + dis = pos)%nat; (dis < length l)%nat)
    LOCAL (temp _res res'; temp _l p; 
      temp _pos (Vint (Int.repr (Z.of_nat pos'))))
    SEP (data_at Tsh t_struct_list
          (Vint (Int.repr (Z_length l)), (head, tail)) p;
    list_single_out l dis head tail res'))%assert.
  { 
    Exists pos 0%nat head.
    entailer!.
    apply node_in_list_begin.
  }
  { 
    entailer!.
  }
  {
    unfold list_single_out.
    assert (HE1 : pos' <> 0%nat).
    { 
      intro. subst. 
      simpl in HRE.
      lia.
    }
    assert (HE2 : (dis + 1 < Datatypes.length l)%nat) by lia.
    destruct (list_nth_out l dis) as [[l1 y] l2] eqn:E.
    pose proof E as E_copy.
    apply list_nth_split in E.
    destruct E as [E1 E2].
    pose proof (list_index_some l dis H3).
    destruct H4 as [x E3].
    rewrite E3 in E2.
    subst y.
    unfold node_in_list.
    Intros tail1 head2.
    unfold node_rep.
    forward.                            (* res = res->next; *)
    forward.                            (* pos -= 1u; *)
    Exists ((pos' - 1)%nat, (dis + 1)%nat, head2).
    simpl fst. simpl snd.
    entailer!; [ do 2 f_equal; lia | ].
    unfold list_single_out.
    (* TODO: 感觉这部分重复率挺高的 *)
    destruct (list_nth_out l (dis + 1)) as [[l3 z] l4] eqn:E.
    pose proof E as E_copy2.
    apply list_nth_split in E.
    destruct E as [E1 E2].
    pose proof (list_index_some l (dis + 1)%nat HE2).
    destruct H2 as [x1 E4].
    rewrite E4 in E2.
    subst.
    unfold node_in_list.
    Exists res'.
    (* show l2 <> [] *)
    pose proof list_nth_out_step.
    specialize (H2 l (list_prefix l (dis + 1)) l4).
    specialize (H2 (list_prefix l dis) l2 x1 x dis).
    rewrite Nat.add_1_r in *.
    specialize (H2 E_copy2 E_copy).
    destruct H2.
    rewrite H2, H8.
    simpl list_1n_rep at 2.
    Intros old_head.
    Exists old_head.
    entailer!.
    eapply derives_trans; [ | apply list_1n_merge ].
    simpl list_1n_rep.
    Exists head2.
    unfold node_rep.
    entailer.
  }
  forward.                              (* return res; *)
  Exists res'.
  assert (pos' = 0%nat) by lia.
  subst pos'.
  simpl plus.
  entailer!.
Qed.

(* proof for merge *)
Theorem body_merge: 
  semax_body Vprog Gprog f_merge merge_spec.
Proof.
  start_function.
  unfold_list_rep.
  Intros head1 tail1 head2 tail2.
  forward.
  forward_if                            (* if (l2->head != NULL) *)
  (PROP (l2 <> [])
   LOCAL (temp _l1 p1; temp _l2 p2)
   SEP (data_at Tsh t_struct_list
          (Vint (Int.repr (Z_length l1)), (head1, tail1)) p1;
   list_1n_rep l1 head1 tail1 nullval nullval;
   data_at Tsh t_struct_list
     (Vint (Int.repr (Z_length l2)), (head2, tail2)) p2;
   list_1n_rep l2 head2 tail2 tail1 nullval)).
  { 
    destruct l2; [ simpl list_1n_rep at 2; Intros; contradiction | ].
    simpl list_1n_rep.
    Intros old_head.
    forward.
    forward.
    { sep_apply list_1n_rep_saturate_local_tail_nullval; entailer!. }
    unfold node_rep.
    forward.                            (* l2->head->prev = l1->tail; *)
    entailer!.
    { discriminate. }
    simpl list_1n_rep.
    Exists old_head.
    unfold node_rep.
    entailer!.
  }
  { 
    forward_call (p2, sizeof t_struct_list); [solve_free | ].
                                        (* freeN(l, sizeof (struct list)); *)
    forward.                            (* return; *)
    entailer!.
    destruct l2; simpl list_1n_rep.
    2: {
      Intros old_head.
      unfold node_rep. 
      entailer!.
      sfcn.
    }
    rewrite app_nil_r.
    unfold_list_rep.
    Exists head1 tail1.
    entailer!.
  }
  assert_PROP (is_pointer_or_null tail1).
  { sep_apply list_1n_rep_saturate_local_tail_nullval; entailer!. }
  assert_PROP (is_pointer_or_null tail2).
  {
    pose proof (list_1n_rep_saturate_local_tail l2 head2 tail2 tail1 nullval H).
    sep_apply H0.
    entailer!.
  }
  forward.
  apply semax_if_seq.
  forward_if.                           (* if (l1->tail != NULL) *)
  {
    destruct l1; simpl list_1n_rep; 
      [ | Intros old_head1; sep_apply list_1n_rep_valid_pointer_tail ]; 
      entailer.
  }
  { (* l1 is not empty *)
    destruct l1; [ simpl list_1n_rep at 1; Intros; contradiction | ].
    forward.
    forward.
    pose proof (list_cons_app l1 z).
    destruct H3 as [l3 [a H3]].
    destruct H3 as [H3 [H4 H5]].
    rewrite H3.
    sep_apply list_1n_split.
    Intros head1' tail1'.
    simpl list_1n_rep.
    Intros tail1_prev.
    subst tail1. subst tail1_prev.
    unfold node_rep at 1.
    forward.                            (* l1->tail->next = l2->head; *)
    forward.
    forward.                            (* l1->tail = l2->tail; *)
    forward.
    forward.
    forward.                            (* l1->size += l2->size; *)
    forward_call (p2, sizeof t_struct_list); [solve_free | ].
                                        (* freeN(l, sizeof (struct list)); *)
    entailer.
    unfold_list_rep.
    Exists head1 tail2.
    rewrite <- H3.
    rewrite Z_length_plus.
    entailer!.
    rewrite H3 at 2.
    remember (list_prefix (z :: l1) (Datatypes.length l1)) as l3.
    pose proof (list_1n_merge l3 (a :: l2) head1 tail1' 
      head1' tail2 nullval nullval).
    rewrite <- app_assoc.
    simpl.
    eapply derives_trans; [ | apply H10 ].
    simpl list_1n_rep.
    Exists head2.
    unfold node_rep.
    entailer!.
  }
  { (* l1 is empty *)
    subst tail1.
    destruct l1.
    2: {
      sep_apply list_tail_nullval.
      Intros.
    }
    simpl list_1n_rep at 1.
    forward.
    forward.                            (* l1->head = l2->head; *)
    forward.
    forward.                            (* l1->tail = l2->tail; *)
    forward.
    forward.
    forward.                            (* l1->size += l2->size; *)
    forward_call (p2, sizeof t_struct_list); [solve_free | ].
                                        (* freeN(l, sizeof (struct list)); *)
    entailer!.
    simpl.
    unfold_list_rep.
    Exists head2 tail2.
    entailer!.
  }
Qed.  *)