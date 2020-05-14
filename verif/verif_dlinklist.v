Require Import VST.floyd.proofauto.
Require Import VST.floyd.Funspec_old_Notation.
Require Import DL.verif.dlinklist.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

(***********************************************************************

Memory representation of doubly link list

***********************************************************************)

Definition t_struct_node : type := Tstruct _node noattr.
Definition t_struct_list : type := Tstruct _list noattr.

Definition node_rep (v : Z) (prev next p : val) : mpred :=
  data_at Tsh t_struct_node 
    (Vint (Int.repr v), (prev, next)) p. 

Fixpoint list_1n_rep (l : list Z) (head tail : val) (prev : val) : mpred :=
  match l with
  | x :: l'   => EX old_head : val,
    node_rep x prev old_head head * list_1n_rep l' old_head tail head
  | nil       => !! (tail = prev /\ head = nullval) && emp
  end.

Definition Z_length (l : list Z) : Z := Z.of_nat (length l).

Definition list_rep (l : list Z) (p : val) : mpred :=
  EX head : val, EX tail : val, 
  data_at Tsh t_struct_list 
    (Vint (Int.repr (Z_length l)), (head, tail)) p * list_1n_rep l head tail nullval.

(* TODO: may be not useful *)
Definition list_fst (l : list Z) : option Z := 
  match l with 
  | x :: l'   => Some x
  | nil       => None
  end.

(* TODO: may be not useful *)
Fixpoint list_lst (l : list Z) : option Z := 
  match l with 
  | nil       => None
  | x :: nil  => Some x
  | x :: l'   => list_lst l'
  end.

Fixpoint list_nth (l : list Z) (n : nat) : (list Z) * (option Z) * (list Z) := 
  match n with 
  | O     =>
    match l with
    | x :: l'   => (nil, Some x, l')
    | nil       => (nil, None, nil)
    end
  | S n'  =>
    match l with
    | x :: l'   => let '(l1, y, l2) := list_nth l' n' in (x :: l1, y, l2)
    | nil       => list_nth nil n'
    end
  end.

Fixpoint list_prefix (l : list Z) (n : nat) : list Z :=
  match n with
  | O     => nil
  | S n'  => 
    match l with
    | x :: l'   => x :: (list_prefix l' n')
    | nil       => list_prefix nil n'
    end
  end.

Lemma nil_prefix_nil : forall n, list_prefix nil n = nil.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. exact IHn.
Qed.

Lemma list_decomposition : forall l n, exists (suf : list Z), 
  l = (list_prefix l n) ++ suf.
Proof.
  intros l. induction l.
  - intros. exists nil. simpl. rewrite nil_prefix_nil. reflexivity.
  - intros. destruct n.
    + exists (a :: l). simpl. reflexivity.
    + specialize (IHl n). destruct IHl as [suf H].
      simpl list_prefix.
      exists suf. simpl.
      rewrite <- H.
      reflexivity. 
Qed.

Lemma list_cons_app : forall l1 x, exists (l2 : list Z) (a : Z), 
  x :: l1 = l2 ++ [a].
Proof.
  intros l1. induction l1; intros.
  - exists nil, x. reflexivity.
  - specialize (IHl1 a).
    destruct IHl1 as [l2 [b H]].
    rewrite H.
    exists (x :: l2), b.
    reflexivity.
Qed.

(* TODO: not sure whether useful *)
Lemma prefix_whole : forall l, 
  list_prefix l (length l) = l.
Proof.
  intros. induction l.
  - apply nil_prefix_nil.
  - simpl. rewrite IHl. reflexivity.
Qed.  

Lemma list_nth_nil : forall n, 
  list_nth nil n = (nil, None, nil).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. exact IHn.
Qed.

Lemma list_nth_prefix : forall l n l1 x l2, 
  list_nth l n = (l1, x, l2) -> 
  l1 = list_prefix l n.
Proof.
  intros l. induction l; intros.
  - rewrite nil_prefix_nil. 
    rewrite  list_nth_nil in H.
    inversion H; subst; reflexivity.
  - destruct n.
    + simpl in *. inversion H; subst; reflexivity.
    + simpl in *. 
      remember (list_nth l n) as res.
      destruct res as [[l3 y] l4].
      inversion H; subst.
      f_equal. 
      apply IHl with (x:=x) (l2:=l2).
      auto.
Qed.

Lemma list_nth_combine : forall (l l1 l2: list Z) (n : nat) (x : Z), 
  list_nth l n = (l1, Some x, l2) -> l1 ++ [x] ++ l2 = l.
Proof.
  intros l.
  induction l; intros.
  - rewrite list_nth_nil in H. inversion H.
  - destruct n.
    + simpl in H. inversion H; subst.
      reflexivity.
    + simpl in H.
      remember (list_nth l n) as res.
      destruct res as [[l3 y] l4].
      inversion H; subst.
      symmetry in Heqres.
      apply IHl in Heqres.
      simpl in *. rewrite Heqres.
      reflexivity.
Qed.

Definition list_single_out (l : list Z) (n : nat) (p : val) : mpred :=
  match list_nth l n with
  | (l1, None, l2)    => !! (p = nullval)
  | (l1, Some x, l2)    => 
    EX head1 : val, EX tail1 : val, 
    EX head2 : val, EX tail2 : val,
      list_1n_rep l1 head1 tail1 nullval * 
      node_rep x tail1 head2 p *
      list_1n_rep l2 head2 tail2 p
  end.

(***********************************************************************

Function specifications

***********************************************************************)

(* mallocN *)
Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [ 1%positive OF tint]
     PROP (4 <= n <= Int.max_unsigned)
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP (malloc_compatible n v)
     LOCAL (temp ret_temp v)
     SEP (memory_block Tsh n v).

(* freeN *)
Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () LOCAL () SEP ().

(* list_new *)
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

(* list_free *)
Definition list_free_spec :=
 DECLARE _list_free
  WITH p : val, l : list Z
  PRE  [ _l OF (tptr t_struct_list) ]
    PROP () 
    LOCAL (temp _l p) 
    SEP (list_rep l p)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (emp).

(* begin *)
(* TODO: bad definition *)
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
    LOCAL ()
    SEP (data_at Tsh t_struct_list
          (Vint (Int.repr (Z_length l)), (head, tail)) p; 
          list_single_out l 0%nat res).

(* end *)
Definition end_spec :=
 DECLARE _end
  WITH p : val, l : list Z
  PRE  [ _l OF (tptr t_struct_list) ]
    PROP () 
    LOCAL (temp _l p) 
    SEP (list_rep l p)
  POST [ tptr t_struct_node ]
    EX res : val, EX head : val, EX tail : val, 
    PROP ()
    LOCAL ()
    SEP (data_at Tsh t_struct_list
          (Vint (Int.repr (Z_length l)), (head, tail)) p; 
          list_single_out l ((length l) - 1)%nat res).

(* all functions of the program *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [
    mallocN_spec;           (* vacuous truth! *)
    freeN_spec;             (* vacuous truth! *)
    list_new_spec;          (* OK! *)
    list_free_spec;         (* OK! *)
    begin_spec;             (* OK! *)
    end_spec 
    (* rbegin_spec *)
    (* rend_spec *)
    (* get_size_spec *)
    (* push_back_spec *)
    (* pop_back_spec *)
    (* push_front_spec *)
    (* pop_front_spec *)
    (* move_spec *)
    (* insert_spec *)
    (* delete_spec *)
    (* merge_spec *)
    (* split_K_spec *)
  ]).

(***********************************************************************

Auxiliary tactics

***********************************************************************)

(* solve field_compatible _ [] nullval *)
Ltac sfcn :=
  match goal with
  | H : field_compatible _ [] nullval |- _  => destruct H; inversion H
  | _                                       => idtac
  end.

(* solve the subgoal generated by freeN *)
Ltac solve_free := 
  entailer!; rewrite memory_block_data_at_ by auto; cancel.

(***********************************************************************

Main proofs

***********************************************************************)

(* TODO: not sure whether useful *)
Lemma node_rep_saturate_local:
  forall x prev next p, node_rep x prev next p |-- !! is_pointer_or_null p.
Proof.
  intros. unfold node_rep. entailer!.
Qed.

Hint Resolve node_rep_saturate_local: saturate_local.

Lemma node_rep_valid_pointer:
  forall x prev next p, node_rep x prev next p |-- valid_pointer p.
Proof.
  intros. unfold node_rep. entailer!.
Qed.

Hint Resolve node_rep_valid_pointer: valid_pointer.

Lemma list_rep_saturate_local:
  forall l p, list_rep l p |-- !! is_pointer_or_null p.
Proof.
  intros. destruct l; unfold list_rep; simpl; Intros head tail; entailer!.
Qed.

Hint Resolve list_rep_saturate_local: saturate_local.

Lemma list_rep_valid_pointer:
  forall l p, list_rep l p |-- valid_pointer p.
Proof.
  intros. destruct l; unfold list_rep; simpl; Intros head tail; entailer!.
Qed.

Hint Resolve list_rep_valid_pointer: valid_pointer.

Lemma list_1n_rep_saturate_local_head:
  forall l head tail prev, list_1n_rep l head tail prev |-- 
    !! is_pointer_or_null head.
Proof.
  intros l. 
  destruct l; intros; simpl.
  - entailer!.
  - Intros old_head. entailer!.
Qed.

Hint Resolve list_1n_rep_saturate_local_head: saturate_local.

Lemma list_1n_rep_valid_pointer_head:
  forall l head tail prev, list_1n_rep l head tail prev |-- 
    valid_pointer head.
Proof.
  intros l. 
  destruct l; intros; simpl.
  - entailer!.
  - Intros old_head. entailer!.
Qed.
Hint Resolve list_1n_rep_valid_pointer_head: valid_pointer.

Lemma list_1n_rep_saturate_local_tail:
  forall l head tail prev, 
    is_pointer_or_null prev -> list_1n_rep l head tail prev |-- 
    !! is_pointer_or_null tail.
Proof.
  intros l. 
  induction l; intros; simpl.
  - entailer!.
  - Intros old_head. 
    assert_PROP (is_pointer_or_null head) by entailer!. 
    sep_apply (IHl old_head tail head H0). 
    entailer!.
Qed.

Hint Resolve list_1n_rep_saturate_local_tail: saturate_local.

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

(* proof for begin *)
Theorem body_begin: 
  semax_body Vprog Gprog f_begin begin_spec.
Proof.
  start_function. 
  unfold list_rep.
  Intros head tail.
  forward.
  forward.                              (* return l->head; *)
  unfold list_single_out.
  destruct (list_nth l 0) as [[l1 y] l2] eqn:E.
  destruct y.
  - destruct l.
    { (* show that l <> [] *)
      rewrite list_nth_nil in E.
      inversion E.
    }
    simpl in E; inversion E; subst.
    simpl list_1n_rep.
    Intros old_head.
    Exists head head tail nullval nullval old_head tail.
    entailer!.
  - Exists nullval head tail.
    destruct l; [| inversion E].
    simpl in E; inversion E; subst.
    simpl list_1n_rep.
    Intros; subst.
    entailer!.
Qed.

(* proof for end *)
(*
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
  destruct (list_nth l 0) as [[l1 y] l2] eqn:E.
  destruct y.
  - destruct l.
    { (* show that l <> [] *)
      rewrite list_nth_nil in E.
      inversion E.
    }
    pose proof (list_cons_app l z0).
    destruct H1 as [l3 [a H1]].
    rewrite H1.
    simpl in E; inversion E; subst.
    simpl list_1n_rep.
    Intros old_head.
    Exists tail head tail head tail old_head tail.
    entailer!.
  - Exists nullval head tail.
    destruct l; [| inversion E].
    simpl in E; inversion E; subst.
    simpl list_1n_rep.
    Intros; subst.
    entailer!.
Qed.
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
  { entailer!. }
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
