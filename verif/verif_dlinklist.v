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

Definition list_fst (l : list Z) : option Z := 
  match l with 
  | x :: l'   => Some x
  | nil       => None
  end.

Fixpoint list_lst (l : list Z) : option Z := 
  match l with 
  | nil       => None
  | x :: nil  => Some x
  | x :: l'   => list_lst l'
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

(* all functions of the program *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [
    mallocN_spec;           (* vacuous truth! *)
    freeN_spec;             (* vacuous truth! *)
    list_new_spec;          (* OK! *)
    list_free_spec          (* OK! *)
    (* begin_spec *)
    (* end_spec *)
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
