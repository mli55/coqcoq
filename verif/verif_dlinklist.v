Require Import VST.floyd.proofauto.
Require Import VST.floyd.Funspec_old_Notation.
Require Import DL.verif.dlinklist.
Require Import DL.verif.verif_dlinklist_def.
(* Require Import DL.verif.verif_dlinklist_proof1.
 *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

(***********************************************************************
V.Main proofs
***********************************************************************)
Lemma list_1n_rep_valid_pointer_tail:
  forall l a old_head head tail prev next, 
    node_rep a prev old_head head * list_1n_rep l old_head tail head next |-- 
    valid_pointer tail.
Proof.
  intros l. 
  induction l; intros; simpl.
  - entailer!.
  - Intros old_head0.
    entailer!.
Qed.

Hint Resolve list_1n_rep_valid_pointer_tail: valid_pointer.

Lemma list_1n_tail_nullval : forall l head prev,   l <> [] -> list_1n_rep l head nullval prev nullval |-- !! False. 
Proof.  
intros l.  
induction l; intros.  
- contradiction.  
- simpl list_1n_rep.    
  destruct l.
  + Intros old_head.      
  simpl list_1n_rep.
  Intros. subst.      
  unfold node_rep.      
  entailer!; sfcn.    
  + assert (z :: l <> []) by (intro; discriminate).      
  Intros old_head.
  specialize (IHl old_head head H0).
  sep_apply IHl.      
  (* entailer. *)
  Intros. contradiction. 
Qed.

Lemma list_1n_tail_nullval2: forall l head prev next,
list_1n_rep l  head nullval prev next |-- !!(l=[]).
Proof.
intros l.  
induction l; intros.
- entailer.
- simpl list_1n_rep.
destruct l.
+ Intros old_head.      
  simpl list_1n_rep.
  Intros. subst.      
  unfold node_rep.      
  entailer!; sfcn.
+ assert (z :: l <> []) by (intro; discriminate).      
  Intros old_head.
  specialize (IHl old_head head).
  sep_apply IHl.
  entailer.
Qed.
(* 不清楚原理，照着上面的写法莫名证出来 *)


Ltac unfold_list_rep := unfold list_rep, list_full_rep.

Definition push_back_spec :=
 DECLARE _push_back
  WITH head:val,tail:val ,p : val, l : list Z, v : Z
  PRE  [ _l OF (tptr t_struct_list), _v OF tuint ]
    PROP () 
    LOCAL (temp _l p; temp _v (Vint (Int.repr v))) 
    SEP (list_full_rep l head tail p)
  POST [ Tvoid ]
  EX  newtail:val,
    PROP ()
    LOCAL ()
    SEP (list_full_rep (l ++ [v]) (if list_empty l then newtail else head)
 newtail p). 
 
Print list_empty.

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

Lemma Z_length_prefix: forall l0 z,
 Z_length (list_prefix (z :: l0) (Datatypes.length l0)) = Z_length (l0).
Proof.
induction l0.
- simpl. reflexivity.
- intros z.  
assert (Datatypes.length (a :: l0) = S (Datatypes.length l0) ). 
{ simpl. reflexivity. }
pose proof Z_length_plus_1 as H0. 
specialize (H0 a l0) as H1.
rewrite <-H1.
rewrite H. simpl.
specialize (H0 z (list_prefix (a :: l0) (Datatypes.length l0))).
rewrite <-H0.
specialize (IHl0 a). 
rewrite IHl0. reflexivity.
Qed.

(* Print Datatypes.length.
Print list_prefix.
 *)
 

Theorem push_back: 
  semax_body Vprog Gprog f_push_back push_back_spec.
Proof.
start_function.
forward_call (sizeof t_struct_node). (* 1. mallocN *) 
   { computable. } 
Intros nd.    
rewrite memory_block_data_at_ by auto. 
forward.   (* nd->val = v; *)
forward. (* nd->next = NULL; *)
simpl.
unfold_list_rep.
Intros.
forward. (* nd->prev = l->tail; 这个forward 拆开执行t'5=l->tail *)
   { (* 证明指针合法性(可赋值) *)
   pose proof (list_1n_rep_saturate_local_tail l head tail    nullval nullval mapsto_memory_block.is_pointer_or_null_nullval ).
    sep_apply H0.
    entailer!. 
    }
forward.  (* nd->prev = l->tail; *)
forward.
forward. (* l->size += 1; *)
forward.
apply semax_if_seq. 
forward_if.
  { (* 证明tail合法性(可比较)，从l中拆出来 *)
    destruct l;simpl.
    - entailer!.
    - Intros oldhead0.
      pose proof list_1n_rep_valid_pointer_tail.
      specialize (H5 l z).
      sep_apply H5.
      entailer!.  
   }  
-  (* l->tail == NULL, 原列表为空情况 *) 
  forward. 
  forward.
  Exists nd.
  entailer.
  unfold_list_rep.
  assert_PROP (l=nil).
  { 
    pose proof list_1n_tail_nullval2 as HIS.
    specialize (HIS l head nullval).
    sep_apply HIS.
    entailer. 
  } 
  subst.
  unfold app. simpl.
  unfold node_rep.
  Exists nullval.
  entailer!.
- (* l->tail != NULL, 原列表不为空情况 *) 
  forward.
(* 证明指针非空，拆l出l->tail *)
  destruct l eqn:E. {simpl. Intros. contradiction. }
  pose proof (list_cons_app) as liscon.
  specialize (liscon  l0 z) as H1.
    destruct H1 as [l1 [a H1]].
    destruct H1 as [H1 [H2 H3]].
    rewrite H1.        (*  把前缀改为后缀，证明l->tail合法 *)
    sep_apply list_1n_split.
    Intros head' tail'. (* 后链表的head'和前链表的tail' *)
    simpl.
    Intros oldhead. (* 后链表[a]中a节点的后继，即nullval *)
    unfold node_rep.
    subst.
  (* l->tail的拆解到此结束 *)
  forward. simpl.
  forward.
  Exists nd.
  assert_PROP (list_empty (z::l0)=false) by  
    (unfold list_empty;   entailer!). 
  entailer!.
  rewrite H2.  (* 化简结论 *)
  (* 7.长度的证明 *)
  assert_PROP ((Z_length [a]) = 1) by  entailer!. 
  assert_PROP (Z_length (list_prefix (z :: l0) (Datatypes.length  l0) ++ [a])=Z_length (z::l0)). 
  { 
    entailer!. 
    specialize ( Z_length_plus (list_prefix (z :: l0)     (Datatypes.length l0)) [a]) as H12.
    rewrite <-H12.
    rewrite H10. simpl.
    pose proof Z_length_prefix l0 z. rewrite H11. 
    apply Z_length_plus_1. 
   }
  assert_PROP (Z_length ((z :: l0)++[v])=Z_length (z :: l0)+1) by
    (rewrite <- (Z_length_plus (z :: l0) [v]); entailer).
  rewrite H11.
  unfold list_full_rep.
  rewrite H12.
  entailer!. 
 (* 8.链表内存的证明:用node_in_list_rev引理*)
  rewrite H1 at 2.
  remember(list_prefix (z :: l0) (Datatypes.length l0)) as l5.
  pose proof node_in_list_rev as nlrev.
  specialize (nlrev l5 [v] a head nd head').
  pose proof app_assoc as assoc.
  specialize (assoc Z l5 [a] [v]).
  rewrite <- assoc.
  
  eapply derives_trans. (* 需要一个trans性质 *)
  2:{ sep_apply nlrev. entailer. }
  1:{
    unfold node_in_list.
    unfold node_rep.
    Exists tail' nd.
    entailer!.
    - unfold list_1n_rep. entailer!.
      Exists nullval. entailer!. 
    }
Qed.

Lemma Z_length_minus_1 : forall a l, Z_length (a :: l) - 1 = Z_length l.
Proof.
  intros.
  unfold Z_length.
  simpl length.
  lia.
Qed.



Lemma prefix_whole' : forall l l1,   list_prefix (l ++ l1) (length l) = l.
Proof.  intros. induction l; intros.  - simpl. reflexivity.   - simpl. rewrite IHl. reflexivity. 
Qed.



Definition pop_back_spec :=
 DECLARE _pop_back
  WITH p : val, l : list Z, head:val, tail:val
  PRE  [ _l OF (tptr t_struct_list) ]
    PROP ( l <> nil) 
    LOCAL (temp _l p) 
    SEP (list_full_rep l head tail p )
  POST [ Tvoid ]
  EX newtail:val,
    PROP ()
    LOCAL ()
    SEP (list_full_rep (list_prefix l ((length l) - 1)%nat )  
    (if list_empty (list_prefix l ((length l) - 1)%nat ) then nullval else head) newtail p).
Theorem pop_back: 
  semax_body Vprog Gprog f_pop_back pop_back_spec.
Proof.
start_function.
(* Fail forward. *)
unfold_list_rep.
Intros.
forward.
  {  (* 证明指针l->tail合法性(可赋值) *)
     pose proof (list_1n_rep_saturate_local_tail l head tail nullval
            nullval mapsto_memory_block.is_pointer_or_null_nullval ).
     sep_apply H0.
     entailer!.
  } 
(* Fail forward. *) 
   (* 证明指针tail非空，拆l出l->tail *)
    destruct l eqn:E.  {simpl. Intros. contradiction. } 
    pose proof (list_cons_app) as liscon.
    specialize (liscon  l0 z) as H1.
      destruct H1 as [l1 [a H1]].
      destruct H1 as [H1 [H2 H3]].
      rewrite H1 at 2. (*  把前缀改为后缀，证明l->tail合法 *)
      sep_apply list_1n_split.
      Intros head' tail'. (* 后链表的head'和前链表的tail' *)
      simpl.
      Intros oldhead. (* 后链表[a]中a节点的后继，即nullval *)
      unfold node_rep.
      subst.
    clear liscon.

forward. (* l->tail = tmp->prev，此处不可simpl*) 
{  (* 证明指针l->tail合法性(可赋值) *)
  pose proof (list_1n_rep_saturate_local_tail 
    (list_prefix (z:: l0) (Datatypes.length l0))  
    head tail' nullval head'   
    mapsto_memory_block.is_pointer_or_null_nullval ).
  sep_apply H0.
  entailer!.
}
forward.  (*  l->tail = tmp->prev; *)
forward_call (head', sizeof t_struct_node); [solve_free | ].
(* freeN(tmp, sizeof (struct node)); *)
forward. 
forward. (* l->size -= 1; *)
forward. (* l->tail == NULL *)
forward_if.
{   (* 证明指针l->tail合法性(可比较) *)
  destruct (list_prefix (z :: l0) (Datatypes.length l0)).
  - simpl. entailer!.
  - rewrite Z_length_minus_1.
    simpl. Intros oldhead0.
    pose proof list_1n_rep_valid_pointer_tail l z0 as H5.
    sep_apply H5.
    entailer!.
}
-  (* empty list *)
  forward. Exists nullval.
  entailer!. 
  assert_PROP (list_prefix (z :: l0) (Datatypes.length l0) =nil).
  { 
    pose proof list_1n_tail_nullval2 as HIS.
    specialize (HIS (list_prefix (z :: l0) (Datatypes.length l0))).
    specialize (HIS  head nullval).
    sep_apply HIS.
    entailer. 
  } 
  assert ((Datatypes.length (z::l0)) =S (Datatypes.length l0)) 
    by (simpl; reflexivity). 
  assert ( ( (Datatypes.length (z::l0))-1)%nat=Datatypes.length l0) 
    by lia. 
  rewrite H6. rewrite H0. 
  rewrite Z_length_minus_1.
  (* 长度化简完成 *)
  unfold list_full_rep. simpl. entailer!.
  (* 证明l0是空的，由前缀为空的条件discriminate *)
  destruct l0.
  + entailer!.
  + simpl in H0. discriminate. 
-  (*not empty list *)
  forward. (* _t=l->tail *)
    destruct (list_prefix (z::l0) (Datatypes.length l0))eqn:E.
       {simpl. Intros. contradiction. }
    pose proof (list_cons_app) as liscon.
    specialize (liscon  l z0) as H11.
      destruct H11 as [l1 [a1 H11]].
      destruct H11 as [H11 [H12 H13]].
      rewrite H11 . (*  把前缀改为后缀，证明l->tail合法 *)
      sep_apply list_1n_split.
      Intros head0' tail0'. (* 后链表的head'和前链表的tail' *)
      simpl.
      Intros oldhead. (* 后链表[a]中a节点的后继，即nullval *)
      unfold node_rep.
      subst.
  forward. (* l->tail->next = NULL; *)
(* 程序运行完成，证明结论 *)
  assert ((Datatypes.length (z::l0)) =S (Datatypes.length l0)) 
    by (simpl; reflexivity). 
  assert ( ( (Datatypes.length (z::l0))-1)%nat=Datatypes.length l0) 
    by lia. 
  rewrite H4.  
  assert_PROP(list_empty (list_prefix (z :: l0) (Datatypes.length l0))   
    =false ) by (entailer!; rewrite E; simpl; reflexivity).  
  rewrite H5.
  assert(z=z0) by  (inversion H1;lia). subst.

  Exists head0'.
  unfold list_full_rep.
  pose proof Z_length_prefix l0 z0.
  rewrite H6.
  entailer!.
  rewrite Z_length_minus_1.
  entailer!.
  rewrite H1.

  assert(l0=l++[a]) by (inversion H1;reflexivity) .
  rewrite H14.
    clear H14.
    clear H12.
    clear H10.
    clear H7 H8 H9.
    clear PNp PNhead' PNhead0'.
    clear H4 H2 H6 H5.
  pose proof prefix_whole' (z0::l).
  assert (Datatypes.length (l++[a])=Datatypes.length (z0::l)).
     { rewrite app_length. simpl. lia. }
  rewrite H4.
  rewrite H2.
  rewrite H11 at 2.
  remember (list_prefix (z0 :: l) (Datatypes.length l) ) as  l5 . 
  pose proof list_1n_merge l5 [a1].
  specialize (H5 head tail0' head0' head0' nullval nullval).
  eapply derives_trans.
  2: { apply H5. }
  1: { 
      entailer!.
      unfold list_1n_rep.
      Exists nullval.
      entailer!. 
      }
Qed.


    

    

