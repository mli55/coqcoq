Require Import VST.floyd.proofauto.
Require Import VST.floyd.Funspec_old_Notation.
Require Import DL.verif.dlinklist.
Require Import DL.verif.verif_dlinklist_def.
Require Import DL.verif.verif_dlinklist_proof1.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

(***********************************************************************
V.Main proofs
***********************************************************************)
Lemma list_1n_rep_valid_pointer_tail:  forall l a old_head head tail prev,     node_rep a prev old_head head * list_1n_rep l old_head tail head |--     valid_pointer tail.
Proof.  intros l.   induction l; intros; simpl.  - entailer!.  - Intros old_head0.    entailer!.
Qed. 
Hint Resolve list_1n_rep_valid_pointer_head: valid_pointer.

(* Definition push_back_spec :=
 DECLARE _push_back
  WITH p : val, l : list Z, v : Z
  PRE  [ _l OF (tptr t_struct_list), _v OF tuint ]
    PROP () 
    LOCAL (temp _l p; temp _v (Vint (Int.repr v))) 
    SEP (list_rep l p)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (list_rep (l ++ [v]) p). *)

Lemma list_1n_tail_nullval : forall l head prev,   l <> [] -> list_1n_rep l head nullval prev |-- !! False. 
Proof.  intros l.  induction l; intros.  - contradiction.  - simpl list_1n_rep.    destruct l.    + Intros old_head.      simpl list_1n_rep.      Intros. subst.      unfold node_rep.      entailer!; sfcn.    + assert (z :: l <> []) by (intro; discriminate).      Intros old_head.      specialize (IHl old_head head H0).      sep_apply IHl.      Intros. contradiction. Qed.



Theorem push_back: 
  semax_body Vprog Gprog f_push_back push_back_spec.
Proof.
start_function.
forward_call (sizeof t_struct_node).  (* mallocN *)
{ computable. }
Intros nd.     (* 新节点nd *)
rewrite memory_block_data_at_ by auto. 
forward.   (* nd->val = v; *)
forward. (* nd->next = NULL; *)
simpl.
Fail forward.
unfold list_rep. 
Intros oldhead oldtail.
forward.

(* 这个forward做了什么？ 拆开执行t'5=l->tail *)
(* 问题1：有一个证明local (liftx (is_pointer_or_null tail)) x，先跳过 *)
1:{  pose proof (list_1n_rep_saturate_local_tail l oldhead oldtail nullval
    mapsto_memory_block.is_pointer_or_null_nullval).
    sep_apply H0.
    entailer!.
}

1:{  
forward.  (* nd->prev = l->tail; *)
forward.
forward. (* l->size += 1; *)
forward.
(* apply semax_if_seq. *) 

forward_if.
(* {  destruct l; entailer.

  }   *)
(* 问题2： 有一个  denote_tc_test_eq tail (Vint (Int.repr 0))，先跳过 *)
{    pose proof (list_1n_rep_saturate_local_tail l oldhead oldtail nullval
    mapsto_memory_block.is_pointer_or_null_nullval).
    sep_apply H5.
    entailer!.
}

2:{ (* l->tail == NULL, 原列表为空情况 *) 
(* 问题3： 需要在Push完之后更新head/tail:已在程序中修改 *)
(* 问题4： _l->_tail == NULL如何推出 l = nil *)
forward. 
forward.
entailer.
unfold list_rep.
Exists nd nd.
entailer.
f_equal.
assert_PROP (l=nil).
{ entailer. 
(*  }
assert_PROP (oldhead=nullval).


3:{   
forward.  
 
Fail forward.
(* 问题5： l->tail！=null还是不能安全执行，要求SEP里面data_at有东西才行，这怎么办，看一下begin,end部分 *)
 }


  }
}
  *)
Abort.

Definition pop_back_spec :=
 DECLARE _pop_back
  WITH p : val, l : list Z, v : Z
  PRE  [ _l OF (tptr t_struct_list) ]
    PROP ( l <> nil) 
    LOCAL (temp _l p; temp _v (Vint (Int.repr v))) 
    SEP (list_rep (l ++ [v]) p)
  POST [ Tvoid ]
    PROP ()
    LOCAL ()
    SEP (list_rep l  p).
Theorem pop_back: 
  semax_body Vprog Gprog f_pop_back pop_back_spec.
Proof.
(* 1. 函数的输入参数只有 一个_l OF (tptr t_struct_list)
2. 空列表也要考虑，后条件不好写 *)
start_function.
