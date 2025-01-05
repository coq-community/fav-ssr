From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype order seq path.
From favssr Require Import bintree bst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Module ASetM.
Structure ASetM (T : eqType): Type :=
  make {tp :> Type;
        empty : tp;
        insert : T -> tp -> tp;
        delete : T -> tp -> tp;
        isin : tp -> T -> bool;

        abs : tp -> pred T;
        invar : tp -> bool;

        _ : invar empty;
        _ : abs empty =i pred0;

        _ : forall x s, invar s -> invar (insert x s);
        _ : forall x s, invar s ->
              abs (insert x s) =i [predU1 x & abs s];

        _ : forall x s, invar s -> invar (delete x s);
        _ : forall x s, invar s ->
              abs (delete x s) =i [predD1 abs s & x];

        _ : forall s, invar s -> isin s =i abs s
        }.
End ASetM.

Section Specification.
Context {disp : Order.disp_t} {T : orderType disp}.

Corollary inorder_empty_pred : inorder (@Leaf T) =i pred0.
Proof. by []. Qed.

Corollary inorder_insert_pred x (t : tree T) :
  bst t ->
  inorder (insert x t) =i [predU1 x & inorder t].
Proof.
move=>H z; move/perm_mem: (inorder_insert x H)=>/(_ z)->.
rewrite inE; case: ifP=>//=.
by case: eqP=>//->->.
Qed.

Corollary inorder_delete_pred x (t : tree T) :
  bst t ->
  inorder (delete x t) =i [predD1 inorder t & x].
Proof.
move=>H z; move/perm_mem: (inorder_delete x H)=>/(_ z)->.
by rewrite mem_filter; rewrite !inE /=.
Qed.

(* direct proofs for unbalanced trees work *)
Definition UASetM :=
  @ASetM.make _ (tree T)
    leaf insert delete isin
    (pred_of_seq \o inorder) bst
    bst_empty inorder_empty_pred
    bst_insert inorder_insert_pred
    bst_delete inorder_delete_pred
    inorder_isin.

Corollary emp_pred0 : (@nil T) =i pred0.
Proof. by []. Qed.

Corollary inorder_ins_list_pred (x : T) xs :
  sorted <%O xs ->
  ins_list x xs =i [predU1 x & xs].
Proof.
move=>H z; move/perm_mem: (inorder_ins_list x H)=>/(_ z)->.
rewrite !inE /=; case: ifP=>//=.
by case: eqP=>//->->.
Qed.

Corollary inorder_del_list_pred (x : T) xs :
  sorted <%O xs ->
  del_list x xs =i [predD1 xs & x].
Proof.
move=>H z; move/perm_mem: (inorder_del_list x H)=>/(_ z)->.
by rewrite mem_filter; rewrite !inE /=.
Qed.

(* sorted lists implement sets *)
Definition LASetM :=
  @ASetM.make _ (seq T)
    [::] ins_list del_list (fun xs s => s \in xs)
    (pred_of_seq \o id) (sorted <%O)
    erefl emp_pred0
    ins_list_sorted inorder_ins_list_pred
    del_list_sorted inorder_del_list_pred
    (fun _ _ _ => erefl).

Corollary bst_list_empty : bst_list (@Leaf T).
Proof. by []. Qed.

Corollary bst_list_insert x (t : tree T) :
  bst_list t -> bst_list (insert x t).
Proof.
move=>H; rewrite /bst_list inorder_insert_list //.
by apply: ins_list_sorted.
Qed.

Corollary inorder_insert_list_set x (t : tree T) :
  bst_list t ->
  inorder (insert x t) =i [predU1 x & inorder t].
Proof.
rewrite /bst_list => Hn.
rewrite inorder_insert_list //.
by apply: inorder_ins_list_pred.
Qed.

Corollary bst_list_delete x (t : tree T) :
  bst_list t -> bst_list (delete x t).
Proof.
move=>H; rewrite /bst_list inorder_delete_list //.
by apply: del_list_sorted.
Qed.

Corollary inorder_delete_list_set x (t : tree T) :
  bst_list t ->
  inorder (delete x t) =i [predD1 inorder t & x].
Proof.
rewrite /bst_list => Hn.
rewrite inorder_delete_list //.
by apply: inorder_del_list_pred.
Qed.

(* unbalanced trees via sorted lists implement sets *)
Definition ULASetM :=
  @ASetM.make _ (tree T)
    leaf insert delete isin
    (pred_of_seq \o inorder) bst_list
    bst_list_empty inorder_empty_pred
    bst_list_insert inorder_insert_list_set
    bst_list_delete inorder_delete_list_set
    inorder_isin_list.

End Specification.

Module Map.
Structure Map (K : eqType) (V : Type) : Type :=
  make {tp :> Type;
        empty : tp;
        update : K -> V -> tp -> tp;
        delete : K -> tp -> tp;
        lookup : tp -> K -> option V;

        invar : tp -> bool;

        _ : invar empty;
        _ : lookup empty =1 fun => None;

        _ : forall k v s, invar s -> invar (update k v s);
        _ : forall k v s, invar s ->
            lookup (update k v s) =1 [eta (lookup s) with k |-> Some v];

        _ : forall k s, invar s -> invar (delete k s);
        _ : forall k s, invar s ->
            lookup (delete k s) =1 [eta (lookup s) with k |-> None]
        }.
End Map.

(* Exercise 6.1 *)

Module ASetI.
Structure ASetI (T : eqType): Type :=
  make {tp :> Type;
        empty : tp;
        insert : T -> tp -> tp;
        delete : T -> tp -> tp;
        isin : tp -> T -> bool;

        (* FIXME *)

        }.
End ASetI.

(* Exercise 6.3 *)

Section MapUnbalanced.
Context {disp : Order.disp_t} {K : orderType disp} {V : Type}.

Notation kvtree := (tree (K*V)).

(* FIXME *)

End MapUnbalanced.
