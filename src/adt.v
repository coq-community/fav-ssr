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
Record ASetM (disp : unit) (T : orderType disp): Type :=
  make {tp :> Type;
        empty : tp;
        insert : T -> tp -> tp;
        delete : T -> tp -> tp;
        isin : tp -> T -> bool;

        abs : tp -> seq T;
        invar : tp -> bool;

        _ : invar empty;
        _ : abs empty = [::];

        _ : forall x s, invar s -> invar (insert x s);
        _ : forall x s, invar s ->
              perm_eq (abs (insert x s))
                      (if x \in abs s then abs s else x :: abs s);

        _ : forall x s, invar s -> invar (delete x s);
        _ : forall x s, invar s ->
              perm_eq (abs (delete x s))
                      (filter (predC1 x) (abs s));

        _ : forall s, invar s -> isin s =i abs s
        }.
End ASetM.

Section Specification.
Context {disp : unit} {T : orderType disp}.

(* direct proofs for unbalanced trees work *)
Definition UASetM :=
  @ASetM.make _ _ (tree T)
    leaf insert delete isin
    inorder bst
    bst_empty inorder_empty
    bst_insert inorder_insert
    bst_delete inorder_delete
    inorder_isin.

(* sorted lists implement sets *)
Definition LASetM :=
  @ASetM.make _ _ (seq T)
    [::] ins_list del_list (fun xs s => s \in xs)
    id (sorted <%O)
    erefl erefl
    ins_list_sorted inorder_ins_list
    del_list_sorted inorder_del_list
    (fun x s H => erefl).

(* unbalanced trees via sorted lists implement sets *)
Definition ULASetM :=
  @ASetM.make _ _ (tree T)
    leaf insert delete isin
    inorder bst_list
    bst_list_empty erefl
    bst_list_insert inorder_insert_list_set
    bst_list_delete inorder_delete_list_set
    inorder_isin_list.

End Specification.

Module Map.
Record Map (disp : unit) (K : orderType disp) (V : Type) : Type :=
  make {tp :> Type;
        empty : tp;
        update : K -> V -> tp -> tp;
        delete : K -> tp -> tp;
        lookup : tp -> K -> option V;

        invar : tp -> bool;

        _ : invar empty;
        _ : forall k', lookup empty k' = None;

        _ : forall k v s, invar s -> invar (update k v s);
        _ : forall k v s k', invar s ->
            lookup (update k v s) k' = if k' == k then Some v else lookup s k';

        _ : forall k s, invar s -> invar (delete k s);
        _ : forall k s k', invar s ->
            lookup (delete k s) k' = if k' == k then None else lookup s k'
        }.
End Map.

(* Exercise 6.1 *)

Module ASetI.
Record ASetI (disp : unit) (T : orderType disp): Type :=
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
        Context {disp : unit} {K : orderType disp} {V : Type}.

        Notation kvtree := (tree (K*V)).

        (* FIXME *)

End MapUnbalanced.
