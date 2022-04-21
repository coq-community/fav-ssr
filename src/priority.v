From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype order seq path.
From favssr Require Import prelude bintree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Module APQ.
Structure APQ (disp : unit) (T : orderType disp): Type :=
  make {tp :> Type;
        empty : tp;
        insert : T -> tp -> tp;
        del_min : tp -> tp;
        get_min : T -> tp -> T;

        mset : tp -> seq T;
        invar : tp -> bool;

        _ : invar empty;
        _ : mset empty = [::];

        _ : forall x s, invar s -> invar (insert x s);
        _ : forall x s, invar s ->
              perm_eq (mset (insert x s)) (x :: mset s);

        _ : forall s, invar s -> ~~ nilp (mset s) -> invar (del_min s);
        _ : forall x0 s, invar s -> ~~ nilp (mset s) ->
              perm_eq (mset (del_min s)) (rem (get_min x0 s) (mset s));

        (* we don't need non-emptiness here since we've made both sides total *)
        _ : forall s x0, invar s ->
              get_min x0 s = mins x0 (mset s)
        }.
End APQ.

Module APQM.
Structure APQ (disp : unit) (T : orderType disp): Type :=
  make {tp :> Type;
        empty : tp;
        insert : T -> tp -> tp;
        del_min : tp -> tp;
        get_min : T -> tp -> T;
        meld : tp -> tp -> tp;

        mset : tp -> seq T;
        invar : tp -> bool;

        _ : invar empty;
        _ : mset empty = [::];

        _ : forall x s, invar s -> invar (insert x s);
        _ : forall x s, invar s ->
              perm_eq (mset (insert x s)) (x :: mset s);

        _ : forall s, invar s -> ~~ nilp (mset s) -> invar (del_min s);
        _ : forall x0 s, invar s -> ~~ nilp (mset s) ->
              perm_eq (mset (del_min s)) (rem (get_min x0 s) (mset s));

        _ : forall s x0, invar s ->
              get_min x0 s = mins x0 (mset s);

        _ : forall s1 s2, invar s1 -> invar s2 -> invar (meld s1 s2);
        _ : forall s1 s2, invar s1 -> invar s2 ->
              perm_eq (mset (meld s1 s2)) (mset s1 ++ mset s2)

        }.
End APQM.

(* Exercise 14.1 *)
Section Exercise.
Context {disp : unit} {T : orderType disp}.

Definition empty_list : seq T := [::].

Fixpoint ins_list (x : T) (xs : seq T) : seq T := xs. (* FIXME *)

Definition del_min_list (xs : seq T) : seq T := xs. (* FIXME *)

Definition get_min_list (x0 : T) (xs : seq T) : T := x0. (* FIXME *)

Definition invar_list (t : seq T) : bool := true. (* FIXME *)

Definition merge_list (xs1 xs2 : seq T) : seq T := xs1. (* FIXME *)

(* PROVE PROPERTIES *)

Definition ListPQM :=
  @APQM.make _ _ (seq T)
  empty_list ins_list del_min_list get_min_list merge_list
  id invar_list
  (* use proved lemmas *)
  .

End Exercise.

Section Heaps.
Context {disp : unit} {T : orderType disp}.

Fixpoint heap (t : tree T) : bool :=
  if t is Node l m r
    then [&& all (>= m) (inorder l ++ inorder r), heap l & heap r]
    else true.

Definition mset_tree : tree T -> seq T := preorder.

Definition empty : tree T := leaf.

Definition get_min (x0 : T) (t : tree T) : T :=
  if t is Node _ x _
    then x else x0.

Fixpoint meld (t1 : tree T) :=
  if t1 is Node l1 a1 r1 then
    let fix meld_t1 t2 :=
      if t2 is Node l2 a2 r2 then
        if a1 <= a2 then Node l1 a1 (meld r1 t2) else Node l2 a2 (meld_t1 r2)
      else t1 in
    meld_t1
  else id.

Definition insert x t := meld (Node leaf x leaf) t.

Definition del_min (t : tree T) : tree T :=
  if t is Node l _ r then meld l r else leaf.

(* Exercise 14.2 *)

Lemma invar_empty : heap empty.
Proof. Admitted.

Lemma mset_empty : mset_tree empty = [::].
Proof. Admitted.

Lemma invar_meld t1 t2 : heap t1 -> heap t2 -> heap (meld t1 t2).
Proof.
Admitted.

Lemma mset_meld t1 t2 : heap t1 -> heap t2 ->
  perm_eq (mset_tree (meld t1 t2)) (mset_tree t1 ++ mset_tree t2).
Proof.
Admitted.

Corollary invar_insert_heap x t : heap t -> heap (insert x t).
Proof. by rewrite /insert=>H; apply: invar_meld. Qed.

Corollary mset_insert x t : heap t ->
  perm_eq (mset_tree (insert x t)) (x :: mset_tree t).
Proof. by rewrite /insert=>H; apply: perm_trans; first by apply: mset_meld. Qed.

Corollary invar_delmin_heap t : heap t -> ~~ nilp (mset_tree t) -> heap (del_min t).
Proof.
case: t=>//=l a r; case/and3P=>_ Hl Hr _.
by apply: invar_meld.
Qed.

Corollary mset_delmin_heap x0 t : heap t -> ~~ nilp (mset_tree t) ->
  perm_eq (mset_tree (del_min t)) (rem (get_min x0 t) (mset_tree t)).
Proof.
case: t=>//=l a r; case/and3P=>_ Hl Hr _; rewrite eq_refl.
by apply: mset_meld.
Qed.

Lemma mins_getmin_heap t x0 : heap t ->
  get_min x0 t = mins x0 (mset_tree t).
Admitted.

Definition HeapPQM :=
  @APQM.make _ _ (tree T)
    empty insert del_min get_min meld
    mset_tree heap
    invar_empty mset_empty
    invar_insert_heap mset_insert
    invar_delmin_heap mset_delmin_heap
    mins_getmin_heap
    invar_meld mset_meld.

End Heaps.
