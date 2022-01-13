From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq order.
From favssr Require Import bintree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Intro.
Context {disp : unit} {T : orderType disp}.

Fixpoint bst (t : tree T) : bool :=
  if t is Node l a r
    then [&& all (< a) (inorder l), all (> a) (inorder r), bst l & bst r]
    else true.

(* Exercise 5.1 *)

Fixpoint nodes {A} (t : tree A) : seq (tree A * A * tree A) := [::]. (* FIXME *)

Definition bst_nodes (t : tree T) : bool :=
  all (fun '(l,a,r) => true) (nodes t). (* FIXME *)

Lemma bst_bst_nodes t : bst t = bst_nodes t.
Proof.
Admitted.

End Intro.

Module ASet.
Context {disp : unit} {T : orderType disp}.

Record ASet : Type :=
  make {tp :> Type;
        empty : tp;
        insert : T -> tp -> tp;
        delete : T -> tp -> tp;
        isin : tp -> T -> bool}.

End ASet.

Section Unbalanced.
Context {disp : unit} {T : orderType disp}.

Variant cmp_val := LT | EQ | GT.

Definition cmp (x y : T) : cmp_val :=
  if x < y then LT else if x == y then EQ else GT.

Definition empty : tree T := @Leaf T.

Fixpoint isin (t : tree T) x : bool :=
  if t is Node l a r
    then match cmp x a with
           | LT => isin l x
           | EQ => true
           | GT => isin r x
         end
  else false.

Fixpoint insert x (t : tree T) : tree T :=
  if t is Node l a r
    then match cmp x a with
           | LT => Node (insert x l) a r
           | EQ => Node l a r
           | GT => Node l a (insert x r)
         end
  else Node (@Leaf T) x (@Leaf T).

Fixpoint split_min (z : T) (t : tree T) : T * tree T :=
  if t is Node l a r
    then if l is Leaf then (a, r)
      else let '(x, l') := split_min z l in
           (x, Node l' a r)
    else (z, @Leaf T).

Check split_min.

Fixpoint delete x (t : tree T) : tree T :=
  if t is Node l a r
    then match cmp x a with
           | LT => Node (delete x l) a r
           | EQ => if r is Leaf then l
                     else let '(a', r') := split_min a r in
                          Node l a' r'
           | GT => Node l a (delete x r)
         end
  else @Leaf T.

Equations join (t1 t2 : tree T) : tree T :=
join t              Leaf           => t;
join Leaf           t              => t;
join (Node l1 a r1) (Node l2 b r2) =>
  if join r1 l2 is Node l3 c r3
    then Node (Node l1 a l3) c (Node r3 b r2)
    else Node l1 a (Node (@Leaf T) b r2).

Lemma join_characteristic l r : inorder (join l r) = inorder l ++ inorder r.
Proof.
funelim (join l r); simp join=>//=; first by rewrite cats0.
case H2: (join r1 l2)=>/=[|l3 c r3]; rewrite {}H2 /= in H.
- by rewrite -catA cat_cons catA -H.
by rewrite -!catA cat_cons -(cat_cons c) catA H -!catA !cat_cons.
Qed.

Fixpoint delete2 x (t : tree T) : tree T :=
  if t is Node l a r
    then match cmp x a with
           | LT => Node (delete2 x l) a r
           | EQ => join l r
           | GT => Node l a (delete2 x r)
         end
  else @Leaf T.

Equations join0 (t1 t2 : tree T) : tree T :=
join0 t              Leaf           => t;
join0 Leaf           t              => t;
join0 (Node l1 a r1) (Node l2 b r2) => Node l1 a (Node (join0 r1 l2) b r2).

(* Exercise 5.2 *)

Lemma join_behaves l r : (height (join l r) <= maxn (height l) (height r) + 1)%N.
Proof.
Admitted.

Section Unbalanced.
