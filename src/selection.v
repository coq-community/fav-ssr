From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path order bigop.
From favssr Require Import prelude.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Selection.
Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys zs: seq T) (k : nat).

Definition kthOrd k xs v :=
  k < size xs ->
  (size [seq x <- xs | x < v ] <= k) &&
  (size [seq x <- xs | x > v ] <  size xs - k).

Definition selection (select : nat -> seq T -> T) := 
  forall k xs, kthOrd k xs (select k xs).

Lemma subseq_consr (s1 s2 : seq T) a : 
  subseq s1 s2 -> subseq s1 (a :: s2).
Proof.
rewrite -{2}[s1]/([::] ++ s1) -[a :: s2]/([::a] ++ s2).
by apply cat_subseq.
Qed.

Lemma subset_filter_impl xs (p q : pred T) :
  (forall x, p x -> q x) ->
  subseq [seq x <- xs | p x] [seq x <- xs | q x].
Proof.
elim: xs => // a xs IH pi /=.
move: (pi a).
case pa: (p a).
  move => -> //=.
  rewrite eq_refl.
  by apply (IH pi).
case qa: (q a) => _.
  apply subseq_consr. by apply (IH pi).
by apply (IH pi).
Qed.

Lemma filter_size_neg_pred p q xs :
  (forall a, p a = ~~ (q a)) ->
  size [seq x <- xs | p x] + size [seq x <- xs | q x ] = size xs.
Proof.
elim: xs => // a sx IH Hpq //=.
move: (Hpq a).
case (q a) => /= ->.
  by rewrite addnS IH.
by rewrite addSn IH.
Qed.

Lemma leq_le_add (a b x y: nat) : (a <= x -> b < y -> a + b < x + y)%N.
Proof.
move => /subnKC <-.
rewrite -addnA (ltn_add2l a) => b_le_y.
by rewrite ltn_addl.
Qed.

Lemma kthOrd_unique k xs x y :
  k < size xs -> 
  kthOrd k xs x -> 
  kthOrd k xs y -> 
  x = y.
Proof.
case heq: (x == y); move: heq => /eqP; first done.
wlog: x y / x < y.
- case: (ltgtP x y) => Hcmp H neq hk xk yk //.
  + by rewrite (H x y Hcmp _ hk xk yk).
  rewrite (H y x Hcmp _ hk yk xk) //.
  move => Hcontra; by apply neq.
move => y_le_x _ ksz Hx Hy.
move: (Hx ksz) (Hy ksz) => /andP [lex gtx] /andP [ley gty] {Hx Hy}.
have lex_subs_ley: subseq [seq x' <- xs | x' <= x] [seq x' <- xs | x' < y].
  apply subset_filter_impl => t tleqx.
  by apply (le_lt_trans tleqx y_le_x).
move: (size_subseq lex_subs_ley).
rewrite -(leq_add2r (size [seq x0 <- xs | x < x0])).
have sizexs_eq: size [seq x' <- xs | x' <= x] + size [seq x0 <- xs | x < x0] = size xs.
  apply filter_size_neg_pred.
  move => a. 
  by apply (leNgt a x).
rewrite sizexs_eq.
have sizexs_le: size [seq x <- xs | x < y] + size [seq x0 <- xs | x < x0] < k + (size xs - k).
  by apply leq_le_add; [apply ley | apply gtx].
have sizexs_le_eq: k + (size xs - k) = size xs.
  by rewrite addnC subnK //; apply (ltW ksz).
rewrite {}sizexs_le_eq in sizexs_le.
move => sizexs_leq.
have contra: size xs < size xs.
  by apply (@le_lt_trans _ _ _ (size xs) _ sizexs_leq sizexs_le).
by rewrite ltxx in contra.
Qed.

End Selection.
