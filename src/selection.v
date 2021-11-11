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

Lemma true_impl P: (true -> P) -> P.
Proof. by apply. Qed.

Lemma subseq_consr (s1 s2 : seq T) a : 
  subseq s1 s2 -> subseq s1 (a :: s2).
Proof.
move => H.
have: s1 = [::] ++ s1. done.
have: a :: s2 = [::a] ++ s2. done.
move => -> ->.
apply cat_subseq.
  done.
by apply H.
Qed.

Lemma subset_filter_impl xs (p q : pred T) :
  (forall x, p x -> q x) ->
  subseq [seq x <- xs | p x] [seq x <- xs | q x].
Proof.
elim: xs => // a xs IH pi /=.
move: (pi a).
case pa: (p a).
  move => /true_impl -> /=.
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
move => H.
rewrite -(subnKC H) -addnA => H'.
rewrite (ltn_add2l a) ltn_addl //.
Qed.

Lemma kthOrd_unique k xs x y :
  k < size xs -> 
  kthOrd k xs x -> kthOrd k xs y -> x = y.
Proof.
case heq: (x == y); move: heq => /eqP; first done.
wlog: x y / x < y.
- case: (ltgtP x y) => Hcmp H neq hk xk yk.
  + by rewrite (H x y Hcmp _ hk xk yk).
  + rewrite (H y x Hcmp _ hk yk xk) //.
    move => Hcontra; by apply neq.
  done.
move => y_le_x _ ksz Hx Hy.
move: (Hx ksz) (Hy ksz) => /andP [H1 H2] /andP [H3 H4].
have G: subseq [seq x' <- xs | x' <= x] [seq x <- xs | x < y].
  apply subset_filter_impl => t tleqx.
  apply (le_lt_trans tleqx y_le_x).
move: (size_subseq G) => Gsz.
rewrite -(leq_add2r (size [seq x0 <- xs | x < x0])) in Gsz.
have Gszsx: size [seq x' <- xs | x' <= x] + size [seq x0 <- xs | x < x0] = size xs.
  apply filter_size_neg_pred.
  move => a. apply (leNgt a x).
  rewrite Gszsx in Gsz.
have t: size [seq x <- xs | x < y] + size [seq x0 <- xs | x < x0] < k + (size xs - k).
  apply leq_le_add.
  apply H3. apply H2.
have szeq: k + (size xs - k) = size xs.
  rewrite addnC subnK //.
  by apply (ltW ksz).
rewrite {}szeq in t.
have Contra: size xs < size xs.
  apply (@le_lt_trans _ _ _ (size xs) _ Gsz t).
rewrite ltxx in Contra.
done.
Qed.
