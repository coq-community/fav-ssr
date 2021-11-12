From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path order bigop.
From favssr Require Import prelude.

Section Basics.
Context {T : Type}.
Implicit Types (xs ys zs: seq T).

(* 1.4 Proofs *)

(* TODO: 1.4.1 gcd example *)

(* 1.5 Running time *)

Fixpoint T_app xs ys : nat :=
  if xs is _ :: xs' then (T_app xs' ys).+1 else 1.

(* Not a real rev implementation from lib *)
Fixpoint rev' xs :=
  if xs is x :: xs' then rev' xs' ++ [:: x] else [::].

Fixpoint T_rev xs : nat :=
  if xs is x :: xs' then T_rev xs' + T_app (rev' xs') [:: x] + 1 else 1.

Lemma T_app_cons x xs ys : T_app (x :: xs) ys = (T_app xs ys).+1.
Proof. by []. Qed.

Lemma T_app_complexity xs ys : T_app xs ys = (size xs).+1.
Proof.
elim: xs => [| x xs IH] //.
by rewrite T_app_cons IH.
Qed.

(* Exercise 1.5.1 formula for T_rev *)

Fixpoint T_catrev xs ys : nat :=
  if xs is x :: xs' then (T_catrev xs' (x :: ys)).+1 else 1.

Lemma catrev_rev_equality xs ys : catrev xs ys = rev' xs ++ ys.
Proof.
rewrite /catrev.
elim: xs ys => [| x xs IH] ys //=.
by rewrite IH -catA.
Qed.

End Basics.
