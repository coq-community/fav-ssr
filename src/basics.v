From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq div.
From favssr Require Import prelude.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Basics.
Context {T : Type}.
Implicit Types (xs ys zs: seq T).

(* 1.2.3 Multisets *)

(* We'll be using perm_eq instead of msets. *)

(* 1.4 Proofs *)

(* GCD is terminating as the second argument is decreasing *)
Equations? gcd' (m n : nat) : nat by wf n lt :=
gcd' m 0 => m;
gcd' m n => gcd' n (m %% n).
Proof. by apply/ssrnat.ltP/ltn_pmod. Qed.

Lemma gcd_ind P :
  (forall m n, (n != 0 -> P n (m %% n)) -> P m n) -> forall m n, P m n.
Proof.
move=>H m n; elim/ltn_ind: n m=>n IH m; apply: H.
by move=>Hn; apply/IH/ltn_pmod; rewrite lt0n.
Qed.

(* Equations generates a more detailed principle (uncomment to run): *)

(* Check gcd'_elim. *)

(***********************************************************)
(* gcd'_elim                                               *)
(*      : forall P : nat -> nat -> nat -> Type,            *)
(*          (forall m : nat, P m 0 m) ->                   *)
(*          (forall m n : nat,                             *)
(*           P n.+1 (m %% n.+1) (gcd' n.+1 (m %% n.+1)) -> *)
(*           P m n.+1 (gcd' n.+1 (m %% n.+1))) ->          *)
(*          forall m n : nat, P m n (gcd' m n)             *)
(***********************************************************)

(* 1.5 Running time *)

Fixpoint T_app xs ys : nat :=
  if xs is _ :: xs' then (T_app xs' ys).+1 else 1.

(* A simplified implementation compared to the lib *)
Fixpoint rev' xs :=
  if xs is x :: xs' then rcons (rev' xs') x else [::].

Lemma rev'_size xs : size (rev' xs) = size xs.
Proof. by elim: xs=>//=x xs IH; rewrite size_rcons IH. Qed.

Fixpoint T_rev xs : nat :=
  if xs is x :: xs' then (T_rev xs' + T_app (rev' xs') [:: x]).+1 else 1.

Lemma T_app_complexity xs ys : T_app xs ys = (size xs).+1.
Proof. by elim: xs=>//= x xs ->. Qed.

Lemma T_rev_bound xs : T_rev xs <= (size xs).+1 ^2.
Proof.
elim: xs=>//=x xs IH.
rewrite T_app_complexity rev'_size -[in _.+2]addn1
  sqrnD -(mulnn 1) !muln1 -addnA.
apply: leq_ltn_add=>//.
by rewrite addnC addn1 ltnS; apply: leq_addr.
Qed.

(* Exercise 1.5.1: exact complexity for T_rev *)
Lemma T_rev_complexity xs : T_rev xs = (size xs).+1 ^2. (* FIXME *)
Proof.
Admitted.

(* itrev is called catrev in the lib *)

Fixpoint T_catrev xs ys : nat :=
  if xs is x :: xs' then (T_catrev xs' (x :: ys)).+1 else 1.

Lemma T_catrev_complexity xs ys : T_catrev xs ys = (size xs).+1.
Proof. by elim: xs ys=>//=x xs IH ys; rewrite IH. Qed.

Lemma catrev_rev_eq xs ys : catrev xs ys = rev' xs ++ ys.
Proof.
elim: xs ys =>//= x xs IH ys.
by rewrite IH -cats1 -catA.
Qed.

End Basics.
