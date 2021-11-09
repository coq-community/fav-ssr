From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path prime.

(* inspect idiom so we can expand let-bound vars in proofs *)

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a erefl.

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

Section Arith.

Lemma uphalf_addn n m : uphalf n + uphalf m = odd n && odd m + uphalf (n + m).
Proof.
rewrite !uphalf_half halfD oddD.
by case: (odd n); case: (odd m)=>//=; rewrite addnCA.
Qed.

Lemma half_le n : (n./2 <= n)%N.
Proof.
elim: n=>//= n IH; rewrite uphalf_half -addn1 (addnC _ 1%N).
by apply: leq_add=>//; apply: leq_b1.
Qed.

Lemma uphalf_le n : (uphalf n <= n)%N.
Proof. by case: n=>//= n; rewrite ltnS; apply: half_le. Qed.

Lemma half_subn n : n - n./2 = uphalf n.
Proof.
have {1}-> : n = n./2 + uphalf n by rewrite uphalf_half addnCA addnn odd_double_half.
by rewrite -addnBAC // subnn.
Qed.

Lemma odd2 n : odd n = odd n.+2.
Proof. by rewrite -addn2 oddD addbF. Qed.

End Arith.

Section Size.

Lemma size1 {A} (xs : seq A) : size xs = 1%N -> {x : A | xs = [::x]}.
Proof. by case: xs=>// x; case=>//= _; exists x. Qed.

Lemma size2 {A} (xs : seq A) :
  (size xs > 1)%N -> {x : A & {y : A & {ys : seq A & xs = [:: x, y & ys]}}}.
Proof. by case: xs=>// x; case=>//= y ys _; exists x,y,ys. Qed.

End Size.

Section Sorted.

Variable (T : Type) (leT : rel T).
Hypothesis (leT_tr : transitive leT).

Lemma sorted_rcons (xs : seq T) x : sorted leT xs -> all (leT^~ x) xs -> sorted leT (rcons xs x).
Proof.
move=>Hs Ha.
rewrite -(revK (rcons _ _)) rev_rcons rev_sorted /= path_sortedE; last first.
- by move=>a b c Hab /leT_tr; apply.
by rewrite all_rev rev_sorted /=; apply/andP.
Qed.

End Sorted.
