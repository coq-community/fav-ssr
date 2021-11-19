From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path prime.

(* inspect idiom so we can expand let-bound vars in proofs *)

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a erefl.

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

Section Arith.

Lemma uphalf_addn n m :
  uphalf n + uphalf m = odd n && odd m + uphalf (n + m).
Proof.
rewrite !uphalf_half halfD oddD.
by case: (odd n); case: (odd m)=>//=; rewrite addnCA.
Qed.

Lemma half_le n : n./2 <= n.
Proof.
elim: n=>//= n IH; rewrite uphalf_half -addn1 (addnC _ 1).
by apply: leq_add=>//; apply: leq_b1.
Qed.

Lemma uphalf_le n : uphalf n <= n.
Proof. by case: n=>//= n; rewrite ltnS; apply: half_le. Qed.

Lemma half_subn n : n - n./2 = uphalf n.
Proof.
have {1}-> : n = n./2 + uphalf n
  by rewrite uphalf_half addnCA addnn odd_double_half.
by rewrite -addnBAC // subnn.
Qed.

Lemma odd2 n : odd n = odd n.+2.
Proof. by rewrite -addn2 oddD addbF. Qed.

Lemma ltn_leq_trans y x z : x < y -> y <= z -> x < z.
Proof.
rewrite !ltn_neqAle => /andP [nexy lexy leyz]; rewrite (leq_trans lexy) // andbT.
by apply: contraNneq nexy => eqxz; rewrite eqxz eqn_leq leyz andbT in lexy *.
Qed.

Lemma leq_ltn_add m1 m2 n1 n2 : m1 <= n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
Proof.
by move=>H1 H2; apply: (leq_ltn_trans (n:=n1 + m2)); rewrite ?ltn_add2l ?leq_add2r.
Qed.

Lemma ex_exp b k : 1 < b -> 0 < k -> {n | b^n <= k < b^n.+1}.
Proof.
move=>Hb; elim: k=>// k IH _.
case/boolP: (k==0).
- by move/eqP=>->; exists 0; rewrite expn1.
rewrite -lt0n => /IH [n Hn].
case/boolP: (k==(b^n.+1).-1).
- move/eqP=>->; exists n.+1; case/andP: Hn=>_ Hn.
  by rewrite (ltn_predK Hn); apply/andP; split=>//; rewrite ltn_exp2l.
move=>Hk; exists n.
case/andP: Hn=>Hn1 Hn2; apply/andP; split; first by apply: leqW.
by rewrite -ltn_predRL ltn_neqAle Hk /= -ltnS (ltn_predK Hn2).
Qed.

Lemma ex_exp2 b k : 1 < b -> 1 < k -> {n | b^n < k <= b^n.+1}.
Proof.
move=>Hb Hk; rewrite -ltn_predRL in Hk.
have H0 : 0 < k by rewrite lt0n; apply/negP=>/eqP; move: Hk=>/[swap]->.
case: (ex_exp b k.-1)=>// n /andP [H1 H2].
exists n; apply/andP; split.
- by apply: (leq_ltn_trans H1); rewrite ltn_predL.
by rewrite -ltnS -(prednK H0).
Qed.

End Arith.

Section Size.

Lemma size1 {A} (xs : seq A) : size xs = 1 -> {x : A | xs = [::x]}.
Proof. by case: xs=>// x; case=>//= _; exists x. Qed.

Lemma size2 {A} (xs : seq A) :
  1 < size xs -> {x : A & {y : A & {ys : seq A & xs = [:: x, y & ys]}}}.
Proof. by case: xs=>// x; case=>//= y ys _; exists x,y,ys. Qed.

End Size.

Section Sorted.

Variable (T : Type) (leT : rel T).
Hypothesis (leT_tr : transitive leT).

Lemma sorted_rcons (xs : seq T) x :
  sorted leT xs -> all (leT^~ x) xs -> sorted leT (rcons xs x).
Proof.
move=>Hs Ha.
rewrite -(revK (rcons _ _)) rev_rcons rev_sorted /= path_sortedE; last first.
- by move=>a b c Hab /leT_tr; apply.
by rewrite all_rev rev_sorted /=; apply/andP.
Qed.

End Sorted.

Section Log2.

(* ceiling of log_2, from https://github.com/thery/mathcomp-extra/blob/master/more_thm.v *)
Definition log2n n :=
  let v := trunc_log 2 n in if n <= 2 ^ v then v else v.+1.

Lemma log2n_eq0 n : (log2n n == 0) = (n <= 1).
Proof.
case: n => [|[|n]]; rewrite /log2n //.
have /= := trunc_log_bounds (isT : 1 < 2) (isT : 0 < n.+2).
by case: (leqP (2 ^ trunc_log 2 n.+2) n.+1).
Qed.

Lemma log2n_gt0 n : (0 < log2n n) = (1 < n).
Proof. by rewrite ltnNge leqn0 log2n_eq0 ltnNge. Qed.

Lemma log2n_bounds n :
  1 < n -> let k := log2n n in 2 ^ k.-1 < n <= 2 ^ k.
Proof.
move=> /= n_gt1.
have n_gt0 : 0 < n by apply: leq_trans n_gt1.
rewrite /log2n.
have /= := trunc_log_bounds (isT : 1 < 2) n_gt0.
case: (leqP n (2 ^ trunc_log 2 n)) => [] H1 /andP[H2 H3].
 rewrite H1 (leq_trans _ H2) // ltn_exp2l // prednK ?leqnn //.
 by case: trunc_log (leq_trans n_gt1 H1).
by rewrite H1 ltnW.
Qed.

Lemma log2nP n : n <= 2 ^ log2n n.
Proof.
case: n => [|[|n]] //.
by have /andP[] := log2n_bounds _ (isT: 1 < n.+2).
Qed.

Lemma log2n_ltn n : 1 < n -> 2 ^ (log2n n).-1 < n.
Proof.
case: n => [|[|n]] _ //.
by have /andP[] := log2n_bounds _ (isT: 1 < n.+2).
Qed.

Lemma log2n_max k j : k <= 2 ^ j -> log2n k <= j.
Proof.
case: k => [|[|k]] // kLj.
rewrite -[log2n _]prednK ?log2n_gt0 // -(@ltn_exp2l 2) //.
by apply: leq_trans (log2n_ltn _ (isT : 1 < k.+2)) _.
Qed.

Lemma leq_log2n m n : m <= n -> log2n m <= log2n n.
Proof. by move=> mLn; apply/log2n_max/(leq_trans _ (log2nP _)). Qed.

Lemma log2n_eq n k : 2^n < k <= 2^n.+1 -> log2n k = n.+1.
Proof.
case/andP=>H1 H2; apply/eqP; rewrite eqn_leq.
apply/andP; split; first by apply: log2n_max.
rewrite -(ltn_exp2l (m:=2)) //.
by move: (log2nP k); apply: ltn_leq_trans.
Qed.

Lemma exp2nK n : log2n (2 ^ n) = n.
Proof. by case: n=>//= n; apply: log2n_eq; rewrite leqnn andbT ltn_exp2l. Qed.

Lemma log2nS n : 1 <= n -> log2n n.+1 = (log2n (n./2.+1)).+1.
Proof.
case: n=>[|[|n _]] //=.
set n0 := n.+3; set m := (n0.-1)./2.+1.
case: (ex_exp2 2 m)=>// i Hi.
rewrite (log2n_eq (i.+1)); first by rewrite (log2n_eq i).
apply/andP; split.
- case/andP: Hi=>Hi1 _.
  rewrite expnS; apply: leq_ltn_trans.
  - by move: Hi1; rewrite /m ltnS -(leq_pmul2l (m:=2)); [apply | move=>//].
  rewrite mul2n -(ltn_add2l (odd (n0.-1))) odd_double_half.
  apply: ltn_addl; rewrite ltn_predL lt0n; apply/negP=>/eqP.
  by move: Hi1=>/[swap]; rewrite /m=>->/=; rewrite ltnS leqn0 expn_eq0.
apply: (leq_trans (n := 2*m)); last first.
- by rewrite expnS leq_mul2l /=; case/andP: Hi.
rewrite /n0 /m -(addn2 _./2) mulnDr mul2n -(leq_add2l (odd n))
  addnA odd_double_half addnC -addn3.
by case: (odd n)=>/=; rewrite -addnA // leq_add2l.
Qed.

End Log2.