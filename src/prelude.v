From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path prime div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* inspect idiom so we can expand let-bound vars in proofs *)

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a erefl.

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

Lemma bool_eq_iff (a b : bool) : (a <-> b) <-> a == b.
Proof.
case: a; case: b=>//; split=>//.
- by case=>/(_ isT).
by case=>_ /(_ isT).
Qed.

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

Lemma half_lt n : 0 < n -> n./2 < n.
Proof.
case: n=>// n _; rewrite -(addn1 n) halfD andbT addn0 -uphalf_half addn1.
apply/leq_ltn_trans/ltnSn.
by exact: uphalf_le.
Qed.

Lemma half_uphalfK n : n = n./2 + uphalf n.
Proof. by rewrite uphalf_half addnCA addnn odd_double_half. Qed.

Lemma half_subn n : n - n./2 = uphalf n.
Proof. by rewrite {1}(half_uphalfK n) -addnBAC // subnn. Qed.

Lemma odd2 n : odd n = odd n.+2.
Proof. by rewrite -addn2 oddD addbF. Qed.

(* is this needed? *)
Lemma ltn_leq_trans y x z : x < y -> y <= z -> x < z.
Proof. by move=>Hx; apply/leq_trans. Qed.

Lemma leq_ltn_add m1 m2 n1 n2 : m1 <= n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
Proof.
by move=>H1 H2; apply: (leq_ltn_trans (n:=n1 + m2)); rewrite ?ltn_add2l ?leq_add2r.
Qed.

End Arith.

Section Size.

Lemma size1 {A} (xs : seq A) : size xs = 1 -> exists x, xs = [::x].
Proof. by case: xs=>// x; case=>//= _; exists x. Qed.

Lemma size2 {A} (xs : seq A) : 1 < size xs -> exists x y ys, xs = [:: x, y & ys].
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

Section TruncLog.

(* TODO added to Mathcomp in https://github.com/math-comp/math-comp/pull/823, should be available in 1.14 *)

Definition trunc_log' p n :=
  let fix loop n k :=
    if k is k'.+1 then if p <= n then (loop (n %/ p) k').+1 else 0 else 0
  in if p <= 1 then 0 else loop n n.

Lemma trunc_log0 p : trunc_log' p 0 = 0.
Proof. by case: p => [] // []. Qed.

Lemma trunc_log0n n : trunc_log' 0 n = 0.
Proof. by []. Qed.

Lemma trunc_log_bounds p n :
  1 < p -> 0 < n -> let k := trunc_log' p n in p ^ k <= n < p ^ k.+1.
Proof.
rewrite {+}/trunc_log' => p_gt1; have p_gt0 := ltnW p_gt1.
rewrite [p <= 1]leqNgt p_gt1 /=.
set loop := (loop in loop n n); set m := n; rewrite [in n in loop m n]/m.
have: m <= n by []; elim: n m => [|n IHn] [|m] //= /ltnSE-le_m_n _.
have [le_p_n | // ] := leqP p _; rewrite 2!expnSr -leq_divRL -?ltn_divLR //.
by apply: IHn; rewrite ?divn_gt0 // -ltnS (leq_trans (ltn_Pdiv _ _)).
Qed.

Lemma trunc_logP p n : 1 < p -> 0 < n -> p ^ trunc_log' p n <= n.
Proof. by move=> p_gt1 /(trunc_log_bounds p_gt1)/andP[]. Qed.

Lemma trunc_log_ltn p n : 1 < p -> n < p ^ (trunc_log' p n).+1.
Proof.
have [-> | n_gt0] := posnP n; first by rewrite trunc_log0 => /ltnW.
by case/trunc_log_bounds/(_ n_gt0)/andP.
Qed.

Lemma trunc_log_max p k j : 1 < p -> p ^ j <= k -> j <= trunc_log' p k.
Proof.
move=> p_gt1 le_pj_k; rewrite -ltnS -(@ltn_exp2l p) //.
exact: leq_ltn_trans (trunc_log_ltn _ _).
Qed.

Lemma leq_trunc_log p m n : m <= n -> trunc_log' p m <= trunc_log' p n.
Proof.
move=> mlen; case: p => [|[|p]]; rewrite ?trunc_log0n ?trunc_log1n //.
case: m mlen => [|m] mlen; first by rewrite trunc_log0.
apply/trunc_log_max => //; apply: leq_trans mlen; exact: trunc_logP.
Qed.

Lemma trunc_log_eq p n k : 1 < p -> p ^ n <= k < p ^ n.+1 -> trunc_log' p k = n.
Proof.
move=> p_gt1 /andP[npLk kLpn]; apply/anti_leq.
rewrite trunc_log_max// andbT -ltnS -(ltn_exp2l _ _ p_gt1).
apply: leq_ltn_trans kLpn; apply: trunc_logP => //.
by apply: leq_trans npLk; rewrite expn_gt0 ltnW.
Qed.

Lemma trunc_expnK p n : 1 < p -> trunc_log' p (p ^ n) = n.
Proof. by move=> ?; apply: trunc_log_eq; rewrite // leqnn ltn_exp2l /=. Qed.

Lemma trunc_logMp p n : 1 < p -> 0 < n ->
  trunc_log' p (p * n) = (trunc_log' p n).+1.
Proof.
case: p => [//|p] => p_gt0 n_gt0; apply: trunc_log_eq => //.
rewrite expnS leq_pmul2l// trunc_logP//=.
by rewrite expnS ltn_pmul2l// trunc_log_ltn.
Qed.

Lemma trunc_log2_double n : 0 < n -> trunc_log' 2 n.*2 = (trunc_log' 2 n).+1.
Proof. by move=> n_gt0; rewrite -mul2n trunc_logMp. Qed.

Lemma trunc_log2S n : 1 < n -> trunc_log' 2 n = (trunc_log' 2 n./2).+1.
Proof.
move=> n_gt1.
rewrite -trunc_log2_double ?half_gt0//.
rewrite -[n in LHS]odd_double_half.
case: odd => //; rewrite add1n.
apply: trunc_log_eq => //.
rewrite leqW ?trunc_logP //= ?double_gt0 ?half_gt0//.
rewrite trunc_log2_double ?half_gt0// expnS.
by rewrite -doubleS mul2n leq_double trunc_log_ltn.
Qed.

End TruncLog.

Section Log2.

(* ceiling of log_2, from https://github.com/thery/mathcomp-extra/blob/master/more_thm.v *)
(* TODO added to Mathcomp in https://github.com/math-comp/math-comp/pull/823, should be available in 1.14 *)
Definition log2n n :=
  let v := trunc_log' 2 n in if n <= 2 ^ v then v else v.+1.

Lemma up_log0 : log2n 0 = 0.
Proof. by []. Qed.

Lemma log2n_eq0 n : (log2n n == 0) = (n <= 1).
Proof.
case: n => [|[|n]]; rewrite /log2n //.
have /= := trunc_log_bounds (isT : 1 < 2) (isT : 0 < n.+2).
by case: (leqP _ n.+1).
Qed.

Lemma log2n_gt0 n : (0 < log2n n) = (1 < n).
Proof. by rewrite ltnNge leqn0 log2n_eq0 ltnNge. Qed.

Lemma log2n_bounds n :
  1 < n -> let k := log2n n in 2 ^ k.-1 < n <= 2 ^ k.
Proof.
move=> /= n_gt1.
have n_gt0 : 0 < n by apply: leq_trans n_gt1.
rewrite /log2n.
have /= /andP[t2Ln nLt2S] := trunc_log_bounds (isT : 1 < 2) n_gt0.
have [nLn2|n2Ln] := leqP n (2 ^ trunc_log' 2 n); last by rewrite n2Ln ltnW.
rewrite nLn2 (leq_trans _ t2Ln) // ltn_exp2l // prednK ?leqnn //.
by case: trunc_log' (leq_trans n_gt1 nLn2).
Qed.

Lemma log2n_geq n : n <= 2 ^ log2n n.
Proof.
by case: n => [|[|n]] //; have /andP[] := log2n_bounds (isT: 1 < n.+2).
Qed.

Lemma log2n_ltn n : 1 < n -> 2 ^ (log2n n).-1 < n.
Proof.
by case: n => [|[|n]] _ //; have /andP[] := log2n_bounds (isT: 1 < n.+2).
Qed.

Lemma log2n_exp k j : k <= 2 ^ j -> log2n k <= j.
Proof.
case: k => [|[|k]] // kLj.
rewrite -[log2n _]prednK ?log2n_gt0 // -(@ltn_exp2l 2) //.
by apply: leq_trans (log2n_ltn (isT : 1 < k.+2)) _.
Qed.

Lemma leq_log2n m n : m <= n -> log2n m <= log2n n.
Proof. by move=> mLn; apply/log2n_exp/(leq_trans _ (log2n_geq _)). Qed.

Lemma log2n_eq n k : 2 ^ n < k <= 2 ^ n.+1 -> log2n k = n.+1.
Proof.
case/andP=>n2Lk kL2n; apply/eqP; rewrite eqn_leq.
apply/andP; split; first by apply: log2n_exp.
rewrite -(ltn_exp2l _ _ (_ : 1 < 2)) //.
by apply: leq_trans n2Lk (log2n_geq k).
Qed.

Lemma exp2nK n : log2n (2 ^ n) = n.
Proof. by case: n=>//= n; apply: log2n_eq; rewrite leqnn andbT ltn_exp2l. Qed.

Lemma log2nS n : 1 <= n -> log2n n.+1 = (log2n (n./2.+1)).+1.
Proof.
case: n=> // [] [|n] // _.
apply/log2n_eq/andP; split.
- apply: leq_trans (_ : n./2.+1.*2 < n.+3); last first.
  by rewrite doubleS !ltnS -[X in _ <= X]odd_double_half leq_addl.
- have /= /andP[H1n _] := log2n_bounds (isT : 1 < n./2.+2).
  by rewrite ltnS -leq_double -mul2n -expnS prednK ?log2n_gt0 // in H1n.
rewrite -[_./2.+1]/(n./2.+2).
have /= /andP[_ H2n] := log2n_bounds (isT : 1 < n./2.+2).
rewrite -leq_double -!mul2n -expnS in H2n.
apply: leq_trans H2n.
rewrite mul2n !doubleS !ltnS.
by rewrite -[X in X <= _]odd_double_half -add1n leq_add2r; case: odd.
Qed.

Lemma trunc_up_log_ltn n :
  trunc_log' 2 n <= log2n n <= trunc_log' 2 n + 1.
Proof.
apply/andP; split.
- case: n; first by rewrite up_log0 trunc_log0.
  move=>n; rewrite -(@leq_exp2l 2) //.
  apply: (leq_trans (n:=n.+1)).
  - by apply: trunc_logP.
  by apply: log2n_geq.
apply: log2n_exp.
by rewrite addn1; apply/ltnW/trunc_log_ltn.
Qed.

End Log2.

Section UpDiv.

Definition up_div p q := (p %/ q) + ~~ (q %| p).

Lemma up_div0n d : up_div 0 d = 0.
Proof. by rewrite /up_div div0n dvdn0. Qed.

Lemma up_divn0 n : up_div n 0 = (n != 0).
Proof. by rewrite /up_div divn0 dvd0n. Qed.

Lemma up_div1n d : up_div 1 d = 1.
Proof. by rewrite /up_div dvdn1; case: d=>//; case. Qed.

Lemma up_divn1 n : up_div n 1 = n.
Proof. by rewrite /up_div divn1 dvd1n addn0. Qed.

Lemma up_div_gt0 p q : 0 < p -> 0 < up_div p q.
Proof.
move=>Hp; rewrite /up_div.
case/boolP: (p < q)%N => Hpq.
- by rewrite divn_small // gtnNdvd.
rewrite -leqNgt in Hpq.
have [->|Hq] := posnP q.
- by rewrite divn0 dvd0n -lt0n Hp.
apply: (ltn_leq_trans (y := p %/ q)); last by apply: leq_addr.
by rewrite divn_gt0.
Qed.

Lemma up_divS p q : up_div p.+1 q = (p %/ q).+1.
Proof.
have [->|Hq] := posnP q.
- by rewrite up_divn0 divn0.
rewrite /up_div divnS // addnAC -[in RHS]addn1 [in RHS]addnC.
by case: (q %| p.+1)%N.
Qed.

Corollary up_div_div p q : 0 < p -> up_div p q = (p.-1 %/ q).+1.
Proof. by case: p=>//=p _; apply: up_divS. Qed.

Corollary div_pred_up_div p q : p.-1 %/ q = (up_div p q).-1.
Proof.
case: p=>/=; first by rewrite div0n up_div0n.
by move=>n; rewrite up_divS.
Qed.

Lemma up_div_divDP p q : 0 < q -> up_div p q = (p + q.-1) %/ q.
Proof.
move=>Hq; have [->|] := posnP p.
- by rewrite up_div0n add0n divn_small // ltn_predL.
case: p=>// p _; rewrite up_divS //.
rewrite -(addn1 p) -subn1 -addnA addnBA // (addnC 1) addnK.
by rewrite divnD // divnn modnn Hq addn1 addn0 leqNgt ltn_pmod //= addn0.
Qed.

Lemma up_div_lt n m : 1 < m -> 1 < n -> up_div n m < n.
Proof.
move=>Hm; have H0: 0 < m by apply/ltn_trans/Hm.
case: n=>// n; rewrite ltnS=>Hn.
rewrite up_divS // ltnS.
by apply: ltn_Pdiv.
Qed.

Lemma leq_up_div2r d m n : m <= n -> up_div m d <= up_div n d.
Proof.
have [->|Hd Hmn] := posnP d.
- rewrite !up_divn0.
  by case: m=>//= m; case: n.
rewrite !up_div_divDP //; apply: leq_div2r.
by rewrite leq_add2r.
Qed.

Lemma leq_up_div n d : up_div n d * d <= n + d.
Proof.
rewrite /up_div mulnDl; apply: leq_add.
- by apply: leq_trunc_div.
by case: (d %| n)=>//=; rewrite mul1n.
Qed.

Lemma up_divnMl p m d : 0 < p -> up_div (p * m) (p * d) = up_div m d.
Proof. by move=>Hp; rewrite /up_div divnMl // dvdn_pmul2l. Qed.

Lemma up_divMA m n p : up_div (up_div m n) p = up_div m (n * p).
Proof.
have [->|Hp] := posnP p.
- rewrite muln0 !up_divn0; case: m=>/= [|m].
  - by rewrite up_div0n.
  by rewrite up_divS.
case: n=>[|n].
- rewrite up_divn0; case: m=>//= [|_].
  - by rewrite up_div0n.
  by rewrite up_div1n.
rewrite !up_div_divDP //=; last by rewrite muln_gt0.
rewrite divnMA; congr (_ %/ p).
rewrite !divnD // (divn_small (ltnSn n)) addn0 -!addnA; apply/eqP.
rewrite eqn_add2l divn_pred dvdn_mulr //= mulKn //.
rewrite subn1 addnC eqn_add2l.
case: n=>[|n]; first by rewrite mul1n !modn1.
rewrite modn_pred //=; last by rewrite muln_gt0.
by rewrite dvdn_mulr // (modn_small (ltnSn n.+1)).
Qed.

Lemma up_div_uphalf n : up_div n 2 = uphalf n.
Proof. by case: n=>//= n; rewrite up_divS // divn2. Qed.

End UpDiv.
