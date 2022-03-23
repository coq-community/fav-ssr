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

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.
Inductive and7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop :=
  And7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Inductive and8 (P1 P2 P3 P4 P5 P6 P7 P8 : Prop) : Prop :=
  And8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Inductive and9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Prop) : Prop :=
  And9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Inductive and10 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Prop) : Prop :=
  And10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.
Inductive and11 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 : Prop) : Prop :=
  And11 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11.
Inductive and12 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 : Prop) : Prop :=
  And12 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12.
Inductive and13 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 : Prop) : Prop :=
  And13 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13.
Inductive and14 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 : Prop) : Prop :=
  And14 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" := (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" := (and8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" := (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" := (and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 & P11 ]" :=
  (and11 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 & P12 ]" :=
  (and12 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 , P12 & P13 ]" :=
  (and13 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 , P12 , P13 & P14 ]" :=
  (and14 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14) : type_scope.

Section ReflectConnectives.
Variable b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : bool.

Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and7P : reflect [/\ b1, b2, b3, b4, b5, b6 & b7] [&& b1, b2, b3, b4, b5, b6 & b7].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and8P : reflect [/\ b1, b2, b3, b4, b5, b6, b7 & b8] [&& b1, b2, b3, b4, b5, b6, b7 & b8].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and9P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8 & b9] [&& b1, b2, b3, b4, b5, b6, b7, b8 & b9].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and10P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10] [&& b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and11P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 & b11]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 & b11].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and12P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 & b12]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 & b12].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
case: b12=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and13P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12 & b13]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12 & b13].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
case: b12=>/=; last by constructor; case.
case: b13=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and14P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13 & b14]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13 & b14].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
case: b12=>/=; last by constructor; case.
case: b13=>/=; last by constructor; case.
case: b14=>/=; last by constructor; case.
by constructor.
Qed.

End ReflectConnectives.

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

Lemma leq_ltn_add m1 m2 n1 n2 : m1 <= n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
Proof.
by move=>H1 H2; apply: (leq_ltn_trans (n:=n1 + m2)); rewrite ?ltn_add2l ?leq_add2r.
Qed.

Lemma maxn_eq0 m n : (maxn m n == 0) = (m == 0) && (n == 0).
Proof. by rewrite maxnE addn_eq0; case: m=>//=; rewrite subn0. Qed.

Lemma leq_max2l m n p : m <= n -> maxn p m <= maxn p n.
Proof. by move=>H; rewrite !maxnE leq_add2l; apply: leq_sub2r. Qed.

Lemma leq_max2r m n p : m <= n -> maxn m p <= maxn n p.
Proof. by move=>H; rewrite maxnC (maxnC n); apply: leq_max2l. Qed.

Lemma maxn_addl n m : maxn (n + m) n = n + m.
Proof. by apply/maxn_idPl/leq_addr. Qed.

Lemma maxn_addr n m : maxn n (n + m) = n + m.
Proof. by apply/maxn_idPr/leq_addr. Qed.

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

Lemma sorted_rconsE (xs : seq T) x :
  sorted leT (rcons xs x) = all (leT^~ x) xs && sorted leT xs.
Proof.
rewrite -(revK (rcons _ _)) rev_rcons rev_sorted /= path_sortedE; last first.
- by move=>a b c Hab /leT_tr; apply.
by rewrite all_rev rev_sorted.
Qed.

Corollary sorted_rcons (xs : seq T) x :
  sorted leT xs -> all (leT^~ x) xs -> sorted leT (rcons xs x).
Proof. by rewrite sorted_rconsE=>->->. Qed.

End Sorted.

Section Allrel.

Lemma perm_allrell {A B : eqType} r (s : seq A) (s1 s2 : seq B) :
  perm_eq s1 s2 -> allrel r s1 s = allrel r s2 s.
Proof. by move=>H; apply: perm_all. Qed.

Lemma perm_allrelr {A B : eqType} r (s : seq A) (s1 s2 : seq B) :
  perm_eq s1 s2 -> allrel r s s1 = allrel r s s2.
Proof. by move=>H; apply: eq_all=>z /=; apply: perm_all. Qed.

End Allrel.

Section Log.

Lemma trunc_up_log_ltn p n :
  1 < p -> trunc_log p n <= up_log p n <= trunc_log p n + 1.
Proof.
move=>Hp.
apply/andP; split.
- case: n; first by rewrite up_log0 trunc_log0.
  move=>n; rewrite -(@leq_exp2l p) //.
  by apply: (leq_trans (n:=n.+1)); [apply: trunc_logP | apply: up_logP].
by apply: up_log_min=>//; rewrite addn1; apply/ltnW/trunc_log_ltn.
Qed.

End Log.

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
apply: (leq_trans (n:=p %/ q)); last by apply: leq_addr.
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
