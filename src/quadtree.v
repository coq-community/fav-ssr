From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype choice ssrnat div bigop ssrAC seq ssralg.
From favssr Require Import prelude.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RegionQuadtreesGen.
Context {A : Type}.

Inductive qtree A := L of A | Q of qtree A & qtree A & qtree A & qtree A.

Fixpoint height (t : qtree A) : nat :=
  match t with
  | L _ => 0
  | Q t0 t1 t2 t3 => (maxn (maxn (maxn (height t0) (height t1)) (height t2)) (height t3)).+1 (* TODO bigop? *)
  end.

Definition select {T} (x y : bool) (a b c d : T) : T :=
  if x then
     if y then a else b
   else
     if y then c else d.

Fixpoint get (n : nat) (t : qtree A) (i j : nat) (a0 : A) : A :=
  match t, n with
  | L a, _ => a
  | Q t0 t1 t2 t3, 0 => a0
  | Q t0 t1 t2 t3, n'.+1 =>
    get n' (select (i < 2 ^ n') (j < 2 ^ n') t0 t1 t2 t3)
           (i %% (2 ^ n')) (j %% (2 ^ n')) a0
  end.

Lemma get_L n a i j a0 : get n (L a) i j a0 = a.
Proof. by case: n. Qed.

End RegionQuadtreesGen.

Section RegionQuadtrees.
Context {A : eqType}.

Definition same_leaf (t1 t2 : qtree A) : bool :=
  match t1, t2 with
  | L a1, L a2 => a1 == a2
  | _, _ => false
  end.

Fixpoint compressed (t : qtree A) : bool :=
  match t with
  | L _ => true
  | Q t0 t1 t2 t3 => [&& compressed t0, compressed t1, compressed t2 & compressed t3] &&
                     ~~ [&& same_leaf t0 t1, same_leaf t0 t2 & same_leaf t0 t3]
  end.

Definition Qc (t0 t1 t2 t3 : qtree A) : qtree A :=
  match t0, t1, t2, t3 with
  | L x0, L x1, L x2, L x3 =>
    if [&& x0 == x1, x1 == x2 & x2 == x3] then L x0 else Q t0 t1 t2 t3
  | _, _, _, _ => Q t0 t1 t2 t3
  end.
(* can be written as: *)
(* if [&& same_leaf t0 t1, same_leaf t0 t2 & same_leaf t0 t3] then t0 else Q t0 t1 t2 t3 *)

Arguments Qc : simpl never.

Lemma compressed_Qc t0 t1 t2 t3 :
  compressed t0 -> compressed t1 -> compressed t2 -> compressed t3 ->
  compressed (Qc t0 t1 t2 t3).
Proof.
case: t0 => [x0 _|t00 t01 t02 t03] /=; last by case/andP=>->->->->->.
case: t1 => [x1 _|t10 t11 t12 t13] /=; last by case/andP=>->->->->.
case: t2 => [x2 _|t20 t21 t22 t23] /=; last by case/andP=>->->->/=; rewrite andbF.
case: t3 => [x3 _|t30 t31 t32 t33] /=; last by case/andP=>->->/=; rewrite !andbF.
rewrite /Qc; case: ifP=>//= /negbT.
by rewrite !negb_and; case: eqP=>//=->; case: eqP=>//=->.
Qed.

Lemma get_Qc n t0 t1 t2 t3 i j a0 :
     height (Q t0 t1 t2 t3) <= n
  -> get n (Qc t0 t1 t2 t3) i j a0 = get n (Q t0 t1 t2 t3) i j a0.
Proof.
case: n=>//= n; rewrite ltnS.
case: t0 => [x0|t00 t01 t02 t03] //=; rewrite max0n.
case: t1 => [x1|t10 t11 t12 t13] //=; rewrite max0n.
case: t2 => [x2|t20 t21 t22 t23] //=; rewrite max0n.
case: t3 => [x3|t30 t31 t32 t33] //= _.
rewrite /Qc; case: ifP=>//; case/and3P=>/eqP->/eqP->/eqP->.
by case: ltnP=>_; case: ltnP=>_ /=; case: n.
Qed.

Lemma compressedQD t0 t1 t2 t3 :
     compressed (Q t0 t1 t2 t3)
  -> [&& compressed t0, compressed t1, compressed t2 & compressed t3].
Proof. by case/andP. Qed.

Lemma height_Qc_Q n t0 t1 t2 t3 :
     height t0 <= n -> height t1 <= n -> height t2 <= n -> height t3 <= n
  -> height (Qc t0 t1 t2 t3) <= n.+1.
Proof.
case: t0 => /= [x0 H0|t00 t01 t02 t03]; case: t1 => /= [x1 H1|t10 t11 t12 t13];
case: t2 => /= [x2 H2|t20 t21 t22 t23]; case: t3 => /= [x3 H3|t30 t31 t32 t33]; rewrite ?max0n ?maxn0 ?maxnSS ?ltnS //.
- by rewrite /Qc; case: ifP.
- by move=>Ha Hb; rewrite gtn_max Ha.
- by move=>_ Ha; rewrite gtn_max H2.
- by move=>Ha _; rewrite gtn_max H3.
- by move=>Ha Hb Hc; rewrite gtn_max Hc andbT gtn_max Ha.
- by move=>_ Ha; rewrite gtn_max H1.
- by move=>Ha _; rewrite gtn_max H1.
- by move=>_ Ha Hb; rewrite gtn_max Hb andbT gtn_max H1.
- by move=>_ _; rewrite gtn_max H2.
- by move=>Ha _ Hb; rewrite gtn_max Hb andbT gtn_max H2.
- by move=>Ha Hb _; rewrite gtn_max Hb andbT gtn_max H3.
by move=>Ha Hb Hc Hd; rewrite gtn_max Hd andbT gtn_max Hc andbT gtn_max Ha.
Qed.

(* TODO is it useful? *)
Definition sq (n : nat) : rel nat :=
  [rel x y | (x < 2 ^ n) && (y < 2 ^ n)].

Definition modify (f : qtree A -> qtree A) (x y : bool) (t0 t1 t2 t3 : qtree A) : qtree A :=
  if x then
    if y then Qc (f t0) t1 t2 t3 else Qc t0 (f t1) t2 t3
  else
    if y then Qc t0 t1 (f t2) t3 else Qc t0 t1 t2 (f t3).

Fixpoint put (i j : nat) (a : A) (n : nat) (t : qtree A) : qtree A :=
  match n, t with
  | 0, _ => L a
  | n'.+1, L b =>
    modify (put (i %% (2 ^ n')) (j %% (2 ^ n')) a n')
           (i < 2 ^ n') (j < 2 ^ n')
           (L b) (L b) (L b) (L b)
  | n'.+1, Q t0 t1 t2 t3 =>
    modify (put (i %% (2 ^ n')) (j %% (2 ^ n')) a n')
           (i < 2 ^ n') (j < 2 ^ n')
           t0 t1 t2 t3
  end.

Lemma height_put i j a n t :
  height t <= n -> height (put i j a n t) <= n.
Proof.
elim: n=>//= n IH in i j t *; case: t=>[b _|t0 t1 t2 t3] /=.
- by case: ltnP=>Hi; case: ltnP=>Hj /=; apply: height_Qc_Q=>//; apply: IH.
rewrite !gtn_max !ltnS -!andbA; case/and4P=>H1 H2 H3 H4.
by case: ltnP=>Hi; case: ltnP=>Hj /=; apply: height_Qc_Q=>//=; apply: IH.
Qed.

Lemma compressed_put i j a n t :
     height t <= n -> compressed t
  -> compressed (put i j a n t).
Proof.
elim: n => //= n IH in i j t *; case: t=>[b _ _|t0 t1 t2 t3] /=.
- by case: ltnP=>Hi; case: ltnP=>Hj /=; apply: compressed_Qc=>//=; apply: IH.
rewrite !gtn_max !ltnS -!andbA; case/and4P=>H1 H2 H3 H4; case/and4P=>Hc1 Hc2 Hc3; case/andP=>Hc4 H.
by case: ltnP=>Hi; case: ltnP=>Hj /=; apply: compressed_Qc=>//=; apply: IH.
Qed.

(* TODO find a better formulation? *)
Lemma get_put n t i j i' j' a0 :
     height t <= n -> sq n i j -> sq n i' j'
  -> get n (put i j a0 n t) i' j' a0 = if (i' == i) && (j' == j) then a0 else get n t i' j' a0.
Proof.
elim: n=>[|n IH] in i j i' j' t *.
- move=>_; rewrite /sq /= expn0 !ltnS !leqn0.
  by do 2!case/andP=>/eqP->/eqP->.
move=>Hn; rewrite /sq; case/andP=>Hi Hj; case/andP=>Hi' Hj'; move: Hn.
case: t=>[b _|t0 t1 t2 t3].
- (* 16 combinations *)
  rewrite [get]lock /=; case: ltnP=>Hi0; case: ltnP=>Hj0 /=; unlock;
    rewrite get_Qc /= ?maxn0 ?max0n; try by apply: height_put.
  - rewrite modn_small // modn_small //.
    case: ltnP=>Hi0'; case: ltnP=>Hj0' /=.
    - rewrite !modn_small // IH //; try by apply/andP.
      by case: ifP=>// _; apply: get_L.
    - rewrite get_L; case: ifP=>//.
      by case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt Hj0.
    - rewrite get_L; case: ifP=>//.
      by case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt Hi0.
    rewrite get_L; case: ifP=>//.
    by case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt Hi0.
  - rewrite modn_small // mod_minus; last by rewrite Hj0 /= -mul2n -expnS.
    case: ltnP=>Hi0'; case: ltnP=>Hj0' /=.
    - rewrite get_L; case: ifP=>//.
      by case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt ltnS Hj0.
    - rewrite modn_small // mod_minus; last by rewrite Hj0' /= -mul2n -expnS.
      rewrite IH //; try by apply/andP; split=>//; rewrite ltn_subLR // addnn -muln2 -expnSr.
      by rewrite eqn_sub2rE //; case: ifP=>// _; apply: get_L.
    - rewrite get_L; case: ifP=>//.
      by case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt ltnS Hj0.
    rewrite get_L; case: ifP=>//.
    by case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt Hi0.
  - rewrite mod_minus; last by rewrite Hi0 /= -mul2n -expnS.
    rewrite modn_small //.
    case: ltnP=>Hi0'; case: ltnP=>Hj0' /=.
    - rewrite get_L; case: ifP=>//.
      by case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt ltnS Hi0.
    - rewrite get_L; case: ifP=>//.
      by case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt Hj0.
    - rewrite mod_minus; last by rewrite Hi0' /= -mul2n -expnS.
      rewrite modn_small // IH //; try by apply/andP; split=>//; rewrite ltn_subLR // addnn -muln2 -expnSr.
      by rewrite eqn_sub2rE //; case: ifP=>// _; apply: get_L.
    rewrite get_L; case: ifP=>//.
    by case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt Hj0.
  rewrite mod_minus; last by rewrite Hi0 /= -mul2n -expnS.
  rewrite mod_minus; last by rewrite Hj0 /= -mul2n -expnS.
  case: ltnP=>Hi0'; case: ltnP=>Hj0' /=.
  - rewrite get_L; case: ifP=>//.
    by case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt ltnS Hi0.
  - rewrite get_L; case: ifP=>//.
    by case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt ltnS Hi0.
  - rewrite get_L; case: ifP=>//.
    by case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt ltnS Hj0.
  rewrite mod_minus; last by rewrite Hi0' /= -mul2n -expnS.
  rewrite mod_minus; last by rewrite Hj0' /= -mul2n -expnS.
  rewrite IH //; try by apply/andP; split=>//; rewrite ltn_subLR // addnn -muln2 -expnSr.
  by rewrite !eqn_sub2rE //; case: ifP=>// _; apply: get_L.
rewrite [get]lock /= !gtn_max !ltnS -!andbA; case/and4P=>HH0 HH1 HH2 HH3.
(* another 16 combinations *)
case: ltnP=>Hi0; case: ltnP=>Hj0 /=; unlock;
  rewrite get_Qc /= ?gtn_max ?ltnS -?andbA; try by apply/and4P; split=>//; apply: height_put.
- rewrite modn_small // modn_small //.
  case: ltnP=>Hi0'; case: ltnP=>Hj0' /=.
  - by rewrite !modn_small // IH //; apply/andP.
  - by case: ifP=>//; case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt Hj0.
  - by case: ifP=>//; case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt Hi0.
  by case: ifP=>//; case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt Hi0.
- rewrite modn_small // mod_minus; last by rewrite Hj0 /= -mul2n -expnS.
  case: ltnP=>Hi0'; case: ltnP=>Hj0' /=.
  - by case: ifP=>//; case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt ltnS Hj0.
  - rewrite modn_small // mod_minus; last by rewrite Hj0' /= -mul2n -expnS.
    rewrite IH //; try by apply/andP; split=>//; rewrite ltn_subLR // addnn -muln2 -expnSr.
    by rewrite eqn_sub2rE.
  - by case: ifP=>//; case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt ltnS Hj0.
  by case: ifP=>//; case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt Hi0.
- rewrite mod_minus; last by rewrite Hi0 /= -mul2n -expnS.
  rewrite modn_small //.
  case: ltnP=>Hi0'; case: ltnP=>Hj0' /=.
  - by case: ifP=>//; case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt ltnS Hi0.
  - by case: ifP=>//; case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt Hj0.
  - rewrite mod_minus; last by rewrite Hi0' /= -mul2n -expnS.
    rewrite modn_small // IH //; try by apply/andP; split=>//; rewrite ltn_subLR // addnn -muln2 -expnSr.
    by rewrite eqn_sub2rE.
  by case: ifP=>//; case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt Hj0.
rewrite mod_minus; last by rewrite Hi0 /= -mul2n -expnS.
rewrite mod_minus; last by rewrite Hj0 /= -mul2n -expnS.
case: ltnP=>Hi0'; case: ltnP=>Hj0' /=.
- by case: ifP=>//; case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt ltnS Hi0.
- by case: ifP=>//; case/andP=>/eqP Ei _; move: Hi0'; rewrite Ei leqNgt ltnS Hi0.
- by case: ifP=>//; case/andP=>_ /eqP Ej; move: Hj0'; rewrite Ej leqNgt ltnS Hj0.
rewrite mod_minus; last by rewrite Hi0' /= -mul2n -expnS.
rewrite mod_minus; last by rewrite Hj0' /= -mul2n -expnS.
rewrite IH //; try by apply/andP; split=>//; rewrite ltn_subLR // addnn -muln2 -expnSr.
by rewrite !eqn_sub2rE.
Qed.

End RegionQuadtrees.

Section BooleanQuadtrees.

Definition qtb := qtree bool.

Fixpoint inter (t1 t2 : qtb) : qtb :=
  match t1 with
  | L b1 => if b1 then t2 else L false
  | Q s1 s2 s3 s4 =>
    match t2 with
    | L b2 => if b2 then t1 else L false
    | Q t1 t2 t3 t4 => Qc (inter s1 t1) (inter s2 t2) (inter s3 t3) (inter s4 t4)
    end
  end.

Lemma height_inter t1 t2 : height (inter t1 t2) <= maxn (height t1) (height t2).
Proof.
elim: t1 t2=>[b1|t10 IH0 t11 IH1 t12 IH2 t13 IH3][b2|t20 t21 t22 t23] /=.
- by case: b1.
- by rewrite max0n; case: b1.
- by rewrite maxn0; case: b2.
rewrite maxnSS; apply: height_Qc_Q.
- apply: leq_trans; first by exact: IH0.
  by rewrite [X in _<=X](AC (4*4)%AC ((1*5)*(2*3*4*6*7*8))%AC) /=; apply: leq_maxl.
- apply: leq_trans; first by exact: IH1.
  by rewrite [X in _<=X](AC (4*4)%AC ((2*6)*(1*3*4*5*7*8))%AC) /=; apply: leq_maxl.
- apply: leq_trans; first by exact: IH2.
  by rewrite [X in _<=X](AC (4*4)%AC ((3*7)*(1*2*4*5*6*8))%AC) /=; apply: leq_maxl.
apply: leq_trans; first by exact: IH3.
by rewrite [X in _<=X](AC (4*4)%AC ((4*8)*(1*2*3*5*6*7))%AC) /=; apply: leq_maxl.
Qed.

Lemma get_inter t1 t2 n i j a0 :
     height t1 <= n -> height t2 <= n
  -> get n (inter t1 t2) i j a0 = get n t1 i j a0 && get n t2 i j a0.
Proof.
elim: t1 t2 n i j=>[b1|t10 IH0 t11 IH1 t12 IH2 t13 IH3][b2|t20 t21 t22 t23] /= n i j.
- by move=>_ _; case: b1; rewrite !get_L.
- by move=>_ H; case: b1; rewrite !get_L.
- by move=>H _; case: b2; rewrite !get_L ?andbT ?andbF.
rewrite !gtn_max -!andbA; case/and4P=>H10 H11 H12 H13; case/and4P=>H20 H21 H22 H23.
rewrite get_Qc /=; last first.
- by rewrite !gtn_max -!andbA; apply/and4P; split; apply: leq_ltn_trans;
    (try by exact: height_inter); rewrite gtn_max ?H10 ?H11 ?H12 ?H13.
case: n H10 H11 H12 H13 H20 H21 H22 H23=>//= n.
rewrite !ltnS=>H10 H11 H12 H13 H20 H21 H22 H23.
by case: ltnP=>Hi; case: ltnP=>Hj /=; [rewrite IH0 | rewrite IH1 | rewrite IH2 | rewrite IH3].
Qed.

Lemma compressed_inter t1 t2 :
     compressed t1 -> compressed t2
  -> compressed (inter t1 t2).
Proof.
elim: t1 t2=>[b1|t10 IH0 t11 IH1 t12 IH2 t13 IH3][b2|t20 t21 t22 t23] /=.
- by move=>_ _; case: b1.
- by move=>_ H; case: b1.
- by move=>H _; case: b2.
case/andP=>/and4P [H10 H11 H12 H13] _; case/andP=>/and4P [H20 H21 H22 H23] _.
by apply: compressed_Qc; [apply: IH0 | apply: IH1 | apply: IH2 | apply: IH3].
Qed.

(* Exercise 13.1 *)

Fixpoint union (t1 t2 : qtb) : qtb := t1. (* FIXME *)

Lemma height_union t1 t2 : height (union t1 t2) <= maxn (height t1) (height t2).
Proof.
Admitted.

Lemma get_union t1 t2 n i j a0 :
     maxn (height t1) (height t2) <= n
  -> get n (union t1 t2) i j a0 = get n t1 i j a0 || get n t2 i j a0.
Proof.
Admitted.

Lemma compressed_union t1 t2 :
     compressed t1 -> compressed t2
  -> compressed (union t1 t2).
Proof.
Admitted.

(* this might get in handy *)
Fixpoint negate (t : qtb) : qtb := t. (* FIXME *)

Fixpoint diff (t1 t2 : qtb) : qtb := t1. (* FIXME *)

Lemma height_diff t1 t2 : height (diff t1 t2) <= maxn (height t1) (height t2).
Proof.
Admitted.

Lemma get_diff t1 t2 n i j a0 :
     maxn (height t1) (height t2) <= n
  -> get n (diff t1 t2) i j a0 = get n t1 i j a0 && ~~ get n t2 i j a0.
Proof.
Admitted.

Lemma compressed_diff t1 t2 :
     compressed t1 -> compressed t2
  -> compressed (diff t1 t2).
Proof.
Admitted.

End BooleanQuadtrees.

Section RegionQuadtreesMisc.
Context {A : eqType}.

Definition Qf (q : qtree A -> qtree A -> qtree A -> qtree A -> qtree A)
              (f : nat -> nat -> qtree A) (i j d : nat) : qtree A :=
  q (f i j) (f i (j+d)) (f (i+d) j) (f (i+d) (j+d)).

Equations? get_sq (n : nat) (t : qtree A) (m : nat) (a0 : A) (i j : nat) : qtree A by wf (n + m) lt :=
get_sq n     (L b)           m      a0 i j => L b;
get_sq n      t              0      a0 i j => L (get n t i j a0);
get_sq 0      t              m'.+1  a0 i j => t;
get_sq n'.+1 (Q t0 t1 t2 t3) m'.+1  a0 i j =>
  if (i %% 2 ^ n' + 2 ^ (m'.+1) <= 2 ^ n') && (j %% 2 ^ n' + 2 ^ (m'.+1) <= 2 ^ n')
  then get_sq n' (select (i < 2 ^ n') (j < 2 ^ n') t0 t1 t2 t3) (m'.+1) a0 (i %% 2 ^ n') (j %% 2 ^ n')
  else Qf Qc (fun x y => get_sq (n'.+1) (Q t0 t1 t2 t3) m' a0 x y) i j (2 ^ m').
Proof. by apply: ssrnat.ltP; rewrite ltn_add2l. Qed.

Lemma height_get_sq n t m a0 i j :
  m <= n -> height (get_sq n t m a0 i j) <= m.
Proof.
funelim (get_sq n t m a0 i j); simp get_sq=>//=.
rewrite ltnS=>Hmn; case: ifP; last first.
- by move=>_; apply: height_Qc_Q; apply: H0=>//=; apply: leqW.
case/andP=>Hi Hj; apply: H.
move: Hmn; rewrite leq_eqVlt=>/orP[/eqP E|H] //.
exfalso; move: Hi; rewrite E; apply: negP;
  rewrite -ltnNge expnSr muln2 -addnn addnA -[X in X<_]add0n ltn_add2r addn_gt0.
by apply/orP; right; rewrite expn_gt0.
Qed.

Lemma get_get_sq n t m a0 i j i' j' :
     height t <= n
  -> i + 2 ^ m <= 2 ^ n -> j + 2 ^ m <= 2 ^ n
  -> i' < 2 ^ m -> j' < 2 ^ m  (* TODO sq? *)
  -> get m (get_sq n t m a0 i j) i' j' a0 = get n t (i+i') (j+j') a0.
Proof.
funelim (get_sq n t m a0 i j); simp get_sq=>//.
- by move=>_ _ _ _ _; unlock; rewrite !get_L.
- by unlock; rewrite expn0 !addn1 !ltnS !leqn0=>_ _ _ /eqP {i'}-> /eqP {j'}->; rewrite !addn0.
rewrite [get]lock /= ltnS !geq_max -!andbA; case/and4P=>H1 H2 H3 H4 Hi Hj Hi' Hj'; case: ifP.
- case/andP=>Ha Hb; unlock; rewrite H //=; last by case: ltnP=>Hi0; case: ltnP=>Hj0.
  rewrite !modnD; try by rewrite expn_gt0.
  have Hi'' : i' < 2 ^ n' by apply: (leq_trans Hi'); apply/leq_trans/Ha; exact: leq_addl.
  have Hj'' : j' < 2 ^ n' by apply: (leq_trans Hj'); apply/leq_trans/Hb; exact: leq_addl.
  rewrite (modn_small (m := i')) // (modn_small (m := j')) //.
  have Hi''' : i %% 2 ^ n' + i' < 2 ^ n' by apply/leq_trans/Ha; rewrite ltn_add2l.
  have Hj''' : j %% 2 ^ n' + j' < 2 ^ n' by apply/leq_trans/Hb; rewrite ltn_add2l.
  rewrite !(leqNgt (2 ^ n')) Hi''' Hj''' /= mul0n !subn0.
  case: ltnP=>Hi0 /=.
  - move: Hi'''; rewrite modn_small // =>-> /=.
    case: ltnP=>Hj0 /=.
    - by move: Hj'''; rewrite modn_small // =>-> /=.
    suff: 2 ^ n' <= j + j' by rewrite ltnNge=>->.
    by apply: (leq_trans Hj0); apply: leq_addr.
  rewrite (ltnNge (i + i')); have ->/=: 2 ^ n' <= i + i' by apply: (leq_trans Hi0); apply: leq_addr.
  case: ltnP=>Hj0 /=.
  - by move: Hj'''; rewrite modn_small // =>-> /=.
  suff: 2 ^ n' <= j + j' by rewrite ltnNge=>->.
  by apply: (leq_trans Hj0); apply: leq_addr.
move/negbT; rewrite negb_and -!ltnNge => H'.
unlock; rewrite /Qf get_Qc; last first.
- have Hmn: m' <= n'.+1.
  - apply: leq_trans; first by exact: leqnSn.
    by rewrite -(leq_exp2l (m:=2)) //; apply/leq_trans/Hi; apply: leq_addl.
  by rewrite /= ltnS !geq_max -!andbA; apply/and4P; split; apply: height_get_sq.
rewrite /=; case: ltnP=>Hi0'; case: ltnP=>Hj0' /=.
- rewrite modn_small // modn_small //; apply: H0=>//=.
  - by rewrite ltnS !geq_max -!andbA; apply/and4P; split.
  - by apply/leq_trans/Hi; rewrite leq_add2l expnS mul2n -addnn; exact: leq_addl.
  by apply/leq_trans/Hj; rewrite leq_add2l expnS mul2n -addnn; exact: leq_addl.
- rewrite modn_small // mod_minus; last by rewrite Hj0' /= -mul2n -expnS.
  rewrite (H0 i (j + 2 ^ m')) //=.
  - suff: j + 2 ^ m' + (j' - 2 ^ m') = j + j' by move=>->.
    by rewrite addnBA // addnAC addnK.
  - by rewrite ltnS !geq_max -!andbA; apply/and4P; split.
  - by apply/leq_trans/Hi; rewrite leq_add2l expnS mul2n -addnn; exact: leq_addl.
  - by apply/leq_trans/Hj; rewrite -addnA leq_add2l addnn -mul2n -expnS.
  by rewrite ltn_subLR // addnn -mul2n -expnS.
- rewrite mod_minus; last by rewrite Hi0' /= -mul2n -expnS.
  rewrite modn_small //.
  rewrite (H0 (i + 2 ^ m') j) //=.
  - suff: i + 2 ^ m' + (i' - 2 ^ m') = i + i' by move=>->.
    by rewrite addnBA // addnAC addnK.
  - by rewrite ltnS !geq_max -!andbA; apply/and4P; split.
  - by apply/leq_trans/Hi; rewrite -addnA leq_add2l addnn -mul2n -expnS.
  - by apply/leq_trans/Hj; rewrite leq_add2l expnS mul2n -addnn; exact: leq_addl.
  by rewrite ltn_subLR // addnn -mul2n -expnS.
rewrite mod_minus; last by rewrite Hi0' /= -mul2n -expnS.
rewrite mod_minus; last by rewrite Hj0' /= -mul2n -expnS.
rewrite (H0 (i + 2 ^ m') (j + 2 ^ m')) //=.
- have ->: i + 2 ^ m' + (i' - 2 ^ m') = i + i' by rewrite addnBA // addnAC addnK.
  suff: j + 2 ^ m' + (j' - 2 ^ m') = j + j' by move=>->.
  by rewrite addnBA // addnAC addnK.
- by rewrite ltnS !geq_max -!andbA; apply/and4P; split.
- by apply/leq_trans/Hi; rewrite -addnA leq_add2l addnn -mul2n -expnS.
- by apply/leq_trans/Hj; rewrite -addnA leq_add2l addnn -mul2n -expnS.
- by rewrite ltn_subLR // addnn -mul2n -expnS.
by rewrite ltn_subLR // addnn -mul2n -expnS.
Qed.

Lemma compressed_get_sq n t m a0 i j :
     height t <= n -> compressed t
  -> compressed (get_sq n t m a0 i j).
Proof.
funelim (get_sq n t m a0 i j); simp get_sq=>//=.
rewrite ltnS !geq_max -!andbA; case/and4P=>H1 H2 H3 H4.
case/and5P=>[H10 H11 H12 H13 N]; case: ifP.
- by case/andP => Hi Hj; apply: H; case: ltnP=>Hi0; case: ltnP=>Hj0.
move/negbT; rewrite negb_and -!ltnNge=>H'.
by rewrite /Qf; apply: compressed_Qc; apply: H0=>//=; (try by rewrite ltnS !geq_max -!andbA; apply/and4P);
  apply/andP; split=>//; apply/and4P.
Qed.

Definition mx A := seq (seq A).

Definition sq_mx (n : nat) (m : mx A) : bool :=
  (size m == 2 ^ n) && all (fun l => size l == 2 ^ n) m.

Definition Qmx (mx0 mx1 mx2 mx3 : mx A) : mx A :=
  map2 cat mx0 mx1 ++ map2 cat mx2 mx3.

Fixpoint mx_of (t : qtree A) (n : nat) : mx A :=
  match t with
  | L x => nseq (2 ^ n) (nseq (2 ^ n) x)
  | Q t0 t1 t2 t3 =>
    match n with
    | 0 => [::]
    | n'.+1 => Qmx (mx_of t0 n') (mx_of t1 n') (mx_of t2 n') (mx_of t3 n')
    end
  end.

Lemma nth_Qmx_select (mx0 mx1 mx2 mx3 : mx A) n i j a0 :
     sq_mx n mx0 -> sq_mx n mx1 -> sq_mx n mx2 -> sq_mx n mx3
  -> i < 2 ^ n.+1 -> j < 2 ^ n.+1 (* TODO sq? *)
  -> nth a0 (nth [::] (Qmx mx0 mx1 mx2 mx3) i) j = nth a0 (nth [::] (select (i < 2^n) (j < 2^n) mx0 mx1 mx2 mx3) (i %% 2^n)) (j %% 2^n).
Proof.
case/andP=>/eqP H00 H01; case/andP=>/eqP H10 H11; case/andP=>/eqP H20 H21; case/andP=>/eqP H30 H31 Hi Hj.
rewrite /Qmx nth_cat size_map2 H00 H10 minnn.
case: ltnP=>Hi' /=.
- rewrite modn_small // (@nth_map _ ([::],[::])); last first.
  - by rewrite size_zip H00 H10 minnn.
  rewrite nth_zip; last by rewrite H00.
  rewrite nth_cat.
  have->: size (nth [::] mx0 i) = 2 ^ n.
  - by apply/eqP; move/allP: H01; apply; apply: mem_nth; rewrite H00.
  case: ltnP=>Hj'; first by rewrite modn_small.
  by rewrite mod_minus // Hj' /= -mul2n -expnS.
rewrite mod_minus; last by rewrite Hi' /= -mul2n -expnS.
rewrite (@nth_map _ ([::],[::])); last first.
- by rewrite size_zip H20 H30 minnn ltn_subLR // addnn -mul2n -expnS.
rewrite nth_zip; last by rewrite H20.
rewrite nth_cat.
have->: size (nth [::] mx2 (i - 2 ^ n)) = 2 ^ n.
- apply/eqP; move/allP: H21; apply; apply: mem_nth; rewrite H20.
  by rewrite ltn_subLR // addnn -mul2n -expnS.
case: ltnP=>Hj'; first by rewrite modn_small.
by rewrite mod_minus // Hj' /= -mul2n -expnS.
Qed.

Lemma sq_mx_mx_of n t :
  height t <= n -> sq_mx n (mx_of t n).
Proof.
elim: t n=>[x|t0 IH0 t1 IH1 t2 IH2 t3 IH3] n /=.
- move=>_; apply/andP; split; first by rewrite size_nseq.
  apply/allP=>l; rewrite mem_nseq; case/andP=>_ /eqP->.
  by rewrite size_nseq.
rewrite !gtn_max -!andbA; case/and4P; case: n=>// n.
rewrite !ltnS => /IH0 /andP {IH0}[/eqP H00 H01] /IH1 /andP {IH1}[/eqP H10 H11]
  /IH2 /andP {IH2}[/eqP H20 H21] /IH3 /andP {IH3}[/eqP H30 H31].
rewrite /Qmx; apply/andP; split.
- by rewrite size_cat !size_map2 H00 H10 H20 H30 minnn addnn -mul2n -expnS.
rewrite all_cat; apply/andP; split.
- rewrite all_map; apply/allP; case=>l1 l2 /= /in_zip [H1 H2]; rewrite size_cat.
  move/allP: H01 =>/(_ _ H1)/eqP->; move/allP: H11 =>/(_ _ H2)/eqP->.
  by rewrite addnn -mul2n -expnS.
rewrite all_map; apply/allP; case=>l1 l2 /= /in_zip [H1 H2]; rewrite size_cat.
move/allP: H21 =>/(_ _ H1)/eqP->; move/allP: H31 =>/(_ _ H2)/eqP->.
by rewrite addnn -mul2n -expnS.
Qed.

Lemma mx_of_get n t i j a0 :
     height t <= n
  -> i < 2 ^ n -> j < 2 ^ n (* TODO sq? *)
  -> nth a0 (nth [::] (mx_of t n) i) j = get n t i j a0.
Proof.
elim: t n i j=>[x|t0 IH0 t1 IH1 t2 IH2 t3 IH3] n i j /=.
- by move=>_ Hi Hj; rewrite nth_nseq Hi nth_nseq Hj get_L.
case: n=>// n; rewrite ltnS !geq_max -!andbA; case/and4P=>H0 H1 H2 H3 Hi Hj /=.
rewrite (nth_Qmx_select (n:=n)) //; try by apply: sq_mx_mx_of.
case: ltnP=>Hi'; case: ltnP=>Hj' /=.
- by rewrite modn_small // modn_small //; apply: IH0.
- rewrite modn_small // mod_minus; last by rewrite Hj' /= -mul2n -expnS.
  by rewrite IH1 // ltn_subLR // addnn -mul2n -expnS.
- rewrite mod_minus; last by rewrite Hi' /= -mul2n -expnS.
  by rewrite modn_small // IH2 // ltn_subLR // addnn -mul2n -expnS.
rewrite mod_minus; last by rewrite Hi' /= -mul2n -expnS.
rewrite mod_minus; last by rewrite Hj' /= -mul2n -expnS.
by rewrite IH3 // ltn_subLR // addnn -mul2n -expnS.
Qed.

Definition decomp (n : nat) (m : mx A) : mx A * mx A * mx A * mx A :=
  let mx01 := take (2 ^ n) m in
  let mx23 := drop (2 ^ n) m in
  (map (take (2 ^ n)) mx01, map (drop (2 ^ n)) mx01, map (take (2 ^ n)) mx23, map (drop (2 ^ n)) mx23).

Fixpoint qt_of (n: nat) (m : mx A) (a0 : A) : qtree A :=
  match n with
  | 0 => L (nth a0 (nth [::] m 0) 0)
  | n'.+1 =>
    let '(mx0, mx1, mx2, mx3) := decomp n' m in
    Qc (qt_of n' mx0 a0) (qt_of n' mx1 a0) (qt_of n' mx2 a0) (qt_of n' mx3 a0)
  end.

Lemma sq_decomp n m :
     sq_mx n.+1 m
  -> let '(mx0, mx1, mx2, mx3) := decomp n m in
     [/\ sq_mx n mx0, sq_mx n mx1, sq_mx n mx2 & sq_mx n mx3].
Proof.
have H1': 2 ^ n < 2 ^ n.+1
  by rewrite expnSr muln2 -addnn -[X in X<_]add0n ltn_add2r expn_gt0.
have H2': 2 ^ n.+1 - 2 ^ n = 2 ^ n
  by rewrite expnSr muln2 -addnn addnK.
case/andP => /eqP H0 /allP H1; rewrite /decomp; split; apply/andP; split.
- by rewrite size_map size_take H0 H1'.
- apply/allP=> l /= /mapP [x] /mem_take /H1 /eqP Hx {l}->.
  by rewrite size_take Hx H1'.
- by rewrite size_map size_take H0 H1'.
- apply/allP=> l /= /mapP [x] /mem_take /H1 /eqP Hx {l}->.
  by rewrite size_drop Hx H2'.
- by rewrite size_map size_drop H0 H2'.
- apply/allP=> l /= /mapP [x] /mem_drop /H1 /eqP Hx {l}->.
  by rewrite size_take Hx H1'.
- by rewrite size_map size_drop H0 H2'.
- apply/allP=> l /= /mapP [x] /mem_drop /H1 /eqP Hx {l}->.
  by rewrite size_drop Hx H2'.
Qed.

Lemma height_qt_of n m a0 :
  sq_mx n m -> height (qt_of n m a0) <= n.
Proof.
elim: n m=>[|n IH] m //= /sq_decomp; rewrite /decomp; case=>H1 H2 H3 H4.
by apply: height_Qc_Q; apply: IH.
Qed.

Lemma get_qt_of n m a0 i j :
     sq_mx n m
  -> i < 2 ^ n -> j < 2 ^ n (* TODO sq? *)
  -> get n (qt_of n m a0) i j a0 = nth a0 (nth [::] m i) j.
Proof.
elim: n m i j=>[|n IH] m i j.
- by move=>_ /=; rewrite expn0 !ltnS !leqn0=>/eqP -> /eqP ->.
have H1': 2 ^ n < 2 ^ n.+1
  by rewrite expnSr muln2 -addnn -[X in X<_]add0n ltn_add2r expn_gt0.
have H2': 2 ^ n.+1 - 2 ^ n = 2 ^ n
  by rewrite expnSr muln2 -addnn addnK.
move=>/[dup]/andP [/eqP Hs /allP Ha] /sq_decomp [H1 H2 H3 H4] Hi Hj; rewrite [get]lock /=; unlock.
rewrite get_Qc /=; last first.
- by rewrite ltnS !geq_max -!andbA; apply/and4P; split; apply: height_qt_of.
case: ltnP=>Hi'; case: ltnP=>Hj' /=; rewrite IH //; try by rewrite ltn_mod expn_gt0.
- rewrite modn_small // modn_small //.
  rewrite (@nth_map _ [::]); last by rewrite size_take Hs H1'.
  by rewrite !nth_take.
- rewrite modn_small // mod_minus; last by rewrite Hj' /= -mul2n -expnS.
  rewrite (@nth_map _ [::]); last by rewrite size_take Hs H1'.
  rewrite nth_take // nth_drop; congr (nth a0 (nth [::] m i)).
  by rewrite addnBCA // subnn addn0.
- rewrite mod_minus; last by rewrite Hi' /= -mul2n -expnS.
  rewrite modn_small //.
  rewrite (@nth_map _ [::]); last first.
  - rewrite size_drop Hs H2' ltn_psubLR; last by rewrite expn_gt0.
    by rewrite addnn -mul2n -expnS.
  rewrite nth_drop nth_take //.
  suff: 2 ^ n + (i - 2 ^ n) = i by move =>->.
  by rewrite addnBCA // subnn addn0.
rewrite mod_minus; last by rewrite Hi' /= -mul2n -expnS.
rewrite mod_minus; last by rewrite Hj' /= -mul2n -expnS.
rewrite (@nth_map _ [::]); last first.
- rewrite size_drop Hs H2' ltn_psubLR; last by rewrite expn_gt0.
  by rewrite addnn -mul2n -expnS.
rewrite !nth_drop.
suff: 2 ^ n + (i - 2 ^ n) = i /\ 2 ^ n + (j - 2 ^ n) = j by case=>->->.
by split; rewrite addnBCA // subnn addn0.
Qed.

Lemma compressed_qt_of n m a0 :
  sq_mx n m -> compressed (qt_of n m a0).
Proof.
elim: n m=>[|n IH] m //= /sq_decomp; rewrite /decomp; case=>H1 H2 H3 H4.
by apply: compressed_Qc; apply: IH.
Qed.

(* Exercise 13.2 *)

Definition shift_mx (f : nat -> nat -> A) (x y i j : nat) : A := f (i+x) (j+y).

Fixpoint qt_of_fun (f : nat -> nat -> A) (n : nat) : qtree A := L (f 0 0). (* FIXME *)

Lemma height_qt_of_fun f n :
  height (qt_of_fun f n) <= n.
Proof.
Admitted.

Lemma get_qt_of_fun f n i j a0 :
     i < 2 ^ n -> j < 2 ^ n (* TODO sq? *)
  -> get n (qt_of_fun f n) i j a0 = f i j.
Proof.
Admitted.

End RegionQuadtreesMisc.

(* we can use arbitrary rings instead of reals *)
(* TODO weaken to semirings after upgrading Mathcomp? *)
Section MatrixQuadtrees.
Context {A : ringType}.

Open Scope ring_scope.
Import GRing.Theory.

(* mathcomp has a similar definition of matrices but it's indexed by finite ordinals *)
Definition ma : Type := nat -> nat -> A.

Definition sq_ma (n : nat) (a : ma) : Prop :=
  forall i j, 2 ^ n <= i \/ 2 ^ n <= j -> a i j = 0.

Definition mk_sq (n : nat) (m : ma) : ma :=
  fun i j => if (i < 2 ^ n) && (j < 2 ^ n) then m i j else 0.

Definition D (n : nat) (x : A) : ma :=
  mk_sq n (fun i j => if i == j then x else 0).

Definition Qma (n : nat) (a b c d : ma) : ma :=
  fun i j =>
    let m := 2 ^ n in
    if i < m then
      if j < m then a i j
      else b i (j - m)%N
    else
      if j < m then c (i - m)%N j
      else d (i - m)%N (j - m)%N.

Lemma D1_Qma n x :
  D n.+1 x = Qma n (D n x) (D n 0) (D n 0) (D n x).
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
rewrite /D /Qma /mk_sq /= !ltn_psubLR; try by rewrite expn_gt0.
rewrite addnn -mul2n -expnS; case: ifP.
- case/andP=>Hi Hj; case: ltnP=>Hi'; case: ltnP=>Hj' //=; last by rewrite eqn_sub2rE.
  - rewrite !if_same; case: eqP=>// E; exfalso.
    by rewrite leqNgt -E Hi' in Hj'.
  rewrite !if_same; case: eqP=>// E; exfalso.
  by rewrite leqNgt E Hj' in Hi'.
move=>H; rewrite !if_same; case: ltnP=>Hi' //=; case: ltnP=>Hj' //=.
exfalso; move/negP: H; apply; apply/andP; split.
- by apply: (leq_trans Hi'); rewrite expnS mul2n -addnn; exact: leq_addl.
by apply: (leq_trans Hj'); rewrite expnS mul2n -addnn; exact: leq_addl.
Qed.

Fixpoint mabs (n : nat) (q : qtree A) : ma :=
  match q with
  | L x => D n x
  | Q t0 t1 t2 t3 =>
    match n with
    | 0 => D 0 0
    | n'.+1 => Qma n' (mabs n' t0) (mabs n' t1) (mabs n' t2) (mabs n' t3)
    end
  end.

Lemma mabsL n x : mabs n (L x) = D n x.
Proof. by case: n. Qed.

Definition add_ma (a b : ma) : ma :=
  fun i j => a i j + b i j.

Definition mul_ma (n : nat) (a b : ma) : ma :=
  fun i j => \sum_(0 <= k < 2 ^ n) (a i k * b k j).  (* TODO can we get rid of 0 <= ? *)

Lemma add_ma_D n x y : add_ma (D n x) (D n y) = D n (x + y).
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
rewrite /add_ma /D /mk_sq /=; case: ifP=>_; last by rewrite addr0.
by case: ifP=>// _; rewrite addr0.
Qed.

Lemma add_ma_D0l n a : add_ma (D n 0) a = a.
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
rewrite /add_ma /D /mk_sq /=; case: ifP=>_; last by rewrite add0r.
by rewrite if_same add0r.
Qed.

Lemma add_ma_D0r n a : add_ma a (D n 0) = a.
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
rewrite /add_ma /D /mk_sq /=; case: ifP=>_; last by rewrite addr0.
by rewrite if_same addr0.
Qed.

Lemma mul_ma_D0l n a : mul_ma n (D n 0) a = D n 0.
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
rewrite /mul_ma /D /mk_sq /=; rewrite !if_same.
have E: \sum_(0 <= k < 2 ^ n) 0 = 0 :> A
  by rewrite big_const_nat subn0; apply: iter_fix; rewrite addr0.
by rewrite -{}[RHS]E; apply: eq_big_nat=> k _; rewrite !if_same mul0r.
Qed.

Lemma mul_ma_D0r n a : mul_ma n a (D n 0) = D n 0.
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
rewrite /mul_ma /D /mk_sq /=; rewrite !if_same.
have E: \sum_(0 <= k < 2 ^ n) 0 = 0 :> A
  by rewrite big_const_nat subn0; apply: iter_fix; rewrite addr0.
by rewrite -{}[RHS]E; apply: eq_big_nat=> k _; rewrite !if_same mulr0.
Qed.

Lemma mul_ma_D n x y : mul_ma n (D n x) (D n y) = D n (x * y).
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
have E: forall a b, \sum_(a <= k < b) 0 = 0 :> A.
  by move=>a b; rewrite big_const_nat; apply: iter_fix; rewrite addr0.
rewrite /mul_ma /D /mk_sq /=; case: ifP; last first.
- move/negbT; rewrite negb_and=>H.
  rewrite -{}[RHS](E 0%N (2 ^ n)); apply: eq_big_nat=> k /andP [_ ->] /=; rewrite andbT.
  by case/orP: H=>/negbTE->; [rewrite mul0r | rewrite mulr0].
- case/andP => Hi Hj; rewrite Hi Hj /=; case: ifP=>/eqP Ei; last first.
  - rewrite -{}[RHS](E 0%N (2 ^ n)); apply: eq_big_nat=> k /andP [_ ->] /=.
    case: ifP=>[/eqP<-|Ni]; last by rewrite mul0r.
    by move/eqP: Ei=>/negbTE->; rewrite mulr0.
rewrite -{j Hj}Ei.
have E': \sum_(0 <= k < 2 ^ n) (if k == i then x * y else 0) = x * y.
- rewrite (@big_cat_nat _ _ _ i) //=; last by apply: ltnW.
  rewrite -[RHS]add0r; congr (_ + _).
  - rewrite -{}[RHS](E 0%N i); apply: eq_big_nat=> k /andP [_ Hk] /=.
    by rewrite ltn_eqF.
  rewrite (@big_cat_nat _ _ _ i.+1) //= big_nat1 eqxx -[RHS]addr0; congr (x * y + _).
  rewrite -{}[RHS](E i.+1 (2 ^ n)); apply: eq_big_nat=> k /andP [Hk _] /=.
  by rewrite gtn_eqF.
rewrite -E'; apply: eq_big_nat=> k /andP [_ ->] /=.
case: ifP=>[/eqP<-|N]; first by rewrite eqxx.
by rewrite mul0r eq_sym N.
Qed.

Lemma add_ma_Qma n a1 b1 c1 d1 a2 b2 c2 d2 :
  add_ma (Qma n a1 b1 c1 d1) (Qma n a2 b2 c2 d2) = Qma n (add_ma a1 a2) (add_ma b1 b2) (add_ma c1 c2) (add_ma d1 d2).
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
by rewrite /add_ma /Qma /mk_sq /=; case: ifP=>Hi; case: ifP=>Hj.
Qed.

Lemma add_ma_D_Qma n x a b c d :
  add_ma (D n.+1 x) (Qma n a b c d) = Qma n (add_ma (D n x) a) b c (add_ma (D n x) d).
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
rewrite /add_ma /D /Qma /mk_sq /= !ltn_psubLR; try by rewrite expn_gt0.
rewrite addnn -mul2n -expnS; case: ifP.
- case/andP=>Hi Hj.
  - case: ltnP=>Hi'; case: ltnP=>Hj' //=; last by rewrite eqn_sub2rE.
    - case: eqP=>[E|N]; last by rewrite add0r.
      by rewrite leqNgt -E Hi' in Hj'.
    case: eqP=>[E|N]; last by rewrite add0r.
    by rewrite leqNgt E Hj' in Hi'.
move=>H; rewrite add0r; case: ltnP=>Hi; case: ltnP=>Hj //=; last by rewrite add0r.
exfalso; move/negP: H; apply; apply/andP; split.
- by apply: (leq_trans Hi); rewrite expnS mul2n -addnn; exact: leq_addl.
by apply: (leq_trans Hj); rewrite expnS mul2n -addnn; exact: leq_addl.
Qed.

Lemma add_ma_Qma_D n x a b c d :
  add_ma (Qma n a b c d) (D n.+1 x) = Qma n (add_ma a (D n x)) b c (add_ma d (D n x)).
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
rewrite /add_ma /D /Qma /mk_sq /= !ltn_psubLR; try by rewrite expn_gt0.
rewrite addnn -mul2n -expnS. case: (ifP ((i < 2 ^ n.+1) && (j < 2 ^ n.+1))).
- case/andP=>Hi Hj.
  - case: ltnP=>Hi'; case: ltnP=>Hj' //=; last by rewrite eqn_sub2rE.
    - case: eqP=>[E|N]; last by rewrite addr0.
      by rewrite leqNgt -E Hi' in Hj'.
    case: eqP=>[E|N]; last by rewrite addr0.
    by rewrite leqNgt E Hj' in Hi'.
move=>H; rewrite addr0; case: ltnP=>Hi; case: ltnP=>Hj //=; last by rewrite addr0.
exfalso; move/negP: H; apply; apply/andP; split.
- by apply: (leq_trans Hi); rewrite expnS mul2n -addnn; exact: leq_addl.
by apply: (leq_trans Hj); rewrite expnS mul2n -addnn; exact: leq_addl.
Qed.

Lemma mult_ma_Qma_Qma n a1 b1 c1 d1 a2 b2 c2 d2 :
  mul_ma n.+1 (Qma n a1 b1 c1 d1) (Qma n a2 b2 c2 d2) =
  Qma n (add_ma (mul_ma n a1 a2) (mul_ma n b1 c2))
        (add_ma (mul_ma n a1 b2) (mul_ma n b1 d2))
        (add_ma (mul_ma n c1 a2) (mul_ma n d1 c2))
        (add_ma (mul_ma n c1 b2) (mul_ma n d1 d2)).
Proof.
apply/functional_extensionality=>i; apply/functional_extensionality=>j.
rewrite /add_ma /mul_ma /Qma /mk_sq /= (@big_cat_nat _ _ _ (2 ^ n)) //=; last by rewrite expnS mul2n -addnn; exact: leq_addr.
case: ltnP=>Hi; case: ltnP=>Hj.
(* TODO repetition *)
- congr (_ + _); first by apply: eq_big_nat=> k /andP [_ ->].
  rewrite -{1}(add0n (2 ^ n)) big_addn expnS mul2n -addnn addnK.
  by apply: eq_big_nat=> k _; rewrite ltnNge leq_addl /= addnK.
- congr (_ + _); first by apply: eq_big_nat=> k /andP [_ ->].
  rewrite -{1}(add0n (2 ^ n)) big_addn expnS mul2n -addnn addnK.
  by apply: eq_big_nat=> k _; rewrite ltnNge leq_addl /= addnK.
- congr (_ + _); first by apply: eq_big_nat=> k /andP [_ ->].
  rewrite -{1}(add0n (2 ^ n)) big_addn expnS mul2n -addnn addnK.
  by apply: eq_big_nat=> k _; rewrite ltnNge leq_addl /= addnK.
congr (_ + _); first by apply: eq_big_nat=> k /andP [_ ->].
rewrite -{1}(add0n (2 ^ n)) big_addn expnS mul2n -addnn addnK.
by apply: eq_big_nat=> k _; rewrite ltnNge leq_addl /= addnK.
Qed.

Definition QcM (q1 q2 q3 q4 : qtree A) : qtree A :=
  match q1, q2, q3, q4 with
  | L x0, L x1, L x2, L x3 =>
      if [&& x1 == 0, x2 == 0 & x0 == x3] then L x0 else Q (L x0) (L x1) (L x2) (L x3)
  | _, _, _, _ => Q q1 q2 q3 q4
  end.

Lemma mabs_QcM n t0 t1 t2 t3 :
  mabs n.+1 (QcM t0 t1 t2 t3) = mabs n.+1 (Q t0 t1 t2 t3).
Proof.
case: t0 t1 t2 t3=>[x0|x0 x1 x2 x3][y0|y0 y1 y2 y3][z0|z0 z1 z2 z3][w0|w0 w1 w2 w3] //=.
case: ifP=>// /and3P [/eqP-> /eqP -> /eqP <-].
by rewrite D1_Qma // !mabsL.
Qed.

Lemma height_QcM_Q t0 t1 t2 t3 :
  height (QcM t0 t1 t2 t3) <= height (Q t0 t1 t2 t3).
Proof.
case: t0 t1 t2 t3=>[x0|x0 x1 x2 x3][y0|y0 y1 y2 y3][z0|z0 z1 z2 z3][w0|w0 w1 w2 w3] //=.
by rewrite !maxn0; case: ifP.
Qed.

Fixpoint compressedM (q : qtree A) : bool :=
  match q with
  | L _ => true
  | Q (L x0) (L x1) (L x2) (L x3) => ~~ [&& x1 == 0, x2 == 0 & x0 == x3]
  | Q t0 t1 t2 t3 => [&& compressedM t0, compressedM t1, compressedM t2 & compressedM t3]
  end.

Lemma compressedM_Q t0 t1 t2 t3 :
     compressedM (Q t0 t1 t2 t3)
  -> [&& compressedM t0, compressedM t1, compressedM t2 & compressedM t3].
Proof.
by case: t0 t1 t2 t3=>[x0|x0 x1 x2 x3][y0|y0 y1 y2 y3][z0|z0 z1 z2 z3][w0|w0 w1 w2 w3].
Qed.

Lemma compressed_QcM t0 t1 t2 t3 :
  compressedM (QcM t0 t1 t2 t3) = [&& compressedM t0, compressedM t1, compressedM t2 & compressedM t3].
Proof.
case: t0 t1 t2 t3=>[x0|x0 x1 x2 x3][y0|y0 y1 y2 y3][z0|z0 z1 z2 z3][w0|w0 w1 w2 w3] //=; rewrite ?andbT -?andbA //.
by case: ifP=>//= ->.
Qed.

Equations? add_qtr (a b : qtree A) : qtree A by wf (height a + height b)%N lt :=
add_qtr (L x)           (L y)           => L (x + y);
add_qtr (L x)           (Q b0 b1 b2 b3) => QcM (add_qtr (L x) b0) b1 b2 (add_qtr (L x) b3);
add_qtr (Q a0 a1 a2 a3) (L y)           => QcM (add_qtr a0 (L y)) a1 a2 (add_qtr a3 (L y));
add_qtr (Q a0 a1 a2 a3) (Q b0 b1 b2 b3) => QcM (add_qtr a0 b0) (add_qtr a1 b1) (add_qtr a2 b2) (add_qtr a3 b3).
Proof.
all: apply: ssrnat.ltP; rewrite ?addn0 ?add0n ?addSn ltnS.
- by rewrite -!maxnA; exact: leq_maxl.
- by exact: leq_maxr.
- by rewrite -!maxnA; exact: leq_maxl.
- by exact: leq_maxr.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add;
  by rewrite -!maxnA; exact: leq_maxl.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add;
  by rewrite [X in _<=X](AC 4%AC (2*(1*3*4))%AC) /=; apply: leq_maxl.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add;
  by rewrite [X in _<=X](AC 4%AC (3*(1*2*4))%AC) /=; apply: leq_maxl.
apply: ltnW; rewrite addnS ltnS; apply: leq_add;
by rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; apply: leq_maxl.
Qed.

Equations? mul_qtr (a b : qtree A) : qtree A by wf (height a + height b)%N lt :=
mul_qtr (L x)           (L y)           => L (x * y);
mul_qtr (L x)           (Q b0 b1 b2 b3) => QcM (mul_qtr (L x) b0) (mul_qtr (L x) b1) (mul_qtr (L x) b2) (mul_qtr (L x) b3);
mul_qtr (Q a0 a1 a2 a3) (L y)           => QcM (mul_qtr a0 (L y)) (mul_qtr a1 (L y)) (mul_qtr a2 (L y)) (mul_qtr a3 (L y));
mul_qtr (Q a0 a1 a2 a3) (Q b0 b1 b2 b3) => QcM (add_qtr (mul_qtr a0 b0) (mul_qtr a1 b2))
                                               (add_qtr (mul_qtr a0 b1) (mul_qtr a1 b3))
                                               (add_qtr (mul_qtr a2 b0) (mul_qtr a3 b2))
                                               (add_qtr (mul_qtr a2 b1) (mul_qtr a3 b3)).
Proof.
all: apply: ssrnat.ltP; rewrite ?addn0 ?add0n ?addSn ltnS.
- by rewrite -!maxnA; exact: leq_maxl.
- by rewrite [X in _<=X](AC 4%AC (2*(1*3*4))%AC) /=; apply: leq_maxl.
- by rewrite [X in _<=X](AC 4%AC (3*(1*2*4))%AC) /=; apply: leq_maxl.
- by rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; apply: leq_maxl.
- by rewrite -!maxnA; exact: leq_maxl.
- by rewrite [X in _<=X](AC 4%AC (2*(1*3*4))%AC) /=; apply: leq_maxl.
- by rewrite [X in _<=X](AC 4%AC (3*(1*2*4))%AC) /=; apply: leq_maxl.
- by rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; apply: leq_maxl.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add;
  by rewrite -!maxnA; exact: leq_maxl.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add.
  - by rewrite [X in _<=X](AC 4%AC (2*(1*3*4))%AC) /=; apply: leq_maxl.
  by rewrite [X in _<=X](AC 4%AC (3*(1*2*4))%AC) /=; apply: leq_maxl.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add.
  - by rewrite -!maxnA; exact: leq_maxl.
  by rewrite [X in _<=X](AC 4%AC (2*(1*3*4))%AC) /=; apply: leq_maxl.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add.
  - by rewrite [X in _<=X](AC 4%AC (2*(1*3*4))%AC) /=; apply: leq_maxl.
  by rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; apply: leq_maxl.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add.
  - by rewrite [X in _<=X](AC 4%AC (3*(1*2*4))%AC) /=; apply: leq_maxl.
  by rewrite -!maxnA; exact: leq_maxl.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add.
  - by rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; apply: leq_maxl.
  by rewrite [X in _<=X](AC 4%AC (3*(1*2*4))%AC) /=; apply: leq_maxl.
- apply: ltnW; rewrite addnS ltnS; apply: leq_add.
  - by rewrite [X in _<=X](AC 4%AC (3*(1*2*4))%AC) /=; apply: leq_maxl.
  by rewrite [X in _<=X](AC 4%AC (2*(1*3*4))%AC) /=; apply: leq_maxl.
apply: ltnW; rewrite addnS ltnS; apply: leq_add.
- by rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; apply: leq_maxl.
by rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; apply: leq_maxl.
Qed.

Lemma height_add s t : height (add_qtr s t) <= maxn (height s) (height t).
Proof.
funelim (add_qtr s t); simp add_qtr => //=; rewrite ?max0n ?maxn0 /= in H H0 *.
- apply: leq_trans; first by exact: height_QcM_Q.
  rewrite /= ltnS geq_max; apply/andP; split; last first.
  - by apply: (leq_trans H0); rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; exact: leq_maxl.
  rewrite -![X in X<=_]maxnA geq_max; apply/andP; split.
  - by apply: (leq_trans H); rewrite -!maxnA; exact: leq_maxl.
  by rewrite [X in _<=X](AC 4%AC ((2*3)*(1*4))%AC) /=; exact: leq_maxl.
- apply: leq_trans; first by exact: height_QcM_Q.
  rewrite /= ltnS geq_max; apply/andP; split; last first.
  - by apply: (leq_trans H0); rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; exact: leq_maxl.
  rewrite -![X in X<=_]maxnA geq_max; apply/andP; split.
  - by apply: (leq_trans H); rewrite -!maxnA; exact: leq_maxl.
  by rewrite [X in _<=X](AC 4%AC ((2*3)*(1*4))%AC) /=; exact: leq_maxl.
apply: leq_trans; first by exact: height_QcM_Q.
rewrite /= maxnSS ltnS !geq_max -!andbA; apply/and4P; split.
- by apply: (leq_trans H); rewrite [X in _<=X](AC (4*4)%AC ((1*5)*(2*3*4*6*7*8))%AC) /=; exact: leq_maxl.
- by apply: (leq_trans H0); rewrite [X in _<=X](AC (4*4)%AC ((2*6)*(1*3*4*5*7*8))%AC) /=; exact: leq_maxl.
- by apply: (leq_trans H1); rewrite [X in _<=X](AC (4*4)%AC ((3*7)*(1*2*4*5*6*8))%AC) /=; exact: leq_maxl.
by apply: (leq_trans H2); rewrite [X in _<=X](AC (4*4)%AC ((4*8)*(1*2*3*5*6*7))%AC) /=; exact: leq_maxl.
Qed.

Lemma height_mul s t : height (mul_qtr s t) <= maxn (height s) (height t).
Proof.
funelim (mul_qtr s t); simp mul_qtr=>//=; rewrite ?max0n ?maxn0 /= in H H0 H1 H2 *.
- apply: leq_trans; first by exact: height_QcM_Q.
  rewrite /= ltnS !geq_max -!andbA; apply/and4P; split.
  - by apply: (leq_trans H); rewrite -!maxnA; exact: leq_maxl.
  - by apply: (leq_trans H0); rewrite [X in _<=X](AC 4%AC (2*(1*3*4))%AC) /=; apply: leq_maxl.
  - by apply: (leq_trans H1); rewrite [X in _<=X](AC 4%AC (3*(1*2*4))%AC) /=; apply: leq_maxl.
  by apply: (leq_trans H2); rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; apply: leq_maxl.
- apply: leq_trans; first by exact: height_QcM_Q.
  rewrite /= ltnS !geq_max -!andbA; apply/and4P; split.
  - by apply: (leq_trans H); rewrite -!maxnA; exact: leq_maxl.
  - by apply: (leq_trans H0); rewrite [X in _<=X](AC 4%AC (2*(1*3*4))%AC) /=; apply: leq_maxl.
  - by apply: (leq_trans H1); rewrite [X in _<=X](AC 4%AC (3*(1*2*4))%AC) /=; apply: leq_maxl.
  by apply: (leq_trans H2); rewrite [X in _<=X](AC 4%AC (4*(1*2*3))%AC) /=; apply: leq_maxl.
apply: leq_trans; first by exact: height_QcM_Q.
rewrite /= maxnSS ltnS !geq_max -!andbA; apply/and4P; split.
- apply: leq_trans; first by exact: height_add.
  rewrite geq_max; apply/andP; split.
  - by apply: (leq_trans H); rewrite [X in _<=X](AC (4*4)%AC ((1*5)*(2*3*4*6*7*8))%AC) /=; exact: leq_maxl.
  by apply: (leq_trans H0); rewrite [X in _<=X](AC (4*4)%AC ((2*7)*(1*3*4*5*6*8))%AC) /=; exact: leq_maxl.
- apply: leq_trans; first by exact: height_add.
  rewrite geq_max; apply/andP; split.
  - by apply: (leq_trans H1); rewrite [X in _<=X](AC (4*4)%AC ((1*6)*(2*3*4*5*7*8))%AC) /=; exact: leq_maxl.
  by apply: (leq_trans H2); rewrite [X in _<=X](AC (4*4)%AC ((2*8)*(1*3*4*5*6*7))%AC) /=; exact: leq_maxl.
- apply: leq_trans; first by exact: height_add.
  rewrite geq_max; apply/andP; split.
  - by apply: (leq_trans H3); rewrite [X in _<=X](AC (4*4)%AC ((3*5)*(1*2*4*6*7*8))%AC) /=; exact: leq_maxl.
  by apply: (leq_trans H4); rewrite [X in _<=X](AC (4*4)%AC ((4*7)*(1*2*3*5*6*8))%AC) /=; exact: leq_maxl.
apply: leq_trans; first by exact: height_add.
rewrite geq_max; apply/andP; split.
- by apply: (leq_trans H5); rewrite [X in _<=X](AC (4*4)%AC ((3*6)*(1*2*4*5*7*8))%AC) /=; exact: leq_maxl.
by apply: (leq_trans H6); rewrite [X in _<=X](AC (4*4)%AC ((4*8)*(1*2*3*5*6*7))%AC) /=; exact: leq_maxl.
Qed.

Lemma mabs_add s t n :
     height s <= n -> height t <= n
  -> mabs n (add_qtr s t) = add_ma (mabs n s) (mabs n t).
Proof.
funelim (add_qtr s t)=>/=; simp add_qtr=>//=.
- by move=>_ _; rewrite !mabsL add_ma_D.
- move=>_; case: n=>// n; rewrite ltnS !geq_max -!andbA; case/and4P=>Hb0 Hb1 Hb2 Hb3.
  by rewrite mabs_QcM /= add_ma_D_Qma H // H0 // !mabsL.
- move/[swap]=>_; case: n=>// n; rewrite ltnS !geq_max -!andbA; case/and4P=>Ha0 Ha1 Ha2 Ha3.
  by rewrite mabs_QcM /= add_ma_Qma_D H // H0 // !mabsL.
case: n=>// n; rewrite !ltnS !geq_max -!andbA;
  case/and4P=>Ha0 Ha1 Ha2 Ha3; case/and4P=>Hb0 Hb1 Hb2 Hb3.
by rewrite mabs_QcM /= add_ma_Qma H // H0 // H1 // H2.
Qed.

Lemma mabs_mul s t n :
     height s <= n -> height t <= n
  -> mabs n (mul_qtr s t) = mul_ma n (mabs n s) (mabs n t).
Proof.
funelim (mul_qtr s t)=>/=; simp mul_qtr=>//=.
- by move=>_ _; rewrite !mabsL mul_ma_D.
- move=>_; case: n=>// n; rewrite ltnS !geq_max -!andbA; case/and4P=>Hb0 Hb1 Hb2 Hb3.
  by rewrite mabs_QcM /= D1_Qma mult_ma_Qma_Qma H // H0 // H1 // H2 //
    !mabsL !mul_ma_D0l !add_ma_D0l !add_ma_D0r.
- move/[swap]=>_; case: n=>// n; rewrite ltnS !geq_max -!andbA; case/and4P=>Ha0 Ha1 Ha2 Ha3.
  by rewrite mabs_QcM /= D1_Qma mult_ma_Qma_Qma H // H0 // H1 // H2 //
    !mabsL !mul_ma_D0r !add_ma_D0l !add_ma_D0r.
case: n=>// n; rewrite !ltnS !geq_max -!andbA;
  case/and4P=>Ha0 Ha1 Ha2 Ha3; case/and4P=>Hb0 Hb1 Hb2 Hb3.
rewrite mabs_QcM /= mult_ma_Qma_Qma !mabs_add;
  try by apply: leq_trans; [exact: height_mul | rewrite geq_max; apply/andP].
by rewrite H // H0 // H1 // H2 // H3 // H4 // H5 // H6.
Qed.

Lemma compressed_add s t :
  compressedM s -> compressedM t -> compressedM (add_qtr s t).
Proof.
funelim (add_qtr s t); simp add_qtr=>//.
- move=>_ /compressedM_Q; case/and4P=>Hb0 Hb1 Hb2 Hb3.
  by rewrite compressed_QcM /= H // Hb1 Hb2 H0.
- move/[swap]=>_ /compressedM_Q; case/and4P=>Ha0 Ha1 Ha2 Ha3.
  by rewrite compressed_QcM /= H // Ha1 Ha2 H0.
move/compressedM_Q; case/and4P=>Ha0 Ha1 Ha2 Ha3; move/compressedM_Q; case/and4P=>Hb0 Hb1 Hb2 Hb3.
by rewrite compressed_QcM /= H // H0 // H1 // H2.
Qed.

Lemma compressed_mul s t :
  compressedM s -> compressedM t -> compressedM (mul_qtr s t).
Proof.
funelim (mul_qtr s t); simp mul_qtr=>//.
- move=>_ /compressedM_Q; case/and4P=>Hb0 Hb1 Hb2 Hb3.
  by rewrite compressed_QcM /= H // H0 // H1 // H2.
- move/[swap]=>_ /compressedM_Q; case/and4P=>Ha0 Ha1 Ha2 Ha3.
  by rewrite compressed_QcM /= H // H0 // H1 // H2.
move/compressedM_Q; case/and4P=>Ha0 Ha1 Ha2 Ha3; move/compressedM_Q; case/and4P=>Hb0 Hb1 Hb2 Hb3.
rewrite compressed_QcM /= !compressed_add //.
- by apply: H5.
- by apply: H6.
- by apply: H3.
- by apply: H4.
- by apply: H1.
- by apply: H2.
- by apply: H.
by apply: H0.
Qed.

End MatrixQuadtrees.

Section KDimRegionTreesGen.
Context {A : Type}.

Inductive kdt A := Box of A | Split of kdt A & kdt A.

Fixpoint heightKD (t : kdt A) : nat :=
  match t with
  | Box _ => 0
  | Split l r => (maxn (heightKD l) (heightKD r)).+1
  end.

Fixpoint subtree (t : kdt A) (s : seq bool) : kdt A :=
  match s, t with
  | [::], _ => t
  | _ :: _, Box _ => t
  | b :: bs, Split l r => subtree (if b then r else l) bs
  end.

Lemma subtree_nil t : subtree t [::] = t.
Proof. by case: t. Qed.

Lemma subtree_Box x bs : subtree (Box x) bs = Box x.
Proof. by case: bs. Qed.

Lemma height_subtree t bs : heightKD (subtree t bs) <= heightKD t - size bs.
Proof.
elim: bs t=>/= [|b bs IH][a|l r] //=; rewrite subSS.
apply: leq_trans; first by exact: IH.
rewrite leq_subLR addnC addnCB; apply: leq_trans; last by exact: leq_addr.
by case: b; [exact: leq_maxr | exact: leq_maxl].
Qed.

Fixpoint getKD (n : nat) (t : kdt A) (ps : seq nat) (a0 : A) : A :=
  match t, n with
  | Box b, _ => b
  | Split _ _, 0 => a0
  | Split _ _, n.+1 => getKD n (subtree t [seq i < 2 ^ n | i <- ps]) [seq i %% 2 ^ n | i <- ps] a0
  end.

Lemma getKD_suc n t ps a0 :
  getKD n.+1 t ps a0 = getKD n (subtree t [seq i < 2 ^ n | i <- ps]) [seq i %% 2 ^ n | i <- ps] a0.
Proof. by case: t=>//=a; case: [seq i < 2 ^ n | i <- ps]=>[|_ _]; case: n. Qed.

Definition cube (k n : nat) : pred (seq nat) :=
  [pred s | (size s == n) && all (fun i => i < 2 ^ k) s ].

End KDimRegionTreesGen.

Section KDimRegionTrees.
Context {A : eqType}.

Definition same_box (l r : kdt A) : bool :=
  match l, r with
  | Box x, Box y => x == y
  | _, _ => false
  end.

Fixpoint compressedKD (t : kdt A) : bool :=
  match t with
  | Box _ => true
  | Split l r => [&& compressedKD l, compressedKD r & ~~ same_box l r]
  end.

Definition SplitC (l r : kdt A) : kdt A :=
  match l, r with
  | Box x, Box y => if x == y then Box x else Split l r
  | _, _ => Split l r
  end.
(* can be also written as: *)
(* if same_box l r then l else Split l r *)

Arguments SplitC : simpl never.

Lemma height_SplitC l r :
  heightKD (SplitC l r) <= (maxn (heightKD l) (heightKD r)).+1.
Proof.
rewrite /SplitC; case: l=>[x|l1 l2]; case: r=>[y|r1 r2] //=.
by rewrite max0n; case: eqP.
Qed.

Lemma compressed_SplitC l r :
  compressedKD l -> compressedKD r -> compressedKD (SplitC l r).
Proof.
case: l r=>[x|l1 l2][y|r1 r2]/=; rewrite ?andbT //; last by move=>->.
by rewrite /SplitC=>_ _; case: eqP=>//= /eqP.
Qed.

Lemma subtree_SplitC l r bs :
     0 < size bs
  -> subtree (SplitC l r) bs = subtree (Split l r) bs.
Proof.
case: l r=>[x|l1 l2][y|r1 r2]//=; case: bs =>//= b bs _.
by rewrite /SplitC; case: eqP=>//= ->; rewrite if_same; case: bs.
Qed.

Fixpoint modifyKD (f : kdt A -> kdt A) (bs : seq bool) (t : kdt A) : kdt A :=
  match bs, t with
  | [::], _ => f t
  | b :: bs, Box _ =>
      let t' := modifyKD f bs t in
      if b then SplitC t t' else SplitC t' t
  | b :: bs, Split l r =>
      if b then SplitC l (modifyKD f bs r) else SplitC (modifyKD f bs l) r
  end.

Fixpoint putKD (ps : seq nat) (a : A) (n : nat) (t : kdt A) : kdt A :=
  match n, t with
  | 0, Box _ => Box a
  | 0, _ => t
  | n.+1, t => modifyKD (putKD [seq i %% 2 ^ n | i <- ps] a n) [seq i < 2 ^ n | i <- ps] t
  end.

Lemma height_modifyKD t nk f bs :
     (forall t, heightKD t <= nk -> heightKD (f t) <= nk)
  -> heightKD t <= size bs + nk
  -> heightKD (modifyKD f bs t) <= size bs + nk.
Proof.
elim: bs t nk=>[|b bs IH][a|l r] nk Hf /= Ht.
- by rewrite add0n; apply: Hf.
- by rewrite add0n in Ht *; apply: Hf.
- case: b.
  - apply: leq_trans; first by exact: height_SplitC.
    by rewrite /= max0n addSn ltnS; apply: IH.
  apply: leq_trans; first by exact: height_SplitC.
  by rewrite /= maxn0 addSn ltnS; apply: IH.
move: Ht; rewrite addSn ltnS geq_max; case/andP=>H1 H2.
case: b=>/=.
- apply: leq_trans; first by exact: height_SplitC.
  by rewrite ltnS geq_max H1 /=; apply: IH.
apply: leq_trans; first by exact: height_SplitC.
by rewrite ltnS geq_max H2 andbT; apply: IH.
Qed.

Lemma height_putKD ps a n t :
     heightKD t <= n * size ps
  -> heightKD (putKD ps a n t) <= n * size ps.
Proof.
elim: n t ps =>[|n IH][x|l r] ps //= Ht; rewrite mulSn.
- rewrite -{1}(@size_map _ _ (fun i => i < 2 ^ n)); apply: height_modifyKD=>//= t H.
  apply: leq_trans; first by apply: IH; rewrite size_map.
  by rewrite size_map.
rewrite -{1}(@size_map _ _ (fun i => i < 2 ^ n));
  apply: height_modifyKD=>/=; last by rewrite size_map -mulSn.
move=>t H; apply: leq_trans; first by apply: IH; rewrite size_map.
by rewrite size_map.
Qed.

Lemma subtree_modifyKD f bs bs' t :
     size bs' = size bs
  -> subtree (modifyKD f bs t) bs' = (if bs' == bs then f (subtree t bs) else subtree t bs').
Proof.
elim: bs bs' t=>[|b bs IH][|b' bs'] //= t; first by move=>_; rewrite !subtree_nil.
case=>H; case: t=>[a|l r] //=; case: b=>/=; rewrite subtree_SplitC=>//=.
- case: b'; last by rewrite subtree_Box.
  rewrite IH // !subtree_Box; case: eqP=>[->|N]; first by rewrite eqxx.
  by case: eqP=>//; case=>E; rewrite E in N.
- case: b'; first by rewrite subtree_Box.
  rewrite IH // !subtree_Box; case: eqP=>[->|N]; first by rewrite eqxx.
  by case: eqP=>//; case=>E; rewrite E in N.
- by case: b'=>//; rewrite IH.
by case: b'=>//; rewrite IH.
Qed.

Lemma get_putKD k n t ps ps' a :
     heightKD t <= k * n
  -> ps \in cube n k
  -> ps' \in cube n k
  -> getKD n (putKD ps a n t) ps' a = (if ps' == ps then a else getKD n t ps' a).
Proof.
elim: n t ps ps'=>[|n IH] t ps ps'.
- rewrite muln0 leqn0; case: t=>//= x _ /andP[/eqP H1 /allP H2] /andP[/eqP H3 /allP H4].
  suff: ps' == ps by move=>->.
  rewrite eqseq_all all2E H1 H3 eqxx /=.
  apply/allP; case=>n m /in_zip [Hn Hm] /=.
  by move: (H2 _ Hm) (H4 _ Hn); rewrite !ltnS !leqn0=>/eqP->.
move=>H1 /andP[/eqP H2 H3] /andP[/eqP H4 H5]; rewrite !getKD_suc /= subtree_modifyKD; last by rewrite !size_map H2.
case: eqP=>[E|N]; last by case: eqP=>// E; rewrite E in N.
rewrite IH; first last.
- apply/andP; split; first by rewrite size_map H4.
  by rewrite all_map; apply/sub_all/H5=>x _ /=; rewrite ltn_mod expn_gt0.
- apply/andP; split; first by rewrite size_map H2.
  by rewrite all_map; apply/sub_all/H3=>x _ /=; rewrite ltn_mod expn_gt0.
- apply: leq_trans; first by exact: height_subtree.
  by rewrite size_map H2 leq_subLR -mulnS.
rewrite -E; apply/esym; case: eqP=>[->|N]; first by rewrite eqxx.
case: ifP=>// E'; exfalso; apply: N.
apply/eqP; rewrite eqseq_all all2E H2 H4 eqxx /=.
apply/allP; case=>x y Hxy /=.
move/eqP: E; rewrite eqseq_all all2E; case/andP=>_; rewrite zip_map2 all_map =>/allP /(_ _ Hxy) /= /eqP E.
move: E'; rewrite eqseq_all all2E; case/andP=>_; rewrite zip_map2 all_map =>/allP /(_ _ Hxy) /= E'.
move/in_zip: Hxy=>[Hx Hy].
move: E'; case: (ltnP x (2 ^ n))=>Hx'; first by rewrite !modn_small // -E.
have Hy': 2 ^ n <= y by rewrite leqNgt -E -leqNgt.
rewrite !mod_minus; first by rewrite eqn_sub2rE.
- apply/andP; split=>//; rewrite -mul2n -expnS.
  by move/allP: H3=>/(_ _ Hy).
apply/andP; split=>//; rewrite -mul2n -expnS.
by move/allP: H5=>/(_ _ Hx).
Qed.

Lemma compressed_modify f bs t :
     compressedKD t -> compressedKD (f (subtree t bs))
  -> compressedKD (modifyKD f bs t).
Proof.
elim: bs t=>[|b bs IH][a|l r] //=.
- by move=>_ H; case: b; apply: compressed_SplitC=>//; apply: IH=>//; rewrite subtree_Box.
by case/and3P=>H1 H2 _; case: b=>H /=; apply: compressed_SplitC=>//; apply: IH.
Qed.

Lemma compressed_subtree t bs :
  compressedKD t -> compressedKD (subtree t bs).
Proof.
elim: bs t=>[|b bs IH][a|l r] //=.
by case/and3P=>H1 H2 _; case: b; apply: IH.
Qed.

Lemma compressed_putKD ps a n t :
     heightKD t <= size ps * n
  -> compressedKD t
  -> compressedKD (putKD ps a n t).
Proof.
elim: n t ps=>[|n IH][x|l r] ps //= Ht Hc.
- by apply: compressed_modify=>//; rewrite subtree_Box; apply: IH.
apply: compressed_modify=>//; apply: IH; last by apply: compressed_subtree.
rewrite size_map; apply: leq_trans; first by exact: height_subtree.
by rewrite /= size_map leq_subLR -mulnS.
Qed.

End KDimRegionTrees.

Section KDimRegionTreesBool.

Fixpoint unionKD (t1 t2 : kdt bool) : kdt bool :=
  match t1, t2 with
  | Box b1, _ => if b1 then t1 else t2
  | Split _ _, Box b2 => if b2 then t2 else t1
  | Split l1 r1, Split l2 r2 => SplitC (unionKD l1 l2) (unionKD r1 r2)
  end.

Lemma union_Boxr t b : unionKD t (Box b) = (if b then Box true else t).
Proof.
case: t=>[a|t1 t2] /=; last by case: b.
case: a=>/=; first by rewrite if_same.
by case: b.
Qed.

Lemma subtree_union t1 t2 bs :
  subtree (unionKD t1 t2) bs = unionKD (subtree t1 bs) (subtree t2 bs).
Proof.
elim: t1 t2 bs=>[a|l1 IH1 r1 IH2][b|l2 r2] bs //; rewrite ?subtree_Box /=.
- by case: a; rewrite subtree_Box.
- by case: a=>//; rewrite subtree_Box.
- by rewrite union_Boxr; case: b=>//; rewrite subtree_Box.
case: bs=>[|b bs]/=; first by rewrite subtree_nil.
by rewrite subtree_SplitC=>//=; case: b=>/=; [exact: IH2 | exact: IH1].
Qed.

Lemma height_unionKD t1 t2 :
  heightKD (unionKD t1 t2) <= maxn (heightKD t1) (heightKD t2).
Proof.
elim: t1 t2=>[a|l1 IH1 r1 IH2][b|l2 r2] //=; rewrite ?max0n ?maxn0.
- by case: a.
- by case: a.
- by case: b.
apply: leq_trans; first by exact: height_SplitC.
rewrite maxnSS ltnS geq_max; apply/andP; split.
- apply: leq_trans; first by apply: IH1.
  by rewrite [X in _<=X](AC (2*2)%AC ((1*3)*(2*4))%AC) /=; apply: leq_maxl.
apply: leq_trans; first by apply: IH2.
by rewrite [X in _<=X](AC (2*2)%AC ((2*4)*(1*3))%AC) /=; apply: leq_maxl.
Qed.

Lemma compressed_unionKD t1 t2 :
  compressedKD t1 -> compressedKD t2 -> compressedKD (unionKD t1 t2).
Proof.
elim: t1 t2=>[a|l1 IH1 r1 IH2][b|l2 r2] /=.
- by move=>_ _; case: a.
- by move=>_ H; case: a.
- by move=>H _; case: b.
case/and3P=>H1 H2 _; case/and3P=>H3 H4 _.
by apply: compressed_SplitC=>//; [apply: IH1 | apply: IH2].
Qed.

End KDimRegionTreesBool.
