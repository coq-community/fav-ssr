From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat prime order seq path.
From favssr Require Import prelude bintree bst adt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Intro.
Context {A : Type}.

Variant col := Red | Black.

Definition eqcol (c1 c2 : col) :=
  match c1, c2 with
  | Red, Red => true
  | Black, Black => true
  | _, _ => false
  end.

Lemma eqcolP : Equality.axiom eqcol.
Proof. by move; case; case; constructor. Qed.

Canonical col_eqMixin := EqMixin eqcolP.
Canonical col_eqType := Eval hnf in EqType col col_eqMixin.

Definition rbt A := tree (A * col).

Definition R l a r : rbt A := Node l (a, Red) r.
Definition B l a r : rbt A := Node l (a, Black) r.

Definition color (t : rbt A) : col :=
  if t is Node _ (_, c) _ then c else Black.

Definition paint (c : col) (t : rbt A) : rbt A :=
  if t is Node l (a, _) r then Node l (a,c) r else empty_a.

Lemma paint2 c1 c2 t : paint c2 (paint c1 t) = paint c2 t.
Proof. by case: t=>//= l [a c] r. Qed.

Lemma paint_black t : color (paint Black t) = Black.
Proof. by case: t=>//= l [a c] r. Qed.

End Intro.

Section Invariants.
Context {A : Type}.

(* red nodes must have black children *)

Fixpoint invc (t : rbt A) : bool :=
  if t is Node l (_, c) r
    then [&& ((c == Red) ==> (color l == Black) && (color r == Black)), invc l & invc r]
    else true.

(* all paths from the root to a leaf have the same number of black nodes *)

Fixpoint bh (t : rbt A) : nat :=
  if t is Node l (_, c) _ then bh l + (c == Black) else 0.

Fixpoint invh (t : rbt A) : bool :=
  if t is Node l _ r
    then [&& bh l == bh r, invh l & invh r]
    else true.

Lemma invh_paint c t : invh t -> invh (paint c t).
Proof. by case: t=>//=l [a c'] r. Qed.

Lemma bh_paint_red t :
  color t = Black -> bh (paint Red t) = bh t - 1.
Proof.
case: t=>//= l [a c] r -> /=.
by rewrite addn0 addnK.
Qed.

Lemma bh_gt0 t : t <> empty_a -> color t = Black -> (0 < bh t)%N.
Proof. by case: t=>//=l [a c] r _ -> /=; rewrite addn1. Qed.

(* TODO separate induction principles for invc/invh? *)
Definition invch (t : rbt A) : bool := invc t && invh t.

Lemma invch_ind (P : rbt A -> Prop) :
  P (Leaf (A*col)) ->
  (forall l a c r,
   (c == Red) ==> (color l == Black) && (color r == Black) -> invc l -> invc r ->
   bh l == bh r -> invh l -> invh r ->
   P l -> P r ->
   P (Node l (a,c) r)) ->
  forall t, invch t -> P t.
Proof.
move=>Pl Pn; elim=>//= l IHl [a c] r IHr /andP [/and3P [I Hcl Hcr] /and3P [E Hhl Hhr]].
by apply: Pn=>//; [apply: IHl| apply: IHr]; apply/andP; split.
Qed.

Arguments invch_ind [P].

Definition rbt_inv (t : rbt A) : bool :=
  invch t && (color t == Black).

(* Logarithmic Height *)

Lemma height_black_height t :
  invch t -> (height t <= 2 * bh t + (color t == Red))%N.
Proof.
elim/invch_ind=>{t}//=l _ c r H1 Hcl Hcr /eqP E Hhl Hhr Hl Hr.
case: c H1=>/= [/andP [/eqP Hcll /eqP Hclr]|_].
- rewrite Hcll E /= addn0 in Hl *; rewrite Hclr /= addn0 in Hr.
  by rewrite leq_add2r addn0 geq_max Hl Hr.
rewrite addn0 mulnDr muln1 {2}(_ : 2 = 1 + 1) // addnA leq_add2r geq_max.
apply/andP; split.
- by apply: (leq_trans Hl); rewrite leq_add2l; case: eqP.
by apply: (leq_trans Hr); rewrite E leq_add2l; case: eqP.
Qed.

Corollary bound_bht t :
  rbt_inv t -> (height t)./2 <= bh t.
Proof.
case/andP=>Hch /eqP Hb.
rewrite -(doubleK (bh t)); apply: half_leq; rewrite -muln2 mulnC.
by move: (height_black_height Hch); rewrite Hb /= addn0.
Qed.

Lemma bh_size1 t :
  invch t -> (2 ^ (bh t) <= size1_tree t)%N.
Proof.
elim/invch_ind=>{t}//=l _ c r _ _ _ /eqP E _ _ Hl Hr.
case: c=>/=; first by rewrite addn0; apply/(leq_trans Hl)/leq_addr.
rewrite expnD expn1 muln2 -addnn; apply: leq_add=>//.
by rewrite E.
Qed.

Lemma rbt_log_height t :
  rbt_inv t -> ((height t)./2 <= up_log 2 (size1_tree t))%N.
Proof.
move=>/[dup] H; case/andP=>[H12 _]; apply: leq_trans; first by exact: bound_bht.
rewrite -(@leq_exp2l 2 _ _ (isT : 1%N < 2)).
by apply/(leq_trans (bh_size1 H12))/up_logP.
Qed.

End Invariants.

Arguments invch_ind [A P].

Section SetImplementation.
Context {disp : unit} {T : orderType disp}.

(* insertion *)

Equations baliL : rbt T -> T -> rbt T -> rbt T :=
baliL (Node (Node t1 (a, Red) t2) (b, Red)  t3                  ) c t4 => R (B t1 a t2) b (B t3 c t4);
baliL (Node  t1                   (a, Red) (Node t2 (b, Red) t3)) c t4 => R (B t1 a t2) b (B t3 c t4);
baliL        tl                                                   a tr => B tl a tr.

Equations baliR : rbt T -> T -> rbt T -> rbt T :=
baliR t1 a (Node       t2              (b, Red) (Node t3 (c, Red) t4)) => R (B t1 a t2) b (B t3 c t4);
baliR t1 a (Node (Node t2 (b, Red) t3) (c, Red)       t4)              => R (B t1 a t2) b (B t3 c t4);
baliR tl a             tr                                              => B tl a tr.

Fixpoint ins (x : T) (t : rbt T) : rbt T :=
  match t with
  | Leaf => R empty_a x empty_a
  | Node l (a, Black) r => match cmp x a with
                           | LT => baliL (ins x l) a r
                           | EQ => B l a r
                           | GT => baliR l a (ins x r)
                           end
  | Node l (a, Red) r => match cmp x a with
                         | LT => R (ins x l) a r
                         | EQ => R l a r
                         | GT => R l a (ins x r)
                         end
  end.

Definition insert x t := paint Black (ins x t).

(* a weaker version of invc *)

Definition invc2 (t : rbt T) := invc (paint Black t).

Lemma invc2I t : invc t -> invc2 t.
Proof. by rewrite /invc2; case: t=>//=l [a c] r /= /and3P [_ ->->]. Qed.

Lemma invc_baliL l a r :
  invc2 l -> invc r -> invc (baliL l a r).
Proof.
rewrite /invc2.
funelim (baliL l a r); simp baliL=>/= /[swap] ->; rewrite !andbT //.
- by case/and3P=>_->->.
- by case/andP; case/and3P=>_->->->.
by case/and4P; case/andP=>->->_->->.
Qed.

Lemma bh_baliL l a r :
  bh l == bh r -> bh (baliL l a r) == bh l + 1.
Proof. by funelim (baliL l a r); simp baliL=>//=; rewrite !addn0. Qed.

Lemma invh_baliL l a r :
  invh l -> invh r -> bh l == bh r ->
  invh (baliL l a r).
Proof.
funelim (baliL l a r); simp baliL=>/= /[swap] ->; rewrite !andbT ?addn0 //.
- by case/and4P=>/eqP<-/eqP<- ->->->; rewrite !eq_refl.
- by case/and4P; rewrite addn1.
- by case/andP=>->->->.
- by case/and3P=>/eqP->/and3P [/eqP->->->] ->->; rewrite !eq_refl.
- by case/and3P=>->/and3P[->->->]->->.
- by case/and3P; rewrite addn1.
- by case/and5P=>/eqP<-/and3P[/eqP->->->] /eqP<- ->->->; rewrite !eq_refl.
- by case/and5P=>->/and3P [->->->] ->->->->.
by case/and3P=>->/and3P[->->->]->->.
Qed.

Lemma invc_baliR l a r :
  invc l -> invc2 r -> invc (baliR l a r).
Proof.
rewrite /invc2; funelim (baliR l a r); simp baliR=>/=->//.
- by rewrite andbT; case/and3P=>_->->.
- by case/and4P=>-> _ ->->.
by case/and3P=>/and3P [_->->]->->.
Qed.

Lemma bh_baliR l a r :
  bh l == bh r -> bh (baliR l a r) == bh l + 1.
Proof. by funelim (baliR l a r); simp baliR=>//=; rewrite !addn0. Qed.

Lemma invh_baliR l a r :
  invh l -> invh r -> bh l == bh r ->
  invh (baliR l a r).
Proof.
funelim (baliR l a r); simp baliR=>/=->/=; rewrite ?andbT ?addn0 //.
- by case/and4P=>/eqP->/eqP<-->->/eqP->; rewrite !eq_refl.
- by case/and4P; rewrite addn1.
- by case/and5P=>/eqP->->/eqP->->->/eqP->; rewrite !eq_refl.
- by case/and4P; rewrite addn1.
- by case/and5P=>/eqP->/and3P [/eqP<- ->->] /eqP->->->/eqP->; rewrite !eq_refl.
- by case/and5P=>->/and3P [->->->] ->->->->.
by case/and3P=>->->->->.
Qed.

Lemma invc_ins x t :
  invc t ->
  invc2 (ins x t) && ((color t == Black) ==> invc (ins x t)).
Proof.
elim: t=>//= l IHl [a c] r IHr /and3P [E Hl Hr].
case/andP: (IHl Hl)=>{IHl} H2l Hil; case/andP: (IHr Hr)=>{IHr} H2r Hir.
case: c E=>/= [/andP [Hcll Hclr]|_].
- rewrite {}Hcll /= in Hil; rewrite {}Hclr /= in Hir.
  rewrite andbT; case: (cmp x a); rewrite /invc2 /=.
  - by rewrite Hil Hr.
  - by rewrite Hl Hr.
  by rewrite Hl Hir.
case: (cmp x a)=>/=.
- suff: invc (baliL (ins x l) a r) by move/[dup]/invc2I=>->->.
  by apply: invc_baliL.
- by rewrite /invc2 /= Hl Hr.
suff: invc (baliR l a (ins x r)) by move/[dup]/invc2I=>->->.
by apply: invc_baliR.
Qed.

Lemma invh_ins x t :
  invh t ->
  invh (ins x t) && (bh (ins x t) == bh t).
Proof.
elim: t=>//= l IHl [a c] r IHr /and3P [/eqP E Hl Hr].
case/andP: (IHl Hl)=>{IHl} H2l Hil; case/andP: (IHr Hr)=>{IHr} H2r Hir.
case: c=>/=; case: (cmp x a)=>/=; rewrite ?addn0.
- by rewrite -E Hil H2l Hr.
- by rewrite E Hl Hr eq_refl.
- by rewrite E eq_sym Hir Hl H2r eq_refl.
- apply/andP; split.
  - by apply: invh_baliL=>//; rewrite -E.
  by rewrite -(eqP Hil); apply: bh_baliL; rewrite -E.
- by rewrite E Hl Hr !eq_refl.
apply/andP; split.
- by apply: invh_baliR=>//; rewrite eq_sym E.
by apply: bh_baliR; rewrite eq_sym E.
Qed.

Corollary inv_insert x t : invch t -> invch (insert x t).
Proof.
rewrite /invch /insert; case/andP=>Hc Hh.
case/andP: (invc_ins x Hc); rewrite /invc2=>-> _ /=.
by rewrite invh_paint //; case/andP: (invh_ins x Hh).
Qed.

Corollary rbt_insert x t : rbt_inv t -> rbt_inv (insert x t).
Proof.
rewrite /rbt_inv /insert paint_black eq_refl andbT.
by case/andP=>/(inv_insert x).
Qed.

(* deletion by replacing *)

Equations baldL : rbt T -> T -> rbt T -> rbt T :=
baldL (Node t1 (a, Red) t2) b  t3                                          => R (B t1 a t2) b t3;
baldL       t1              a (Node t2                      (b, Black) t3) => baliR t1 a (R t2 b t3);
baldL       t1              a (Node (Node t2 (b, Black) t3) (c, Red)   t4) => R (B t1 a t2) b (baliR t3 c (paint Red t4));
baldL       tl              a       tr                                     => R tl a tr.

Equations baldR : rbt T -> T -> rbt T -> rbt T :=
baldR  t1                                        a (Node t2 (b, Red) t3) => R t1 a (B t2 b t3);
baldR (Node t1 (a, Black) t2)                    b  t3                   => baliL (R t1 a t2) b t3;
baldR (Node t1 (a, Red) (Node t2 (b, Black) t3)) c  t4                   => R (baliL (paint Red t1) a t2) b (B t3 c t4);
baldR       tl                                   a  tr                   => R tl a tr.

Fixpoint split_min (l : rbt T) (a : T) (r : rbt T) : T * rbt T :=
  if l is Node l' (a', c') r'
    then let: (x, m) := split_min l' a' r' in
         (x, if c' == Black then baldL m a r else R m a r)
    else (a, r).

Fixpoint del (x : T) (t : rbt T) : rbt T :=
  if t is Node l (a, _) r then
    match cmp x a with
    | LT => let: l' := del x l in
            if (l != empty_a) && (color l == Black) then baldL l' a r else R l' a r
    | EQ => if r is Node lr (ar, _) rr
            then let: (a', r') := split_min lr ar rr in
                 if color r == Black then baldR l a' r' else R l a' r'
            else l
    | GT => let: r' := del x r in
            if (r != empty_a) && (color r == Black) then baldR l a r' else R l a r'
    end
    else empty_a.

Definition delete x t := paint Black (del x t).

Lemma invh_baldL_invc l a r :
  invh l -> invh r -> bh l + 1 == bh r -> invc r ->
  invh (baldL l a r) && (bh (baldL l a r) == bh r).
Proof.
funelim (baldL l a r); simp baldL=>//=; rewrite ?addn0.
- move=>_ /and3P [E24 /and3P [E23 -> H3] H4].
  rewrite eqn_add2r=>E /and3P [/eqP Ec _ _]; rewrite E /= andbT.
  have H': bh t3 == bh (paint Red t4).
  - by rewrite bh_paint_red // -(eqP E23) -(eqP E24) addnK.
  apply/andP; split.
  - rewrite eq_sym; have {1}->: (0%N = bh t3) by rewrite -(eqP E23) (eqP E).
    by apply: bh_baliR.
  by apply: invh_baliR=>//; rewrite invh_paint.
- move=>_ H; rewrite eqn_add2r=>E /andP [Hc2 Hc3].
  apply/andP; split; first by apply: invh_baliR=>//=; rewrite addn0.
  have->: bh t2 = bh (Leaf (T * col)) by rewrite /= -(eqP E).
  by apply: bh_baliR=>/=; rewrite addn0.
- by move=>->->->.
- by move=>_ _; rewrite addn1.
- by move=>_ _; rewrite addn1.
- move=>-> /and3P [E24 /and3P [E23 -> H3] H4].
  rewrite eqn_add2r=>E /and3P [/eqP Ec _ _]; rewrite E /= andbT.
  have H': bh t3 == bh (paint Red t4).
  - by rewrite bh_paint_red // -(eqP E23) -(eqP E24) addnK.
  apply/andP; split.
  - by rewrite eq_sym (eqP E) (eqP E23); apply: bh_baliR.
  by apply: invh_baliR=>//; rewrite invh_paint.
move=>H H2; rewrite eqn_add2r=>E2; case/andP=>Hc2 Hc3.
apply/andP; split; first by apply: invh_baliR=>//=; rewrite addn0.
have->: bh t2 = bh (Node t (s0, Black) t0)by  rewrite /= -(eqP E2).
by apply: bh_baliR=>/=; rewrite addn0.
Qed.

Lemma invc2_baldL l a r :
  invc2 l -> invc r -> invc2 (baldL l a r).
Proof.
funelim (baldL l a r); simp baldL; rewrite /invc2 =>//=.
- move=>_ /and3P [_ /andP [-> H3] H4] /=.
  by apply: invc_baliR=>//; rewrite /invc2 paint2; apply/invc2I.
- by move=>_ H; apply/invc2I/invc_baliR.
- by move=>->->.
- by move=>->.
- by move=>->->.
- move=>-> /and3P [_ /andP [-> H3] H4] /=.
  by apply: invc_baliR=>//; rewrite /invc2 paint2; apply: invc2I.
by move=>H1 H2; apply/invc2I/invc_baliR.
Qed.

Lemma invc_baldL l a r :
  invc2 l -> invc r -> color r == Black -> invc (baldL l a r).
Proof.
funelim (baldL l a r); simp baldL; rewrite /invc2 =>//=.
- by move=>_ H _; apply: invc_baliR.
- by move=>->->->.
- by move=>->.
by move=>H1 H2 _; apply: invc_baliR.
Qed.

Lemma invh_baldR_invc l a r :
  invh l -> invh r -> bh l == bh r + 1 -> invc l ->
  invh (baldR l a r) && (bh (baldR l a r) == bh l).
Proof.
funelim (baldR l a r); simp baldR=>//=; rewrite ?andbT ?addn0.
- by case/andP=>->->; rewrite eq_refl.
- by move=>_ _ _; case/and5P; case/andP.
- case/and5P=>E12 H1 /eqP <- H2 -> _ E1 /and4P [/eqP Ec _ _ _].
  rewrite (eqP E12) eqn_add2r in E1.
  rewrite E1 /= andbT andbC (eqP E12) andbA andbb.
  have E' : bh (paint Red t1) = bh t2 by rewrite bh_paint_red // (eqP E12) addnK.
  apply/andP; split=>//.
  - by rewrite -E'; apply/bh_baliL; rewrite E'.
  apply: invh_baliL=>//; first by rewrite invh_paint.
  by rewrite E'.
- move=>H _; rewrite eqn_add2r=>E1 _.
  apply/andP; split; first by apply/invh_baliL=>//=; rewrite addn0.
  have->: bh t1 = bh (R t1 a t2) by rewrite /= addn0.
  by apply/bh_baliL=>/=; rewrite addn0.
- by move=>->->->; rewrite eq_refl.
- by move=>_ _; rewrite addn1.
- by case/andP=>/eqP->_ _; rewrite addn1.
- by move=>_ _ _; case/and5P; case/andP.
- case/and5P=>E12 H1 /eqP <- H2 -> -> E; case/and4P=>/eqP Ec Hc1 Hc2 Hc3.
  rewrite /= andbT andbC (eqP E12) andbA andbb.
  have E' : bh (paint Red t1) = bh t2 by rewrite bh_paint_red // (eqP E12) addnK.
  apply/and3P; split=>//.
  - by rewrite -E'; apply/bh_baliL; rewrite E'.
  - apply: invh_baliL=>//; first by rewrite invh_paint.
    by rewrite E'.
  by rewrite -(eqn_add2r 1) -(eqP E) eq_sym.
move=>H1 H2; rewrite eqn_add2r=>E _.
apply/andP; split; first by apply: invh_baliL=>//=; rewrite addn0.
have->: bh t1 = bh (R t1 a t2) by rewrite /= addn0.
by apply/bh_baliL=>/=; rewrite addn0.
Qed.

Lemma invc2_baldR l a r :
  invc l -> invc2 r -> invc2 (baldR l a r).
Proof.
funelim (baldR l a r); simp baldR=>//=; rewrite /invc2 /= ?andbT //.
- case/and4P=>_ H1 H2 -> _; rewrite andbT.
  by apply/invc_baliL=>//; rewrite /invc2 paint2; apply/invc2I.
- case/andP=>H1 H2 _.
  by apply/invc2I/invc_baliL=>//; rewrite /invc2 /= H1 H2.
- by move=>->->.
- by move=>->->.
- by case/and5P; case/andP.
- case/and4P=>E H1 H2 ->->; rewrite /= andbT.
  by apply/invc_baliL=>//; rewrite /invc2 paint2; apply/invc2I.
case/andP=>H1 H2 H0.
by apply/invc2I/invc_baliL=>//; rewrite /invc2 /= H1 H2.
Qed.

Lemma invc_baldR l a r :
  invc l -> invc2 r -> color l == Black ->
  invc (baldR l a r).
Proof.
funelim (baldR l a r); simp baldR=>//=; rewrite /invc2 /=.
- case/andP=>H1 H2 _ _.
  by apply/invc_baliL=>//; rewrite /invc2 /= H1 H2.
- by move=>->->->.
case/andP=>H1 H2 H0 _.
by apply/invc_baliL=>//; rewrite /invc2 /= H1 H2.
Qed.

Lemma split_min_invc l a r x t :
  split_min l a r = (x, t) ->
  invc l -> invc r ->
  invc2 t && ((color l == Black) && (color r == Black) ==> invc t).
Proof.
elim: l a r t=>/= [|l' IHl [a' c'] r' _] a r t.
- by case =>_->_ /[dup]/invc2I->->/=; apply: implybT.
case Hsm: (split_min l' a' r')=>[x0 m][E0 Et]; rewrite {x0}E0 in Hsm.
case/and3P=>I Hl' Hr' Hr; case/andP: (IHl _ _ _ Hsm Hl' Hr')=>H2m /implyP Hm.
rewrite /invc2; case: c' Et I=><- /=.
- by move/Hm=>->; rewrite Hr.
move=>_; apply/andP; split; first by apply/invc2_baldL.
by apply/implyP=>Hcr; apply/invc_baldL.
Qed.

Lemma split_min_invh l a r x t :
  split_min l a r = (x, t) ->
  invc l -> invc r -> invh l -> invh r ->
  bh l == bh r ->
  invh t && (bh t == bh l).
Proof.
elim: l a r t=>/= [|l' IHl [a' c'] r' _] a r t.
- by case=>_->_ _ _ ->; rewrite eq_sym.
case Hsm: (split_min l' a' r')=>[x0 m][E0 Et]; rewrite {x0}E0 in Hsm.
case/and3P=>_ Hcl' Hcr' Hcr; case/and3P=>E' Hhl' Hhr' Hhr.
case/andP: (IHl _ _ _ Hsm Hcl' Hcr' Hhl' Hhr' E'); rewrite /invch=>Hhm Em.
case: c' Et=><-/=.
- by rewrite !addn0=>/eqP <-; rewrite Em Hhm Hhr.
move/eqP=>E''; rewrite E''.
by apply: invh_baldL_invc=>//; rewrite -E'' eqn_add2r.
Qed.

Lemma invc_del x t :
  invc t ->
  invc2 (del x t) && ((color t == Red) ==> invc (del x t)).
Proof.
elim: t=>//= l IHl [a c] r IHr /and3P [E Hl Hr].
case/andP: (IHl Hl)=>{IHl} H2l Hil; case/andP: (IHr Hr)=>{IHr} H2r Hir.
rewrite /invc2 /=; case: c E=>/= [/andP [Hcll Hclr]|_]; case: (cmp x a).
- case: eqP=>El /=; first by rewrite El /= Hclr Hr.
  rewrite Hcll; apply/andP; split; last by apply: invc_baldL.
  - by apply/invc2I/invc_baldL.
- case: {H2r Hir} r Hr Hclr=>/=.
  - by move=>_ _; apply/andP; split=>//; apply/invc2I.
  move=>lr [ar cr] rr /and3P [_ Hclr Hcrr] ->.
  case Hsm: (split_min lr ar rr)=>[a' r'] /=.
  case/andP: (split_min_invc Hsm Hclr Hcrr)=>H2r' Hr'.
  apply/andP; split; last by apply: invc_baldR.
  by apply/invc2I/invc_baldR.
- case: eqP=>Er /=; first by rewrite Er /= Hcll Hl.
  rewrite Hclr; apply/andP; split; last by apply: invc_baldR.
  by apply/invc2I/invc_baldR.
- case: eqP=>El /=; first by rewrite El /= Hr.
  rewrite andbT; case Hcl: (color l)=>/=.
  - by move: Hil; rewrite Hcl /= Hr => ->.
  by apply: invc2_baldL.
- rewrite andbT; case: {H2r Hir} r Hr=>/=.
  - by move=>_; apply: invc2I.
  move=>lr [ar cr] rr /and3P [E Hclr Hcrr].
  case Hsm: (split_min lr ar rr)=>[a' r'] /=.
  case/andP: (split_min_invc Hsm Hclr Hcrr)=>H2r' /implyP Hr'.
  case: cr E=>/=.
  - by move/Hr'=>->; rewrite Hl.
  by move=>_; apply: invc2_baldR.
case: eqP=>Er /=; first by rewrite Er /= Hl.
rewrite andbT; case Hcr: (color r)=>/=.
- by move: Hir; rewrite Hcr /= Hl => ->.
by apply: invc2_baldR.
Qed.

Lemma invh_del x t :
  invch t ->
  invh (del x t) && (bh (del x t) == bh t - (color t == Black)).
Proof.
elim/invch_ind=>{t}//= l a c r I Hcl Hcr /eqP E Hhl Hhr /andP [Hhdl Icl] /andP [Hhdr Icr].
rewrite addnK; case: (cmp x a)=>/=.
- case: eqP=>El /=; first by rewrite El /= in E *; rewrite -E Hhr.
  move: Icl; case Cl: (color l)=>/=.
  - by rewrite subn0 =>/eqP->; rewrite addn0 E Hhdl Hhr eq_refl.
  rewrite -(eqn_add2r 1) subnK; last by apply: bh_gt0.
  by rewrite E=>Ed; apply: invh_baldL_invc.
- case: {I Hhdr Icr}r E Hcr Hhr; first by rewrite Hhl eq_refl.
  move=>lr [ar cr] rr /= E /and3P [Ecr Hclr Hcrr] /and3P [Ebr Hhlr Hhrr].
  case Hsm: (split_min lr ar rr)=>[a' r'] /=.
  case/andP: (split_min_invh Hsm Hclr Hcrr Hhlr Hhrr Ebr)=>Hhr' E'.
  move: E; case Ccr: cr=>/=.
  - by rewrite !addn0=>->; rewrite Hhl Hhr' eq_refl eq_sym /= !andbT.
  by move=>E; apply: invh_baldR_invc=>//; rewrite E eqn_add2r eq_sym.
case: eqP=>Er /=; first by rewrite Er /= in E *; rewrite E Hhl.
move: Icr; case Cr: (color r)=>/=.
- by rewrite subn0 =>/eqP->; rewrite addn0 E Hhdr Hhl eq_refl.
rewrite -(eqn_add2r 1) subnK; last by apply: bh_gt0.
by rewrite -E eq_sym=>Ed; apply: invh_baldR_invc.
Qed.

Corollary inv_delete x t : invch t -> invch (delete x t).
Proof.
move/[dup]=>H; rewrite /invch /delete; case/andP=>Hc _.
case/andP: (invc_del x Hc); rewrite /invc2=>-> _ /=.
by rewrite invh_paint //; case/andP: (invh_del x H).
Qed.

Corollary rbt_delete x t : rbt_inv t -> rbt_inv (delete x t).
Proof.
rewrite /rbt_inv /delete paint_black eq_refl andbT.
by case/andP=>/(inv_delete x).
Qed.

(* correctness via sorted lists *)

Lemma inorder_paint c (t : rbt T) : inorder_a (paint c t) = inorder_a t.
Proof. by case: t=>//=l [a c0] r. Qed.

Lemma inorder_baliL l a r : inorder_a (baliL l a r) = inorder_a l ++ a :: inorder_a r.
Proof.
by funelim (baliL l a r); simp baliL=>//=; rewrite -!catA // !cat_cons -catA.
Qed.

Lemma inorder_baliR l x r : inorder_a (baliR l x r) = inorder_a l ++ x :: inorder_a r.
Proof.
by funelim (baliR l x r); simp baliR=>//=; rewrite -!catA.
Qed.

Lemma inorder_ins x t :
  bst_list_a t -> inorder_a (ins x t) = ins_list x (inorder_a t).
Proof.
rewrite /bst_list_a; elim: t=>//= l IHl [a c] r IHr.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite inslist_sorted_cat_cons_cat //.
case Hc: (cmp x a)=>/=.
- move/cmp_lt: Hc=>->; case: c=>/=.
  - by rewrite IHl // (cat_sorted2 H1).
  by rewrite inorder_baliL IHl // (cat_sorted2 H1).
- by move/cmp_eq: Hc=>/eqP ->; rewrite ltxx eq_refl; case: c.
move/cmp_gt: Hc=>/[dup] Hx.
rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
rewrite -cat1s in H2.
case: c=>/=.
- by rewrite IHr // (cat_sorted2 H2).
by rewrite inorder_baliR IHr // (cat_sorted2 H2).
Qed.

Corollary inorder_insert x t :
  bst_list_a t ->
  inorder_a (insert x t) = ins_list x (inorder_a t).
Proof.
rewrite /insert => H.
by rewrite inorder_paint; apply: inorder_ins.
Qed.

Lemma inorder_baldL l a r :
  inorder_a (baldL l a r) = inorder_a l ++ a :: inorder_a r.
Proof.
by funelim (baldL l a r); simp baldL=>//=;
rewrite inorder_baliR //= inorder_paint -!catA.
Qed.

Lemma inorder_baldR l a r :
  inorder_a (baldR l a r) = inorder_a l ++ a :: inorder_a r.
Proof.
by funelim (baldR l a r); simp baldR=>//=;
rewrite inorder_baliL //= inorder_paint -!catA !cat_cons -!catA.
Qed.

Lemma inorder_split_min (l r t : rbt T) a x :
  split_min l a r = (x, t) ->
  x :: inorder_a t = inorder_a l ++ a :: inorder_a r.
Proof.
elim: l a r t=>/= [|ll IHl [al cl] rl _] a r t; first by case=>->->.
case Hsm: (split_min ll al rl)=>[x0 l'][Hx <-] /=.
rewrite {}Hx in Hsm; case: cl=>/=.
- by rewrite -cat_cons (IHl _ _ _ Hsm).
by rewrite inorder_baldL -cat_cons (IHl _ _ _ Hsm).
Qed.

Lemma inorder_del x t :
  bst_list_a t -> inorder_a (del x t) = del_list x (inorder_a t).
Proof.
rewrite /bst_list_a /=; elim: t=>//=l IHl [a c] r IHr /[dup] H.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite dellist_sorted_cat_cons_cat //.
case Hc: (cmp x a)=>/=.
- move/cmp_lt: Hc=>->; case: ifP=>/= _.
  - by rewrite inorder_baldL IHl // (cat_sorted2 H1).
  by rewrite IHl // (cat_sorted2 H1).
- move/cmp_eq: Hc=>/eqP ->; rewrite ltxx eq_refl.
  case: {IHr H H2}r=>//=; first by rewrite cats0.
  move=>lr [ar cr] rr.
  case Hsm: (split_min lr ar rr)=>[a' r'] /=.
  move: (inorder_split_min Hsm)=>Esm.
  case: cr=>/=; first by rewrite Esm.
  by rewrite inorder_baldR Esm.
move/cmp_gt: Hc=>/[dup] Hx.
rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
rewrite -cat1s in H2.
case: ifP=>/= _.
- by rewrite inorder_baldR IHr // (cat_sorted2 H2).
by rewrite IHr // (cat_sorted2 H2).
Qed.

Corollary inorder_delete x t :
  bst_list_a t ->
  inorder_a (delete x t) = del_list x (inorder_a t).
Proof.
rewrite /delete => H.
by rewrite inorder_paint; apply: inorder_del.
Qed.

(* corollaries *)

Definition invariant (t : rbt T) := bst_list_a t && rbt_inv t.

Lemma invariant_empty : invariant empty_a.
Proof. by []. Qed.

Corollary invariant_insert x (t : rbt T) :
  invariant t -> invariant (insert x t).
Proof.
rewrite /invariant /bst_list_a => /andP [H1 H2].
apply/andP; split; last by apply: rbt_insert.
by rewrite inorder_insert //; apply: ins_list_sorted.
Qed.

Corollary inorder_insert_list x (t : rbt T) :
  invariant t ->
  perm_eq (inorder_a (insert x t))
          (if x \in inorder_a t then inorder_a t else x :: inorder_a t).
Proof.
rewrite /invariant /bst_list_a => /andP [H1 _].
by rewrite inorder_insert //; apply: inorder_ins_list.
Qed.

Corollary invariant_delete x (t : rbt T) :
  invariant t -> invariant (delete x t).
Proof.
rewrite /invariant /bst_list_a => /andP [H1 H2].
apply/andP; split; last by apply: rbt_delete.
by rewrite inorder_delete //; apply: del_list_sorted.
Qed.

Corollary inorder_delete_list x (t : rbt T) :
  invariant t ->
  perm_eq (inorder_a (delete x t))
          (filter (predC1 x) (inorder_a t)).
Proof.
rewrite /invariant /bst_list_a => /andP [H1 H2].
by rewrite inorder_delete //; apply: inorder_del_list.
Qed.

Corollary inv_isin_list x (t : rbt T) :
  invariant t ->
  isin_a t x = (x \in inorder_a t).
Proof. by rewrite /invariant => /andP [H1 _]; apply: inorder_isin_list_a. Qed.

Definition SetRBT :=
  @ASetM.make _ _ (rbt T)
    empty_a insert delete isin_a
    inorder_a invariant
    invariant_empty erefl
    invariant_insert inorder_insert_list
    invariant_delete inorder_delete_list
    inv_isin_list.

(* deletion by joining *)

Equations? join (l r : rbt T) : rbt T by wf (size_tree l + size_tree r) lt :=
join Leaf t => t;
join t Leaf => t;
join (Node t1 (a, Red) t2) (Node t3 (c, Red) t4) =>
  match join t2 t3 with
  | Node u2 (b, Red) u3 => R (R t1 a u2) b (R u3 c t4)
  | t23 => R t1 a (R t23 c t4)
  end;
join (Node t1 (a, Black) t2) (Node t3 (c, Black) t4) =>
  match join t2 t3 with
  | Node u2 (b, Red) u3 => R (B t1 a u2) b (B u3 c t4)
  | t23 => baldL t1 a (B t23 c t4)
  end;
join t1 (Node t2 (a, Red) t3) => R (join t1 t2) a t3;
join (Node t1 (a, Red) t2) t3 => R t1 a (join t2 t3).
Proof.
all: apply: ssrnat.ltP.
- rewrite !addnA -addn1 leq_add2r.
  nat_norm; rewrite [X in (_<=X.+1)%N]addnC addnA -addnA -addnS.
  by apply: leq_addr.
- rewrite ltn_add2r -addn1 leq_add2r.
  by apply: leq_addl.
- rewrite !addnA -addn1 leq_add2r.
  by apply: leq_addr.
rewrite !addnA -addn1 leq_add2r.
nat_norm; rewrite [X in (_<=X.+1)%N]addnC addnA -addnA -addnS.
by apply: leq_addr.
Qed.

Fixpoint del_j (x : T) (t : rbt T) : rbt T :=
  if t is Node l (a, _) r then
    match cmp x a with
    | LT => if (l != empty_a) && (color l == Black)
              then baldL (del_j x l) a r
              else R (del_j x l) a r
    | EQ => join l r
    | GT => if (r != empty_a) && (color r == Black)
              then baldR l a (del_j x r)
              else R l a (del_j x r)
    end
    else empty_a.

Definition delete_j x t := paint Black (del_j x t).

Lemma invc_join l r :
  invc l -> invc r ->
  invc2 (join l r) &&
      ((color l == Black) && (color r == Black) ==> invc (join l r)).
Proof.
funelim (join l r); simp join=>/=.
- by move=>_ /[dup] /invc2I ->->/=; apply: implybT.
- case: p=>a c; rewrite /invc2 /= =>/and3P [->->->] _; apply: implybT.
- rewrite -!andbA andbT.
  case/and4P=>Hc1 Hc2 H1 H2; case/and4P=>Hc3 Hc4 H3 H4.
  rewrite /invc2; case Ej: (join t2 t3)=>[|l [x c'] r]/=.
  - by rewrite H1 Hc4 H4.
  move: (H H2 H3); rewrite /invc2 Ej /= -!andbA Hc2 Hc3 /=.
  case/and5P=>Hl Hr + _ _; case: {Ej} c'=>/=; rewrite H1 Hc4 Hl Hr H4 //.
  by case/andP=>->->; rewrite Hc1.
- rewrite -andbA; rewrite /invc2 /= eq_refl !andbT in H *.
  case/and4P=>_ Hc2 -> H2 H0 /=.
  by case/andP: (H H2 H0)=>_ /implyP; apply.
- move=>H0; rewrite -andbA; rewrite /invc2 /= andbT in H *.
  case/and4P=>Hc2 _ H2 ->; rewrite andbT.
  by case/andP: (H H0 H2)=>_ /implyP; apply.
case/andP=>H1 H2; case/andP=>H3 H4.
case Ej: (join t2 t3)=>[|l [x c'] r]/=.
- suff: invc (baldL t1 a (B (Leaf (T * col)) c t4)) by move/[dup]/invc2I=>->->.
  by apply: invc_baldL=>//=; apply/invc2I.
rewrite Ej /invc2 /= in H.
case/andP: (H H2 H3); case/andP=>Hl Hr.
case: {Ej H}c'=>/=.
- by rewrite /invc2 /= H1 Hl Hr H4.
move=>_; suff: invc (baldL t1 a (B (Node l (x, Black) r) c t4)) by move/[dup]/invc2I=>->->.
apply: invc_baldL=>//=; first by apply/invc2I.
by rewrite Hl Hr H4.
Qed.

Lemma invh_baldL_black l a r :
  invh l -> invh r -> bh l + 1 == bh r -> color r = Black ->
  invh (baldL l a r) && (bh (baldL l a r) == bh r).
Proof.
funelim (baldL l a r); simp baldL=>//=; rewrite ?addn0.
- move=>_ H; rewrite eqn_add2r=> E _.
  apply/andP; split; first by apply: invh_baliR=>//=; rewrite addn0.
  have-> : bh t2 = bh (@Leaf (T*col)) by rewrite -(eqP E).
  by apply: bh_baliR=>/=; rewrite addn0.
- by move=>->->->.
- by move=>_ _; rewrite addn1.
move=>H1 H2; rewrite eqn_add2r=>E _.
apply/andP; split; first by apply: invh_baliR=>//=; rewrite addn0.
have->: bh t2 = bh (Node t (s0, Black) t0) by rewrite -(eqP E).
by apply: bh_baliR=>/=; rewrite addn0.
Qed.

Lemma invh_join l r :
  invh l -> invh r -> bh l == bh r ->
  invh (join l r) && (bh (join l r) == bh l).
Proof.
funelim (join l r); simp join=>/=.
- by move=>_->; rewrite eq_sym.
- by case: p=>_ c->; rewrite eq_refl.
- case/and3P=>/eqP E12 H1 H2; case/and3P=>/eqP E34 H3 H4.
  rewrite eqn_add2r addn0=>E13.
  have E23: bh t2 == bh t3 by rewrite -E12.
  case/andP: (H H2 H3 E23); case: (join t2 t3)=>[|l [x c'] r]/=.
  - by rewrite E12 -E34 -(eqP E23) H1 H4=>_ /eqP <-.
  case/and3P=>/eqP E Hl Hr; case: c'=>/=; rewrite !addn0 H1 Hl Hr H4 /= !andbT E.
  - by rewrite -E34 -(eqP E23) E12; move/eqP=>->; rewrite eq_refl.
  by move/eqP->; rewrite E12 -E34 -(eqP E23) !eq_refl.
- case/and3P=>/eqP E12 H1 H2 H03.
  rewrite addn0 H1 eq_refl /= andbT =>E10.
  have E20: bh t2 == bh t0 + 1 by rewrite -E12.
  by case/andP: (H H2 H03 E20)=>->/eqP->; rewrite E12 eq_refl.
- move=>H0; case/and3P=>/eqP E23 H2 H3.
  rewrite !addn0 H3 -E23 andbC=>E2; rewrite (eqP E2) andbA andbb andbT.
  by case/andP: (H H0 H2 E2)=>->/eqP->/=; rewrite andbT.
case/and3P=>/eqP E12 H1 H2; case/and3P=>/eqP E34 H3 H4.
rewrite eqn_add2r=>E13.
have E23: bh t2 == bh t3 by rewrite -E12.
case/andP: (H H2 H3 E23); case: (join t2 t3)=>[|l [x c'] r]/=.
- move=>_ E2'.
  have->: bh t1 + 1 = bh (B (Leaf (T * col)) c t4) by rewrite /= E12 -(eqP E2').
  apply/invh_baldL_black=>//=.
  - by rewrite H4 andbT -E34 -(eqP E23).
  by rewrite eqn_add2r E12 eq_sym.
case/and3P=>/eqP E Hl Hr; case: c'=>/=.
- rewrite !addn0 H1 Hl Hr H4 /= !andbT E => /eqP ->.
  by rewrite E12 -E34 -(eqP E23) !eq_refl.
move=>E2.
have->: bh t1 + 1 = bh (B (Node l (x, Black) r) c t4) by rewrite /= (eqP E2) E12.
apply/invh_baldL_black=>//=.
- by rewrite (eqP E2) -E34 E23 E Hl Hr H4 eq_refl.
by rewrite (eqP E2) E12.
Qed.

Lemma invc_del_j x t :
  invc t ->
  invc2 (del_j x t) && ((color t == Red) ==> invc (del_j x t)).
Proof.
elim: t=>//= l IHl [a c] r IHr /and3P [E Hl Hr].
case/andP: (IHl Hl)=>{IHl} H2l Hil; case/andP: (IHr Hr)=>{IHr} H2r Hir.
rewrite /invc2 /=; case: c E=>/= [/andP [Hcll Hclr]|_]; case: (cmp x a).
- case: eqP=>El /=; first by rewrite El /= Hclr Hr.
  rewrite Hcll; apply/andP; split; last by apply: invc_baldL.
  - by apply/invc2I/invc_baldL.
- by case/andP: (invc_join Hl Hr); rewrite /invc2 Hcll Hclr =>->.
- case: eqP=>Er /=; first by rewrite Er /= Hcll Hl.
  rewrite Hclr; apply/andP; split; last by apply: invc_baldR.
  by apply/invc2I/invc_baldR.
- case: eqP=>El /=; first by rewrite El /= Hr.
  rewrite andbT; case Hcl: (color l)=>/=.
  - by move: Hil; rewrite Hcl /= Hr => ->.
  by apply: invc2_baldL.
- by rewrite andbT; case/andP: (invc_join Hl Hr).
case: eqP=>Er /=; first by rewrite Er /= Hl.
rewrite andbT; case Hcr: (color r)=>/=.
- by move: Hir; rewrite Hcr /= Hl => ->.
by apply: invc2_baldR.
Qed.

Lemma invh_del_j x t :
  invch t ->
  invh (del_j x t) && (bh (del_j x t) == bh t - (color t == Black)).
Proof.
elim/invch_ind=>{t}//= l a c r I Hcl Hcr /eqP E Hhl Hhr /andP [Hhdl Icl] /andP [Hhdr Icr].
rewrite addnK; case: (cmp x a)=>/=.
- case: eqP=>El /=; first by rewrite El /= in E *; rewrite -E Hhr.
  move: Icl; case Cl: (color l)=>/=.
  - by rewrite subn0 =>/eqP->; rewrite addn0 E Hhdl Hhr eq_refl.
  rewrite -(eqn_add2r 1) subnK; last by apply: bh_gt0.
  by rewrite E=>Ed; apply: invh_baldL_invc.
- by apply: invh_join=>//; rewrite E eq_refl.
case: eqP=>Er /=; first by rewrite Er /= in E *; rewrite E Hhl.
move: Icr; case Cr: (color r)=>/=.
- by rewrite subn0 =>/eqP->; rewrite addn0 E Hhdr Hhl eq_refl.
rewrite -(eqn_add2r 1) subnK; last by apply: bh_gt0.
by rewrite -E eq_sym=>Ed; apply: invh_baldR_invc.
Qed.

Corollary inv_delete_j x t : invch t -> invch (delete_j x t).
Proof.
move/[dup]=>H; rewrite /invch /delete_j; case/andP=>Hc _.
case/andP: (invc_del_j x Hc); rewrite /invc2=>-> _ /=.
by rewrite invh_paint //; case/andP: (invh_del_j x H).
Qed.

Corollary rbt_delete_j x t : rbt_inv t -> rbt_inv (delete_j x t).
Proof.
rewrite /rbt_inv /delete_j paint_black eq_refl andbT.
by case/andP=>/(inv_delete_j x).
Qed.

Lemma inorder_join l r :
  inorder_a (join l r) = inorder_a l ++ inorder_a r.
Proof.
funelim (join l r); simp join=>//=.
- by rewrite cats0.
- case H23: (join t2 t3)=>[|l' [x c'] r']/=; rewrite {}H23 /= in H.
  - by rewrite -!catA cat_cons catA -H.
  case: c'=>/=.
  - by rewrite -!catA cat_cons -(cat_cons x) catA H -!catA cat_cons.
  by rewrite H -!catA cat_cons.
- by rewrite H /= -!catA cat_cons.
- by rewrite H /= -catA.
case H23: (join t2 t3)=>[|l' [x c'] r']/=; rewrite {}H23 /= in H.
- by rewrite inorder_baldL /= -!catA cat_cons catA -H.
case: c'=>/=.
- by rewrite -!catA cat_cons -(cat_cons x) catA H -!catA cat_cons.
by rewrite inorder_baldL /= H -!catA cat_cons.
Qed.

Lemma inorder_del_j x t :
  bst_list_a t -> inorder_a (del_j x t) = del_list x (inorder_a t).
Proof.
rewrite /bst_list_a /=; elim: t=>//=l IHl [a c] r IHr /[dup] H.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite dellist_sorted_cat_cons_cat //.
case Hc: (cmp x a)=>/=.
- move/cmp_lt: Hc=>->; case: ifP=>/= _.
  - by rewrite inorder_baldL IHl // (cat_sorted2 H1).
  by rewrite IHl // (cat_sorted2 H1).
- move/cmp_eq: Hc=>/eqP ->; rewrite ltxx eq_refl.
  by rewrite inorder_join.
move/cmp_gt: Hc=>/[dup] Hx.
rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
rewrite -cat1s in H2.
case: ifP=>/= _.
- by rewrite inorder_baldR IHr // (cat_sorted2 H2).
by rewrite IHr // (cat_sorted2 H2).
Qed.

Corollary inorder_delete_j x t :
  bst_list_a t ->
  inorder_a (delete_j x t) = del_list x (inorder_a t).
Proof.
rewrite /delete_j => H.
by rewrite inorder_paint; apply: inorder_del_j.
Qed.

Corollary inorder_delete_j_list x (t : rbt T) :
  invariant t ->
  perm_eq (inorder_a (delete_j x t))
          (filter (predC1 x) (inorder_a t)).
Proof.
rewrite /invariant /bst_list_a => /andP [H1 H2].
by rewrite inorder_delete_j //; apply: inorder_del_list.
Qed.

Corollary invariant_delete_j x (t : rbt T) :
  invariant t -> invariant (delete_j x t).
Proof.
rewrite /invariant /bst_list_a => /andP [H1 H2].
apply/andP; split; last by apply: rbt_delete_j.
by rewrite inorder_delete_j //; apply: del_list_sorted.
Qed.

Definition SetRBTj :=
  @ASetM.make _ _ (rbt T)
    empty_a insert delete_j isin_a
    inorder_a invariant
    invariant_empty erefl
    invariant_insert inorder_insert_list
    invariant_delete_j inorder_delete_j_list
    inv_isin_list.

End SetImplementation.

Section Exercises.

(* Exercise 8.1 *)

Lemma log_height_inv {A} (t : rbt A) :
  invch t ->
  (height t)./2 <= up_log 2 (size1_tree t) + 1.
Proof.
Admitted.

(* Exercise 8.2 *)

Fixpoint bhs {A} (t : rbt A) : seq nat :=
  if t is Node l (_,c) r then
    let: H := bhs l ++ bhs r in
    if c == Black then map S H else H
  else [::0].

Lemma same_black {T : eqType} (t : rbt T) : invh t <-> undup (bhs t) = [::bh t].
Proof.
Admitted.

(* Exercise 8.3 *)

Definition rbt_of_list {A} (xs : seq A) : rbt A :=
  Leaf (A*col).  (* FIXME *)

Lemma inorder_rol {A} (xs : seq A) : inorder_a (rbt_of_list xs) = xs.
Proof.
Admitted.

Lemma rbt_rol {T : eqType} (xs : seq T) : rbt_inv (rbt_of_list xs).
Proof.
Admitted.

End Exercises.
