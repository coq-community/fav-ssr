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
  if t is Node l (a, _) r then Node l (a,c) r else @Leaf (A * col).

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
  if t is Node l (_, c) _
    then if c == Black then bh l + 1 else bh l
    else 0.

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
by rewrite addnK.
Qed.

Definition rbt_inv (t : rbt A) : bool :=
  [&& invc t, invh t & color t == Black].

(* Logarithmic Height *)

Lemma height_black_height t :
  invc t -> invh t -> (height t <= 2 * bh t + (color t == Red))%N.
Proof.
elim: t=>//=l IHl [a c] r IHr /and3P [H1 Hcl Hcr] /and3P [/eqP E Hhl Hhr].
move: (IHl Hcl Hhl)=>Hl; move: (IHr Hcr Hhr)=>Hr.
case: c H1=>/=.
- case/andP=>/eqP Hcll /eqP Hclr; rewrite leq_add2r.
  rewrite Hcll E /= addn0 in Hl *; rewrite Hclr /= addn0 in Hr.
  by rewrite geq_max Hl Hr.
move=>_; rewrite addn0 mulnDr muln1 {2}(_ : 2 = 1 + 1) // addnA leq_add2r.
rewrite geq_max; apply/andP; split.
- by apply: (leq_trans Hl); rewrite leq_add2l; case: eqP.
by apply: (leq_trans Hr); rewrite E leq_add2l; case: eqP.
Qed.

Corollary bound_bht t :
  rbt_inv t -> (height t)./2 <= bh t.
Proof.
rewrite /rbt_inv; case/and3P=>Hc Hh /eqP Hb.
rewrite -(doubleK (bh t)); apply: half_leq; rewrite -muln2 mulnC.
by move: (height_black_height Hc Hh); rewrite Hb /= addn0.
Qed.

Lemma bh_size1 t :
  invc t -> invh t -> 2 ^ (bh t) <= size1_tree t.
Proof.
elim: t=>//=l IHl [a c] r IHr /and3P [H1 Hcl Hcr] /and3P [/eqP E Hhl Hhr].
move: (IHl Hcl Hhl)=>Hl; move: (IHr Hcr Hhr)=>Hr.
case: {H1}c=>/=.
- by apply: (leq_trans Hl); apply: leq_addr.
rewrite expnD expn1 muln2 -addnn.
apply: leq_add=>//.
by rewrite E.
Qed.

Lemma rbt_log_height t :
  rbt_inv t -> ((height t)./2 <= up_log 2 (size1_tree t))%N.
Proof.
move=>/[dup] H /and3P [H1 H2 _]; apply: leq_trans; first by exact: bound_bht.
rewrite -(@leq_exp2l 2 _ _ (isT : 1%N < 2)).
by apply/(leq_trans (bh_size1 H1 H2))/up_logP.
Qed.

End Invariants.

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

Lemma inv_baliL l a r :
  invh l -> invh r -> invc2 l -> invc r -> bh l == bh r ->
  [&& invc (baliL l a r), invh (baliL l a r) & (bh (baliL l a r) == bh l + 1)].
Proof.
move=>Hhl Hhr Hcl Hcr E.
funelim (baliL l a r); simp baliL=>/=.
- (* l = Leaf *)
  by rewrite Hhr Hcr E eq_refl.
- (* l = R Leaf s0 Leaf *)
  by rewrite Hhr Hcr E eq_refl.
- (* l = R Leaf a (R t2 b t3) *)
  rewrite /= in Hhl E; rewrite /invc2 /= in Hcl.
  case/and4P: Hhl=>/eqP E2 /eqP <- ->->.
  case/and3P: Hcl=>_ ->->.
  by rewrite -E2 Hhr Hcr E !eq_refl.
- (* l = R Leaf s0 (B t s1 t0) *)
  rewrite /= in Hhl E; rewrite /invc2 /= in Hcl.
  case/and4P: Hhl=>/eqP <- /eqP <- ->->.
  case/andP: Hcl=>->->.
  by rewrite E Hhr Hcr !eq_refl.
- (* l = B Leaf s0 t0 *)
  rewrite /= in Hhl E; rewrite /invc2 /= in Hcl.
  case/andP: Hhl=>->->.
  by rewrite Hcl Hcr Hhr E eq_refl.
- (* l = R (R t1 a t2) b t3 *)
  rewrite /= -!andbA in Hhl E; rewrite /invc2 /= -!andbA in Hcl.
  case/and5P: Hhl=>/eqP <-; rewrite E=>->->->->.
  case/and5P: Hcl=>_ _ ->->->.
  by rewrite Hhr Hcr eq_refl.
- (* l = B (R t s0 t1) s1 t0 *)
  rewrite /= -!andbA in Hhl E; rewrite /invc2 /= -!andbA in Hcl.
  case/and5P: Hhl=>->->->->->.
  case/and5P: Hcl=>->->->->->.
  by rewrite E Hhr Hcr eq_refl.
- (* l = R (B t s0 t1) s1 Leaf *)
  rewrite /= -!andbA in Hhl E; rewrite /invc2 /= -!andbA in Hcl.
  case/and5P: Hhl=>->->->->_.
  case/and3P: Hcl=>->->_.
  by rewrite E Hhr Hcr eq_refl.
- (* l = R (B t s0 t1) a (R t2 b t3) *)
  rewrite /= -!andbA in Hhl E; rewrite /invc2 /= -!andbA in Hcl.
  move/eqP: E=><-.
  case/and7P: Hhl=>/eqP ->->->->/eqP->->->.
  case/and6P: Hcl=>->->_ _ ->->.
  by rewrite Hhr Hcr !eq_refl.
- (* l = R (B t s0 t1) s1 (B t0 s2 t2) *)
  rewrite /= -!andbA in Hhl E; rewrite /invc2 /= -!andbA in Hcl.
  case/and7P: Hhl=>->->->->->->->.
  case/and4P: Hcl=>->->->->.
  by rewrite E Hhr Hcr eq_refl.
- (* l = B (B t s0 t1) s1 t0 *)
  rewrite /= -!andbA in Hhl E; rewrite /invc2 /= -!andbA in Hcl.
  case/and5P: Hhl=>->->->->->.
  case/and3P: Hcl=>->->->.
  by rewrite E Hhr Hcr eq_refl.
Qed.

Lemma inv_baliR l a r :
  invh l -> invh r -> invc l -> invc2 r -> bh l == bh r ->
  [&& invc (baliR l a r), invh (baliR l a r) & (bh (baliR l a r) == bh l + 1)].
Proof.
move=>Hhl Hhr Hcl Hcr E.
funelim (baliR l a r); simp baliR=>/=.
- (* l = Leaf *)
   by rewrite Hhl Hcl E eq_refl.
- (* l = R Leaf s0 Leaf *)
  by rewrite Hhl Hcl E eq_refl.
- (* l = R (R t2 b t3) c Leaf *)
  rewrite /= -!andbA in Hhr E; rewrite /invc2 /= -!andbA in Hcr.
  case/and5P: Hhr=>/eqP E2 /eqP <- ->->_.
  case/and5P: Hcr=>_ _->->_.
  by move/eqP: E=>->; rewrite E2 Hhl Hcl !eq_refl.
- (* l = R (B t s1 t0) s0 Leaf *)
  rewrite /= -!andbA in Hhr E; rewrite /invc2 /= -!andbA in Hcr.
  case/and5P: Hhr=>->->->->_.
  case/and3P: Hcr=>->->_.
  by rewrite E Hhl Hcl eq_refl.
- (* l = R t2 b (R t3 c t4) *)
  rewrite /= in Hhr E; rewrite /invc2 /= -!andbA in Hcr.
  case/and5P: Hhr=>/eqP E2 ->->->->; rewrite -{}E2.
  case/and5P: Hcr=>->_ _->->.
  by move/eqP: E=>->; rewrite Hhl Hcl !eq_refl.
- (* l = R Leaf s0 (B t0 s1 t1) *)
  rewrite /= in Hhr E; rewrite /invc2 /= in Hcr.
  case/and4P: Hhr=>->->->->.
  case/andP: Hcr=>->->.
  by rewrite Hhl Hcl E eq_refl.
- (* l = R (R t2 b t3) c (B t0 s1 t4) *)
  rewrite /= -!andbA in Hhr E; rewrite /invc2 /= -!andbA in Hcr.
  move/eqP: E=>->.
  case/and7P: Hhr=>/eqP <- /eqP ->->->->->->.
  case/and6P: Hcr=>_ _->->->->.
  by rewrite Hhl Hcl !eq_refl.
- (* l = R (B t s2 t2) s0 (B t0 s1 t1) *)
  rewrite /= -!andbA in Hhr E; rewrite /invc2 /= -!andbA in Hcr.
  case/and7P: Hhr=>->->->->->->->.
  case/and4P: Hcr=>->->->->.
  by rewrite E Hhl Hcl eq_refl.
- (* l = B t s0 t0 *)
  rewrite /= in Hhr E; rewrite /invc2 /= in Hcr.
  case/and3P: Hhr=>->->->.
  case/andP: Hcr=>->->.
  by rewrite E Hhl Hcl eq_refl.
Qed.

Lemma inv_ins x t :
  invc t -> invh t ->
  [&& invc2 (ins x t), (color t == Black) ==> invc (ins x t), invh (ins x t) & bh (ins x t) == bh t].
Proof.
elim: t=>//=l IHl [a c] r IHr /and3P [H Hcl Hcr] /and3P [E Hhl Hhr].
case: c H=>/=.
- case/andP=>Hcll Hclr; rewrite /invc2.
  case: (cmp x a)=>/=.
  - rewrite Hcr Hhr !andbT.
    by case/and4P: (IHl Hcl Hhl)=>_; move/eqP: E=><-; rewrite Hcll /= =>->->->.
  - by rewrite Hcl Hcr Hhl Hhr E eq_refl.
  rewrite Hcl Hhl /=.
  case/and4P: (IHr Hcr Hhr)=>_; move/eqP: E=>->; rewrite Hclr /= =>->->/eqP ->.
  by rewrite eq_refl.
move=>_; case: (cmp x a)=>/=.
- case/and4P: (IHl Hcl Hhl)=>Hi2 _ Hhi Hbi.
  move/eqP: E=>E; rewrite E in Hbi.
  case/and3P: (inv_baliL a Hhi Hhr Hi2 Hcr Hbi)=>/[dup] H ->-> /eqP->.
  move/eqP: Hbi=>->; rewrite E eq_refl /= andbT.
  by apply: invc2I.
- by rewrite /invc2 /= Hcl Hcr Hhl Hhr E eq_refl.
case/and4P: (IHr Hcr Hhr)=>Hi2 _ Hhi Hbi.
move/eqP: E=>E; rewrite -E eq_sym in Hbi.
case/and3P: (inv_baliR a Hhl Hhi Hcl Hi2 Hbi)=>/[dup] H ->->-> /=; rewrite andbT.
by apply: invc2I.
Qed.

Corollary rbt_insert x t : rbt_inv t -> rbt_inv (insert x t).
Proof.
rewrite /rbt_inv /insert paint_black eq_refl andbT.
case/and3P=>Hct Hht Hc.
case/and4P: (inv_ins x Hct Hht).
by rewrite Hc /= /invc2 =>-> _ /(invh_paint Black) ->.
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

Lemma inv_baldL l a r :
  invh l -> invh r -> bh l + 1 = bh r -> invc2 l -> invc r ->
  [ && invh (baldL l a r), bh (baldL l a r) == bh r, invc2 (baldL l a r) &
       (color r == Black) ==> invc (baldL l a r)].
Proof.
move=>Hhl Hhr Hbh Hc2l Hcr.
funelim (baldL l a r); simp baldL=>//=.
- rewrite /= -!andbA in Hhr Hbh Hcr; rewrite /invc2 /= => {Hhl Hc2l}.
  rewrite !addn1 in Hbh; move/succn_inj: Hbh=>Hbh.
  case/and5P: Hhr=>E4 E22 -> Hh3 Hh4.
  rewrite -Hbh add0n !eq_refl /= andbT in E4 E22 *.
  case/and4P: Hcr=>Ec4 -> Hc3 Hc4.
  have Hr4 : invc2 (paint Red t4) by rewrite /invc2 paint2; apply: invc2I.
  have Eb : bh t3 == bh (paint Red t4).
  - rewrite bh_paint_red; last by move/eqP: Ec4.
    by move/eqP: E4=><-; move/eqP: E22=><-.
  case/and3P: (inv_baliR c Hh3 (invh_paint Red Hh4) Hc3 Hr4 Eb)=>->->/eqP->.
  by move/eqP: E22=><-.
- rewrite /= in Hhr Hbh Hcr; rewrite /invc2 /= => {Hhl Hc2l}.
  rewrite !addn1 in Hbh; move/succn_inj: Hbh=>Hbh.
  case/and3P: Hhr=>E2 Hh2 Hh3.
  case/andP: Hcr=>Hc2 Hc3.
  have Hhr : invh (R t2 b t3) by rewrite /= E2 Hh2 Hh3.
  have Hc2r : invc2 (R t2 b t3) by rewrite /invc2 /= Hc2 Hc3.
  have Hbb : bh (Leaf (T * col)) == bh (R t2 b t3) by rewrite /= -Hbh.
  case/and3P: (inv_baliR a (isT : invh empty_a) Hhr (isT : invc empty_a) Hc2r Hbb)=>/[dup] Hcb -> -> /eqP -> /=.
  by rewrite -Hbh /= andbT; apply: invc2I.
- rewrite /= in Hhl Hbh; rewrite /invc2 /= in Hc2l *.
  case/and3P: Hhl=>->->->.
  case/andP: Hc2l=>->->.
  by rewrite Hbh Hhr Hcr eq_refl /= andbT implybb.
- by rewrite /= addn1 in Hbh.
- by rewrite /= addn1 in Hbh.
- rewrite /= -!andbA in Hhl Hhr Hbh Hcr; rewrite /invc2 /= in Hc2l *.
  rewrite addn1 [in RHS]addn1 in Hbh; move/succn_inj: Hbh=>->.
  case/andP: Hc2l=>->->.
  case/and3P: Hhl=>->->->.
  case/and5P: Hhr=>/eqP E2 E3 -> Hh3 Hh4.
  case/and4P: Hcr=>Hcl4 -> Hc3 Hc4.
  rewrite E2 !eq_refl /= andbT.
  have Hr4 : invc2 (paint Red t4) by rewrite /invc2 paint2; apply: invc2I.
  have Eb : bh t3 == bh (paint Red t4).
  - rewrite bh_paint_red; last by move/eqP: Hcl4.
    by move/eqP: E3=><-; rewrite -E2 addnK.
  case/and3P: (inv_baliR c Hh3 (invh_paint Red Hh4) Hc3 Hr4 Eb)=>->->/eqP->.
  by rewrite -E2; move/eqP: E3=>->; rewrite eq_refl.
rewrite /= addn1 [in RHS]addn1 in Hbh; move/succn_inj: Hbh=>Hbh.
have Hhr' : invh (R t2 b t3) by apply: Hhr.
have Hcl' : invc (Node t (s0, Black) t0) by apply: Hc2l.
have Hc2r' : invc2 (R t2 b t3) by apply: Hcr.
have Hbh' : bh (Node t (s0, Black) t0) == bh (R t2 a t3) by rewrite /= Hbh.
case/and3P: (inv_baliR a Hhl Hhr' Hcl' Hc2r' Hbh')=>/[dup] Hc -> -> /eqP -> /=.
by rewrite Hbh eq_refl /= andbT; apply: invc2I.
Qed.

Lemma inv_baldR l a r :
  invh l -> invh r -> bh l = bh r +1 -> invc l -> invc2 r ->
  [ && invh (baldR l a r), bh (baldR l a r) == bh l, invc2 (baldR l a r) &
       (color l == Black) ==> invc (baldR l a r)].
Proof.
move=>Hhl Hhr Hbh Hcl Hc2r.
funelim (baldR l a r); simp baldR=>//=.
- by rewrite /= add0n in Hbh Hhl; rewrite Hbh in Hhl.
- by rewrite /= andbF in Hcl.
- rewrite /= eq_refl andbT in Hhl Hbh Hcl; rewrite /invc2 /= !andbT => {Hhr Hc2r}.
  case/and5P: Hhl; rewrite Hbh eqn_add2r eq_sym => E2 Hh1 /eqP<- Hh2 ->.
  case/and4P: Hcl=>/eqP C1 Hc1 Hc2 ->; rewrite (eqP E2) add0n !andbT.
  have Hr1 : invc2 (paint Red t1) by rewrite /invc2 paint2; apply: invc2I.
  have Eb : bh (paint Red t1) == bh t2 by rewrite bh_paint_red // Hbh addnK eq_sym.
  case/and3P: (inv_baliL a (invh_paint Red Hh1) Hh2 Hr1 Hc2 Eb)=>->->/eqP->.
  by rewrite bh_paint_red // Hbh.
- rewrite /= in Hhl Hbh Hcl; rewrite /invc2 /= => {Hhr Hc2r}.
  case/and3P: Hhl=>E1 Hh1 Hh2.
  case/andP: Hcl=>Hc1 Hc2.
  rewrite Hbh; rewrite addn1 add0n in Hbh; move/succn_inj: Hbh=>Hbh.
  have Hhl : invh (R t1 a t2) by rewrite /= E1 Hh1 Hh2.
  have Hc2l : invc2 (R t1 a t2) by rewrite /invc2 /= Hc1 Hc2.
  have Hbb : bh (R t1 a t2) == bh (Leaf (T * col)) by rewrite /= Hbh.
  case/and3P: (inv_baliL b Hhl (isT : invh empty_a) Hc2l (isT : invc empty_a) Hbb)=>/[dup] Hcb ->->/eqP -> /=.
  by rewrite Hbh /= andbT; apply: invc2I.
- rewrite /= in Hhr Hbh; rewrite /invc2 /= in Hc2r *.
  case/and3P: Hhr=>->->->.
  case/andP: Hc2r=>->->.
  by rewrite Hbh Hhl Hcl !eq_refl /= !andbT; exact: implybb.
- by rewrite /= addn1 in Hbh.
- by move: Hhl Hbh => /= /and3P [/eqP -> _ _]; rewrite addn1.
- by rewrite /= andbF in Hcl.
- rewrite /= eq_refl andbT in Hhl Hhr Hbh Hcl; rewrite /invc2 /= in Hc2r *.
  case/and5P: Hhl=>E1 Hh1 /eqP<- Hh2 ->.
  case/and3P: Hhr=>->->->.
  case/and4P: Hcl=>/eqP C1 Hc1 Hc2->.
  case/andP: Hc2r=>->->.
  rewrite Hbh eqn_add2r in E1.
  have Hl1 : invc2 (paint Red t1) by rewrite /invc2 paint2; apply: invc2I.
  have Eb : bh (paint Red t1) == bh t2 by rewrite bh_paint_red // Hbh addnK.
  case/and3P: (inv_baliL a (invh_paint Red Hh1) Hh2 Hl1 Hc2 Eb)=>->-> /eqP-> /=.
  by rewrite bh_paint_red // Hbh addnK (eqP E1) !eq_refl.
have Hhl' : invh (R t1 a t2) by apply: Hhl.
have Hcr' : invc (Node t (s0, Black) t0) by apply: Hc2r.
have Hc2l' : invc2 (R t1 a t2) by apply: Hcl.
have Hbh' : bh (R t1 a t2) == bh (Node t (s0, Black) t0).
- by rewrite /= addn1 [in RHS]addn1 in Hbh; move/succn_inj: Hbh=>/= ->.
case/and3P: (inv_baliL b Hhl' Hhr Hc2l' Hcr' Hbh')=>/[dup] Hc ->->/eqP -> /=.
by rewrite eq_refl /= andbT; apply: invc2I.
Qed.

Lemma split_min_inv l a c r x t' :
  split_min l a r = (x, t') ->
  bh l == bh r -> invh l -> invh r ->  (* invh (Node l _ r) *)
  (c == Red) ==> (color l == Black) && (color r == Black) -> invc l -> invc r ->  (* invc (Node l (_, c) r) *)
  [&& invh t', (c == Red) ==> (bh t' == (if c == Black then bh l + 1 else bh l)) && invc t' &   (* bh (Node l (_, c) _) *)
               (c == Black) ==> (bh t' == (if c == Black then bh l else bh l - 1)) && invc2 t'].
Proof.
elim: l a c r t'=>/= [|l' IHl [a' c'] r' _] a c r t'.
- case=>_ <- /eqP <- _ -> H _ Hcr /=.
  case: c H=>/=; first by rewrite Hcr.
  by move=>_; apply: invc2I.
case Hsm: (split_min l' a' r')=>[x0 m][E0 Et'] Er /and3P [E' Hhl' Hhr' Hhr Ic] /and3P [Ic' Hcl' Hcr' Hcr].
rewrite {x0}E0 in Hsm.
case/and3P: (IHl _ c' _ _ Hsm E' Hhl' Hhr' Ic' Hcl' Hcr')=>Hhm Icr' Icb'.
case: {IHl}c Ic=>/=.
- case/andP=>[/eqP Ec' Ecr].
  rewrite {Icr'}Ec' /= in Et' Er Icb' *.
  case/andP: Icb'=>/eqP Em' Hcm2; rewrite -Et' andbT; rewrite -Em' in Er.
  case/and4P: (inv_baldL a Hhm Hhr (eqP Er) Hcm2 Hcr)=>->/eqP->_.
  by rewrite Ecr -Em' eq_sym /= =>->; rewrite andbT.
move=>_; case: c' Et' Er Ic' Icr' Icb'=>/=.
- move=><-/= /eqP <-; rewrite /invc2 /= => _ /andP [->->] _ /=.
  by rewrite Hhm Hhr Hcr.
move=><-/= /eqP Ebl' _ _ /andP [/eqP Ebm Hcm2]; rewrite -Ebm in Ebl'.
case/and4P: (inv_baldL a Hhm Hhr Ebl' Hcm2 Hcr)=>-> /eqP-> -> _ /=.
by rewrite -Ebl' Ebm eq_refl.
Qed.

Lemma del_inv x t : invc t -> invh t ->
  [&& invh (del x t),
      (color t == Red) ==> (bh (del x t) == bh t) && invc (del x t) &
      (color t == Black) ==> (bh (del x t) == bh t - 1) && invc2 (del x t) ].
Proof.
elim: t=>//=l IHl [a c] r IHr /and3P [I Hcl Hcr] /and3P [E Hhl Hhr].
case Hxa: (cmp x a)=>/=.
- case: eqP=>El /=.
  - rewrite El /invc2 /= in E *; rewrite E Hhr Hcr !andbT /=.
    by case: c I=>/= [/andP [_->]|_].
  case/and3P: (IHl Hcl Hhl)=>Hhdl.
  case Cl: (color l)=>/=.
  - rewrite Hhdl /= /invc2 /= => /andP [/eqP-> ->] _.
    rewrite E Hhr Hcr !andbT /=.
    by case: c I=>/=; [rewrite Cl | rewrite addnK eq_refl].
  move=>_ /andP [/eqP Ebdl Hcd2].
  have Ebdl1 : bh (del x l) + 1 = bh r.
  - rewrite Ebdl -(eqP E) subnK //.
    case: {IHl I Hcl E Hhl Hhdl Ebdl Hcd2}l El Cl=>//= ? [??] ? _ ->.
    by rewrite eq_refl addn1.
  case/and3P: (inv_baldL a Hhdl Hhr Ebdl1 Hcd2 Hcr) =>->/eqP->/andP [-> Hcbd] /=.
  rewrite andbT; case: c I=>/=; last by rewrite (eqP E) addnK eq_refl.
  by case/andP=>_ /(implyP Hcbd) ->; rewrite eq_sym !andbT.
- case: {IHr}r Hcr Hhr E I=>[_ _ /eqP -> _|lr [ar cr] rr /and3P [Ecr Hclr Hcrr] /and3P [Ebr Hhlr Hhrr] /= E I].
  - by rewrite Hhl Hcl (invc2I Hcl) /= !andbT; case: c.
  case Hsm: (split_min lr ar rr)=>[a' r'] /=.
  case/and3P: (split_min_inv Hsm Ebr Hhlr Hhrr Ecr Hclr Hcrr).
  case Ccr: cr=>/=.
  - rewrite Ccr andbF implybF /= in I E.
    rewrite /invc2 /= Hcl => -> /andP [/eqP -> ->] _.
    by rewrite E Hhl /= !andbT; case: c I=>//=; rewrite addnK eq_refl.
  rewrite Ccr /= in E.
  move=>Hhr' _ /andP [/eqP Ebr' Hc2r']; rewrite -Ebr' in E.
  case/and4P: (inv_baldR a' Hhl Hhr' (eqP E) Hcl Hc2r')=>-> /eqP->->.
  case: c I=>/=.
  - by case/andP=>-> /= _ ->; rewrite eq_refl.
  by rewrite addnK eq_refl.
case: eqP=>Er /=.
- rewrite Er /invc2 /= in E *; rewrite E Hhl Hcl !andbT /=.
  by case: c I=>/= [/andP [->_]|_]; rewrite ?addnK eq_refl.
case/and3P: (IHr Hcr Hhr)=>Hhdr.
case Cr: (color r)=>/=.
- rewrite Hhdr /= /invc2 /= => /andP [/eqP-> ->] _.
  rewrite E Hhl Hcl !andbT /=.
  by case: c I=>/=; [rewrite Cr andbF| rewrite addnK eq_refl].
move=>_ /andP [/eqP Ebdr Hcd2].
have Ebdr1 : bh l = bh (del x r) + 1.
- rewrite Ebdr subnK; first by move/eqP: E.
  case: {IHr I Hcr E Hhr Hhdr Ebdr Hcd2}r Er Cr=>//= ? [??] ? _ ->.
  by rewrite eq_refl addn1.
case/and4P: (inv_baldR a Hhl Hhdr Ebdr1 Hcl Hcd2)=>->/eqP->-> /=.
rewrite andbT; case: c I=>/=; last by rewrite addnK eq_refl.
by case/andP=>-> _ /= ->; rewrite eq_refl.
Qed.

Corollary rbt_delete x t : rbt_inv t -> rbt_inv (delete x t).
Proof.
rewrite /rbt_inv /delete; case/and3P=>Hct Hht /eqP Ct.
case/and3P: (del_inv x Hct Hht)=>Hhd; rewrite Ct /= =>_ /andP [Ev Hcd2].
apply/and3P; split.
- by apply: Hcd2.
- by apply: invh_paint.
by rewrite paint_black eq_refl.
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

Definition bst_list (t : rbt T) : bool := sorted <%O (inorder_a t).

Lemma inorder_ins x t :
  bst_list t -> inorder_a (ins x t) = ins_list x (inorder_a t).
Proof.
rewrite /bst_list; elim: t=>//= l IHl [a c] r IHr.
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
  bst_list t ->
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
  bst_list t -> inorder_a (del x t) = del_list x (inorder_a t).
Proof.
rewrite /bst_list /=; elim: t=>//=l IHl [a c] r IHr /[dup] H.
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
  bst_list t ->
  inorder_a (delete x t) = del_list x (inorder_a t).
Proof.
rewrite /delete => H.
by rewrite inorder_paint; apply: inorder_del.
Qed.

Lemma inorder_isin_list x (t : rbt T) :
  bst_list t ->
  isin_a t x = (x \in inorder_a t).
Proof.
rewrite /bst_list /=; elim: t=>//= l IHl [a c] r IHr.
rewrite mem_cat inE sorted_cat_cons_cat=>/andP [H1 H2].
case Hc: (cmp x a)=>/=.
- move/cmp_lt: Hc=>Hx; rewrite IHl; last by rewrite (cat_sorted2 H1).
  have ->: (x==a)=false by move: Hx; rewrite lt_neqAle=>/andP [/negbTE].
  have ->: x \in inorder_a r = false; last by rewrite /= orbF.
  apply/negbTE/count_memPn; rewrite -(count_pred0 (inorder_a r)).
  apply/eq_in_count=>z; move: H2=>/= /(order_path_min lt_trans)/allP/(_ z)/[apply] Hz.
  by move: (lt_trans Hx Hz); rewrite lt_neqAle eq_sym=>/andP [/negbTE].
- by move/cmp_eq: Hc=>/eqP->; rewrite eq_refl /= orbT.
move/cmp_gt: Hc=>Hx; rewrite IHr; last first.
- by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
have ->: (x==a)=false by move: Hx; rewrite lt_neqAle eq_sym=>/andP [/negbTE].
suff: x \in inorder_a l = false by move=>->.
apply/negbTE/count_memPn; rewrite -(count_pred0 (inorder_a l)).
apply/eq_in_count=>z /=.
move: H1; rewrite (sorted_pairwise lt_trans) pairwise_cat /= allrel1r andbT.
case/andP=>+ _ =>/allP/(_ z)/[apply] Hz.
by move: (lt_trans Hz Hx); rewrite lt_neqAle eq_sym=>/andP [/negbTE].
Qed.

(* corollaries *)

Definition invariant t := bst_list t && rbt_inv t.

Corollary inorder_insert_list x (t : rbt T) :
  invariant t ->
  perm_eq (inorder_a (insert x t))
          (if x \in inorder_a t then inorder_a t else x :: inorder_a t).
Proof.
rewrite /invariant /bst_list => /andP [H1 _].
by rewrite inorder_insert //; apply: inorder_ins_list.
Qed.

Corollary inorder_delete_list x (t : rbt T) :
  invariant t ->
  perm_eq (inorder_a (delete x t))
          (filter (predC1 x) (inorder_a t)).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
by rewrite inorder_delete //; apply: inorder_del_list.
Qed.

Corollary invariant_empty : invariant empty_a.
Proof. by []. Qed.

Corollary invariant_insert x (t : rbt T) :
  invariant t -> invariant (insert x t).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
apply/andP; split; last by apply: rbt_insert.
by rewrite inorder_insert //; apply: ins_list_sorted.
Qed.

Corollary invariant_delete x (t : rbt T) :
  invariant t -> invariant (delete x t).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
apply/andP; split; last by apply: rbt_delete.
by rewrite inorder_delete //; apply: del_list_sorted.
Qed.

Lemma inv_isin_list x (t : rbt T) :
  invariant t ->
  isin_a t x = (x \in inorder_a t).
Proof. by rewrite /invariant => /andP [H1 _]; apply: inorder_isin_list. Qed.

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

Lemma join_inv l r :
  invh l -> invh r -> bh l = bh r -> invc l -> invc r ->
  [&& invh (join l r), bh (join l r) == bh l, invc2 (join l r) &
      (color l == Black) && (color r == Black) ==> invc (join l r)].
Proof.
move=>Hhl Hhr E Hcl Hcr.
funelim (join l r); simp join=>/=.
- rewrite /= in E; rewrite -E Hhr Hcr implybT andbT /=.
  by apply: invc2I.
- rewrite /invc2 /=; case: p Hhl E Hcl=>/=p c ->-> /and3P [->->->].
  by rewrite !eq_refl /= implybT.
- rewrite /= -!andbA in Hhl Hcl Hhr Hcr E.
  case/and3P: Hhl=>E12 Hh1 Hh2.
  case/and3P: Hhr=>E34 Hh3 Hh4.
  case/and4P: Hcl=>Ec1 Ec2 Hc1 Hc2.
  case/and4P: Hcr=>Ec3 Ec4 Hc3 Hc4.
  rewrite E eq_sym in E12; rewrite /invc2 /= in H *.
  case/and3P: (H Hh2 Hh3 (eqP E12) Hc2 Hc3).
  case: (join t2 t3)=>[|l [x c'] r]/=.
  - move=>_ /eqP Eb2 _.
    by rewrite E -(eqP E34) -(eqP E12) -Eb2 Hh1 Hh4 Hc1 Ec4 Hc4 eq_refl.
  case/and3P=>Eblr Hhl Hhr; rewrite Ec2 Ec3 /=.
  case: c'=>/=.
  - rewrite E -(eqP E34) -(eqP E12) -(eqP Eblr) -!andbA => /eqP ->.
    by case/and6P=>->->->->_ _; rewrite eq_refl Hh1 Hhl Hhr Hh4 Hc1 Hc4 Ec1 Ec4.
  move/eqP=>->; rewrite (eqP E12) E -!andbA.
  by case/and4P=>->->_ _; rewrite eq_refl Hh1 E34 Eblr Hhl Hhr Hh4 Hc1 Hc4 Ec4.
- rewrite /= -!andbA in Hhl Hhr Hcl Hcr E H.
  rewrite /invc2 /= in H *.
  case/and3P: Hhl=>E12 Hh1 Hh2.
  case/andP: Hcr=>Hc0 Hc3.
  case/and4P: Hcl=>Ec1 Ec2 Hc1 Hc2.
  rewrite (eqP E12) in E.
  have Hc03 : invc t0 && invc t3 by apply/andP; split.
  case/and4P: (H Hh2 Hhr E Hc2 Hc03)=>-> /eqP-> _.
  by rewrite E12 Hh1 Hc1 Ec2 !eq_refl /= => ->.
- rewrite /= -!andbA in Hhl Hhr Hcl Hcr E H.
  rewrite /invc2 /= in H *.
  case/and3P: Hhr=>E23 Hh2 Hh3.
  case/and4P: Hcr=>Ec2 Ec3 Hc2 Hc3.
  case/and4P: (H Hhl Hh2 E Hcl Hc2)=>-> /eqP-> _.
  by rewrite E E23 Hh3 Hc3 Ec2 eq_refl /= => ->.
rewrite /= in Hhl Hcl Hhr Hcr E.
case/and3P: Hhl=>E12 Hh1 Hh2.
case/and3P: Hhr=>E34 Hh3 Hh4.
case/andP: Hcl=>Hc1 Hc2.
case/andP: Hcr=>Hc3 Hc4.
rewrite !addn1 in E; move/succn_inj: E=>E13.
rewrite E13 eq_sym in E12.
case/and4P: (H Hh2 Hh3 (eqP E12) Hc2 Hc3).
case: (join t2 t3)=>[|l [x c'] r]/=.
- rewrite /invc2 /= => _ /eqP Eb2 _ _.
  have Hhr: invh (B (Leaf (T * col)) c t4) by rewrite /= -(eqP E34) -(eqP E12) -Eb2 Hh4.
  have Eb: bh t1 + 1 = bh (B (Leaf (T * col)) c t4) by rewrite /= E13 -(eqP E12) -Eb2.
  case/and4P: (inv_baldL a Hh1 Hhr Eb (invc2I Hc1) Hc4)=>->/eqP-> /=.
  by rewrite /invc2=>->->; rewrite Eb.
case/and3P=>Eblr Hhl Hhr; rewrite /invc2 /=.
case: c'=>/=.
- rewrite E13 -(eqP E34) -(eqP E12) -(eqP Eblr) => /eqP ->.
  by case/andP=>->->_; rewrite Hh1 Hhl Hhr Hh4 Hc1 Hc4 !eq_refl.
move=>Ebl /andP [Hcl Hcr] ?.
have Hhrb: invh (B (B l x r) c t4) by rewrite /= (eqP Ebl) (eqP E12) E34 Eblr Hhl Hhr Hh4.
have Eb: bh t1 + 1 = bh (B (B l x r) c t4) by rewrite /= (eqP Ebl) E13 -(eqP E12).
have Hhcb: invc (B (B l x r) c t4) by rewrite /= Hcl Hcr Hc4.
case/and4P: (inv_baldL a Hh1 Hhrb Eb (invc2I Hc1) Hhcb)=>-> /eqP->.
by rewrite /invc2=>-> /=->; rewrite (eqP Ebl) E13 -(eqP E12) eq_refl.
Qed.

Lemma del_j_inv x t : invc t -> invh t ->
  [&& invh (del_j x t),
      (color t == Red) ==> (bh (del_j x t) == bh t) && invc (del_j x t) &
      (color t == Black) ==> (bh (del_j x t) == bh t - 1) && invc2 (del_j x t) ].
Proof.
elim: t=>//= l IHl [a c] r IHr /and3P [I Hcl Hcr] /and3P [E Hhl Hhr].
case Hxa: (cmp x a)=>/=.
- case: eqP=>El /=.
  - rewrite El /invc2 /= in E *; rewrite E Hhr Hcr !andbT /=.
    by case: c I=>/= [/andP [_->]|_].
  case/and3P: (IHl Hcl Hhl)=>Hhdl.
  case Cl: (color l)=>/=.
  - rewrite Hhdl /= /invc2 /= => /andP [/eqP-> ->] _.
    rewrite E Hhr Hcr !andbT /=.
    by case: c I=>/=; [rewrite Cl | rewrite addnK eq_refl].
  move=>_ /andP [/eqP Ebdl Hcd2].
  have Ebdl1 : bh (del_j x l) + 1 = bh r.
  - rewrite Ebdl -(eqP E) subnK //.
    case: {IHl I Hcl E Hhl Hhdl Ebdl Hcd2}l El Cl=>//= ? [??] ? _ ->.
    by rewrite eq_refl addn1.
  case/and3P: (inv_baldL a Hhdl Hhr Ebdl1 Hcd2 Hcr) =>->/eqP->/andP [-> Hcbd] /=.
  rewrite andbT; case: c I=>/=; last by rewrite (eqP E) addnK eq_refl.
  by case/andP=>_ /(implyP Hcbd) ->; rewrite eq_sym !andbT.
- case/and4P: (join_inv Hhl Hhr (eqP E) Hcl Hcr)=>-> /eqP->->.
  case: c I=>/=; last by rewrite addnK eq_refl.
  by case/andP=>->-> /= ->; rewrite eq_refl.
case: eqP=>Er /=.
- rewrite Er /invc2 /= in E *; rewrite E Hhl Hcl !andbT /=.
  by case: c I=>/= [/andP [->_]|_]; rewrite ?addnK eq_refl.
case/and3P: (IHr Hcr Hhr)=>Hhdr.
case Cr: (color r)=>/=.
- rewrite Hhdr /= /invc2 /= => /andP [/eqP-> ->] _.
  rewrite E Hhl Hcl !andbT /=.
  by case: c I=>/=; [rewrite Cr andbF| rewrite addnK eq_refl].
move=>_ /andP [/eqP Ebdr Hcd2].
have Ebdr1 : bh l = bh (del_j x r) + 1.
- rewrite Ebdr subnK; first by move/eqP: E.
  case: {IHr I Hcr E Hhr Hhdr Ebdr Hcd2}r Er Cr=>//= ? [??] ? _ ->.
  by rewrite eq_refl addn1.
case/and4P: (inv_baldR a Hhl Hhdr Ebdr1 Hcl Hcd2)=>->/eqP->-> /=.
rewrite andbT; case: c I=>/=; last by rewrite addnK eq_refl.
by case/andP=>-> _ /= ->; rewrite eq_refl.
Qed.

Corollary rbt_delete_j x t : rbt_inv t -> rbt_inv (delete_j x t).
Proof.
rewrite /rbt_inv /delete_j; case/and3P=>Hct Hht /eqP Ct.
case/and3P: (del_j_inv x Hct Hht)=>Hhd; rewrite Ct /= =>_ /andP [Ev Hcd2].
apply/and3P; split.
- by apply: Hcd2.
- by apply: invh_paint.
by rewrite paint_black eq_refl.
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
  bst_list t -> inorder_a (del_j x t) = del_list x (inorder_a t).
Proof.
rewrite /bst_list /=; elim: t=>//=l IHl [a c] r IHr /[dup] H.
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
  bst_list t ->
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
rewrite /invariant /bst_list => /andP [H1 H2].
by rewrite inorder_delete_j //; apply: inorder_del_list.
Qed.

Corollary invariant_delete_j x (t : rbt T) :
  invariant t -> invariant (delete_j x t).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
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
  invc t -> invh t ->
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
