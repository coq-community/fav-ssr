From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq order path prime div.
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

Lemma maxn_expn k n m : 0 < k -> maxn (k^n) (k^m) = k ^ maxn n m.
Proof.
case: k=>//; case=>[|k _]; first by rewrite !exp1n.
rewrite /maxn; case: (ltnP n m).
- by rewrite ltn_exp2l // =>->.
by rewrite ltnNge leq_exp2l // =>->.
Qed.

End Arith.

Section Size.

Lemma size1 {A} (xs : seq A) : size xs = 1 -> exists x, xs = [::x].
Proof. by case: xs=>// x; case=>//= _; exists x. Qed.

Lemma size2 {A} (xs : seq A) : 1 < size xs -> exists x y ys, xs = [:: x, y & ys].
Proof. by case: xs=>// x; case=>//= y ys _; exists x,y,ys. Qed.

Lemma size_ind {T} P :
  (forall xs, size xs = 0 -> P xs) ->
  (forall n, (forall xs, size xs <= n -> P xs) -> forall xs, size xs <= n.+1 -> P xs) ->
  forall (xs : seq T), P xs.
Proof.
(* from https://stackoverflow.com/a/45883068/919707 *)
move=>H0 Hn xs; move: {2}(size _) (leqnn (size xs)) =>n; elim: n xs=>[|n IH] xs.
- by rewrite leqn0=>/eqP; apply: H0.
by apply/Hn/IH.
Qed.

End Size.

Section Mem.
Context {A B : eqType}.

Lemma all_notin (p : pred A) xs y :
  all p xs -> ~~ p y -> y \notin xs.
Proof. by move/allP=>Ha; apply/contra/Ha. Qed.

Lemma in_zip (l1 : seq A) (l2 : seq B) x y :
  (x, y) \in zip l1 l2 -> x \in l1 /\ y \in l2.
Proof.
elim: l1 l2=>[|a l1 IH][|b l2] //=.
rewrite !inE; case/orP.
- by case/eqP=>->->; rewrite !eqxx.
by move/IH=>[H1 H2]; rewrite H1 H2 !orbT.
Qed.

End Mem.

Section Zip.

Lemma zip_map2 {P Q R S} (f : P -> R) (g : Q -> S) (s1 : seq P) (s2 : seq Q) :
        zip (map f s1) (map g s2) =
        map (fun '(x1,x2) => (f x1,g x2)) (zip s1 s2).
Proof.
elim: s1 s2=>/= [|x1 s1 IH] [|x2 s2] //=.
by congr cons.
Qed.

End Zip.

Section Map2.
Context {A B C : Type}.

Definition map2 (f : A -> B -> C) (l1 : seq A) (l2 : seq B) : seq C :=
  [seq f x y | '(x, y) <- zip l1 l2].

Lemma size_map2 f l1 l2 :
  size (map2 f l1 l2) = minn (size l1) (size l2).
Proof. by elim: l1 l2=>[|a l1 IH][|b l2] //=; rewrite IH minnSS. Qed.

End Map2.

Section Butlast.
Context {A : Type}.

Definition butlast (xs : seq A) :=
  if xs is x :: s then belast x s else [::].

Lemma belast_butlast (x : A) xs : 0 < size xs -> belast x xs = x :: butlast xs.
Proof. by case: xs. Qed.

Lemma size_butlast (xs : seq A) : size (butlast xs) = (size xs).-1.
Proof. by case: xs=>//=x s; rewrite size_belast. Qed.

End Butlast.

Section Mins.
Context {disp : unit} {T : orderType disp}.
Variable (x0 : T).

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Definition mins (xs : seq T) := if xs is x::xs' then foldl Order.min x xs' else x0.

Lemma mins_min_in xs : xs != [::] -> all (>= mins xs) xs && (mins xs \in xs).
Proof.
case: xs=>//=x xs _; elim/last_ind: xs=>/=.
- by rewrite lexx inE eq_refl.
move=>xs y /andP [/andP [IH1 IH2]]; rewrite !inE=>IH3.
rewrite foldl_rcons le_minl IH1 /= mem_rcons inE eq_minr all_rcons le_minl lexx orbT /=.
rewrite {1 3 6}/Order.min; case: ifP.
- by rewrite IH2 /= =>H; case/orP: IH3=>[/eqP->|->]; rewrite ?eqxx ?orbT.
move/negbT; rewrite -leNgt=>Hy; rewrite Hy /= orbT andbT.
by apply/sub_all/IH2=>z; apply/le_trans.
Qed.

(* TODO restructure? *)
Lemma all_foldl_le (x : T) xs y :
  y <= x ->
  all (>= y) xs ->
  y <= foldl Order.min x xs.
Proof.
move=>Hyx; elim/last_ind: xs=>//=t h IH.
rewrite all_rcons foldl_rcons; case/andP=>Hy Ha.
by rewrite le_minr Hy IH.
Qed.

Lemma all_foldl_eq (x : T) xs :
  all (>= x) xs ->
  foldl Order.min x xs = x.
Proof.
elim/last_ind: xs=>//=t h IH.
rewrite all_rcons foldl_rcons; case/andP=>Hx Ha.
by rewrite IH // minElt; case: ltgtP Hx.
Qed.

Lemma all_foldl_ge (x : T) xs y :
  y <= x ->
  all (>= y) xs ->
  y \in xs ->
  foldl Order.min x xs = y.
Proof.
move=>Hyx; elim/last_ind: xs=>//=t h IH.
rewrite all_rcons foldl_rcons mem_rcons inE; case/andP=>Hy Ha.
case/orP.
- move/eqP=>E; rewrite E in Hyx Ha *; apply/min_idPr.
  by apply: all_foldl_le.
by move=>H; rewrite IH //; apply/min_idPl.
Qed.

Lemma eq_mins_iff m xs :
  xs != [::] -> m = mins xs <-> all (>= m) xs && (m \in xs).
Proof.
move=>H; split.
- by move=>->; apply: mins_min_in.
case: xs H=>//=x xs _; elim/last_ind: xs=>/=.
- by rewrite andbT inE; by case/andP=>_/eqP.
move=>xs y; rewrite foldl_rcons !inE mem_rcons inE all_rcons minElt -!andbA.
move=>IH; case/and4P=>Hx Hy Ha Ho; case: ltP=>H.
- apply: IH; rewrite Hx Ha /=; case/or3P: Ho.
  - by move=>->.
  - move/eqP=>E; rewrite E in Hx Ha.
    move: (all_foldl_le Hx Ha)=>H'.
    by move: (le_lt_trans H' H); rewrite ltxx.
  by move=>->; rewrite orbT.
apply/eqP; rewrite eq_le Hy /=.
case/or3P: Ho.
- move/eqP=>E; rewrite E in Hy Ha *.
  by rewrite all_foldl_eq in H.
- by move/eqP=>->.
by move=>Hm; rewrite (all_foldl_ge Hx Ha Hm) in H.
Qed.

Lemma mins_cat xs ys :
  xs != [::] ->
  ys != [::] ->
  mins (xs ++ ys) = Order.min (mins xs) (mins ys).
Proof.
move=>Hx Hy; symmetry; apply/eq_mins_iff.
- by case: xs Hx.
case/andP: (mins_min_in Hx)=>Hax Hix.
case/andP: (mins_min_in Hy)=>Hay Hiy.
apply/andP; split.
- rewrite all_cat; apply/andP; split.
  - by apply/sub_all/Hax=>z Hz; rewrite le_minl Hz.
  by apply/sub_all/Hay=>z Hz; rewrite le_minl Hz orbT.
rewrite minElt; case: ifP=>_; rewrite mem_cat.
- by rewrite Hix.
by rewrite Hiy orbT.
Qed.

End Mins.

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

Section Option.

Definition olist {A} (o : option A) : seq A :=
  if o is Some x then [:: x] else [::].

Definition omap {T S} (f : T -> option S) (xs : seq T) : seq S :=
  flatten (map (olist \o f) xs).

Lemma omap_nil {T S} (f : T -> option S) :
  omap f [::] = [::].
Proof. by []. Qed.

Lemma omap_cons {T S} (f : T -> option S) (x : T) xs :
  omap f (x::xs) = olist (f x) ++ omap f xs.
Proof. by []. Qed.

Lemma omap_rcons {T S} (f : T -> option S) (x : T) xs :
  omap f (rcons xs x) = omap f xs ++ olist (f x).
Proof. by rewrite /omap map_rcons flatten_rcons. Qed.

Lemma omap_cat {T S} (f : T -> option S) xs ys :
  omap f (xs ++ ys) = omap f xs ++ omap f ys.
Proof. by elim: xs=>//=x s IH; rewrite !omap_cons IH catA. Qed.

Lemma omap_empty {T S} (f : T -> option S) xs :
  all (fun x => ~~ f x) xs -> omap f xs = [::].
Proof.
elim: xs=>//=x s IH /andP [Hx /IH].
by rewrite omap_cons=>->; case: (f x) Hx.
Qed.

End Option.

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

(* not needed so far *)
Lemma trunc_logM p x y :
  0 < x -> 0 < y ->
  trunc_log p x + trunc_log p y <= trunc_log p (x * y) <= trunc_log p x + trunc_log p y + 1.
Proof.
move=>Hx Hy; case: p=>//=; case=>//= n; set p:=n.+2.
apply/andP; split.
- apply: trunc_log_max=>//; rewrite expnD.
  by apply: leq_mul; apply: trunc_logP.
rewrite -ltnS -(ltn_exp2l (m:=p)) // expnS !expnD expn1 !mulnA (mulnC p) -mulnA -!expnSr.
apply: leq_ltn_trans; first by apply: trunc_logP=>//; rewrite muln_gt0 Hx Hy.
by apply: ltn_mul; apply: trunc_log_ltn.
Qed.

End Log.

Section Mod.

Lemma mod_minus m i :
  m <= i < m.*2 -> i %% m = i - m.
Proof.
case/andP=>H1 H2; have H0: 0 < m by case: {H1}m H2.
rewrite {2}(divn_eq i m) addnC.
suff: i %/ m = 1 by move=>->; rewrite mul1n addnK.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by rewrite -ltnS ltn_divLR // mul2n.
by rewrite leq_divRL // mul1n.
Qed.

End Mod.

Section UpDiv.

Definition up_div x y :=
  let: (q,r) := edivn x y in q + (r != 0).

Lemma up_divE x y : up_div x y = x %/ y + ~~ (y %| x).
Proof.
by rewrite /up_div /divn /dvdn modn_def; case: (edivn x y).
Qed.

Lemma up_div0n d : up_div 0 d = 0.
Proof. by rewrite up_divE div0n dvdn0. Qed.

Lemma up_divn0 n : up_div n 0 = (n != 0).
Proof. by rewrite up_divE divn0 dvd0n. Qed.

Lemma up_div1n d : up_div 1 d = 1.
Proof. by rewrite up_divE dvdn1; case: d=>//; case. Qed.

Lemma up_divn1 n : up_div n 1 = n.
Proof. by rewrite up_divE divn1 dvd1n addn0. Qed.

Lemma up_div_gt0 p q : 0 < p -> 0 < up_div p q.
Proof.
move=>Hp; rewrite up_divE.
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
by rewrite up_divE divnS // addnC addnA addn_negb add1n.
Qed.

Corollary up_div_div p q : 0 < p -> up_div p q = (p.-1 %/ q).+1.
Proof. by case: p=>//=p _; apply: up_divS. Qed.

Corollary div_pred_up_div p q : p.-1 %/ q = (up_div p q).-1.
Proof.
case: p=>/= [|p]; first by rewrite div0n up_div0n.
by rewrite up_divS.
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
rewrite up_divE mulnDl; apply: leq_add.
- by apply: leq_trunc_div.
by rewrite mulnbl; case: ifP.
Qed.

Lemma up_divnMl p m d : 0 < p -> up_div (p * m) (p * d) = up_div m d.
Proof. by move=>Hp; rewrite !up_divE divnMl // dvdn_pmul2l. Qed.

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
