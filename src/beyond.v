From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype order ssrnat seq.
From favssr Require Import prelude bintree bst redblack.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

(* TODO switch to packed structures to reuse ASetM *)
Module ASetM2.
Record ASetM2 (disp : unit) (T : orderType disp): Type :=
  make {tp :> Type;
        empty : tp;
        insert : T -> tp -> tp;
        delete : T -> tp -> tp;
        isin : tp -> T -> bool;
        uni : tp -> tp -> tp;
        int : tp -> tp -> tp;
        dif : tp -> tp -> tp;

        abs : tp -> seq T;
        invar : tp -> bool;

        _ : invar empty;
        _ : abs empty = [::];

        _ : forall x s, invar s -> invar (insert x s);
        _ : forall x s, invar s ->
            perm_eq (abs (insert x s))
                    (if x \in abs s then abs s else x :: abs s);

        _ : forall x s, invar s -> invar (delete x s);
        _ : forall x s, invar s ->
            perm_eq (abs (delete x s))
                    (filter (predC1 x) (abs s));

        _ : forall x s, invar s ->
            isin s x = (x \in abs s);

        _ : forall s1 s2, invar s1 -> invar s2 -> invar (uni s1 s2);
        _ : forall s1 s2, invar s1 -> invar s2 ->
            perm_eq (abs (uni s1 s2))
                    (abs s1 ++ filter [predC mem (abs s1)] (abs s2));

        _ : forall s1 s2, invar s1 -> invar s2 -> invar (int s1 s2);
        _ : forall s1 s2, invar s1 -> invar s2 ->
            perm_eq (abs (int s1 s2))
                    (filter (mem (abs s2)) (abs s1));

        _ : forall s1 s2, invar s1 -> invar s2 -> invar (dif s1 s2);
        _ : forall s1 s2, invar s1 -> invar s2 ->
            perm_eq (abs (dif s1 s2))
                    (filter [predC mem (abs s2)] (abs s1))
        }.
End ASetM2.

Section JustJoin.
Context {disp : unit} {A : orderType disp} {B : Type}.

Parameter join : tree (A*B) -> A -> tree (A*B) -> tree (A*B).
Parameter inv : tree (A*B) -> bool.

(* TODO perm_eq's should probably be strengthened to prop equality to simplify proofs *)
(* see if the join implementations for RBT and 2-3 allow this *)

Parameter join_inorder : forall l a r,
  perm_eq (inorder_a (join l a r))
          (inorder_a l ++ a :: inorder_a r).
Parameter bst_join : forall l a r,
  all (< a) (inorder_a l) -> all (> a) (inorder_a r) ->
  bst_a l -> bst_a r ->
  bst_a (join l a r).
Parameter inv_leaf : inv empty_a.
Parameter inv_join : forall l a r, inv l -> inv r -> inv (join l a r).
Parameter inv_node : forall l a b r, inv (Node l (a, b) r) -> inv l && inv r.

Fixpoint split (t : tree (A*B)) (x : A) : (tree (A*B) * bool * tree (A*B)) :=
  if t is Node l (a,_) r then
      match cmp x a with
      | LT => let: (l1, b, l2) := split l x in
              (l1, b, join l2 a r)
      | EQ => (l, true, r)
      | GT => let: (r1, b, r2) := split r x in
              (join l a r1, b, r2)
      end
    else (empty_a, false, empty_a).

Fixpoint split_min (l : tree (A*B)) (a : A) (r : tree (A*B)) : (A * tree (A*B)) :=
  if l is Node ll (al, _) rl then
      let: (m, l') := split_min ll al rl in
      (m, join l' a r)
    else (a, r).

Definition join2 (l : tree (A*B)) (r : tree (A*B)) : tree (A*B) :=
  if r is Node lr (ar, _) rr then
      let: (m, r') := split_min lr ar rr in
      join l m r'
  else l.

Definition insert' (x : A) (t : tree (A*B)) : tree (A*B) :=
  let: (l, b, r) := split t x in join l x r.

Definition delete' (x : A) (t : tree (A*B)) : tree (A*B) :=
  let: (l, b, r) := split t x in join2 l r.

Fixpoint union (t1 t2 : tree (A*B)) : tree (A*B) :=
  if t1 is Node l1 (a1,_) r1 then
    if t2 isn't Leaf then
      let: (l2, _, r2) := split t2 a1 in
      join (union l1 l2) a1 (union r1 r2)
    else t1
  else t2.

Fixpoint inter (t1 t2 : tree (A*B)) : tree (A*B) :=
  if t1 is Node l1 (a1,_) r1 then
    if t2 isn't Leaf then
      let: (l2, b2, r2) := split t2 a1 in
      let l' := inter l1 l2 in
      let r' := inter r1 r2 in
      if b2 then join l' a1 r' else join2 l' r'
    else empty_a
  else empty_a.

Fixpoint diff (t1 t2 : tree (A*B)) : tree (A*B) :=
  if t2 is Node l2 (a2,_) r2 then
    if t1 isn't Leaf then
      let: (l1, _, r1) := split t1 a2 in
      join2 (diff l1 l2) (diff r1 r2)
    else empty_a
  else t1.

(* Correctness *)

Lemma split_bst t x l b r :
  split t x = (l, b, r) -> bst_a t ->
  [&& perm_eq (inorder_a l) (filter (< x) (inorder_a t)),
      perm_eq (inorder_a r) (filter (> x) (inorder_a t)),
      b == (x \in inorder_a t),
      bst_a l & bst_a r].
Proof.
elim: t l r=>/= [|tl IHl [a b'] tr IHr] l r; first by case=><-<-<-.
rewrite !filter_cat mem_cat inE /=; case Hxa: (cmp x a)=>/=.
- move/cmp_lt: Hxa=>Hxa.
  case E: (split tl x)=>[[l1 bb] l2][El Eb Er]; rewrite {l1}El {bb}Eb in E.
  case/and4P=>Hal Har Hbl Hbr; rewrite Hxa ltNge le_eqVlt Hxa orbT /=.
  case/and5P: (IHl _ _ E Hbl)=>Pl Pl2 /eqP -> -> Hbl2 /=.
  rewrite -Er; apply/and4P; split.
  - apply: (perm_trans Pl).
    rewrite -[X in perm_eq X _]cats0 perm_cat2l.
    rewrite (eq_in_filter (a2:=pred0)); first by rewrite filter_pred0.
    move=>z /= /(allP Har) Hz; apply/negbTE; rewrite -leNgt.
    by apply/ltW/(lt_trans Hxa).
  - apply: perm_trans; first by apply: join_inorder.
    apply: perm_cat=>//; rewrite perm_cons.
    suff: all (> x) (inorder_a tr) by move/all_filterP=>{1}<-.
    by apply/sub_all/Har=>z Hz; apply/lt_trans/Hz.
  - suff: x \notin inorder_a tr.
    - move/negbTE=>->; move: (Hxa); rewrite lt_neqAle.
      by case/andP=>/negbTE -> /=; rewrite orbF.
    apply/count_memPn/eqP; rewrite eqn0Ngt -has_count -all_predC.
    apply/sub_all/Har=>z /(lt_trans Hxa) /=.
    by rewrite lt_neqAle eq_sym; case/andP.
   apply: bst_join=>//; rewrite (perm_all (<a) Pl2) all_filter.
   by apply/sub_all/Hal=>z /= Hz; apply/implyP.
- move/cmp_eq: Hxa=>/eqP-> [-><-->] /and4P [Hal Har ->->] /=.
  rewrite eq_refl orbT /= andbT ltxx.
  move/all_filterP: (Hal)=>->; move/all_filterP: (Har)=>->.
  apply/andP; split.
  - rewrite -[X in perm_eq X _]cats0 perm_cat2l.
    rewrite (eq_in_filter (a2:=pred0)); first by rewrite filter_pred0.
    by move=>z /= /(allP Har) Hz; apply/negbTE; rewrite -leNgt; apply: ltW.
  rewrite -[X in perm_eq X _]cat0s perm_cat2r.
  rewrite (eq_in_filter (a2:=pred0)); first by rewrite filter_pred0.
  by move=>z /= /(allP Hal) Hz; apply/negbTE; rewrite -leNgt; apply: ltW.
move/cmp_gt: Hxa=>Hxa.
case E: (split tr x)=>[[r1 bb] r2][El Eb Er]; rewrite {r2}Er {bb}Eb in E.
case/and4P=>Hal Har Hbl Hbr; rewrite Hxa ltNge le_eqVlt Hxa orbT /=.
case/and5P: (IHr _ _ E Hbr)=>Pr1 Pr /eqP -> Hbr1 -> /=.
rewrite andbT -El; apply/and4P; split.
- apply: perm_trans; first by apply: join_inorder.
  apply: perm_cat; last by rewrite perm_cons.
  suff: all (< x) (inorder_a tl) by move/all_filterP=>{1}<-.
  by apply/sub_all/Hal=>z /= Hz; apply/lt_trans/Hxa.
- apply: (perm_trans Pr).
  rewrite -[X in perm_eq X _]cat0s perm_cat2r.
  rewrite (eq_in_filter (a2:=pred0)); first by rewrite filter_pred0.
  move=>z /= /(allP Hal) Hz; apply/negbTE; rewrite -leNgt.
  by apply/ltW/(lt_trans Hz).
- suff: x \notin inorder_a tl.
  - move/negbTE=>->; move: (Hxa); rewrite lt_neqAle /= eq_sym.
    by case/andP=>/negbTE ->.
  apply/count_memPn/eqP; rewrite eqn0Ngt -has_count -all_predC.
  apply/sub_all/Hal=>z /= Hz; move: (lt_trans Hz Hxa).
  by rewrite lt_neqAle eq_sym; case/andP.
 apply: bst_join=>//; rewrite (perm_all (>a) Pr1) all_filter.
 by apply/sub_all/Har=>z /= Hz; apply/implyP.
Qed.

Lemma split_inv t x l b r :
  split t x = (l, b, r) -> inv t ->
  inv l && inv r.
Proof.
elim: t l r=>/= [|tl IHl [a b'] tr IHr] l r; first by case=><-_<-; rewrite inv_leaf.
case Hxa: (cmp x a)=>/=.
- case E: (split tl x)=>[[l1 bb] l2][E1 Eb <-]; rewrite {l1}E1 {bb}Eb in E.
  by case/inv_node/andP=>Hl Hr; case/andP: (IHl _ _ E Hl)=>->/= Hl2; apply: inv_join.
- by case=>-> _ -> /inv_node.
case E: (split tr x)=>[[r1 bb] r2][<- Eb E2]; rewrite {r2}E2 {bb}Eb in E.
by case/inv_node/andP=>Hl Hr; case/andP: (IHr _ _ E Hr)=>Hr1 ->/=; rewrite andbT; apply: inv_join.
Qed.

Lemma split_min_inorder l a r m t :
  split_min l a r = (m, t) ->
  perm_eq (inorder_a l ++ a :: inorder_a r) (m :: inorder_a t).
Proof.
elim: l a r t=>/= [|ll IHl [al _] rl _] a r t; first by case=>->->.
case Hsm: (split_min ll al rl)=>[m' l'][E' {t}<-]; rewrite {m'}E' in Hsm.
move: (join_inorder l' a r); rewrite -(perm_cons m) perm_sym=>H.
by apply/perm_trans/H; rewrite -cat_cons perm_cat2r; apply: IHl.
Qed.

Lemma split_min_bst l a r m t :
  split_min l a r = (m, t) ->
  all (< a) (inorder_a l) -> all (> a) (inorder_a r) -> bst_a l -> bst_a r ->
  bst_a t && all (> m) (inorder_a t).
Proof.
elim: l a r t=>/= [|ll IHl [al _] rl _] a r t; first by case=>->->_->_->.
case Hsm: (split_min ll al rl)=>[m' l'][E' {t}<-]; rewrite {m'}E' in Hsm.
rewrite (perm_all (< a) (split_min_inorder Hsm))=>Haml' Har.
case/and4P=>Halll Halrl Hbll Hbrl Hbr.
case/andP: (IHl _ _ _ Hsm Halll Halrl Hbll Hbrl)=>Hbl' Hal'.
apply/andP; split; first by apply: bst_join=>//; case/andP: Haml'.
rewrite (perm_all (> m) (join_inorder l' a r)) all_cat Hal' /=.
have Hma : m < a by case/andP: Haml'.
by rewrite Hma /=; apply/sub_all/Har=>z /(lt_trans Hma).
Qed.

Lemma split_min_inv l a b r m t :
  split_min l a r = (m, t) -> inv (Node l (a, b) r) ->
  inv t.
Proof.
move=>+ /inv_node /andP [].
elim: l a r t=>/= [|ll IHl [al bl] rl _] a r t; first by case=>_->.
case Hsm: (split_min ll al rl)=>[m' l'][E' {t}<-]; rewrite {m'}E' in Hsm.
case/inv_node/andP=>Hll Hrl Hr; apply: inv_join=>//.
by apply: (IHl al rl).
Qed.

Lemma join2_inorder l r :
  perm_eq (inorder_a (join2 l r)) (inorder_a l ++ inorder_a r).
Proof.
case: r=>/= [|lr [ar _] rr]; first by rewrite cats0.
case Hsm: (split_min lr ar rr)=>[m r'].
apply: (perm_trans (join_inorder l m r')); rewrite perm_cat2l perm_sym.
by apply: split_min_inorder.
Qed.

Lemma join2_bst l r :
  bst_a l -> bst_a r -> allrel [eta <%O] (inorder_a l) (inorder_a r) ->
  bst_a (join2 l r).
Proof.
move=>Hbl; case: r=>//=lr [ar _] rr /and4P [Halr Harr Hblr Hbrr].
case Hsm: (split_min lr ar rr)=>[m r'].
rewrite (perm_allrelr [eta <%O] _ (split_min_inorder Hsm)) allrel_consr; case/andP=>Ham Har'.
case/andP: (split_min_bst Hsm Halr Harr Hblr Hbrr)=>Hbr' Hmr'.
by apply: bst_join.
Qed.

Lemma join2_inv l r : inv l -> inv r -> inv (join2 l r).
Proof.
move=>Hbl; case: r=>//=lr [ar br] rr H.
case Hsm: (split_min lr ar rr)=>[m r']; apply: inv_join=>//.
by apply: (split_min_inv (b:=br) Hsm).
Qed.

(* TODO move to bst? not needed *)
Lemma bst_a_uniq (t : tree (A*B)) : bst_a t -> uniq (inorder_a t).
Proof.
elim: t=>//=l IHl [a b] r IHr /and4P [Hal Har /IHl Hl /IHr Hr].
rewrite cat_uniq /= Hl Hr andbT /= negb_or -andbA; apply/and3P; split.
- apply/count_memPn/eqP; rewrite eqn0Ngt -has_count -all_predC.
  by apply/sub_all/Hal=>z /=; rewrite lt_neqAle; case/andP.
- rewrite -all_predC; apply/sub_all/Har=>z Hz /=.
  apply/count_memPn/eqP; rewrite eqn0Ngt -has_count -all_predC.
  by apply/sub_all/Hal=>y /= Hy; move: (lt_trans Hy Hz); rewrite lt_neqAle; case/andP.
apply/count_memPn/eqP; rewrite eqn0Ngt -has_count -all_predC.
by apply/sub_all/Har=>z /=; rewrite eq_sym lt_neqAle; case/andP.
Qed.

(* TODO move to prelude *)
Lemma eq_perm {T : eqType} (s1 s2 : seq A) : s1 = s2 -> perm_eq s1 s2.
Proof. by move=>->. Qed.

(* union *)

Lemma union_inorder t1 t2 :
  bst_a t1 -> (* we actually also need this because we reason on sequences *)
  bst_a t2 ->
  perm_eq (inorder_a (union t1 t2))
          (inorder_a t1 ++ filter [predC mem (inorder_a t1)] (inorder_a t2)).
Proof.
elim: t1 t2=>/= [|l1 IHl [a1 b1] r1 IHr] t2.
- suff: filter [predC mem nil] (inorder_a t2) = inorder_a t2 by move=>->.
  by apply/all_filterP/allP.
case/and4P=>Hal1 Har1 Hbl1 Hbr1.
case E2: t2=>[|l2 [a2 b2] r2]; first by rewrite /= cats0.
rewrite -{}E2=>H2; case Hs: (split t2 a1)=>[[l' b'] r'].
case/and5P: (split_bst Hs H2)=>Hl' Hr' Hb' Hbl' Hbr'.
apply: perm_trans; first by exact: join_inorder.
move: (IHr _ Hbr1 Hbr'); rewrite -(perm_cons a1) => /(perm_cat (IHl _ Hbl1 Hbl'))=>H.
apply: (perm_trans H); rewrite perm_catAC -cat_cons -!catA !perm_cat2l.
move: (perm_cat (perm_filter [predC inorder_a r1] Hr') (perm_filter [predC inorder_a l1] Hl'))=>H'.
apply/(perm_trans H')/perm_trans; last by apply/permEl/(perm_filterC (<= a1)).
rewrite -!filter_predI perm_catC; apply: perm_cat.
- apply/(@eq_perm A)/eq_filter=>z /=; rewrite mem_cat inE !negb_or.
  case: (ltgtP z a1)=>//=; last by rewrite andbF.
  rewrite andbT=>Hz; suff: z \notin inorder_a r1 by move=>->; rewrite andbT.
  apply/count_memPn/eqP; rewrite eqn0Ngt -has_count -all_predC.
  by apply/sub_all/Har1=>y /= /(lt_trans Hz); rewrite eq_sym lt_neqAle; case/andP.
apply/(@eq_perm A)/eq_filter=>z /=; rewrite mem_cat inE !negb_or.
case: (ltgtP a1 z)=>/=; try by rewrite andbF.
rewrite andbT=>Hz; suff: z \notin inorder_a l1 by move=>->.
apply/count_memPn/eqP; rewrite eqn0Ngt -has_count -all_predC.
by apply/sub_all/Hal1=>y /= Hy; move: (lt_trans Hy Hz); rewrite lt_neqAle; case/andP.
Qed.

Lemma union_bst t1 t2 : bst_a t1 -> bst_a t2 -> bst_a (union t1 t2).
Proof.
elim: t1 t2=>//=l1 IHl [a1 b1] r1 IHr t2.
case/and4P=>Hal1 Har1 Hbl1 Hbr1.
case E2: t2=>[|l2 [a2 b2] r2]; first by rewrite /= Hal1 Har1 Hbl1 Hbr1.
rewrite -{}E2=>H2; case Hs: (split t2 a1)=>[[l' b'] r'].
case/and5P: (split_bst Hs H2)=>Hl' Hr' Hb' Hbl' Hbr'.
apply: bst_join.
- rewrite (perm_all (< a1) (union_inorder Hbl1 Hbl')) all_cat all_filter Hal1 /=.
  rewrite (perm_all _ Hl') all_filter /=.
  by apply/sub_all/all_predT=>z /= _; apply/implyP=>->; apply: implybT.
- rewrite (perm_all (> a1) (union_inorder Hbr1 Hbr')) all_cat all_filter Har1 /=.
  rewrite (perm_all _ Hr') all_filter /=.
  by apply/sub_all/all_predT=>z /= _; apply/implyP=>->; apply: implybT.
- by apply: IHl.
by apply: IHr.
Qed.

Lemma union_inv t1 t2 : inv t1 -> inv t2 -> inv (union t1 t2).
Proof.
elim: t1 t2=>//=l1 IHl [a1 b1] r1 IHr t2 H1.
case E2: t2=>[|l2 [a2 b2] r2] //; rewrite -{}E2=>H2.
case/inv_node/andP: H1=>Hl1 Hr1.
case Hs: (split t2 a1)=>[[l' b'] r'].
case/andP: (split_inv Hs H2)=>Hl' Hr'.
by apply: inv_join; [apply: IHl|apply: IHr].
Qed.

(* intersection *)

Lemma inter_inorder t1 t2 :
  bst_a t1 ->
  bst_a t2 ->
  perm_eq (inorder_a (inter t1 t2))
          (filter (mem (inorder_a t2)) (inorder_a t1)).
Proof.
elim: t1 t2=>//= l1 IHl [a1 b1] r1 IHr t2.
case/and4P=>Hal1 Har1 Hbl1 Hbr1.
case E2: t2=>[|l2 [a2 b2] r2].
- move=>_ /=; set s := inorder_a l1 ++ a1 :: inorder_a r1.
  suff: filter (mem nil) s = [::] by move=>->.
  by rewrite -(filter_pred0 s); apply: eq_filter=>z /=; rewrite mem_filter.
rewrite -{}E2=>H2; case Hs: (split t2 a1)=>[[l' b'] r'].
case/and5P: (split_bst Hs H2)=>Hl' Hr' Hb' Hbl' Hbr'.
case: {Hs}b' Hb'; rewrite eq_sym => /eqP Ha1.
- apply: perm_trans; first by exact: join_inorder.
  move: (IHr _ Hbr1 Hbr'); rewrite -(perm_cons a1) => /(perm_cat (IHl _ Hbl1 Hbl'))=>H.
  apply: (perm_trans H); rewrite filter_cat /= Ha1; apply: perm_cat.
  - apply/(@eq_perm A)/eq_in_filter=>z /(allP Hal1) /= Hz.
    by move/perm_mem: Hl' =>/(_ z) ->; rewrite mem_filter /= Hz.
  rewrite perm_cons; apply/(@eq_perm A)/eq_in_filter=>z /(allP Har1) /= Hz.
  by move/perm_mem: Hr' =>/(_ z) ->; rewrite mem_filter /= Hz.
apply: perm_trans; first by exact: join2_inorder.
move: (IHr _ Hbr1 Hbr') => /(perm_cat (IHl _ Hbl1 Hbl'))=>H.
apply: (perm_trans H); rewrite filter_cat /= Ha1; apply: perm_cat.
- apply/(@eq_perm A)/eq_in_filter=>z /(allP Hal1) /= Hz.
by move/perm_mem: Hl' =>/(_ z) ->; rewrite mem_filter /= Hz.
apply/(@eq_perm A)/eq_in_filter=>z /(allP Har1) /= Hz.
by move/perm_mem: Hr' =>/(_ z) ->; rewrite mem_filter /= Hz.
Qed.

Lemma inter_bst t1 t2 : bst_a t1 -> bst_a t2 -> bst_a (inter t1 t2).
Proof.
elim: t1 t2=>//=l1 IHl [a1 b1] r1 IHr t2.
case/and4P=>Hal1 Har1 Hbl1 Hbr1.
case E2: t2=>[|l2 [a2 b2] r2] //; rewrite -{}E2=>H2.
case Hs: (split t2 a1)=>[[l' b'] r'].
case/and5P: (split_bst Hs H2)=>Hl' Hr' Hb' Hbl' Hbr'.
case: {Hs}b' Hb'; rewrite eq_sym => /eqP Ha1.
- apply: bst_join.
  - rewrite (perm_all (< a1) (inter_inorder Hbl1 Hbl')) all_filter.
    by apply/sub_all/Hal1=>z /= Hz; apply/implyP.
  - rewrite (perm_all (> a1) (inter_inorder Hbr1 Hbr')) all_filter.
    by apply/sub_all/Har1=>z /= Hz; apply/implyP.
  - by apply: IHl.
  by apply: IHr.
apply: join2_bst.
- by apply: IHl.
- by apply: IHr.
rewrite (perm_allrell _ _ (inter_inorder Hbl1 Hbl')) (perm_allrelr _ _ (inter_inorder Hbr1 Hbr')).
apply/allrel_filterl/allrel_filterr.
by apply/sub_all/Hal1=>z /= Hz; apply/sub_all/Har1=>y Hy; apply/lt_trans/Hy.
Qed.

Lemma inter_inv t1 t2 : inv t1 -> inv t2 -> inv (inter t1 t2).
Proof.
elim: t1 t2=>//=l1 IHl [a1 b1] r1 IHr t2 H1.
case E2: t2=>[|l2 [a2 b2] r2] //; rewrite -{}E2=>H2.
case/inv_node/andP: H1=>Hl1 Hr1.
case Hs: (split t2 a1)=>[[l' b'] r'].
case/andP: (split_inv Hs H2)=>Hl' Hr'.
case: {Hs}b'.
- by apply: inv_join; [apply: IHl|apply: IHr].
by apply: join2_inv; [apply: IHl|apply: IHr].
Qed.

(* difference *)

Lemma diff_inorder t1 t2 :
  bst_a t1 ->
  bst_a t2 ->
  perm_eq (inorder_a (diff t1 t2))
          (filter [predC mem (inorder_a t2)] (inorder_a t1)).
Proof.
elim: t2 t1=>/= [|l2 IHl [a2 _] r2 IHr] t1.
- move=>H1 _; suff: filter [predC mem nil] (inorder_a t1) = inorder_a t1 by move=>->.
  by apply/all_filterP/allP.
case E1: t1=>[|l1 [a1 b1] r1] //; rewrite -{}E1=>H1.
case/and4P=>Hal2 Har2 Hbl2 Hbr2.
case Hs: (split t1 a2)=>[[l' b'] r'].
case/and5P: (split_bst Hs H1)=>Hl' Hr' _ Hbl' Hbr'.
apply: perm_trans; first by exact: join2_inorder.
move: (IHr _ Hbr' Hbr2) => /(perm_cat (IHl _ Hbl' Hbl2))=>H.
apply: (perm_trans H).
move: (perm_cat (perm_filter [predC inorder_a l2] Hl') (perm_filter [predC inorder_a r2] Hr')) =>H'.
apply/(perm_trans H')/perm_trans; last by apply/permEl/(perm_filterC (<= a2)).
rewrite -!filter_predI; apply: perm_cat.
- apply/(@eq_perm A)/eq_filter=>z /=; rewrite mem_cat inE !negb_or.
  case: (ltgtP z a2)=>//=; last by rewrite andbF.
  rewrite andbT=>Hz; suff: z \notin inorder_a r2 by move=>->; rewrite andbT.
  apply/count_memPn/eqP; rewrite eqn0Ngt -has_count -all_predC.
  by apply/sub_all/Har2=>y /= /(lt_trans Hz); rewrite eq_sym lt_neqAle; case/andP.
apply/(@eq_perm A)/eq_filter=>z /=; rewrite mem_cat inE !negb_or.
case: (ltgtP a2 z)=>/=; try by rewrite andbF.
rewrite andbT=>Hz; suff: z \notin inorder_a l2 by move=>->.
apply/count_memPn/eqP; rewrite eqn0Ngt -has_count -all_predC.
by apply/sub_all/Hal2=>y /= Hy; move: (lt_trans Hy Hz); rewrite lt_neqAle; case/andP.
Qed.

Lemma diff_bst t1 t2 : bst_a t1 -> bst_a t2 -> bst_a (diff t1 t2).
Proof.
elim: t2 t1=>//=l2 IHl [a2 _] r2 IHr t1.
case E1: t1=>[|l1 [a1 b1] r1] //; rewrite -{}E1=>H1.
case/and4P=>Hal2 Har2 Hbl2 Hbr2.
case Hs: (split t1 a2)=>[[l' b'] r'].
case/and5P: (split_bst Hs H1)=>Hl' Hr' _ Hbl' Hbr'.
apply: join2_bst.
- by apply: IHl.
- by apply: IHr.
rewrite (perm_allrell _ _ (diff_inorder Hbl' Hbl2)) (perm_allrelr _ _ (diff_inorder Hbr' Hbr2)).
apply/allrel_filterl/allrel_filterr; rewrite (perm_allrell _ _ Hl') (perm_allrelr _ _ Hr').
rewrite /allrel all_filter.
apply/sub_all/all_predT=>z /= _; apply/implyP=>Hz; rewrite all_filter.
by apply/sub_all/all_predT=>y /= _; apply/implyP=>Hy; apply/lt_trans/Hy.
Qed.

Lemma diff_inv t1 t2 : inv t1 -> inv t2 -> inv (diff t1 t2).
Proof.
elim: t2 t1=>//=l2 IHl [a2 b2] r2 IHr t1.
case E1: t1=>[|l1 [a1 b1] r1] //; rewrite -{}E1=>H1.
case/inv_node/andP=>Hl2 Hr2.
case Hs: (split t1 a2)=>[[l' b'] r'].
case/andP: (split_inv Hs H1)=>Hl' Hr'.
by apply: join2_inv; [apply: IHl|apply: IHr].
Qed.

End JustJoin.

Section JoiningRedBlackTrees.
Context {disp : unit} {T : orderType disp}.

Lemma ne_bhgt (t1 t2 : rbt T) : non_empty_if (bh t1 < bh t2)%N t2.
Proof.
case: ltnP; last by move=>_; apply: Def.
by case: t2=>//= l [a n] r _; apply: Nd.
Qed.

Equations? joinL (l : rbt T) (x : T) (r : rbt T) : rbt T by wf (size_tree r) lt :=
joinL l x r with (ne_bhgt l r) := {
  | @Nd lr (xr, Red)   rr _ _ => R     (joinL l x lr) xr rr
  | @Nd lr (xr, Black) rr _ _ => baliL (joinL l x lr) xr rr
  | Def => R l x r
  }.
Proof.
all: apply: ssrnat.ltP.
- by rewrite addn1 ltnS; apply: leq_addr.
by rewrite addn1 ltnS; apply: leq_addr.
Qed.

Equations? joinR (l : rbt T) (x : T) (r : rbt T) : rbt T by wf (size_tree l) lt :=
joinR l x r with (ne_bhgt r l) := {
  | @Nd ll (xl, Red)   rl _ _ => R     ll xl (joinR rl x r)
  | @Nd ll (xl, Black) rl _ _ => baliR ll xl (joinR rl x r)
  | Def => R l x r
  }.
Proof.
all: apply: ssrnat.ltP.
- by rewrite addn1 addnC ltnS; apply: leq_addr.
by rewrite addn1 addnC ltnS; apply: leq_addr.
Qed.

Definition joinRBT (l : rbt T) (x : T) (r : rbt T) : rbt T :=
  if (bh r < bh l)%N
    then paint Black (joinR l x r)
    else if (bh l < bh r)%N
      then paint Black (joinL l x r)
      else B l x r.

(* Correctness *)

(* joinL *)

Lemma invc2_joinL l x r :
  invc l -> invc r -> (bh l <= bh r)%N ->
  invc2 (joinL l x r) && ((bh l != bh r) && (color r == Black) ==> invc (joinL l x r)).
Proof.
funelim (joinL l x r); simp joinL; rewrite {}Heq /=.
- rewrite /invc2; rewrite {}e /= addn0 in i *.
  have/negbTE->: (Red != Black) by [].
  rewrite andbF /= andbT=> Hcl /and3P [/andP [Hlrb _] Hclr -> E]; rewrite andbT.
  case/andP: (H Hcl Hclr E)=>_; rewrite Hlrb !andbT /= => /implyP; apply.
  by move: i; rewrite ltn_neqAle E andbT.
- rewrite e /= in i *; rewrite eq_refl /= andbT.
  move=>Hcl /andP [Hclr Hcrr] _; move: i; rewrite addn1 ltnS=>E.
  case/andP: (H Hcl Hclr E)=>H2 _.
  have Hib := invc_baliL xr H2 Hcrr.
  by rewrite Hib (invc2I Hib) /=; exact: implybT.
rewrite /invc2 /= =>->-> /= Hlr; rewrite andbT.
move: i0; rewrite -leqNgt=>Hrl.
have/eqP->: bh l == bh r by rewrite eqn_leq Hlr Hrl.
by rewrite eq_refl.
Qed.

Lemma bh_joinL l x r :
  invh l -> invh r -> (bh l <= bh r)%N ->
  bh (joinL l x r) == bh r.
Proof.
funelim (joinL l x r); simp joinL; rewrite {}Heq /=.
- move=>Hl; rewrite {}e /= !addn0 => /and3P [_ Hlr _] E.
  by apply: H.
- move=>Hl; rewrite {}e /= in i *; case/and3P=>E1 Hlr _ _.
  move: i; rewrite {1}addn1 ltnS=>E.
  move/eqP: (H Hl Hlr E)=>E2; rewrite -E2.
  by apply: bh_baliL; rewrite E2.
move=>_ _; move: i0; rewrite -leqNgt=>Hrl Hlr.
by rewrite addn0 eqn_leq Hlr Hrl.
Qed.

Lemma invh_joinL l x r :
  invh l -> invh r -> (bh l <= bh r)%N ->
  invh (joinL l x r).
Proof.
funelim (joinL l x r); simp joinL; rewrite {}Heq /=.
- move=>Hl; rewrite {Heqcall r}e /= addn0 in i *.
  case/and3P=>/eqP<- Hlr -> E; rewrite andbT.
  by apply/andP; split; [apply: bh_joinL | apply: H].
- move=>Hl; rewrite {Heqcall r}e /= in i *; case/and3P=>/eqP E1 Hlr Hrr _.
  move: i; rewrite addn1 ltnS=>E.
  apply: invh_baliL=>//; first by apply: H.
  by rewrite -E1; apply: bh_joinL.
move=>->->/=; move: i0; rewrite andbT -leqNgt=>Hrl Hlr.
by rewrite eqn_leq Hlr Hrl.
Qed.

Lemma joinL_inorder l a r :
  perm_eq (inorder_a (joinL l a r)) (inorder_a l ++ a :: inorder_a r).
Proof.
funelim (joinL l a r); simp joinL; rewrite {}Heq //= e /=.
- by rewrite -cat_cons catA perm_cat2r.
by rewrite inorder_baliL -cat_cons catA perm_cat2r.
Qed.

Lemma bst_baliL (l : rbt T) a r :
  bst_a l -> bst_a r -> all (< a) (inorder_a l) -> all (> a) (inorder_a r) ->
  bst_a (baliL l a r).
Proof.
funelim (baliL l a r); simp baliL=>/= /[swap] ->; rewrite !andbT //.
- by move=>_->->.
- rewrite !all_cat /= -!andbA.
  case/and7P=>->->_->->->->/and4P[_ _ Hbc ->] H4 /=; rewrite Hbc H4 /= andbT.
  by apply/sub_all/H4=>z Hz; apply/lt_trans/Hz.
- rewrite !all_cat /= -!andbA.
  by case/and7P=>->->->->->->->/and4P[->->->->]->.
- by case/andP=>->->/andP[->->]->.
- rewrite !all_cat /= -!andbA.
  case/and9P=>->->->->->->->->->/and5P[_ _ _ Hbc ->] H4 /=; rewrite Hbc H4 /= andbT.
  by apply/sub_all/H4=>z Hz; apply/lt_trans/Hz.
- rewrite !all_cat /= -!andbA.
  by case/and9P=>->->->->->->->->->/and5P[->->->->->]->.
- rewrite !all_cat /= -!andbA andbT.
  by case/and7P=>->->->->->->->/and4P[->->->->]->.
- rewrite !all_cat /= -!andbA all_cat /=.
  case/and14P=>H0 H0a H1 ->Hab _->->->->->->->->/and7P[_ _ _ _ _ Hbc ->] H4/=.
  rewrite H0 H0a H1 Hab Hbc H4 /= andbT.
  apply/and4P; split.
  - by apply/sub_all/H0=>z /= Hz; apply/lt_trans/Hab.
  - by apply/lt_trans/Hab.
  - by apply/sub_all/H1=>z /= Hz; apply/lt_trans/Hab.
  by apply/sub_all/H4=>z /(lt_trans Hbc).
- rewrite !all_cat /= -!andbA all_cat /= -!andbA.
  by case/and14P=>->->->->->->->->->->->->->->/and7P[->->->->->->->]->.
rewrite !all_cat /= -!andbA.
by case/and9P=>->->->->->->->->->/and5P[->->->->->]->.
Qed.

Lemma bst_joinL l a r :
  all (< a) (inorder_a l) -> all (> a) (inorder_a r) ->
  bst_a l -> bst_a r ->
  (bh l <= bh r)%N ->
  bst_a (joinL l a r).
Proof.
funelim (joinL l a r); simp joinL; rewrite {}Heq /=; last by move=>->->->->.
- rewrite {}e /= addn0 all_cat /= => Hal /and3P [Halr Hx _] Hbl /and4P [Halr' -> Hblr ->] E /=.
  rewrite andbT; apply/andP; split; last by apply: H.
  rewrite (perm_all _ (joinL_inorder l x lr)) all_cat /= Hx Halr' /= andbT.
  by apply/sub_all/Hal=>z /= Hz; apply/lt_trans/Hx.
rewrite {}e /= in i *.
rewrite all_cat /= => Hal /and3P [Halr Hx _] Hbl /and4P [Halr' Harr' Hblr Hbrr] _.
apply: bst_baliL=>//; first by apply: H=>//; move: i; rewrite addn1 ltnS.
rewrite (perm_all _ (joinL_inorder l x lr)) all_cat /= Hx Halr' /= andbT.
by apply/sub_all/Hal=>z /= Hz; apply/lt_trans/Hx.
Qed.

(* joinR *)

(* we need extra invh's because bh only counts left branches *)
Lemma invc2_joinR l x r :
  invc l -> invc r -> invh l -> invh r -> (bh r <= bh l)%N ->
  invc2 (joinR l x r) && ((bh l != bh r) && (color l == Black) ==> invc (joinR l x r)).
Proof.
funelim (joinR l x r); simp joinR; rewrite {}Heq /=.
- rewrite /invc2; rewrite {}e /= addn0 in i *.
  have/negbTE->: (Red != Black) by [].
  rewrite andbF /= andbT => /and3P [/andP [_ Hrlb] -> Hcrl] Hcr /and3P [/eqP E1 Hhll Hhrl] Hhr E /=.
  rewrite E1 in E i.
  case/andP: (H Hcrl Hcr Hhrl Hhr E)=>_; rewrite Hrlb !andbT /= => /implyP; apply.
  by move: i; rewrite ltn_neqAle E andbT eq_sym.
- rewrite e /= in i *; rewrite eq_refl /= andbT.
  move=>/andP [Hcll Hcrl] Hcr /and3P [/eqP E1 Hhll Hhrl] Hhr _.
  move: i; rewrite addn1 ltnS E1=>E.
  case/andP: (H Hcrl Hcr Hhrl Hhr  E)=>H2 _.
  have Hib := invc_baliR xl Hcll H2.
  by rewrite Hib (invc2I Hib) /=; exact: implybT.
rewrite /invc2 /= =>->-> _ _/= Hlr; rewrite andbT.
move: i0; rewrite -leqNgt=>Hrl.
have/eqP->: bh l == bh r by rewrite eqn_leq Hlr Hrl.
by rewrite eq_refl.
Qed.

Lemma bh_joinR l x r :
  invh l -> invh r -> (bh r <= bh l)%N ->
  bh (joinR l x r) == bh l.
Proof.
funelim (joinR l x r); simp joinR; rewrite {}Heq /= ?addn0 //.
- by rewrite {}e /= addn0.
rewrite {}e /= in i *; case/and3P=>/eqP E1 Hll Hrl Hr ?.
move: i; rewrite {1}addn1 ltnS E1=>E.
move/eqP: (H Hrl Hr E)=>E2; rewrite -E1.
by apply: bh_baliR; rewrite E2 E1.
Qed.

Lemma invh_joinR l x r :
  invh l -> invh r -> (bh r <= bh l)%N ->
  invh (joinR l x r).
Proof.
funelim (joinR l x r); simp joinR; rewrite {}Heq /=.
- rewrite {Heqcall l i}e /= addn0; case/and3P=>/eqP E1 -> Hrl Hr E /=; rewrite E1 in E *.
  by rewrite eq_sym; apply/andP; split; [apply: bh_joinR | apply: H].
- rewrite {Heqcall l}e /= in i *; case/and3P=>/eqP E1 Hll Hrl ? ?.
  move: i; rewrite addn1 ltnS E1=>E.
  apply: invh_baliR=>//; first by apply: H.
  by rewrite E1 eq_sym; apply: bh_joinR.
move=>->->/=; move: i0; rewrite andbT -leqNgt=>Hrl Hlr.
by rewrite eqn_leq Hlr Hrl.
Qed.

Lemma joinR_inorder l a r :
  perm_eq (inorder_a (joinR l a r)) (inorder_a l ++ a :: inorder_a r).
Proof.
funelim (joinR l a r); simp joinR; rewrite {}Heq //= e /=.
- by rewrite -catA perm_cat2l perm_cons.
by rewrite inorder_baliR -catA perm_cat2l perm_cons.
Qed.

Lemma bst_baliR (l : rbt T) a r :
  bst_a l -> bst_a r -> all (< a) (inorder_a l) -> all (> a) (inorder_a r) ->
  bst_a (baliR l a r).
Proof.
funelim (baliR l a r); simp baliR=>/=->; rewrite ?andbT //=.
- by move=>_->->.
- rewrite !all_cat /= -!andbA andbT.
  case/and7P=>_->->->->->->H1/and4P[-> Hab _ _] /=; rewrite H1 Hab /= andbT.
  by apply/sub_all/H1=>z /= Hz; apply/lt_trans/Hab.
- rewrite !all_cat /= -!andbA /= andbT.
  by case/and7P=>->->->->->->->->/and4P[->->->->].
- rewrite !all_cat /= -!andbA all_cat /=.
  case/and9P=>->->->->->->->->->H1/and5P[->Hab _ _ _] /=; rewrite H1 Hab /= andbT.
  by apply/sub_all/H1=>z /= Hz; apply/lt_trans/Hab.
- rewrite !all_cat /= -!andbA.
  by case/and7P=>->->->->->->->->/and4P[->->->->].
- rewrite !all_cat /= -!andbA !all_cat /= -!andbA.
  case/and14P=>_ Hbc->H0 Hc1 H4 ->->->->->->->->H1/and7P[->Hab _ _ _ _ _] /=.
  rewrite H0 H1 H4 Hab Hbc Hc1 /= andbT.
  apply/and4P; split.
  - by apply/sub_all/H1=>z /= Hz; apply/lt_trans/Hab.
  - by apply/sub_all/H0=>z /(lt_trans Hbc).
  - by apply/lt_trans/Hc1.
  by apply/sub_all/H4=>z /(lt_trans Hbc).
- rewrite !all_cat /= -!andbA /= all_cat /= -!andbA.
  by case/and14P=>->->->->->->->->->->->->->->->/and7P[->->->->->->->].
rewrite !all_cat /= -!andbA.
by case/and4P=>->->->->->/and3P[->->->].
Qed.

Lemma bst_joinR l a r :
  all (< a) (inorder_a l) -> all (> a) (inorder_a r) ->
  bst_a l -> bst_a r ->
  bst_a (joinR l a r).
Proof.
funelim (joinR l a r); simp joinR; rewrite {}Heq /=; last by move=>->->->->.
- rewrite {}e /= all_cat /= => /and3P [_ Hx Harl] Har /and4P [-> Harl' -> Hbrl] Hbr /=.
  apply/andP; split; last by apply: H.
  rewrite (perm_all _ (joinR_inorder rl x r)) all_cat /= Hx Harl' /=.
  by apply/sub_all/Har=>z /= /(lt_trans Hx).
rewrite {}e /= in i *.
rewrite all_cat /= => /and3P [_ Hx Harl] Har /and4P [Hall' Harl' Hbll Hbrl] Hbr.
apply: bst_baliR=>//; first by apply: H.
rewrite (perm_all _ (joinR_inorder rl x r)) all_cat /= Hx Harl' /=.
by apply/sub_all/Har=>z /= /(lt_trans Hx).
Qed.

(* joinRBT *)

Lemma joinRBT_inorder l a r :
  perm_eq (inorder_a (joinRBT l a r))
          (inorder_a l ++ a :: inorder_a r).
Proof.
rewrite /joinRBT; case: ifP=>_.
- by rewrite inorder_paint; exact: joinR_inorder.
by case: ifP=>_ //; rewrite inorder_paint; exact: joinL_inorder.
Qed.

Lemma bst_paint (t : rbt T) c : bst_a (paint c t) = bst_a t.
Proof. by case: t=>//=l [a c'] r. Qed.

Lemma bst_joinRBT l a r :
  all (< a) (inorder_a l) -> all (> a) (inorder_a r) ->
  bst_a l -> bst_a r ->
  bst_a (joinRBT l a r).
Proof.
move=>Hal Har Hbl Hbr; rewrite /joinRBT; case: ifP=>E.
- by rewrite bst_paint; apply: bst_joinR.
case: ifP=>_ /=; last by rewrite Hal Har Hbl Hbr.
rewrite bst_paint; apply: bst_joinL=>//.
by move/negbT: E; rewrite -leqNgt.
Qed.

Definition invr (t : rbt T) := invc t && invh t.

Lemma invr_leaf : invr empty_a.
Proof. by []. Qed.

Lemma invr_joinRBT l a r : invr l -> invr r -> invr (joinRBT l a r).
Proof.
rewrite /invr; case/andP=>Hcl Hhl; case/andP=>Hcr Hhr.
rewrite /joinRBT; case: ltnP=>[/ltnW|] E.
- apply/andP; split; last by apply/invh_paint/invh_joinR.
  by case/andP: (invc2_joinR a Hcl Hcr Hhl Hhr E); rewrite /invc2.
case: ltnP=>E' /=; last by rewrite Hcl Hcr Hhl Hhr /= andbT eqn_leq E E'.
apply/andP; split; last by apply/invh_paint/invh_joinL.
by case/andP: (invc2_joinL a Hcl Hcr E); rewrite /invc2.
Qed.

Lemma invr_node l a b r : invr (Node l (a, b) r) -> invr l && invr r.
Proof. by rewrite /invr /= -!andbA; case/and6P=>_->->_->->. Qed.

End JoiningRedBlackTrees.