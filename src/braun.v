From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq prime bigop ssrAC.
From favssr Require Import prelude bintree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Array.
Record Array (T : Type) : Type :=
  make {tp :> Type;
        lookup : T -> tp -> nat -> T;
        update : nat -> T -> tp -> tp;
        len : tp -> nat;
        array : seq T -> tp;

        list : tp -> seq T;
        invar : tp -> bool;

        _ : forall x0 ar n, invar ar -> n < len ar ->
              lookup x0 ar n = nth x0 (list ar) n;
        _ : forall x ar n, invar ar -> n < len ar ->
              invar (update n x ar);
        _ : forall x0 x ar n, invar ar -> n < len ar ->
              list (update n x ar) = set_nth x0 (list ar) n x;
        _ : forall ar, invar ar -> len ar = size (list ar);
        _ : forall xs, invar (array xs);
        _ : forall xs, list (array xs) = xs
        }.
End Array.

Section BraunTrees.
Context {A : Type}.

Fixpoint braun (t : tree A) : bool :=
  if t is Node l _ r
    then [&& ((size_tree l == size_tree r) || (size_tree l == size_tree r + 1)),
             braun l & braun r]
    else true.

Lemma acomplete_compose (l : tree A) x r :
  acomplete l -> acomplete r ->
  size_tree l == size_tree r + 1 ->
  acomplete (Node l x r).
Proof.
move=>Hl Hr E; rewrite /acomplete.
have/eqP->: height (Node l x r) == up_log 2 (size1_tree r + 1) + 1.
- rewrite /= eqn_add2r (acomplete_h Hl) (acomplete_h Hr) size1_size (eqP E) -size1_size.
  by apply/eqP/maxn_idPl/leq_up_log/leq_addr.
have/eqP->: min_height (Node l x r) == trunc_log 2 (size1_tree r) + 1.
- rewrite /= eqn_add2r (acomplete_mh Hl) (acomplete_mh Hr) size1_size (eqP E) -size1_size.
  by apply/eqP/minn_idPr/leq_trunc_log/leq_addr.
rewrite -subnBA ?addnK; last by rewrite addn1.
rewrite up_log_trunc_log //; last by rewrite size1_size !addn1.
by rewrite addn1 /= subSnn.
Qed.

Lemma braun_acomplete t : braun t -> acomplete t.
Proof.
elim: t=>//=l IHl a r IHr /and3P [E /IHl Hl /IHr Hr].
case/orP: E=>[/eqP E|E]; last by apply: acomplete_compose.
rewrite /acomplete /= -subnBA ?addnK; last by rewrite addn1.
have ->: height l = height r.
- by rewrite (acomplete_h Hl) (acomplete_h Hr) !size1_size E.
have ->: min_height l = min_height r.
- by rewrite (acomplete_mh Hl) (acomplete_mh Hr) !size1_size E.
by rewrite maxnn minnn.
Qed.

End BraunTrees.

Section ArraysViaBraunTrees.
Context {A : Type}.

Fixpoint lookup1 (x0 : A) (t : tree A) (n : nat) : A :=
  if t is Node l x r then
    if n == 1 then x else lookup1 x0 (if ~~ odd n then l else r) n./2
    else x0.

Fixpoint update1 (n : nat) (x : A) (t : tree A) : tree A :=
  if t is Node l a r then
    if n == 1 then Node l x r
      else if ~~ odd n
        then Node (update1 n./2 x l) a r
        else Node l                  a (update1 n./2 x r)
    else Node leaf x leaf.

Fixpoint adds (xs : seq A) (n : nat) (t : tree A) : tree A :=
  if xs is x::s then
    adds s n.+1 (update1 n.+1 x t)
  else t.

(* operations *)

Definition br_tree T : Type := tree T * nat.

Definition lookup x0 (t : br_tree A) n :=
  lookup1 x0 t.1 n.+1.

Definition update n x (t : br_tree A) :=
  let: (t', m) := t in
  (update1 n.+1 x t', m).

Definition len (t : br_tree A) := t.2.

Definition array xs := (adds xs 0 leaf, size xs).

(* Functional Correctness *)

Equations? splice (xs ys : seq A) : seq A by wf (size xs + size ys) lt :=
splice [::]   ys => ys;
splice (x::s) ys => x :: splice ys s.
Proof. by apply: ssrnat.ltP; rewrite addnC addSn ltnS. Qed.

Lemma size_splice xs ys : size (splice xs ys) = size xs + size ys.
Proof. by funelim (splice xs ys); simp splice=>//=; rewrite H addnC addSn. Qed.

Fixpoint list1 (t : tree A) : seq A :=
  if t is Node l x r then x :: splice (list1 l) (list1 r) else [::].

Lemma size_list1 t : size_tree t = size (list1 t).
Proof. by elim: t=>//=l -> _ r ->; rewrite size_splice addn1. Qed.

Lemma list1_empty t : list1 t = [::] -> t = leaf.
Proof. by case: t. Qed.

(* TODO this is awkward *)
Lemma braun_iota (l : tree A) x r n :
  braun (Node l x r) -> n \in iota 1 (size_tree (Node l x r)) -> 1 < n ->
  (odd n ==> (n./2 \in iota 1 (size_tree r))) && (~~ odd n ==> (n./2 \in iota 1 (size_tree l))).
Proof.
rewrite /=; case/and3P=>E Hl Hr.
case: n=>//=; case=>//=; elim=>/=.
- rewrite !mem_iota /= addnC -addnA {1}(_ : 2 = 0+2) // ltn_add2r addn_gt0 => E2 _.
  rewrite addnC addn1=>/=; rewrite ltnS.
  by case/orP: E2=>//; case/orP: E=>/eqP->// _; rewrite addn1.
move=>n; rewrite !mem_iota /= addnC -addnA -addn2 leq_add2r ltn_add2r.
case Ho: (odd n)=>/=; rewrite andbT=>IH H _.
- have H': n < size_tree l + size_tree r by apply/ltn_trans/H/ltnSn.
  move: (IH H' erefl); rewrite addnC (addnC 1) -(addn1 n./2) -(addn1 (uphalf n)) !ltn_add2r.
  rewrite uphalf_half Ho /= addnC.
  case/orP: E=>/eqP S H''; last by rewrite S ltn_add2r.
  move: H; rewrite S addnn =>/uphalf_leq; rewrite uphalf_double=>H'''.
  apply/leq_trans/H'''; rewrite uphalf_half -{2}addn2 halfD /= Ho andbF /= add0n.
  by rewrite addn1 ltnS.
have H': n < size_tree l + size_tree r by apply/ltn_trans/H/ltnSn.
move: (IH H' erefl); rewrite addnC (addnC 1) -(addn1 n./2) -(addn1 (uphalf n)) !ltn_add2r.
rewrite uphalf_half Ho /= add0n.
case/orP: E=>/eqP S H''; first by rewrite -S.
move: (H); rewrite S addnAC -(addn1 n) ltn_add2r addnn =>/half_leq.
rewrite doubleK -(addn1 n) halfD Ho /= addn0 add0n.
rewrite ltn_neqAle=>->; rewrite andbT; apply/negP=>/eqP E.
by move: H; rewrite S -E addnAC addnn -{1}(odd_double_half n) Ho add0n addn1 ltnn.
Qed.

Lemma nth_splice x0 n xs ys :
  n < size xs + size ys -> size ys <= size xs <= size ys + 1 ->
  nth x0 (splice xs ys) n = nth x0 (if ~~odd n then xs else ys) n./2.
Proof.
funelim (splice xs ys); simp splice=>/=.
- rewrite add0n leqn0=>/[swap]; case/andP=>/eqP/size0nil->/=_.
  by move/ltnW; rewrite leqn0=>/eqP->.
case: n=>//=n H1 H2; rewrite H; first last.
- by move: H2; rewrite !addn1 ltnS; case/andP=>->->.
- by move: H1; rewrite addnC addnS.
by rewrite uphalf_half; case: (odd n).
Qed.

Lemma lookup1_braun x0 t n :
  braun t -> n < size_tree t -> lookup1 x0 t n.+1 = nth x0 (list1 t) n.
Proof.
elim: t n=>/=[|l IHl a r IHr] n; first by move=>_/ltnW; rewrite leqn0=>/eqP->.
case/and3P=>E Hl Hr; case: n=>//=n; rewrite -(addn1 n) ltn_add2r=>H.
rewrite nth_splice; first last.
- by rewrite -!size_list1; case/orP: E=>/eqP->; rewrite leqnn leq_addr.
- by rewrite -!size_list1.
have H' : braun (Node l a r) by rewrite /= E Hl Hr.
have H'': n.+2 \in iota 1 (size_tree (Node l a r)).
- by rewrite mem_iota /= addnC -addnA -addn2 leq_add2r.
move: (braun_iota H' H'' (isT : 1 < n.+2))=>/=.
by case Ho: (odd n)=>/=; rewrite ?andbT mem_iota /= add1n ltnS=>Hr';
[apply: IHr | apply: IHl].
Qed.

Lemma list_lookup1 x0 t :
  braun t -> list1 t = map (lookup1 x0 t) (iota 1 (size_tree t)).
Proof.
move=>H; apply/(eq_from_nth (x0:=x0)).
- by rewrite size_map size_iota size_list1.
move=>i Hi.
rewrite size_list1 (nth_map 0); last by rewrite size_iota.
by rewrite nth_iota // add1n lookup1_braun // size_list1.
Qed.

Lemma update1_size n x t :
  braun t -> n \in iota 1 (size_tree t) ->
  size_tree (update1 n x t) == size_tree t.
Proof.
elim: t n=>//=l IHl a r IHr n /and3P [E Hl Hr].
case: n=>/=; first by rewrite mem_iota ltnn.
case=>//=n H.
have H' : braun (Node l a r) by rewrite /= E Hl Hr.
have H'': n.+2 \in iota 1 (size_tree (Node l a r)) by [].
move: (braun_iota H' H'' (isT : 1 < n.+2))=>/=.
case Ho: (odd n)=>/=; rewrite ?andbT => Hn.
- by rewrite eqn_add2r eqn_add2l; apply: IHr.
by rewrite -!addnA eqn_add2r; apply: IHl.
Qed.

Lemma update1_braun n x t :
  braun t -> n \in iota 1 (size_tree t) ->
  braun (update1 n x t).
Proof.
elim: t n=>//=l IHl a r IHr n /and3P [E Hl Hr].
case: n=>/=; first by rewrite mem_iota ltnn.
case=>/= [_|n H]; first by rewrite E Hl Hr.
have H' : braun (Node l a r) by rewrite /= E Hl Hr.
have H'': n.+2 \in iota 1 (size_tree (Node l a r)) by [].
move: (braun_iota H' H'' (isT : 1 < n.+2))=>/=.
case Ho: (odd n)=>/=; rewrite ?andbT => Hn.
- rewrite Hl /=; apply/andP; split; last by apply: IHr.
  by case/orP: E=>/eqP->; apply/orP; [left|right];
    rewrite eq_sym ?eqn_add2r; apply: update1_size.
rewrite Hr andbT; apply/andP; split; last by apply: IHl.
by case/orP: E=>/eqP<-; apply/orP; [left|right];
  rewrite ?eqn_add2r; apply: update1_size.
Qed.

Lemma update1_lookup x0 n m x t :
  braun t -> n \in iota 1 (size_tree t) ->
  lookup1 x0 (update1 n x t) m = (if n == m then x else lookup1 x0 t m).
Proof.
elim: t n m=>//=l IHl a r IHr n m /and3P [E Hl Hr].
case: n=>/=; first by rewrite mem_iota ltnn.
case=>/=[_|n H].
- case: ifP; first by move/eqP=>->.
  by rewrite eq_sym=>->.
have H' : braun (Node l a r) by rewrite /= E Hl Hr.
have H'': n.+2 \in iota 1 (size_tree (Node l a r)) by [].
move: (braun_iota H' H'' (isT : 1 < n.+2))=>/=.
case Ho: (odd n)=>/=; rewrite ?andbT => Hn.
- case: ifP; first by move/eqP=>->.
  move=>_; case Hom: (odd m)=>/=.
  - rewrite IHr //.
    suff: (n./2.+1 == m./2) = (n.+2 == m) by move=>->.
    rewrite -(odd_double_half n.+2) /= Ho /= -{2}(odd_double_half m) Hom /=.
    by rewrite eqn_add2l -!muln2  eqn_pmul2r.
  by case: ifP=>//; move: Hom=>/[swap] /eqP<-; rewrite -odd2 Ho.
case: ifP; first by move/eqP=>->.
move=>_; case Hom: (odd m)=>/=.
- by case: ifP=>//; move: Hom=>/[swap] /eqP<-; rewrite -odd2 Ho.
rewrite IHl //.
suff: (n./2.+1 == m./2) = (n.+2 == m) by move=>->.
rewrite -(odd_double_half n.+2) /= Ho /= -{2}(odd_double_half m) Hom /=.
by rewrite eqn_add2l -!muln2  eqn_pmul2r.
Qed.

Lemma update1_list x0 n x t:
  braun t -> n \in iota 1 (size_tree t) ->
  list1 (update1 n x t) = set_nth x0 (list1 t) n.-1 x.
Proof.
move=>H1 H2; move/eqP: (update1_size x H1 H2)=>Hu.
move: (H2); rewrite mem_iota; case/andP=>H21 H22.
apply/(eq_from_nth (x0:=x0)).
- rewrite -size_list1 Hu size_set_nth prednK // -size_list1.
  by symmetry; apply/maxn_idPr.
move=>i; rewrite -size_list1 Hu=>Hi.
rewrite -lookup1_braun //; first last.
- by rewrite Hu.
- by apply: update1_braun.
rewrite nth_set_nth /= update1_lookup // lookup1_braun //.
case: ifP; first by move/eqP=>->/=; rewrite eq_refl.
move=>E; case: ifP=>//; move: E=>/[swap]/eqP->.
by rewrite prednK // eq_refl.
Qed.

Lemma update1_size_extend t x :
  braun t ->
  size_tree (update1 (size_tree t + 1) x t) = size_tree t + 1.
Proof.
elim: t=>//=l IHl a r IHr /and3P [E /IHl Hl /IHr Hr].
rewrite -{1 2}addnA addn2 /=.
case Ho: (odd (size_tree l + size_tree r))=>/=.
- apply/eqP; rewrite eqn_add2r -[X in _ == X]addnA eqn_add2l -Hr.
  suff : (size_tree l + size_tree r + 1 + 1)./2 == size_tree r + 1 by move/eqP=>->.
  rewrite -addnA halfD Ho /= add0n eqn_add2r.
  case/orP: E=>/eqP->; first by rewrite addnn doubleK.
  by rewrite addnAC addnn halfD odd_double /= addn0 add0n doubleK.
apply/eqP; rewrite eqn_add2r [X in _ == X]addnAC eqn_add2r -Hl -addnA halfD Ho /= add0n.
case/orP: E=>/eqP E; first by rewrite E addnn doubleK.
by move: Ho; rewrite E addnAC addnn addn1 /= odd_double.
Qed.

Lemma update1_braun_extend t x :
  braun t -> braun (update1 (size_tree t + 1) x t).
Proof.
elim: t=>//=l IHl a r IHr /and3P [E Hl Hr].
rewrite -{1 2}addnA addn2 /=.
have H' : braun (Node l a r) by rewrite /= E Hl Hr.
case Ho: (odd (size_tree l + size_tree r))=>/=.
- case/orP: E=>/eqP E; first by move: Ho; rewrite E addnn odd_double.
  move/eqP: (update1_size_extend x H')=>/=.
  rewrite -{1 2}addnA addn2 /= Ho /= eqn_add2r -[X in _ == X]addnA eqn_add2l=>/eqP->.
  rewrite E Hl /= eq_refl /= (addnAC _ 1 _) addnn -!addnA halfD odd_double /= add0n doubleK.
  by apply: IHr.
case/orP: E=>/eqP E; last by move: Ho; rewrite E addnAC addnn addn1 /= odd_double.
move/eqP: (update1_size_extend x H')=>/=.
rewrite -{1 2}addnA addn2 /= Ho /= eqn_add2r {2}addnAC eqn_add2r=>/eqP->.
rewrite E Hr /= eq_refl orbT /= andbT addnn -addnA halfD odd_double /= add0n doubleK -E.
by apply: IHl.
Qed.

Lemma splice_rcons x y xs ys :
  (size ys <= size xs     -> splice (rcons xs x) ys = rcons (splice xs ys) x) *
  (size xs <= size ys + 1 -> splice xs (rcons ys y) = rcons (splice xs ys) y).
Proof.
funelim (splice xs ys); do!(simp splice=>/=).
- by split=>//; rewrite leqn0=>/eqP/size0nil->.
split.
- by rewrite -addn1=>H1; case: (H y x0)=>_ /(_ H1) ->.
by rewrite addn1 ltnS=>H2; case: (H y x0)=>+ _ =>/(_ H2) ->.
Qed.

Lemma update1_braun_rcons t x :
  braun t -> list1 (update1 (size_tree t + 1) x t) = rcons (list1 t) x.
Proof.
elim: t=>//=l IHl a r IHr /and3P [E /IHl Hl /IHr Hr].
rewrite -{1 2}addnA addn2 /=.
case Ho: (odd (size_tree l + size_tree r))=>/=.
- case/orP: E=>/eqP E; first by move: Ho; rewrite E addnn odd_double.
  rewrite E /= (addnAC _ 1 _) addnn -!addnA halfD odd_double /= add0n doubleK.
  by rewrite Hr (splice_rcons x x) // -!size_list1 E.
case/orP: E=>/eqP E; last by move: Ho; rewrite E addnAC addnn addn1 /= odd_double.
rewrite E addnn -addnA halfD odd_double /= add0n doubleK -E.
by rewrite Hl (splice_rcons x x) // -!size_list1 E.
Qed.

Lemma adds_braun t xs :
  braun t ->
  (size_tree (adds xs (size_tree t) t) == size_tree t + size xs) &&
    braun (adds xs (size_tree t) t).
Proof.
elim: xs t=>[|x s IH] t /=; first by move=>->; rewrite addn0 eq_refl.
move=>H; move: (update1_braun_extend x H); rewrite addn1=>H'.
case/andP: (IH _ H'); move: (update1_size_extend x H); rewrite addn1=>->/eqP->->.
by rewrite andbT addSn addnS.
Qed.

Lemma adds_list t xs :
  braun t -> list1 (adds xs (size_tree t) t) = list1 t ++ xs.
Proof.
elim: xs t=>[|x s IH] t /=; first by rewrite cats0.
move=>H; move: (update1_braun_extend x H); rewrite addn1=>H'.
move: (IH _ H'); move: (update1_size_extend x H); rewrite addn1=>->->.
move: (update1_braun_rcons x H); rewrite addn1=>->.
by rewrite -cats1 -catA.
Qed.

(* corollaries *)

Definition invar (t : br_tree A) : bool := braun t.1 && (t.2 == size_tree t.1).

Definition list (t : br_tree A) := list1 t.1.

Corollary invar_lookup x0 ar n :
  invar ar -> n < len ar ->
  lookup x0 ar n = nth x0 (list ar) n.
Proof.
rewrite /invar /lookup /list; case: ar=>t ln /=; case/andP=>H1 /eqP-> H2.
by apply: lookup1_braun.
Qed.

Corollary invar_update x ar n :
  invar ar -> n < len ar ->
  invar (update n x ar).
Proof.
rewrite /invar /update; case: ar=>t ln /=; case/andP=>H1 /eqP-> H2.
have Hn: n.+1 \in iota 1 (size_tree t) by rewrite mem_iota /= add1n.
apply/andP; split; first by apply: update1_braun.
by rewrite eq_sym; apply: update1_size.
Qed.

Corollary invar_list_update x0 x ar n :
  invar ar -> n < len ar ->
  list (update n x ar) = set_nth x0 (list ar) n x.
Proof.
rewrite /invar /update /list; case: ar=>t ln /=; case/andP=>H1 /eqP-> H2.
by rewrite (update1_list x0)=>//; rewrite mem_iota /= add1n.
Qed.

Corollary invar_len t :
  invar t ->
  len t = size (list t).
Proof. case: t=>t n; rewrite /invar /len /list /=; case/andP=>_ /eqP->; exact: size_list1. Qed.

Corollary invar_array xs : invar (array xs).
Proof.
rewrite /invar /array /=.
have /(adds_braun xs)/=: braun (@Leaf A) by [].
by rewrite add0n; case/andP=>/eqP->->; rewrite eq_refl.
Qed.

Corollary invar_list_array xs : list (array xs) = xs.
Proof.
rewrite /list /array /=.
by have /(adds_list xs)/=: braun (@Leaf A) by [].
Qed.

Definition ArrayBraun :=
  @Array.make _ (br_tree A)
    lookup update len array
    list invar
    invar_lookup
    invar_update invar_list_update
    invar_len
    invar_array invar_list_array.

End ArraysViaBraunTrees.

(* TODO switch to packed structures *)
Module ArrayFlex.
Record ArrayFlex (T : Type) : Type :=
  make {tp :> Type;
        lookup : T -> tp -> nat -> T;
        update : nat -> T -> tp -> tp;
        len : tp -> nat;
        array : seq T -> tp;

        add_lo : T -> tp -> tp;
        del_lo : tp -> tp;
        add_hi : T -> tp -> tp;
        del_hi : tp -> tp;

        list : tp -> seq T;
        invar : tp -> bool;

        _ : forall x0 ar n, invar ar -> n < len ar ->
              lookup x0 ar n = nth x0 (list ar) n;
        _ : forall x ar n, invar ar -> n < len ar ->
              invar (update n x ar);
        _ : forall x0 x ar n, invar ar -> n < len ar ->
              list (update n x ar) = set_nth x0 (list ar) n x;
        _ : forall ar, invar ar -> len ar = size (list ar);
        _ : forall xs, invar (array xs);
        _ : forall xs, list (array xs) = xs;

        _ : forall a ar, invar ar -> invar (add_lo a ar);
        _ : forall a ar, invar ar -> list (add_lo a ar) = a :: list ar;
        _ : forall ar, invar ar -> invar (del_lo ar);
        _ : forall ar, invar ar -> list (del_lo ar) = behead (list ar);
        _ : forall a ar, invar ar -> invar (add_hi a ar);
        _ : forall a ar, invar ar -> list (add_hi a ar) = rcons (list ar) a;
        _ : forall ar, invar ar -> invar (del_hi ar);
        _ : forall ar, invar ar -> list (del_hi ar) = butlast (list ar)
        }.
End ArrayFlex.

Section FlexibleArrays.
Context {A : Type}.

Fixpoint del_hi1 (n : nat) (t : tree A) : tree A :=
  if t is Node l x r then
    if n == 1 then leaf
      else if ~~ odd n then Node (del_hi1 n./2 l) x r
                       else Node l x (del_hi1 n./2 r)
  else leaf.

Fixpoint add_lo1 (x : A) (t : tree A) : tree A :=
  if t is Node l a r
    then Node (add_lo1 a r) x l
    else Node leaf x leaf.

Fixpoint merge (l r : tree A) : tree A :=
  if l is Node ll al rl
    then Node r al (merge ll rl)
    else r.

Definition del_lo1 (t : tree A) : tree A :=
  if t is Node l _ r
    then merge l r
    else leaf.

Definition add_lo (x : A) (t : br_tree A) : br_tree A :=
  let: (t,l) := t in (add_lo1 x t, l.+1).
Definition del_lo (t : br_tree A) : br_tree A :=
  let: (t,l) := t in (del_lo1 t, l.-1).
Definition add_hi (x : A) (t : br_tree A) : br_tree A :=
  let: (t,l) := t in (update1 l.+1 x t, l.+1).
Definition del_hi (t : br_tree A) : br_tree A :=
  let: (t,l) := t in (del_hi1 l t, l.-1).

(* Functional Correctness *)

Lemma butlast_splice (xs ys : seq A) :
  butlast (splice xs ys) = if size ys < size xs then splice (butlast xs) ys
                                                else splice xs (butlast ys).
Proof.
funelim (splice xs ys); simp splice=>//=.
rewrite ltnS; move: H; case: leqP=>{Heqcall}.
- case: s=>[|z s] /=; first by rewrite leqn0=>/eqP/size0nil->.
  simp splice=>_<-.
  by apply: belast_butlast; rewrite size_splice /= addnS.
case: ys=>[|y ys]/=; first by rewrite ltn0.
by simp splice=>/=_->.
Qed.

Lemma del_hi1_list t :
  braun t ->
  list1 (del_hi1 (size_tree t) t) = butlast (list1 t).
Proof.
elim: t=>//=l IHl a r IHr /and3P [E /IHl Hl /IHr Hr].
rewrite -{2}(add0n 1) eqn_add2r; case: ifP.
- by rewrite addn_eq0; case/andP=>/eqP/size0leaf->/eqP/size0leaf->.
move/negbT=>E1; rewrite addn1=>/=; case: ifP=>/=.
- move/negbNE; case/orP: E=>/eqP E; rewrite E; first by rewrite addnn odd_double.
  move=>_; rewrite addnAC addnn addn1 /= doubleK -addn1 -E Hl.
  rewrite belast_butlast; last first.
  - by rewrite size_splice -!size_list1 E addnAC addn1.
  by rewrite butlast_splice -!size_list1 E addn1 ltnS leqnn.
move/negbT/negbNE; case/orP: E=>/eqP E; rewrite E; last first.
- by rewrite addnAC addnn addn1 /= odd_double.
move=>_; rewrite addnn uphalf_double Hr belast_butlast; last first.
- by rewrite size_splice -!size_list1 lt0n.
by rewrite butlast_splice -!size_list1 E ltnn.
Qed.

Lemma del_hi1_braun t : braun t -> braun (del_hi1 (size_tree t) t).
Proof.
elim: t=>//=l IHl a r IHr /and3P [E Hl Hr].
rewrite -{2}(add0n 1) eqn_add2r; case: ifP=>//.
move/negbT=>E1; rewrite addn1=>/=; case: ifP=>/=.
- move/negbNE; case/orP: E=>/eqP E; rewrite E; first by rewrite addnn odd_double.
  move=>_; rewrite addnAC addnn addn1 /= doubleK -addn1 -E Hr IHl //= andbT.
  by rewrite size_list1 del_hi1_list // size_butlast -size_list1 E addn1 /= eq_refl.
move/negbT/negbNE; case/orP: E=>/eqP E; rewrite E; last first.
- by rewrite addnAC addnn addn1 /= odd_double.
move=>_; rewrite addnn uphalf_double Hl IHr //= andbT.
rewrite (size_list1 (del_hi1 _ _)) del_hi1_list // size_butlast -size_list1 addn1.
rewrite prednK ?eq_refl ?orbT //.
by move: E1; rewrite -lt0n addn_gt0 E orbb.
Qed.

Lemma add_lo1_list a t :
  braun t -> list1 (add_lo1 a t) = a :: list1 t.
Proof.
elim: t a=>//=l _ x r IHr a /and3P [_ _ Hr].
by rewrite IHr //; simp splice.
Qed.

Lemma add_lo1_braun x t :
  braun t -> braun (add_lo1 x t).
Proof.
elim: t x=>//=l IHl a r IHr x /and3P [E Hl Hr].
rewrite Hl IHr //= andbT size_list1 add_lo1_list //= -size_list1.
by case/orP: E=>/eqP->; rewrite addn1 eq_refl // orbT.
Qed.

Lemma merge_list l r :
  (size_tree l == size_tree r) || (size_tree l == size_tree r + 1) ->
  braun l -> braun r ->
  list1 (merge l r) = splice (list1 l) (list1 r).
Proof.
elim: l r=>//=ll IHl al rl _ r E /and3P [El Hll Hrl] Hr.
by simp splice; rewrite IHl.
Qed.

Lemma merge_braun l r :
  (size_tree l == size_tree r) || (size_tree l == size_tree r + 1) ->
  braun l -> braun r ->
  braun (merge l r).
Proof.
elim: l r=>//=ll IHl al rl _ r E /and3P [El Hll Hrl] -> /=.
apply/andP; split; last by apply: IHl.
rewrite (size_list1 (merge _ _)) merge_list // size_splice -!size_list1.
by case/orP: E; rewrite eq_sym ?eqn_add2r =>->//; rewrite orbT.
Qed.

Lemma del_lo1_list t : braun t -> list1 (del_lo1 t) = behead (list1 t).
Proof. by case: t=>//=l _ r /and3P [E Hl Hr]; apply: merge_list. Qed.

Lemma del_lo1_braun t : braun t -> braun (del_lo1 t).
Proof. by case: t=>//=l _ r /and3P [E Hl Hr]; apply: merge_braun. Qed.

(* Corollaries *)

Corollary invar_add_lo a t : invar t -> invar (add_lo a t).
Proof.
rewrite /invar /add_lo; case: t=>[t n]/= /andP [E /eqP ->].
apply/andP; split; first by apply: add_lo1_braun.
by rewrite !size_list1 add_lo1_list.
Qed.

Corollary list_add_lo a t : invar t -> list (add_lo a t) = a :: list t.
Proof.
rewrite /invar /add_lo /list; case: t=>[t n]/= /andP [E _].
by apply: add_lo1_list.
Qed.

Corollary invar_del_lo t : invar t -> invar (del_lo t).
Proof.
rewrite /invar /del_lo; case: t=>[t n]/= /andP [E /eqP ->].
apply/andP; split; first by apply: del_lo1_braun.
by rewrite !size_list1 del_lo1_list // size_behead.
Qed.

Corollary list_del_lo t : invar t -> list (del_lo t) = behead (list t).
Proof.
rewrite /invar /add_lo /list; case: t=>[t n]/= /andP [E _].
by apply: del_lo1_list.
Qed.

Corollary invar_add_hi a t : invar t -> invar (add_hi a t).
Proof.
rewrite /invar /add_hi; case: t=>[t n]/= /andP [E /eqP ->].
rewrite -addn1; apply/andP; split; first by apply: update1_braun_extend.
by rewrite update1_size_extend.
Qed.

Corollary list_add_hi a t : invar t -> list (add_hi a t) = rcons (list t) a.
Proof.
rewrite /invar /add_hi /list; case: t=>[t n]/= /andP [E /eqP ->].
by rewrite -addn1; apply: update1_braun_rcons.
Qed.

Corollary invar_del_hi t : invar t -> invar (del_hi t).
Proof.
rewrite /invar /del_hi; case: t=>[t n]/= /andP [E /eqP ->].
apply/andP; split; first by apply: del_hi1_braun.
by rewrite (size_list1 (del_hi1 _ _)) del_hi1_list // size_butlast size_list1.
Qed.

Corollary list_del_hi t : invar t -> list (del_hi t) = butlast (list t).
Proof.
rewrite /invar /del_hi /list; case: t=>[t n]/= /andP [E /eqP ->].
by rewrite del_hi1_list.
Qed.

End FlexibleArrays.

Section BiggerBetterFasterMore.
Context {A : Type}.

(* Fast Size of Braun Trees *)

Fixpoint diff (t : tree A) (n : nat) : nat :=
  if t is Node l _ r then
    if n == 0 then 1
      else if ~~ odd n then diff r n./2.-1 else diff l n./2
  else 0.

Fixpoint size_fast (t : tree A) : nat :=
  if t is Node l _ r then
    let n := size_fast r in 1 + n.*2 + diff l n
  else 0.

Lemma diff_braun t n :
  braun t -> (size_tree t == n) || (size_tree t == n.+1) ->
  diff t n = size_tree t - n.
Proof.
elim: t n =>//=l IHl _ r IHr n /and3P [E Hl Hr] En.
case: eqP=>Hn.
- move: En; rewrite Hn; case/orP; first by rewrite addn1.
  by rewrite -{2}(add0n 1) eqn_add2r addn_eq0; case/andP=>/eqP->/eqP->.
case: ifP=>[|/negbT/negbNE] Ho.
- move: En; case/orP: E=>/eqP->.
  - rewrite addnn; case/orP.
    - by move: Ho=>/[swap]/eqP<- /=; rewrite oddD odd_double.
    rewrite -(addn1 n) eqn_add2r =>/eqP Hn'.
    have Hs : 0 < size_tree r.
    - by rewrite -(ltn_pmul2r (isT : 0 < 2)) mul0n muln2 Hn' lt0n; apply/eqP.
    rewrite IHr //; last first.
    - by rewrite -Hn' doubleK prednK // eq_refl orbT.
    by rewrite -Hn' doubleK -subn1 subnA // -addnBAC // !subnn.
  rewrite (addnAC _ 1) addnn; case/orP; last first.
    - by rewrite -(addn1 n) eqn_add2r; move: Ho=>/[swap]/eqP<-; rewrite oddD odd_double.
  rewrite !addn1=>/eqP <- /=; rewrite doubleK.
  by rewrite IHr // ?subnn // eq_refl.
move: En; case/orP: E=>/eqP E; rewrite E.
- rewrite addnn; case/orP; last first.
  - by rewrite -(addn1 n) eqn_add2r; move: Ho=>/[swap]/eqP<-; rewrite odd_double.
  move/eqP=>Hn'.
  rewrite -Hn' subnn addn1 /= uphalf_double -E.
  by rewrite IHl // ?subnn // eq_refl.
case/orP.
- by rewrite -addnA addnn => /eqP Hn'; move: Ho; rewrite -Hn' odd_double.
rewrite (addnAC _ 1) addnn -(addn1 n) eqn_add2r addn1 => /eqP<-/=.
rewrite uphalf_double -addnBAC // subnn add0n.
rewrite IHl // E; last by rewrite addn1 eq_refl orbT.
by rewrite -addnBAC // subnn.
Qed.

Lemma size_fast_size t : braun t -> size_fast t = size_tree t.
Proof.
elim: t=>//=l IHl _ r IHr /and3P [E Hl Hr].
rewrite (IHr Hr) diff_braun //; last by rewrite -addn1.
rewrite addnC (addnC 1) -addnn !addnA; apply/eqP.
rewrite !eqn_add2r subnK //.
by case/orP: E=>/eqP->//; apply: leq_addr.
Qed.

(* Initializing a Braun Tree with a Fixed Value *)

Equations? braun_of_naive (x : A) (n : nat) : tree A by wf n lt :=
braun_of_naive _ 0 => leaf;
braun_of_naive x (k.+1) with inspect k./2 => {
  | m eqn: Hm with inspect (~~ odd k) => {
    | true  eqn: Ho => Node (braun_of_naive x m   ) x (braun_of_naive x m)
    | false eqn: Ho => Node (braun_of_naive x m.+1) x (braun_of_naive x m)
    }
  }.
Proof.
all: apply: ssrnat.ltP; rewrite ltnS; try by apply: half_le.
by apply: half_lt; move/negbT/negbNE/odd_gt0: Ho.
Qed.

Equations? braun2_of (x : A) (n : nat) : tree A * tree A by wf n lt :=
braun2_of _ 0      => (leaf, Node leaf x leaf);
braun2_of x (k.+1) =>
  let: (s,t) := braun2_of x k./2 in
  if ~~ odd k then (Node s x s, Node t x s)
              else (Node t x s, Node t x t).
Proof. by apply: ssrnat.ltP ; rewrite ltnS; apply: half_le. Qed.

Definition braun_of (x : A) (n : nat) : tree A :=
  (braun2_of x n).1.

Lemma braun2_of_size_braun x n s t :
  braun2_of x n = (s, t) ->
  [&& size_tree s == n, size_tree t == n.+1, braun s & braun t].
Proof.
funelim (braun2_of x n); simp braun2_of; first by case=><-<-.
case Hbo: (braun2_of x k./2)=>[s' t']{Heqcall}.
case/and4P: (H _ _ Hbo)=>/eqP Hss /eqP Hst Hs Ht.
case: ifP=>[|/negbT/negbNE] Ho; case=>{s}<-{t}<-/=;
rewrite -!andbA Hss Hst Hs Ht !addn1 !eq_refl orbT /= andbT.
- rewrite addSn addnn; suff: (k./2).*2 = k by move=>->; rewrite !eq_refl.
  by rewrite -[in RHS](odd_double_half k) (negbTE Ho).
rewrite !addSn addnS addnn; suff: (k./2).*2.+1 = k by move=>->; rewrite !eq_refl.
by rewrite -[in RHS](odd_double_half k) Ho addnC addn1.
Qed.

Lemma splice_nseq k (x : A) : splice (nseq k x) (nseq k x) = nseq k.*2 x.
Proof. by elim: k=>//=k IH; simp splice; rewrite IH. Qed.

Lemma braun2_of_nseq x n s t :
  braun2_of x n = (s,t) ->
  list1 s = nseq n x /\ list1 t = nseq n.+1 x.
Proof.
funelim (braun2_of x n); simp braun2_of=>/=; first by case=><-<-.
case Hbo: (braun2_of x k./2)=>[s' t']{Heqcall}.
case:  (H _ _ Hbo)=>Es Et.
case: ifP=>[|/negbT/negbNE] Ho; case=>{s}<-{t}<-/=;
rewrite Es Et /=; simp splice.
- suff: splice (nseq k./2 x) (nseq k./2 x) = nseq k x by move=>->.
  rewrite -[in RHS](odd_double_half k) (negbTE Ho) add0n.
  by exact: splice_nseq.
suff: x :: splice (nseq k./2 x) (nseq k./2 x) = nseq k x by move=>->.
rewrite -[in RHS](odd_double_half k) Ho /=.
by rewrite splice_nseq.
Qed.

Corollary braun_of_braun x n : braun (braun_of x n).
Proof.
rewrite /braun_of; case Hbo: (braun2_of x n)=>[s t] /=.
by case/and4P: (braun2_of_size_braun Hbo).
Qed.

Corollary braun_of_nseq x n : list1 (braun_of x n) = nseq n x.
Proof.
rewrite /braun_of; case Hbo: (braun2_of x n)=>[s t] /=.
by case: (braun2_of_nseq Hbo).
Qed.

(* Converting a List into a Braun Tree *)

Equations nodes {A} (ls : seq (tree A)) (xs : seq A) (rs : seq (tree A)) : seq (tree A) :=
nodes (l::ls) (x::xs) (r::rs) => Node l    x r    :: nodes ls   xs rs;
nodes (l::ls) (x::xs) [::]    => Node l    x leaf :: nodes ls   xs [::];
nodes [::]    (x::xs) (r::rs) => Node leaf x r    :: nodes [::] xs rs;
nodes [::]    (x::xs) [::]    => Node leaf x leaf :: nodes [::] xs [::];
nodes ls      [::]    rs      => [::].

Equations? brauns {A} (k : nat) (xs : seq A) : seq (tree A) by wf (size xs) lt :=
brauns k [::] => [::];
brauns k xs   => let ys := take (2^k) xs in
                 let zs := drop (2^k) xs in
                 let ts := brauns k.+1 zs in
                 nodes ts ys (drop (2^k) ts).
Proof.
apply: ssrnat.ltP; rewrite /zs /xs ltnS.
rewrite size_drop /= -addn1 -subnBA; last by rewrite expn_gt0.
by apply: leq_subr.
Qed.

Definition brauns1 {A} (xs : seq A) : tree A :=
  nth leaf (brauns 0 xs) 0.

(* Functional Correctness *)

(* every 2k-th element in `drop i xs` *)
Fixpoint take_nths {A} (i k : nat) (xs : seq A) : seq A :=
  if xs is x::s
    then if i is j.+1 then take_nths j k s
                      else x :: take_nths (2^k-1) k s
  else [::].

Lemma take_nths_drop {T} i k j (xs : seq T) :
  take_nths i k (drop j xs) = take_nths (i + j) k xs.
Proof.
elim: xs j=>//=x s IH j; rewrite drop_cons.
case: j=>/=[|j]; first by rewrite addn0.
by rewrite addnS.
Qed.

Lemma take_nths_00 {T} (xs : seq T) : take_nths 0 0 xs = xs.
Proof. by elim: xs=>//=x s ->. Qed.

Lemma splice_take_nths {T} (xs : seq T) :
  splice (take_nths 0 1 xs) (take_nths 1 1 xs) = xs.
Proof. by elim: xs=>//=x s IH; simp splice; rewrite IH. Qed.

Lemma take_nths_take_nths {T} i m j n (xs : seq T) :
  take_nths i m (take_nths j n xs) = take_nths (i * 2^n + j) (m + n) xs.
Proof.
elim: xs i j=>//=x s IH i j.
have Hn: 0 < 2^n by rewrite expn_gt0.
case: j=>/=[|j]; last by rewrite addnS.
rewrite addn0; case: i=>/=[|i]; rewrite IH.
- rewrite expnD mulnBl mul1n addnBA // subnK //.
  by apply: leq_pmull; rewrite expn_gt0.
by rewrite mulSnr -{4}(prednK Hn) addnS subn1.
Qed.

Lemma take_nths_empty {T} i k (xs : seq T) :
  take_nths i k xs = [::] <-> size xs <= i.
Proof. by elim: xs i=>//=x s IH; case. Qed.

Lemma hd_take_nths {T} x0 i k (xs : seq T) :
  i < size xs -> head x0 (take_nths i k xs) = nth x0 xs i.
Proof. by elim: xs i=>//=x s IH; case. Qed.

Lemma take_nths_01_splice {T} (xs : seq T) ys :
  (size xs == size ys) || (size xs == size ys + 1) ->
  take_nths 0 1 (splice xs ys) = xs /\ take_nths 1 1 (splice xs ys) = ys.
Proof.
funelim (splice xs ys); simp splice=>/=.
- by rewrite addn1; case/orP=>//=; rewrite eq_sym=>/eqP/size0nil->.
rewrite -addn1 eqn_add2r orbC eq_sym [X in _||X]eq_sym.
by case/H=>->->.
Qed.

Lemma size_take_nths_00 {T} (xs : seq T) :
  (size (take_nths 0 1 xs) == size (take_nths 1 1 xs)) ||
  (size (take_nths 0 1 xs) == size (take_nths 1 1 xs) + 1).
Proof.
elim: xs=>//=_ s; rewrite (_ : 2^1 - 1 = 1) // -(addn1 (size _)) eqn_add2r.
by case/orP; rewrite eq_sym=>->//; rewrite orbT.
Qed.

Lemma size_nodes {T} ls (xs : seq T) rs : size (nodes ls xs rs) = size xs.
Proof. by funelim (nodes ls xs rs); simp nodes=>//=; rewrite H. Qed.

Lemma nth_nodes {T} x0 i ls (xs : seq T) rs :
  i < size xs ->
  nth leaf (nodes ls xs rs) i = Node (nth leaf ls i)
                                     (nth x0 xs i)
                                     (nth leaf rs i).
Proof.
funelim (nodes ls xs rs); simp nodes=>//=;
rewrite /= in H; rewrite ltnS; case: i=>//=i /(H x0)->;
by rewrite ?nth_nil.
Qed.

Theorem size_brauns {T} k (xs : seq T) :
  size (brauns k xs) = minn (size xs) (2 ^ k).
Proof.
funelim (brauns k xs); simp brauns=>/=; first by rewrite min0n.
by rewrite size_nodes size_take /= minnC.
Qed.

Fixpoint braun_list {T : eqType} (t : tree T) (xs : seq T) : bool :=
  if t is Node l a r
    then if xs is x::s
           then [&& a == x, braun_list l (take_nths 1 1 xs) &
                            braun_list r (take_nths 2 1 xs)]
         else false
  else nilp xs.

Lemma braun_list_eq {T : eqType} (t : tree T) xs :
  braun_list t xs <-> braun t /\ xs = list1 t.
Proof.
elim: t xs=>/=[|l IHl a r IHr] xs; first by split; [move/nilP | case=>_->].
case: xs=>/=[|x s]; first by split=>//; case.
move: (IHl (take_nths 0 1 s))=>{}IHl; move: (IHr (take_nths 1 1 s))=>{}IHr.
rewrite !size_list1; split.
- case/and3P=>/eqP->/IHl [-> <-] /IHr [-> <-] /=.
  by rewrite size_take_nths_00 splice_take_nths.
case; case/and3P=>E Hl Hr; case=>-> Es; rewrite eq_refl /=.
move: (take_nths_01_splice E); rewrite -Es; case=>El Er.
by apply/andP; split; [apply/IHl|apply/IHr].
Qed.

Lemma braun_list_not_nil {T : eqType} (x0 : T) t (xs : seq T) :
  ~~ nilp xs ->
  braun_list t xs <->
  exists l a r, [&& t == Node l a r,
                    a == head x0 xs,
                    braun_list l (take_nths 1 1 xs) &
                    braun_list r (take_nths 2 1 xs)].
Proof.
move=>H; case: t=>/=.
- by move/negbTE: H=>->; split=>//; case=>_[_][_].
move=>l a r; split.
- case: xs H=>//=x s _ /and3P [/eqP-> Hl Hr].
  by exists l, x, r; rewrite !eq_refl Hl Hr.
case=>l'[x'][r'] /and4P [/eqP [->->->]].
by case: xs H=>//=x s _ ->->->.
Qed.

Theorem brauns_correct {T : eqType} i (xs : seq T) k :
  i < minn (size xs) (2 ^ k) ->
  braun_list (nth leaf (brauns k xs) i) (take_nths i k xs).
Proof.
elim/(@size_ind T): xs i k=>[|n IH] xs + i k.
- by move=>->; rewrite min0n.
case: xs=>[|x s]; first by move=>_; rewrite min0n.
rewrite {4}[x::s]lock /= ltnS =>E Hi; simp brauns.
set zs := drop (2 ^ k) (x :: s); rewrite /=.
have Hz: size zs <= n.
- rewrite /zs size_drop /=; apply/leq_trans/E.
  rewrite -addn1 -subnBA; last by rewrite expn_gt0.
  by apply: leq_subr.
set ts := brauns k.+1 zs.
have H: forall m n, n = m + 2^k -> m < size ts ->
          braun_list (nth leaf ts m) (take_nths n k.+1 (x::s)).
- move=>m _ ->; rewrite {1}/ts size_brauns => Hm.
  by move: (IH _ Hz _ _ Hm); rewrite {2}/zs take_nths_drop.
set ts' := drop (2 ^ k) ts.
rewrite (nth_nodes x) /=; last first.
- by rewrite size_take /=; move: Hi; rewrite minnC.
move: (Hi); rewrite leq_min; case/andP=>Hi1 Hi2.
case Ht: (take_nths i k (locked (x :: s)))=>[|h t].
- by move/take_nths_empty: Ht; rewrite -lock leqNgt Hi1.
rewrite -Ht !take_nths_take_nths -lock; apply/andP; split.
- rewrite nth_take // -(hd_take_nths _ k) //.
  by move: Ht; rewrite -lock=>->.
rewrite mul1n addnC add1n -expnS; case: (ltnP i (size ts))=>Hit.
- apply/andP; split; first by apply: H.
  case: (ltnP i (size ts'))=>Hit'.
  - rewrite /ts' nth_drop; apply: H; first by rewrite addnAC addnn expnS mul2n.
    by move: Hit'; rewrite /ts' size_drop ltn_subRL.
  rewrite nth_default // [x :: s]lock /=.
  apply/nilP/take_nths_empty; rewrite -lock /=.
  move: Hit'; rewrite /ts' /ts /zs size_drop size_brauns size_drop /=.
  rewrite subn_minl geq_min {1}expnS mul2n -addnn addnK (leqNgt (2^k)) Hi2 orbF.
  by rewrite -subnDA addnn leq_subLR expnS mul2n.
have Hsi: size s < i + 2 ^ k.
- move: Hit; rewrite /ts size_brauns /zs size_drop /= geq_min.
  case/orP; first by rewrite leq_subLR addnC.
  move=>H'; move: (leq_ltn_trans H' Hi2).
  by rewrite expnS -{2}(mul1n (2^k)) ltn_mul2r andbF.
rewrite nth_default // [x :: s]lock /=; apply/andP; split.
- by apply/nilP/take_nths_empty; rewrite -lock.
rewrite nth_default /=; last first.
- by rewrite /ts' size_drop leq_subLR; apply/(leq_trans Hit)/leq_addl.
apply/nilP/take_nths_empty; rewrite -lock /=; apply: (ltn_trans Hsi).
by rewrite addnC ltn_add2r ltn_exp2l.
Qed.

Corollary brauns1_correct {T : eqType} (xs : seq T) :
  braun (brauns1 xs) /\ list1 (brauns1 xs) = xs.
Proof.
move: (leq0n (size xs)); rewrite leq_eqVlt eq_sym; case/orP.
- by move/eqP/size0nil=>->.
move: (brauns_correct (i:=0) (xs:=xs) (k:=0)).
rewrite expn0 leq_min andbT=>/[apply]/braun_list_eq [-> <-]; split=>//.
by exact: take_nths_00.
Qed.

(* Running Time Analysis *)

Equations? T_brauns (k : nat) (xs : seq A) : nat by wf (size xs) lt :=
T_brauns _ [::] => 0;
T_brauns k xs => let ys := take (2^k) xs in
                 let zs := drop (2^k) xs in
                 let ts := brauns (k+1) zs in
                 4 * minn (2^k) (size xs) + T_brauns (k+1) zs.
Proof.
apply: ssrnat.ltP; rewrite /zs /xs size_drop /= ltn_subrL andbT.
by apply: expn_gt0.
Qed.

Theorem T_brauns_eq k xs : T_brauns k xs = 4 * size xs.
Proof.
funelim (T_brauns k xs); simp T_brauns=>//=.
rewrite H size_drop /= -mulnDr; set x := 2^k; set y:= (size l).+1.
apply/eqP; rewrite eqn_pmul2l // minnC minnE -addnBn -subnDA.
suff: y - (x + y) == 0 by move/eqP=>->; rewrite addn0.
by rewrite subn_eq0; exact: leq_addl.
Qed.

(* Converting a Braun Tree into a List *)

Definition value {A} (t : tree A) : option A :=
  if t is Node _ x _ then Some x else None.

Definition left {A} (t : tree A) : option (tree A) :=
  if t is Node l _ _ then Some l else None.

Definition right {A} (t : tree A) : option (tree A) :=
  if t is Node _ _ r then Some r else None.

Definition phi {A} (ts : seq (tree A)) : nat :=
  \sum_(t <- ts) (2 * size_tree t + 1).

Lemma phi_left_right {T} (t : tree T) :
  phi (olist (left t)) + phi (olist (right t)) < phi [:: t].
Proof.
case: t=>/=[|l a r]; rewrite /phi !big_seq1 ?big_nil //=.
by rewrite addnAC ltn_add2r !mulnDr addnA muln1 ltn_add2l.
Qed.

Equations? list_fast_rec {T} (xs : seq (tree T)) : seq T by wf (phi xs) lt :=
list_fast_rec xs with inspect (omap value xs) => {
  | [::] eqn: _  => [::];
  | vs   eqn: Hv => let ls := omap left xs in
                    let rs := omap right xs in
                    vs ++ list_fast_rec (ls ++ rs)
}.
Proof.
apply: ssrnat.ltP; rewrite /phi {}/ls {}/rs.
case: {list_fast_rec}xs Hv=>//= x + _; elim=>/=[|h s IH].
- rewrite big_cat /= !omap_cons !omap_nil !cats0.
  by apply: phi_left_right.
rewrite !omap_cons !big_cat !big_cons /= -!/(phi _) !mul2n !addnA in IH *.
rewrite (ACl ((2*5)*(1*3*4*6))%AC) /= [X in _<X](ACl ((3*4)*(1*5)*2)%AC) /= addn1 ltnS.
apply: leq_add; last by rewrite [X in _<X]addnAC addn1 ltnS in IH.
by apply: ltnW; move: (phi_left_right h); rewrite {3}/phi big_seq1 mul2n.
Qed.

Definition list_fast {T} (t : tree T) : seq T :=
  list_fast_rec [::t].

(* Functional Correctness *)

Lemma list_fast_rec_all_leaf {T} (ts : seq (tree T)) :
  all (fun t => ~~ is_node t) ts -> list_fast_rec ts = [::].
Proof.
funelim (list_fast_rec ts); rewrite -Heqcall //= => Ha.
move: {H H0}Hv; suff: omap value xs = [::] by move=>->.
by apply/omap_empty/sub_all/Ha; case.
Qed.

Lemma take_nths_lt {T} i k (xs : seq T) :
  i < size xs <= 2 ^ k ->
  take_nths i k xs = take 1 (drop i xs).
Proof.
elim: xs i =>//=x s IH i; rewrite ltnS.
case: i=>/=[|i].
- have/prednK{1}<-: 0 < 2^k by rewrite expn_gt0.
  by rewrite subn1 take0 ltnS=>/take_nths_empty ->.
by case/andP=>Hi1 Hi2; rewrite IH // Hi1 /=; apply/ltnW.
Qed.

Lemma size_omap_lvr {T} (xs : seq (tree T)) :
  (size (omap value xs) = count is_node xs) *
  (size (omap left  xs) = count is_node xs) *
  (size (omap right xs) = count is_node xs).
Proof.
rewrite /omap !size_flatten /shape -!map_comp !(eq_map (f1:=size \o _) (f2:=is_node));
  try by case.
by rewrite sumn_count.
Qed.

Lemma nth_omap_lvr {T} (xs : seq (tree T)) x0 x1 i l a r :
  i < size xs ->
  (* technically we only need is_node upto i *)
  all is_node xs ->
  nth leaf xs i = Node l a r ->
  (nth x0 (omap value xs) i = a) *
  (nth x1 (omap left  xs) i = l) *
  (nth x1 (omap right xs) i = r).
Proof.
elim/last_ind: xs i=>//=s x IH i.
rewrite size_rcons nth_rcons all_rcons ltnS leq_eqVlt; case/orP.
- move/eqP=>->; case/andP=>_ Ha; rewrite ltnn eq_refl=>->.
  rewrite !omap_rcons !nth_cat /= !size_omap_lvr.
  by move: Ha; rewrite all_count=>/eqP->; rewrite ltnn subnn.
move=>Hi; case/andP=>Hx Ha; rewrite Hi !omap_rcons !nth_cat !size_omap_lvr => H.
by move: (Ha); rewrite all_count=>/eqP->; rewrite Hi !IH.
Qed.

(* x0 is a dummy variable for nth on xs *)
Theorem list_fast_rec_correct {T : eqType} (x0 : T) ts k (xs : seq T) :
  size ts = 2 ^ k ->
  (forall i, i < 2 ^ k -> braun_list (nth leaf ts i) (take_nths i k xs)) ->
  list_fast_rec ts = xs.
Proof.
elim/(@size_ind T): xs k ts=>[|n IH] xs + k ts.
- move/size0nil=>->/= Hs Hl.
  apply/list_fast_rec_all_leaf/(all_nthP leaf)=>i; rewrite Hs.
  by case/Hl/braun_list_eq=>_; case: (nth leaf ts i).
move=>Hs Ht Hl; case: (ltnP (size xs) (2 ^ k))=>Hs'.
- (* size xs < 2 ^ k *)
  have ->: ts = map (fun x => Node leaf x leaf) xs ++ nseq (size ts - size xs) leaf.
  - apply: (eq_from_nth (x0:=leaf)).
    - by rewrite size_cat size_map size_nseq subnKC // Ht; apply: ltnW.
    move=>i Hi; rewrite nth_cat size_map nth_nseq if_same.
    move: Hi; rewrite Ht=>{}/Hl; case: ltnP=>Hi'.
    - rewrite (nth_map x0) //.
      have/minn_idPl Hxi: 1 <= size xs - i by rewrite subn_gt0.
      rewrite take_nths_lt; last by rewrite Hi' /=; apply: ltnW.
      have ->: take 1 (drop i xs) = [:: nth x0 xs i].
      - apply: (eq_from_nth (x0:=x0)); first by rewrite /= size_take size_drop.
        move=>j; rewrite size_take size_drop -/(minn _ _) Hxi ltnS leqn0 =>/eqP{j}->/=.
        by rewrite nth_take // nth_drop addn0.
      case: (nth leaf ts i)=>[|l a r] //=.
      case/and3P=>/eqP->/braun_list_eq [_] Hl' /braun_list_eq [_] Hr'.
      by symmetry in Hl'; move/list1_empty: Hl'=>->; symmetry in Hr'; move/list1_empty: Hr'=>->.
    move/(take_nths_empty _ k): Hi' =>->/braun_list_eq [_ H'].
    by symmetry in H'; move/list1_empty: H'=>->.
  simp list_fast_rec=>/=.
  rewrite omap_cat [X in _ ++ X]omap_empty; last first.
  - by apply/(all_nthP leaf)=>i _; rewrite nth_nseq if_same.
  rewrite cats0; have->: omap value [seq Node leaf x leaf | x <- xs] = xs.
  - by rewrite /omap -map_comp /= (eq_map (f2:=fun x => [::x])) // flatten_seq1.
  case: {Hs Hl Hs'}xs=>//x s.
  rewrite list_fast_rec_all_leaf; first by rewrite cats0.
  apply/allP=>z; rewrite mem_cat; case/orP.
  - rewrite omap_cat mem_cat /omap; case/orP.
    - rewrite -map_comp (eq_map (f2:=fun=>[::leaf])) // flatten_map1.
      by case/mapP=>y _ ->.
    rewrite map_nseq /=; case/flattenP=>y; rewrite mem_nseq.
    by case/andP=>_/eqP->.
  rewrite omap_cat mem_cat /omap; case/orP.
  - rewrite -map_comp (eq_map (f2:=fun=>[::leaf])) // flatten_map1.
    by case/mapP=>y _ ->.
  rewrite map_nseq /=; case/flattenP=>y; rewrite mem_nseq.
  by case/andP=>_/eqP->.
(* 2 ^ k <= size xs *)
have {Hl}H' : forall i, i < 2^k ->
              exists lt xt rt,
              [&& nth leaf ts i == Node lt xt rt,
                  xt == nth x0 xs i,
                  braun_list lt (take_nths (i +     2 ^ k) k.+1 xs) &
                  braun_list rt (take_nths (i + 2 * 2 ^ k) k.+1 xs)].
- move=>i Hi; move: (Hl _ Hi).
  have Hn: ~~ nilp (take_nths i k xs).
  - case E: (take_nths i k xs)=>[|ht tt] //.
    by move/take_nths_empty: E; rewrite leqNgt; move: (leq_trans Hi Hs')=>->.
  rewrite (braun_list_not_nil x0) //; case=>l'[a'][r'].
  case/and4P=>Hnd Ha; rewrite !take_nths_take_nths mul1n addnC (addnC _ i) add1n=>Hl' Hr'.
  exists l', a', r'; rewrite Hnd; move: Ha; rewrite hd_take_nths; last by apply/leq_trans/Hs'.
  by move=>->/=; rewrite Hl' Hr'.
have Ha' : all is_node ts.
- apply/allP=>t /[dup] Hit.
  rewrite -index_mem; set i:= index t ts; rewrite Ht=>/H'.
  by case=>l'[a'][r']; case/and4P=>+ _ _ _; rewrite /i nth_index // =>/eqP->.
simp list_fast_rec=>/=; have {Hs'}->: omap value ts = take (2^k) xs.
- apply: (eq_from_nth (x0:=x0)).
  - rewrite size_take -/(minn _ _) (minn_idPl Hs') size_omap_lvr -Ht.
    by apply/eqP; rewrite -all_count.
  move=> i; rewrite size_omap_lvr; move: (Ha'); rewrite all_count=>/eqP->.
  rewrite Ht=>/[dup] Hi' /H'; case=>l'[a'][r']; case/and4P=>H1 H2 _ _.
  have Hi'': i < size xs by apply/leq_trans/Hs'.
  rewrite nth_take // -(eqP H2); rewrite -Ht in Hi'.
  by rewrite (nth_omap_lvr x0 _ Hi' Ha' (eqP H1)).
have{Hs H'}->: list_fast_rec (omap left ts ++ omap right ts) = drop (2^k) xs.
- apply: (IH _ _ k.+1).
  - rewrite size_drop leq_subLR; apply: (leq_trans Hs).
    by rewrite -{1}(add0n n) ltn_add2r expn_gt0.
  - rewrite size_cat !size_omap_lvr.
    by move: Ha'; rewrite all_count=>/eqP->; rewrite Ht addnn expnS mul2n.
  move=>i Hi; rewrite nth_cat size_omap_lvr.
  move: (Ha'); rewrite all_count=>/eqP->; rewrite Ht; case: ltnP; rewrite take_nths_drop.
  - move=>/[dup] Hi' /H'; case=>l'[a'][r']; case/and4P=>H1 _ H3 _.
    by rewrite -Ht in Hi'; rewrite (nth_omap_lvr x0 leaf Hi' Ha' (eqP H1)).
  move=>Hi'; have Hi'': i - 2^k < 2^k.
  - rewrite ltn_psubLR; last by rewrite expn_gt0.
    by rewrite addnn -mul2n -expnS.
  move: (H' _ Hi''); case=>l'[a'][r']; case/and4P=>H1 _ _.
  rewrite mul2n -addnn addnBAC // addnA addnK; rewrite -Ht in H1 Hi'' *.
  by rewrite (nth_omap_lvr x0 leaf Hi'' Ha' (eqP H1)).
case E: (take (2 ^ k) xs)=>[|ht tt].
- case: xs E=>// x s.
  rewrite take_cons; case E': (2^k)=>//.
  by move/eqP: E'; rewrite expn_eq0.
by rewrite -cat_cons -E cat_take_drop.
Qed.

Corollary list_fast_correct {T : eqType} (x0 : T) t (xs : seq T) :
  braun_list t xs -> list_fast t = xs.
Proof.
move=>H; apply: (list_fast_rec_correct x0 (k:=0))=>// i.
rewrite ltnS leqn0=>/eqP->/=.
by rewrite take_nths_00.
Qed.

(* Running Time Analysis *)

Equations? T_list_fast_rec {T} (ts : seq (tree T)) : nat by wf (phi ts) lt :=
T_list_fast_rec ts with inspect (omap value ts) => {
  | [::] eqn: _  => size ts;
  | vs   eqn: Hv => let ls := omap left ts in
                    let rs := omap right ts in
                    3*size ts + size vs + size ls + T_list_fast_rec (ls ++ rs)
}.
Proof.
apply: ssrnat.ltP; rewrite /phi {}/ls {}/rs.
case: {T_list_fast_rec}ts Hv=>//= x + _; elim=>/=[|h s IH].
- rewrite big_cat /= !omap_cons !omap_nil !cats0.
  by apply: phi_left_right.
rewrite !omap_cons !big_cat !big_cons /= -!/(phi _) !mul2n !addnA in IH *.
rewrite (ACl ((2*5)*(1*3*4*6))%AC) /= [X in _<X](ACl ((3*4)*(1*5)*2)%AC) /= addn1 ltnS.
apply: leq_add; last by rewrite [X in _<X]addnAC addn1 ltnS in IH.
by apply: ltnW; move: (phi_left_right h); rewrite {3}/phi big_seq1 mul2n.
Qed.

Lemma sum_tree_list_children {T} (ts : seq (tree T)) k :
  \sum_(t <- ts) (k * size_tree t) =
  \sum_(t <- omap left ts ++ omap right ts) (k * size_tree t) + k * (count is_node ts).
Proof.
elim: ts=>/=[|t ts IH]; first by rewrite big_nil muln0.
rewrite big_cons !omap_cons !big_cat /=.
case: t=>/=[|l a r].
- by rewrite big_nil muln0 !add0n IH big_cat.
rewrite !big_seq1 /= IH big_cat /= add1n mulnS.
by rewrite ![in RHS]addnA (ACl ((1*3*5)*(2*4*6))%AC) /= -mulnDr -mulnSr addn1.
Qed.

(* this upper bound is somewhat ad-hoc but still linear, right? *)
Theorem T_list_fast_rec_ub {T} (ts : seq (tree T)) :
  T_list_fast_rec ts <= \sum_(t <- ts) (8*size_tree t + 1) + 2*size ts.
Proof.
move: {2}(phi ts) (leqnn (phi ts)) =>n; elim: n ts=>[|n IH] ts.
- rewrite leqn0 /phi big_split /= sum1_size addn_eq0.
  by case/andP=>_ /eqP/size0nil->.
move=>H; simp T_list_fast_rec=>/=.
case Ho: (omap value ts)=>[|h t].
- rewrite mul2n -addnn addnA; apply: leq_addl.
(* vs is non-empty *)
rewrite (_ : (size t).+1 = size (h :: t)) // -Ho big_split /= sum1_size.
have/IH: phi (omap left ts ++ omap right ts) <= n.
- move: H; rewrite /phi big_split /= [X in _ -> X <= _]big_split /= !sum1_size => H.
  rewrite size_cat !size_omap_lvr addnn -mul2n -sum_tree_list_children.
  case E: ts Ho H=>[|h' t']//; rewrite -{1 2 4}E /= => Ho.
  by rewrite addnS ltnS=>H; apply/leq_trans/H/leq_addr.
rewrite big_split /= sum1_size size_cat !size_omap_lvr addnn -mul2n.
rewrite -(leq_add2l (3 * size ts + count is_node ts + count is_node ts))=>H'.
rewrite [X in _<=X+_+_]sum_tree_list_children; apply: (leq_trans H').
rewrite 2!addnA (ACl (4*(2*3*5*6)*1)%AC) /= -[X in _<=X]addnA.
by rewrite mulnA -{1 2}(mul1n (count _ _)) -!mulnDl -{2}(mul1n (size _)) -mulnDl.
Qed.

End BiggerBetterFasterMore.

Section Exercises.
Context {A : Type}.

(* Exercise 11.1 *)

Lemma braun_exp_ht (t : tree A) : braun t -> 2 ^ height t <= 2 * size_tree t + 1.
Proof.
Admitted.

Corollary braun_log (t : tree A) : braun t -> height t = up_log 2 (size1_tree t).
Proof.
Admitted.

(* Exercise 11.2 *)

Variable x0 : A.

Lemma bal_braun n xs t zs : n <= size xs -> bal x0 n xs = (t, zs) -> braun t.
Proof.
Admitted.

(* Exercise 11.3 *)

Fixpoint nat_of (bs : seq bool) : nat :=
  if bs is b :: s then
    2 * nat_of s + b
    else 1.

Lemma nat_of_gt0 bs : 0 < nat_of bs.
Proof. by elim: bs=>//=b s IH; rewrite addn_gt0 muln_gt0 IH. Qed.

Fixpoint lookup_trie (x0 : A) (t : tree A) (bs : seq bool) : A := x0. (* FIXME *)

Fixpoint update_trie (bs : seq bool) (x : A) (t : tree A) {struct t} : tree A := t. (* FIXME *)

Lemma braun_lookup_trie_1 t bs :
  braun t -> nat_of bs <= size_tree t -> (* nat_of bs always >= 1 *)
  lookup_trie x0 t bs = lookup1 x0 t (nat_of bs).
Proof.
Admitted.

Lemma update_trie_1 bs x t :
  update_trie bs x t = update1 (nat_of bs) x t.
Proof.
Admitted.

(* Exercise 11.4 *)

Fixpoint del_lo2 (t : tree A) : tree A := t. (* FIXME *)

Lemma del_lo_eq t : del_lo2 t = del_lo1 t.
Proof.
Admitted.

(* Exercise 11.5 *)

Fixpoint left_height (t : tree A) : nat := 0. (* FIXME *)

Lemma braun_lh t : braun t -> left_height t = height t.
Proof.
Admitted.

(* Exercise 11.6 *)

Fixpoint T_diff (t : tree A) (n : nat) : nat := 0. (* FIXME *)

Fixpoint T_size_fast (t : tree A) : nat := 0. (* FIXME *)

Lemma T_size_fast_bound t : T_size_fast t <= (height t)^2.
Proof.
Admitted.

(* Exercise 11.7 *)

Lemma braun_of_naive_nseq (x : A) n : list1 (braun_of_naive x n) = nseq n x.
Proof.
Admitted.

End Exercises.
