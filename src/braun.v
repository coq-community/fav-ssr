From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq prime.
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

(* TODO move to prelude *)
Definition butlast {A : Type} (xs : seq A) :=
  if xs is x :: s then belast x s else [::].

Lemma belast_butlast {A} (x : A) xs : 0 < size xs -> belast x xs = x :: butlast xs.
Proof. by case: xs. Qed.

Lemma size_butlast {A} (xs : seq A) : size (butlast xs) = (size xs).-1.
Proof. by case: xs=>//=x s; rewrite size_belast. Qed.

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
  if t is Node l a r
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
