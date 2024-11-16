From Equations Require Import Equations.
From mathcomp Require Import all_ssreflect.
From favssr Require Import prelude.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive tree A := Leaf | Node of (tree A) & A & (tree A).

Definition leaf {A} : tree A := @Leaf A.

Definition is_node {A} (t : tree A) :=
  if t is Node _ _ _ then true else false.

Lemma not_node_leaf {A} (t : tree A) : ~~ is_node t -> t = leaf.
Proof. by case: t. Qed.

(* dependent helper for irrefutable pattern matching *)
Inductive non_empty_if {A} (b : bool) (t : tree A) : Type :=
| Nd l a r : t = Node l a r -> b -> non_empty_if b t
| Def      :                ~~ b -> non_empty_if b t.

Section BasicFunctions.
Context {A B : Type}.

Fixpoint map_tree (f : A -> B) (t : tree A) : tree B :=
  if t is Node l x r
    then Node (map_tree f l) (f x) (map_tree f r)
  else leaf.

Fixpoint inorder {A} (t : tree A) : seq A :=
  if t is Node l x r
    then inorder l ++ [:: x] ++ inorder r
  else [::].

Fixpoint preorder (t : tree A) : seq A :=
  if t is Node l x r
    then x :: preorder l ++ preorder r
  else [::].

Fixpoint postorder (t : tree A) : seq A :=
  if t is Node l x r
    then postorder l ++ postorder r ++ [:: x]
  else [::].

(* number of nodes *)
Fixpoint size_tree (t : tree A) : nat :=
  if t is Node l _ r
    then size_tree l + size_tree r + 1
  else 0.

Lemma size0leaf t : size_tree t = 0 -> t = leaf.
Proof. by case: t=>//=l a r; rewrite addn1. Qed.

(* number of leaves *)
Fixpoint size1_tree (t : tree A) : nat :=
  if t is Node l _ r
    then size1_tree l + size1_tree r
  else 1.

Lemma size1_size t : size1_tree t = size_tree t + 1.
Proof.
elim: t=>//= l -> _ r ->.
by rewrite addnAC addnA.
Qed.

Lemma size_inorder t : size (inorder t) = size_tree t.
Proof.
elim: t=>//=l IHl x r IHr.
by rewrite size_cat /= IHl IHr addnS addn1.
Qed.

Lemma map_inorder f t : map f (inorder t) = inorder (map_tree f t).
Proof.
elim: t=>//=l IHl x r IHr.
by rewrite map_cat map_cons IHl IHr.
Qed.

Fixpoint height (t : tree A) : nat :=
  if t is Node l _ r
    then maxn (height l) (height r) + 1
  else 0.

Lemma heightE (t : tree A) : reflect (t = leaf) (height t == 0).
Proof.
apply: (iffP idP); last by move=>->.
by case: t=>//= l a r; rewrite addn1 => /eqP.
Qed.

Fixpoint min_height (t : tree A) : nat :=
  if t is Node l _ r
    then minn (min_height l) (min_height r) + 1
  else 0.

Lemma h_leq t : height t <= size_tree t.
Proof.
elim: t=>//= l IHl _ r IHr; rewrite leq_add2r geq_max.
apply/andP; split.
- by apply/(leq_trans IHl)/leq_addr.
by apply/(leq_trans IHr)/leq_addl.
Qed.

Lemma mh_leq t : min_height t <= height t.
Proof.
elim: t=>//= l IHl _ r IHr; rewrite leq_add2r leq_max /minn.
by case: ifP=>H; rewrite ?IHl ?IHr // orbT.
Qed.

Lemma exp_mh_leq t : 2 ^ min_height t <= size1_tree t.
Proof.
elim: t=>//= l IHl _ r IHr.
rewrite expnD expn1 muln2 -addnn.
apply: (leq_trans (n := 2^ min_height l + 2^ min_height r)); last by apply: leq_add.
by apply: leq_add; rewrite leq_exp2l //; [apply: geq_minl | apply: geq_minr].
Qed.

Lemma exp_h_geq t : size1_tree t <= 2 ^ height t.
Proof.
elim: t=>//= l IHl _ r IHr.
rewrite expnD expn1 muln2 -addnn.
apply: (leq_trans (n := 2^ height l + 2^ height r)); first by apply: leq_add.
by apply: leq_add; rewrite leq_exp2l //; [apply: leq_maxl | apply: leq_maxr].
Qed.

Fixpoint subtrees (t : tree A) : seq (tree A) :=
  if t is Node l x r
    then Node l x r :: subtrees l ++ subtrees r
  else [:: leaf].

(* Exercise 4.1 *)

Fixpoint inorder2 (t : tree A) (acc : seq A) : seq A := [::]. (* FIXME *)

Lemma inorder2_correct t xs : inorder2 t xs = inorder t ++ xs.
Proof.
Admitted.

End BasicFunctions.

Section EqTree.
Context {T : eqType}.

Fixpoint eqtree (t1 t2 : tree T) :=
  match t1, t2 with
  | Leaf, Leaf => true
  | Node l1 x1 r1, Node l2 x2 r2 => [&& x1 == x2, eqtree l1 l2 & eqtree r1 r2]
  | _, _ => false
  end.

Lemma eqtreeP : Equality.axiom eqtree.
Proof.
move; elim=> [|l1 IHl x1 r1 IHr] [|l2 x2 r2] /=; try by constructor.
have [<-/=|neqx] := x1 =P x2; last by apply: ReflectF; case.
apply: (iffP andP).
- by case=>/IHl->/IHr->.
by case=><-<-; split; [apply/IHl|apply/IHr].
Qed.

Canonical tree_eqMixin := EqMixin eqtreeP.
Canonical tree_eqType := Eval hnf in EqType (tree T) tree_eqMixin.

Lemma perm_pre_in (t : tree T) : perm_eq (inorder t) (preorder t).
Proof.
elim: t=>//=l IHl a r IHr.
rewrite perm_catC /= perm_cons perm_catC.
by apply: perm_cat.
Qed.

Lemma subtree_self (t : tree T) : t \in subtrees t.
Proof. by case: t=>//=l x r; rewrite inE eq_refl. Qed.

End EqTree.

Section CompleteTrees.
Context {A : Type}.

(* aka perfect *)

Fixpoint complete (t : tree A) : bool :=
  if t is Node l x r
    then [&& height l == height r, complete l & complete r]
  else true.

Lemma complete_mh_h t : complete t <-> min_height t == height t.
Proof.
elim: t=>//= l IHl _ r IHr; split.
- by case/and3P=>/eqP H /IHl /eqP -> /IHr /eqP ->; rewrite H minnn maxnn.
rewrite eqn_add2r /minn /maxn; case: ltnP=>H1; case: ltnP=>H2 /eqP H.
- by rewrite H ltnNge mh_leq in H1.
- rewrite H in H1; move: (leq_ltn_trans H2 H1).
  by rewrite ltnNge mh_leq.
- rewrite -H in H2; move: (leq_trans H2 H1).
  by rewrite ltnNge mh_leq.
rewrite H in H1; rewrite -H in H2.
have /IHl->: min_height l == height l by rewrite eq_sym eqn_leq H1 mh_leq.
have /[dup]: min_height r == height r by rewrite eq_sym eqn_leq H2 mh_leq.
by rewrite {1}H=>/eqP->/IHr->; rewrite eq_refl.
Qed.

Lemma complete_size1 t : complete t -> size1_tree t = 2^height t.
Proof.
elim: t=>//= l IHl _ r IHr /and3P [/eqP H /IHl -> /IHr ->].
by rewrite H maxnn addnn expnD expn1 muln2.
Qed.

Lemma ncomplete_size1 t : ~~ complete t -> size1_tree t < 2^height t.
Proof.
elim: t=>//= l IHl _ r IHr; rewrite !negb_and.
rewrite expnD expn1 muln2 -addnn.
case H: (_ == _)=>/=.
- case/orP=>//; move/eqP: H=>H.
  - move/IHl=>H2; rewrite -H maxnn.
    apply: (leq_trans (n:=2 ^ height l + size1_tree r)); first by rewrite ltn_add2r.
    by rewrite leq_add2l H exp_h_geq.
  move/IHr=>H2; rewrite H maxnn.
  apply: (leq_trans (n:=size1_tree l + 2 ^ height r)); first by rewrite ltn_add2l.
  by rewrite leq_add2r -H exp_h_geq.
move=>_; move/negbT: H; rewrite neq_ltn.
case/orP=>H; rewrite /maxn.
- rewrite H.
  apply: (leq_ltn_trans (n:=2 ^ height l + 2 ^ height r)).
  - by apply: leq_add; rewrite exp_h_geq.
  by rewrite ltn_add2r ltn_exp2l.
move: (H); rewrite ltnNge leq_eqVlt negb_or =>/andP [_ /negbTE ->].
apply: (leq_ltn_trans (n:=2 ^ height l + 2 ^ height r)).
- by apply: leq_add; rewrite exp_h_geq.
by rewrite ltn_add2l ltn_exp2l.
Qed.

Lemma ncomplete_mh_size1 t : ~~ complete t -> 2^min_height t < size1_tree t.
Proof.
elim: t=>//= l IHl _ r IHr; rewrite negb_and.
rewrite expnD expn1 muln2 -addnn.
case H: (_ && _)=>/=.
- rewrite orbF; case/andP: H=>/complete_mh_h/eqP H1 /complete_mh_h/eqP H2.
  rewrite neq_ltn; case/orP=>H; rewrite /minn.
  - rewrite H1 H2 H.
    apply: (leq_trans (n:=2 ^ height l + 2 ^ height r)).
    - by rewrite ltn_add2l ltn_exp2l.
    by apply: leq_add; rewrite -?H1 -?H2 exp_mh_leq.
  move: (H); rewrite ltnNge leq_eqVlt negb_or H1 H2 =>/andP [_ /negbTE ->].
  apply: (leq_trans (n:=2 ^ height l + 2 ^ height r)).
  - by rewrite ltn_add2r ltn_exp2l.
  by apply: leq_add; rewrite -?H1 -?H2 exp_mh_leq.
move=>_; move/negbT: H; rewrite negb_and; case/orP.
- move/IHl=>H.
  apply: (leq_ltn_trans (n:=2 ^ min_height l + size1_tree r)).
  - apply: leq_add; first by rewrite leq_exp2l // geq_minl.
    apply: (leq_trans _ (exp_mh_leq r)).
    by rewrite leq_exp2l // geq_minr.
  by rewrite ltn_add2r.
move/IHr=>H.
apply: (leq_ltn_trans (n:=size1_tree l + 2 ^ min_height r)).
- apply: leq_add; last by rewrite leq_exp2l // geq_minr.
  apply: (leq_trans _ (exp_mh_leq l)).
  by rewrite leq_exp2l // geq_minl.
by rewrite ltn_add2l.
Qed.

Corollary completeE t : complete t <-> size1_tree t = 2^height t.
Proof.
split; first by exact: complete_size1.
move=>E; move/contraR: (@ncomplete_size1 t); apply.
by rewrite E ltnn.
Qed.

(* Exercise 4.2 *)

Fixpoint mcs (t : tree A) : tree A := t. (* FIXME *)

Lemma complete_mcs t : complete (mcs t).
Proof.
Admitted.

End CompleteTrees.

Section CompleteTreesEq.
Context {T : eqType}.

Lemma subtree_mcs (t : tree T) : mcs t \in subtrees t.
Proof.
Admitted.

Lemma mcs_maximal (t u : tree T) :
  u \in subtrees t -> complete u ->
  height u <= height (mcs t).
Proof.
Admitted.

End CompleteTreesEq.

Section AlmostCompleteTrees.
Context {A : Type}.

Definition acomplete (t : tree A) : bool :=
  height t - min_height t <= 1.

Lemma acomplete_h1 t :
  acomplete t -> ~~ complete t ->
  height t = (min_height t).+1.
Proof.
rewrite /acomplete leq_eqVlt; case/orP.
- rewrite -(eqn_add2r (min_height t)) addnBAC; last by exact: mh_leq.
  by rewrite addnK add1n=>/eqP ->.
rewrite ltnS leqn0 subn_eq0=>E.
suff : min_height t == height t by move/complete_mh_h=>->.
by rewrite eqn_leq E mh_leq.
Qed.

Lemma acomplete_minimal (s t : tree A) :
  acomplete s -> size_tree s <= size_tree t ->
  height s <= height t.
Proof.
case/boolP: (complete s).
- move/completeE=>H _ S; rewrite -(leq_exp2l (m:=2)) // -H.
  apply/leq_trans/(exp_h_geq t).
  by rewrite !size1_size leq_add2r.
move=>/[dup] H /[swap] /acomplete_h1 /[apply] -> S.
rewrite -(ltn_exp2l (m:=2)) //.
apply: (leq_trans (ncomplete_mh_size1 H)).
apply/leq_trans/(exp_h_geq t).
by rewrite !size1_size leq_add2r.
Qed.

Lemma acomplete_h t : acomplete t -> height t = up_log 2 (size1_tree t).
Proof.
case/boolP: (complete t).
- by move/completeE=>->_; rewrite up_expnK.
move=>/[dup] H /[swap] /acomplete_h1 /[apply] E; rewrite E; symmetry.
apply: up_log_eq=>//; rewrite (ncomplete_mh_size1 H) /= -E.
by exact: exp_h_geq.
Qed.

Lemma acomplete_mh t : acomplete t -> min_height t = trunc_log 2 (size1_tree t).
Proof.
case/boolP: (complete t).
- move/[dup]/complete_mh_h/eqP=>->.
  by move/completeE =>->_; rewrite trunc_expnK.
move=>/[dup] H /[swap] /acomplete_h1 /[apply] E; symmetry.
apply: trunc_log_eq=>//; rewrite exp_mh_leq /=.
by apply: (leq_trans (ncomplete_size1 H)); rewrite E.
Qed.

Variable x0 : A.

Equations? bal (n : nat) (xs : seq A) : tree A * seq A by wf n lt :=
bal n xs with inspect (n == 0) := {
  | true eqn: Hn => (leaf, xs)
  | false eqn: Hn =>
      let m := n./2 in
      let: (l, ys) := bal m xs in
      let: (r, zs) := bal (n-1-m) (behead ys) in
      (Node l (head x0 ys) r, zs)
}.
Proof.
all: apply: ssrnat.ltP; move/negbT: Hn; rewrite /m -lt0n=>Hn.
- by apply: half_lt.
rewrite subnAC half_subn.
apply/leq_trans/uphalf_le.
by rewrite subn1 ltn_predL uphalf_gt0.
Defined.

Definition bal_list n xs := (bal n xs).1.

Definition balance_list xs := bal_list (size xs) xs.

Definition bal_tree n t := bal_list n (inorder t).

Definition balance_tree t := bal_tree (size_tree t) t.

Lemma bal_prefix_suffix n xs t ss :
  n <= size xs ->
  bal n xs = (t, ss) ->
  xs = inorder t ++ ss /\ size_tree t = n.
Proof.
elim/ltn_ind: n xs t ss; case.
- by move=>_ ??? _; simp bal=>/=; case=><-<-.
move=>n IH xs t ss Hn; simp bal=>/=; rewrite subn1 /=.
set m := uphalf n.
have Hm : m<=n by exact: uphalf_le.
set m' := n - m.
have Hm' : m'<=n by exact: leq_subr.
case H1: (bal m xs)=>[l ys].
case H2: (bal m' (behead ys))=>[r zs].
case=>{t}<- E; rewrite {zs}E /= in H2 *.
case: (IH m _ xs l ys)=>//.
- by apply: (leq_trans Hm); rewrite ltnW.
move=>E1 E2.
have Hys: m + size ys = size xs.
- by rewrite -E2 -size_inorder -size_cat -E1.
have H3: 0 < size ys.
- rewrite -(ltn_add2l m) addn0 Hys.
  by apply/leq_ltn_trans/Hn.
case: (IH m' _ (behead ys) r ss)=>//.
- rewrite size_behead -ltnS prednK //.
  by rewrite -(ltn_add2r m) addnBAC // addnK addnC Hys.
rewrite -catA cat_cons E1 E2=><-->; split.
- by case: {H1 H2 E1 Hys}ys H3.
by rewrite (addnC m) addnBAC // addnK addn1.
Qed.

Corollary bal_suffix_size n xs :
  n <= size xs -> size (bal n xs).2 = size xs - n.
Proof.
move=>Hn; case E: (bal n xs)=>[l ys] /=.
case: (bal_prefix_suffix Hn E)=>-> H.
by rewrite size_cat size_inorder H addnC addnK.
Qed.

Corollary bal_list_take n xs :
  n <= size xs -> inorder (bal_list n xs) = take n xs.
Proof.
move=>Hn; rewrite /bal_list.
case E: (bal n xs)=>[l ys] /=.
case: (bal_prefix_suffix Hn E)=>-> H.
by rewrite take_cat size_inorder H ltnn subnn take0 cats0.
Qed.

Corollary inorder_balance_list xs : inorder (balance_list xs) = xs.
Proof. by rewrite /balance_list bal_list_take // take_oversize. Qed.

Corollary bal_tree_take n t :
  n <= size_tree t -> inorder (bal_tree n t) = take n (inorder t).
Proof. by move=>Hn; rewrite /bal_tree bal_list_take // size_inorder. Qed.

Corollary inorder_balance_tree t : inorder (balance_tree t) = inorder t.
Proof. by rewrite /balance_tree bal_tree_take // take_oversize // size_inorder. Qed.

Lemma bal_h_mh n xs t ss :
  n <= size xs -> bal n xs = (t, ss) ->
  height t = up_log 2 n.+1 /\ min_height t = trunc_log 2 n.+1.
Proof.
elim/ltn_ind: n xs t ss; case.
- by move=>_ ??? _; simp bal=>/=; case=><-.
move=>n IH xs t ss Hn; simp bal=>/=; rewrite subn1 /=.
set m := uphalf n.
have Hm : m<=n by exact: uphalf_le.
have Hm2 : m < size xs by apply: (leq_ltn_trans Hm).
set m' := n - m.
have Hm' : m'<=n by exact: leq_subr.
case H1: (bal m xs)=>[l ys].
have Hys: size ys = size xs - m.
- rewrite (surjective_pairing (bal m xs)) in H1.
  by case: H1=>_<-; rewrite bal_suffix_size //; apply: ltnW.
case H2: (bal m' (behead ys))=>[r zs].
case=>{t}<- E; rewrite {zs}E /= in H2 *.
case: (IH _ Hm _ _ _ _ H1)=>[|->->]; first by apply: ltnW.
case: (IH _ Hm' _ _ _ _ H2)=>[|->->].
- by rewrite size_behead -ltnS prednK Hys ?ltn_sub2r // subn_gt0.
have Hmm : m' <= m.
- rewrite /m' (half_uphalfK n) /m addnK uphalf_half.
  by apply: leq_addl.
rewrite -(leq_add2r 1) !addn1 in Hmm.
rewrite /maxn /minn !ltnNge leq_up_log // leq_trunc_log //=.
rewrite (up_log2S (isT : 0 < n.+1)) (trunc_log2S (isT : 1 < n.+2)); split.
- by rewrite -addn1 addn1.
rewrite /m' /m {1}(half_uphalfK n) addnK.
by rewrite -(addn2 n) halfD /= andbF /= add0n !addn1.
Qed.

Corollary bal_acomplete n xs t ss :
  n <= size xs -> bal n xs = (t, ss) -> acomplete t.
Proof.
rewrite /acomplete.
move/bal_h_mh => /[apply] [[->->]].
have/andP [H1 H2] := trunc_up_log_ltn n.+1 (isT : 1 < 2).
by rewrite -(leq_add2r (trunc_log 2 n.+1)) addnBAC // addnK addnC.
Qed.

(* Exercise 4.3 *)

Fixpoint acomplete_rec (t : tree A) : bool :=
  if t is Node l x r then
    false (* FIXME *)
  else true.

Lemma acomplete_rec_correct t : acomplete_rec t = acomplete t.
Proof.
Admitted.

(* Exercise 4.4 *)

Equations T_bal (n : nat) : nat by wf n lt :=
T_bal n => 1.  (* FIXME *)

Parameters c1 c2 : nat.

Lemma T_bal_linear n : T_bal n <= c1 * n + c2.
Proof.
Admitted.

End AlmostCompleteTrees.

Section AugmentedTrees.
Context {A B : Type}.

Fixpoint preorder_a (t : tree (A*B)) : seq A :=
  if t is Node l (x,_) r
    then x :: preorder_a l ++ preorder_a r
  else [::].

Fixpoint inorder_a (t : tree (A*B)) : seq A :=
  if t is Node l (x, _) r
    then inorder_a l ++ [:: x] ++ inorder_a r
  else [::].

Definition inorder_a' (t : tree (A*B)) : seq A := map fst (inorder t).

Definition inorder_a'' (t : tree (A*B)) : seq A := inorder (map_tree fst t).

Lemma in_a : inorder_a =1 inorder_a'.
Proof.
elim=>//=l -> [x y] r ->.
by rewrite /inorder_a' map_cat map_cons.
Qed.

Lemma in_a' : inorder_a =1 inorder_a''.
Proof.
elim=>//=l -> [x y] r ->.
by rewrite /inorder_a'' -!map_inorder /= map_cat map_cons.
Qed.

Definition sz (t : tree (A*nat)) : nat :=
  if t is Node _ (_, n) _ then n else 0.

Definition node_sz (l : tree (A*nat)) (a : A) (r : tree (A*nat)) : tree (A*nat) :=
  Node l (a, sz l + sz r + 1) r.

Fixpoint invar_sz (t : tree (A*nat)) : bool :=
  if t is Node l (_, n) r then
    [&& n == sz l + sz r + 1, invar_sz l & invar_sz r ]
  else true.

Lemma size_invar t : invar_sz t -> sz t = size_tree t.
Proof. by elim: t=>//=l IHl [a n] r IHr /and3P [/eqP -> /IHl <- /IHr <-]. Qed.

End AugmentedTrees.

Section AugmentedTreesEq.
Context {A : eqType} {B : Type}.

Lemma inorder_a_empty_pred : inorder_a (@Leaf (A*B)) =i pred0.
Proof. by []. Qed.

Lemma perm_pre_in_a (t : tree (A*B)) : perm_eq (inorder_a t) (preorder_a t).
Proof.
elim: t=>//=l IHl [a _] r IHr.
rewrite perm_catC /= perm_cons perm_catC.
by apply: perm_cat.
Qed.

End AugmentedTreesEq.

(* generalized form *)
(* we don't always need a meaningful invariant (and thus an eqType constraint) *)
(* e.g. if B is the value in a KV map *)

Section AugmentedTreesGen.
Context {A : Type} {B : eqType}.

Variables (zero : B) (f : B -> A -> B -> B).

Fixpoint F (t : tree (A*B)) : B :=
  if t is Node l (a,_) r then f (F l) a (F r) else zero.

Definition b_val (t : tree (A*B)) : B :=
  if t is Node _ (_,b) _ then b else zero.

Definition node_f (l : tree (A*B)) (a : A) (r : tree (A*B)) : tree (A*B) :=
  Node l (a, f (b_val l) a (b_val r)) r.

Fixpoint invar_f (t : tree (A*B)) : bool :=
  if t is Node l (a,b) r then
    [&& b == f (b_val l) a (b_val r), invar_f l & invar_f r ]
  else true.

Lemma F_invar t : invar_f t -> b_val t = F t.
Proof. by elim: t=>//=l IHl [a n] r IHr /and3P [/eqP -> /IHl <- /IHr <-]. Qed.

End AugmentedTreesGen.

From mathcomp Require Import order bigop.
Import Order.TotalTheory.

Section AugmentedTreesEx.

Context {A : Type}.

(* Exercise 4.5 *)

Definition T : Type := bool * unit. (* FIXME *)

Definition ch (t : tree (A*T)) : T := (true, tt).  (* FIXME *)

Definition node_ch (l : tree (A*T)) (a : A) (r : tree (A*T)) : tree (A*T) :=
  @Leaf (A*T).  (* FIXME *)

Definition invar_ch (t : tree (A*T)) : bool := true. (* FIXME *)

Lemma ch_invar (t : tree (A*T)) : invar_ch t -> ch t = (complete t, tt).  (* FIXME *)
Proof.
Admitted.

Lemma ch_invar_node (l : tree (A*T)) (a : A) (r : tree (A*T)) :
  invar_ch l -> invar_ch r -> invar_ch (node_ch l a r).
Proof.
Admitted.

(* Exercise 4.6 *)

Context {disp : unit} {P : orderType disp}.
Variable (x0 : P) (lmin : left_id x0 Order.max).

Lemma rmin : right_id x0 Order.max.
Proof. by move=>x; rewrite maxC lmin. Qed.

Canonical max_monoid := Monoid.Law maxA lmin rmin.

Definition max_seq (xs : seq P) : P :=
  \big[Order.max/x0]_(x<-xs) x.

Definition mx (t : tree (P*P)) : option P :=
  None.  (* FIXME *)

Definition node_mx (l : tree (P*P)) (a : P) (r : tree (P*P)) : tree (P*P) :=
  @Leaf (P*P).   (* FIXME *)

Fixpoint invar_mx (t : tree (P*P)) : bool :=
  true.  (* FIXME *)

Lemma max_invar t :
  invar_mx t ->
  mx t = if t is Leaf then None else Some (max_seq (inorder_a t)).
Proof.
Admitted.

End AugmentedTreesEx.
