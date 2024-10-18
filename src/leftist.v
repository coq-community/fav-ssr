From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype order seq path prime.
From favssr Require Import prelude bintree priority.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Intro.
Context {disp : unit} {T : orderType disp}.

Definition lheap T := tree (T * nat).

Definition mht (h : lheap T) : nat :=
  if h is Node _ (_,n) _ then n else 0.

Fixpoint heap_a {B} (t : tree (T*B)) : bool :=
  if t is Node l (m,_) r
    then [&& all (>= m) (inorder_a l ++ inorder_a r), heap_a l & heap_a r]
    else true.

Fixpoint ltree (h : lheap T) : bool :=
  if h is Node l (_, n) r
    then [&& min_height r <= min_height l,
             n == (min_height r).+1,
             ltree l &
             ltree r]
  else true.

(* Exercise 15.1 *)

Fixpoint rank {A} (t : tree A) : nat :=
  if t is Node _ _ r then (rank r).+1 else 0.

Lemma ltree_rank_min t : ltree t -> rank t = min_height t.
Proof.
Admitted.

End Intro.

Section ImplementationPQM.
Context {disp : unit} {T : orderType disp}.

Definition empty_lheap : lheap T := leaf.

Definition get_min_lheap (x0 : T) (t : lheap T) : T :=
  if t is Node _ (a, _) _
    then a else x0.

Definition node (l : lheap T) (a : T) (r : lheap T) : lheap T :=
  let mhl := mht l in
  let mhr := mht r in
  if mhr <= mhl then Node l (a, mhr.+1) r
                else Node r (a, mhl.+1) l.

Fixpoint merge_lheap (h1 : lheap T) : lheap T -> lheap T :=
  if h1 is Node l1 (a1,_) r1 then
    let fix merge_lheap_h1 (h2 : lheap T) :=
      if h2 is Node l2 (a2,_) r2 then
        if a1 <= a2 then node l1 a1 (merge_lheap r1 h2)
                    else node l2 a2 (merge_lheap_h1 r2)
      else h1 in
    merge_lheap_h1
  else id.

Definition insert x h : lheap T :=
  merge_lheap (Node leaf (x,1%N) leaf) h.

Definition del_min (t : lheap T) : lheap T :=
  if t is Node l _ r then merge_lheap l r else leaf.

End ImplementationPQM.

Section Correctness.
Context {disp : unit} {T : orderType disp}.

Definition mset_lheap (h : lheap T) : seq T := preorder_a h.

Definition invar (h : lheap T) : bool := heap_a h && ltree h.

Lemma mht_min_height (t : lheap T) :
  ltree t -> mht t = min_height t.
Proof.
case: t=>//=l [_ n] r /and4P [H /eqP -> _ _].
apply/eqP; rewrite -addn1 eqn_add2r eq_sym.
by apply/eqP/minn_idPr.
Qed.

Lemma mset_node (l : lheap T) a r :
  perm_eq (mset_lheap (node l a r)) (a :: mset_lheap l ++ mset_lheap r).
Proof. by rewrite /node; case: ifP=>//= _; rewrite perm_cons perm_catC. Qed.

Lemma ltree_node (l : lheap T) a r :
  ltree (node l a r) <-> ltree l /\ ltree r.
Proof.
rewrite /node; split.
- by case: ifP=>/= _ /and4P [_ _ -> ->].
case=>Hl Hr; case: ifP=>/=.
- by move=>H; rewrite -!mht_min_height // H eq_refl Hl Hr.
move/negbT; rewrite -ltNge=>H.
rewrite -!mht_min_height // eq_refl Hl Hr /= andbT.
by apply: ltW.
Qed.

Lemma heap_node (l : lheap T) a r :
  heap_a (node l a r) <->
    [/\ all (>= a) (inorder_a l ++ inorder_a r), heap_a l & heap_a r].
Proof.
rewrite /node; split.
- case: ifP=>/= _ /and3P // [Ha Hlr Hr]; split=>//.
  by rewrite !all_cat in Ha *; case/andP: Ha=>->->.
case=>Ha Hl Hr; case: ifP=>/= _; rewrite Hl Hr /= andbT //.
by rewrite !all_cat in Ha *; case/andP: Ha=>->->.
Qed.

Lemma all_foldl_a {B} (x : T) (t : tree (T*B)) :
  all (>= x) (inorder_a t) ->
  foldl Order.min x (preorder_a t) = x.
Proof.
elim: t x =>//=l IHl [a _] r IHr x; rewrite all_cat /=.
case/and3P=>Hal Hxa Har; rewrite foldl_cat.
by rewrite min_l // IHl // IHr.
Qed.

Lemma get_min_mins_heap (h : lheap T) x0 :
  heap_a h ->
  get_min_lheap x0 h = mins x0 (mset_lheap h).
Proof.
case: h=>//=l [a n] r /and3P [+ Hl Hr].
by rewrite all_cat /mins foldl_cat; case/andP=>/all_foldl_a->/all_foldl_a->.
Qed.

Corollary get_min_mins (h : lheap T) x0 :
  invar h ->
  get_min_lheap x0 h = mins x0 (mset_lheap h).
Proof. by rewrite /invar => /andP [+ _]; exact: get_min_mins_heap. Qed.

Lemma mset_merge_heap (h1 h2 : lheap T) :
  perm_eq (mset_lheap (merge_lheap h1 h2)) (mset_lheap h1 ++ mset_lheap h2).
Proof.
elim: h1 h2=>//= l1 _ [a1 n1] r1 IHr1; elim=>/= [|l2 _ [a2 n2] r2 IHr2].
- by rewrite cats0 /=.
case: ifP=>/= _; apply: perm_trans; try by apply: mset_node.
- rewrite perm_cons perm_sym -catA perm_cat2l perm_sym.
  by apply: IHr1=>//=; rewrite H2 Hl2 Hr2.
rewrite perm_sym -!cat_cons perm_catCA perm_cat2l /= perm_sym.
by apply: IHr2.
Qed.

Lemma ltree_merge_heap (l r : lheap T) :
  ltree l -> ltree r -> ltree (merge_lheap l r).
Proof.
elim: l r=>//= l1 _ [a1 n1] r1 IHr1; elim=>//= l2 _ [a2 n2] r2 IHr2.
case/and4P=>Eh1 En1 Hl1 Hr1; case/and4P=>Eh2 En2 Hl2 Hr2.
case: ifP=>/= _; apply/ltree_node; split=>//.
- by apply: IHr1=>//=; rewrite Eh2 En2 Hl2 Hr2.
by apply: IHr2=>//; rewrite Eh1 En1 Hl1 Hr1.
Qed.

Lemma heap_merge_heap (l r : lheap T) :
  heap_a l -> heap_a r -> heap_a (merge_lheap l r).
Proof.
elim: l r=>//= l1 _ [a1 n1] r1 IHr1; elim=>//= l2 _ [a2 n2] r2 IHr2.
case/and3P=>Ha1 Hl1 Hr1; case/and3P=>Ha2 Hl2 Hr2.
case: ifP=>/= Ha; apply/heap_node; split=>//.
- rewrite !all_cat in Ha1 *; case/andP: Ha1=>-> Ha1 /=.
  rewrite (perm_all _ (perm_pre_in_a _)) (perm_all _ (mset_merge_heap _ _))
    all_cat /= all_cat -!(perm_all _ (perm_pre_in_a _)) Ha Ha1 /=.
  rewrite all_cat in Ha2; case/andP: Ha2=>Hal2 Har2.
  apply/andP; split.
  - by apply/sub_all/Hal2=>z Hz; apply/le_trans/Hz.
  by apply/sub_all/Har2=>z Hz; apply/le_trans/Hz.
- by apply: IHr1=>//=; rewrite Ha2 Hl2 Hr2.
- move/negbT: Ha; rewrite -ltNge=>Ha.
  rewrite !all_cat in Ha2 *; case/andP: Ha2=>-> Ha2 /=.
  move: (@mset_merge_heap (Node l1 (a1, n1) r1) r2)=>/= H'.
  rewrite (perm_all _ (perm_pre_in_a _)) (perm_all _ H') /= !all_cat
    -!(perm_all _ (perm_pre_in_a _)) (ltW Ha) Ha2 /= andbT.
  rewrite all_cat in Ha1; case/andP: Ha1=>Hal1 Har1.
  apply/andP; split.
  - by apply/sub_all/Hal1=>z Hz; apply/ltW/lt_le_trans/Hz.
  by apply/sub_all/Har1=>z Hz; apply/ltW/lt_le_trans/Hz.
by apply: IHr2=>//; rewrite Ha1 Hl1 Hr1.
Qed.

Corollary invar_merge h1 h2 :
  invar h1 -> invar h2 -> invar (merge_lheap h1 h2).
Proof.
rewrite /invar; case/andP=>Hh1 Hl1; case/andP=>Hh2 Hl2.
apply/andP; split.
- by apply: heap_merge_heap.
by apply: ltree_merge_heap.
Qed.

Corollary mset_merge h1 h2 :
  invar h1 -> invar h2 ->
  perm_eq (mset_lheap (merge_lheap h1 h2)) (mset_lheap h1 ++ mset_lheap h2).
Proof. by move=>_ _; exact: mset_merge_heap. Qed.

Lemma invar_empty : invar empty_lheap.
Proof. by []. Qed.

Lemma mset_empty : mset_lheap empty_lheap = [::].
Proof. by []. Qed.

Corollary invar_insert x h :
  invar h -> invar (insert x h).
Proof. by exact: invar_merge. Qed.

Corollary mset_insert x h :
  invar h -> perm_eq (mset_lheap (insert x h)) (x :: mset_lheap h).
Proof. by move=>_; apply: mset_merge_heap. Qed.

Corollary invar_delmin h :
  invar h -> ~~ nilp (mset_lheap h) -> invar (del_min h).
Proof.
rewrite /invar; case: h=>//= l [a n] r /and5P [/and3P [_ Hhl Hhr] _ _ Hll Hlr] _.
by apply/andP; split; [apply: heap_merge_heap | apply: ltree_merge_heap].
Qed.

Corollary mset_delmin x0 h :
  invar h -> ~~ nilp (mset_lheap h) ->
  perm_eq (mset_lheap (del_min h)) (rem (get_min_lheap x0 h) (mset_lheap h)).
Proof.
rewrite /invar; case: h=>//= l [a n] r /and5P [/and3P [_ Hhl Hhr] _ _ Hll Hlr] _.
apply: perm_trans; first by apply: mset_merge_heap.
by rewrite rem_cons eq_refl.
Qed.

Definition LHeapPQM :=
  @APQM.make _ _ (lheap T)
    empty_lheap insert del_min get_min_lheap merge_lheap
    mset_lheap invar
    invar_empty mset_empty
    invar_insert mset_insert
    invar_delmin mset_delmin
    get_min_mins
    invar_merge mset_merge.

End Correctness.

Section RunningTimeAnalysis.
Context {disp : unit} {T : orderType disp}.

Fixpoint T_merge (h1 : lheap T) : lheap T -> nat :=
  if h1 is Node l1 (a1,_) r1 then
    let fix T_merge_h1 (h2 : lheap T) :=
      if h2 is Node l2 (a2,_) r2 then
        if a1 <= a2 then T_merge r1 h2
                    else T_merge_h1 r2
      else 1%N in
    T_merge_h1
  else fun=>1%N.

Definition T_insert x h :=
  T_merge (Node leaf (x,1%N) leaf) h + 1.

Definition T_del_min (t : lheap T) : nat :=
  if t is Node l _ r then T_merge l r + 1 else 1%N.

Lemma T_merge_bound l r :
  ltree l -> ltree r ->
  T_merge l r <= min_height l + min_height r + 1.
Proof.
elim: l r=>/=; first by move=>r _ _; rewrite add0n; apply: leq_addl.
move=>l1 _ [a1 n1] r1 IHr1; elim=>/=; first by move=>_ _; rewrite addn0 addn1.
move=>l2 _ [a2 n2] r2 IHr2.
case/and4P=>Hm1 En1 Hl1 Hr1; case/and4P=>Hm2 En2 Hl2 Hr2.
case: ifP=>/= Ha.
- apply: leq_trans; first by apply: IHr1=>//=; rewrite Hm2 En2 Hl2 Hr2.
  rewrite /= !addnA !leq_add2r addn1.
  by apply: ltnW; rewrite ltnS leq_min -leEnat Hm1 lexx.
apply: leq_trans; first by apply: IHr2=>//=; rewrite Hm1 En1 Hl1 Hr1.
rewrite /=  leq_add2r leq_add2l addn1.
by apply: ltnW; rewrite ltnS leq_min -leEnat Hm2 lexx.
Qed.

Corollary T_merge_log l r :
  ltree l -> ltree r ->
  T_merge l r <= trunc_log 2 (size1_tree l) + trunc_log 2 (size1_tree r) + 1.
Proof.
move=>Hl Hr; apply: leq_trans; first by by apply: T_merge_bound.
by rewrite leq_add2r; apply: leq_add; apply: trunc_log_max=>//; apply: exp_mh_leq.
Qed.

Corollary T_insert_log t x :
  ltree t -> T_insert x t <= trunc_log 2 (size1_tree t) + 3.
Proof.
move=>H; rewrite /T_insert (_ : 3 = 2 + 1) // addnA leEnat leq_add2r.
apply: leq_trans; first by apply: T_merge_log.
by rewrite addnAC addnC.
Qed.

Lemma trunc_log2_ltD x y :
  (0 < x -> 0 < y ->
  trunc_log 2 x + trunc_log 2 y + 1 < 2 * up_log 2 (x + y))%N.
Proof.
move=>Hx Hy.
have H: (2 ^ (trunc_log 2 x + trunc_log 2 y + 1) <= 2*x*y)%N.
- rewrite !expnD expn1 mulnC -mulnA leq_pmul2l //.
  by apply: leq_mul; apply: trunc_logP.
have H' : (2*x*y < (x+y)^2)%N.
- by rewrite sqrnD mulnA -[X in (X < _)%N]add0n ltn_add2r addn_gt0 !sqrn_gt0 Hx Hy.
have H'': ((x+y)^2 <= 2 ^ (2 * up_log 2 (x + y)))%N.
- rewrite (mulnC 2) expnM leq_exp2r //.
  by apply: up_logP.
rewrite -(ltn_exp2l _ _ (isT : (1 < 2)%N)).
by apply: (leq_ltn_trans H); apply: (leq_trans H').
Qed.

Lemma T_del_min_log t :
  ltree t -> T_del_min t <= 2 * up_log 2 (size1_tree t) + 1.
Proof.
case: t=>//= l [a n] r /and4P [Hm En Hl Hr]; rewrite leEnat leq_add2r.
apply: leq_trans; first by by apply: T_merge_bound.
apply: (leq_trans (n:=trunc_log 2 (size1_tree l) + trunc_log 2 (size1_tree r) + 1)).
- by rewrite leq_add2r; apply: leq_add; apply: trunc_log_max=>//; apply: exp_mh_leq.
by apply/ltnW/trunc_log2_ltD; rewrite size1_size addn1.
Qed.

End RunningTimeAnalysis.
