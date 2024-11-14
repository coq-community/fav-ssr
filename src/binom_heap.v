From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype order seq path bigop prime binomial.
From favssr Require Import prelude basics priority.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Tree.
Context {A : Type}.

Inductive tree A := Node of nat & A & seq (tree A).

Definition rank (t : tree A) : nat :=
  let: Node r _ _ := t in r.

Definition root (t : tree A) : A :=
  let: Node _ x _ := t in x.

Definition heap A := seq (tree A).

(* from https://github.com/affeldt-aist/succinct/ *)
Lemma tree_ind' (P : tree A -> Prop) :
  (forall r a l, foldr (fun t => and (P t)) True l -> P (Node r a l)) ->
  forall t, P t.
Proof.
move=>indu; fix H 1.
elim => r a l; apply: indu.
by elim: l.
Qed.

Lemma tree_rec' (P : tree A -> Type) :
  (forall r a l, foldr (fun t => prod (P t)) True l -> P (Node r a l)) ->
  forall t, P t.
Proof.
move=>indu; fix H 1.
elim => r a l; apply: indu.
by elim: l.
Qed.

End Tree.

Section TreeEq.
Context {A : eqType}.

Fixpoint eqtree (t1 t2 : tree A) :=
  match t1, t2 with
  | Node r1 x1 ts1, Node r2 x2 ts2 => [&& r1 == r2, x1 == x2 & all2 eqtree ts1 ts2]
  end.

Lemma eqtreeP : Equality.axiom eqtree.
Proof.
move; elim/(tree_rec' (A:=A))=>r1 a1 l1 IH; case=>r2 a2 l2 /=.
have [<-/=|neqx] := r1 =P r2; last by apply: ReflectF; case.
have [<-/=|neqx] := a1 =P a2; last by apply: ReflectF; case.
elim: l1 IH l2=>/=.
- move=>_ l2; case: l2=>[|h2 t2]; first by apply: ReflectT.
  by apply: ReflectF.
move=>h1 t1 IH; case=>H1 /IH {IH} H2.
case=>[|h2 t2]; first by apply: ReflectF.
case: H1=>H12 /=; last by apply: ReflectF; case.
rewrite {}H12; case: H2.
- by case=>->; apply: ReflectT.
by move=>H12; apply: ReflectF; case=>E; rewrite E in H12.
Qed.

Canonical tree_eqMixin := EqMixin eqtreeP.
Canonical tree_eqType := Eval hnf in EqType (tree A) tree_eqMixin.

Lemma tree_ind_eq (P : tree A -> Prop) :
  (forall r a l, (forall x, x \in l -> P x) -> P (Node r a l)) ->
  forall t, P t.
Proof.
move=> H; apply tree_ind' => r a s IH; apply: H.
elim: s IH => // b s IH /= [Pb K] t.
by rewrite in_cons => /orP[/eqP -> //|]; apply: IH.
Qed.

End TreeEq.

Section TreeOrd.
Context {disp : unit} {T : orderType disp}.

Fixpoint invar_btree (t : tree T) : bool :=
  let: Node r _ ts := t in
  all invar_btree ts && (map rank ts == rev (iota 0 r)).

Fixpoint invar_otree (t : tree T) : bool :=
  let: Node _ x ts := t in
  all (fun t' => invar_otree t' && (x <= root t')) ts.

Definition invar_tree (t : tree T) : bool :=
  invar_btree t && invar_otree t.

Definition invar (ts : heap T) :=
  all invar_tree ts && (sorted <%O (map rank ts)).

Lemma invar_cons t ts :
  invar (t::ts) = [&& invar_tree t, all (> rank t) (map rank ts) & invar ts].
Proof. by rewrite /invar /= (path_sortedE lt_trans) -andbA (andbCA (all _ _)). Qed.

Lemma invar_children r v ts :
  invar_tree (Node r v ts) -> invar (rev ts).
Proof.
rewrite /invar /invar_tree /= -andbA; case/and3P=>Ha1 Hi Ha2.
rewrite all_rev map_rev (eqP Hi) revK iota_ltn_sorted andbT.
apply/allP=>z Hz; apply/andP; split.
- by move/allP: Ha1=>/(_ _ Hz).
by move/allP: Ha2=>/(_ _ Hz); case/andP.
Qed.

End TreeOrd.

Section Size.
Context {disp : unit} {T : orderType disp}.

Fixpoint mset_tree (t : tree T) : seq T :=
  let: Node _ a ts := t in
  a :: flatten (map mset_tree ts).

Lemma mset_tree_nonempty t : mset_tree t != [::].
Proof. by case: t. Qed.

Lemma root_in_mset t : root t \in mset_tree t.
Proof. by case: t=>/=_ a ts; rewrite inE eq_refl. Qed.

Definition mset_heap (ts : heap T) : seq T :=
  flatten (map mset_tree ts).

Lemma mset_heap_nil : mset_heap [::] = [::].
Proof. by []. Qed.

Lemma mset_heap_cons t ts :
  mset_heap (t::ts) = mset_tree t ++ mset_heap ts.
Proof. by []. Qed.

Lemma mset_heap_empty_iff ts : mset_heap ts != [::] <-> ts != [::].
Proof.
case: ts=>//=t s; rewrite mset_heap_cons.
by split=>// _; have:= mset_tree_nonempty t; case: (mset_tree t).
Qed.

Lemma perm_mset_heap xs ys :
  perm_eq xs ys -> perm_eq (mset_heap xs) (mset_heap ys).
Proof. by move=>H; rewrite /mset_heap; apply/perm_flatten/perm_map. Qed.

Corollary mset_heap_rev ts : perm_eq (mset_heap (rev ts)) (mset_heap ts).
Proof. by apply: perm_mset_heap; rewrite perm_rev. Qed.

Lemma sum_pow2 n : (\sum_(0 <= i < n) 2 ^ i).+1 = 2 ^ n.
Proof.
elim: n=>/=; first by rewrite big_nil.
move=>n IH; rewrite big_nat_recl // expn0 add1n.
have ->: \sum_(0 <= i < n) 2 ^ i.+1 = \sum_(0 <= i < n) 2 * 2 ^ i.
- by apply: eq_big_nat=>z _; rewrite expnS.
by rewrite -big_distrr /= -addn2 -{3}(muln1 2) -mulnDr addn1 IH expnS.
Qed.

Lemma size_mset_btree t :
  invar_btree t ->
  size (mset_tree t) = 2^(rank t).
Proof.
elim/(tree_ind_eq (A:=T)): t=>/= r _ ts IH.
case/andP=>Ha /eqP Hm.
have {}IH: forall x, x \in ts -> size (mset_tree x) = 2 ^ rank x.
- by move=>x Hx; apply: IH=>//; move/allP: Ha; apply.
rewrite size_flatten /shape -map_comp sumnE big_map (eq_big_seq _ IH).
have -> : \sum_(i <- ts) 2 ^ rank i = \sum_(i <- map rank ts) 2^i by rewrite big_map.
rewrite {}Hm; have Hp: perm_eq (rev (iota 0 r)) (iota 0 r) by rewrite perm_rev.
by rewrite (perm_big _ Hp) /= -{1}(subn0 r) sum_pow2.
Qed.

Lemma size_mset_heap_tree ts :
  size (mset_heap ts) = \sum_(t <- ts) (size (mset_tree t)).
Proof.
elim: ts=>/=; first by rewrite big_nil.
by move=>t s IH; rewrite big_cons -{}IH /mset_heap /= size_cat.
Qed.

Lemma size_sorted_bound s n :
  all ((< n)%N) s ->  (* technically we only need last s < n *)
  sorted ltn s ->
  (size s <= n)%N.
Proof.
elim/last_ind: s n=>// t h IH n.
rewrite size_rcons all_rcons; case/andP=>Hh _.
rewrite (sorted_rconsE ltn_trans); case/andP=>Ha Hs.
case: n Hh=>// n; rewrite !ltnS => Hh.
apply: IH=>//; apply/allP=>z Hz; move/allP: Ha=>/(_ z Hz) Hzh.
by apply: (leq_trans Hzh).
Qed.

(* simplified to nats *)
Lemma sorted_ltn_sum_mono_lowerbound (f : nat -> nat) ns :
  {homo f : x y / (x <= y)%N} ->
  sorted ltn ns ->
  \sum_(0<=i<size ns) f i <= \sum_(n<-ns) f n.
Proof.
move=>Hm; elim/last_ind: ns=>//s n IH.
rewrite (sorted_rconsE ltn_trans) size_rcons.
case/andP=>Ha Hs; move: (IH Hs)=>{}IH.
rewrite big_nat_recr //= -cats1 big_cat /= big_seq1.
apply: leq_add=>//; apply: Hm.
by apply: size_sorted_bound.
Qed.

Lemma size_mset_heap ts :
  invar ts ->
  size ts <= trunc_log 2 (size (mset_heap ts) + 1).
Proof.
rewrite /invar; case/andP=>Ha Hs.
apply: trunc_log_max=>//; rewrite size_mset_heap_tree.
have->: \sum_(t <- ts) size (mset_tree t) = \sum_(t <- ts) 2^(rank t).
- apply: eq_big_seq=> t Ht; apply: size_mset_btree.
  by move/allP: Ha=>/(_ t Ht); rewrite /invar_tree; case/andP.
rewrite addn1 -sum_pow2 ltnS.
have ->: \sum_(i <- ts) 2 ^ rank i = \sum_(i <- map rank ts) 2^i by rewrite big_map.
rewrite -(@size_map _ _ rank); apply: sorted_ltn_sum_mono_lowerbound=>//.
by move=>x y Hx; rewrite leq_exp2l.
Qed.

End Size.

Section PriorityQueueImplementation.
Context {disp : unit} {T : orderType disp}.

(* insert *)

(* aka smash *)
Definition link (t1 t2 : tree T) : tree T :=
  let: Node r x1 ts1 := t1 in
  let: Node _ x2 ts2 := t2 in
  if x1 <= x2
    then Node r.+1 x1 (t2::ts1)
    else Node r.+1 x2 (t1::ts2).

Lemma invar_link t1 t2 :
  invar_tree t1 ->
  invar_tree t2 ->
  rank t1 = rank t2 ->
  invar_tree (link t1 t2).
Proof.
case: t1=>r x1 ts1; case: t2=>r2 x2 ts2 /=.
rewrite /invar_tree /= -!andbA.
case/and3P=>Hab1 Hs1 Hao1; case/and3P=>Hab2 Hs2 Hao2.
move=>E; rewrite -{r2}E in Hs2 *.
case: leP=>/= Hx; rewrite Hab1 Hab2 Hao1 Hao2 /= !andbT.
- by rewrite Hx Hs2 /= andbT (eqP Hs1) -rev_rcons -cats1
       (_:[::r] = iota r 1) // -{2}(add0n r) -iotaD addn1.
by rewrite (ltW Hx) Hs1 /= andbT (eqP Hs2) -rev_rcons -cats1
  (_:[::r] = iota r 1) // -{2}(add0n r) -iotaD addn1.
Qed.

Lemma rank_link t1 t2 :
  rank (link t1 t2) = (rank t1).+1.
Proof. by case: t1=>r x1 ts1; case: t2=>r2 x2 ts2 /=; case: ifP. Qed.

Lemma mset_link t1 t2 :
  perm_eq (mset_tree (link t1 t2)) (mset_tree t1 ++ mset_tree t2).
Proof.
case: t1=>r x1 ts1; case: t2=>r2 x2 ts2 /=.
case: ifP=>_ /=.
- by rewrite perm_cons -cat1s catA perm_catAC -catA perm_catCA perm_cat2l.
by rewrite -cat1s -(cat1s x1) perm_catCA perm_cons perm_catCA perm_cat2l.
Qed.

(* aka carry *)
Fixpoint ins_tree (t1 : tree T) (h : heap T) : heap T :=
  if h is t2::ts then
    if rank t1 < rank t2
      then t1::t2::ts
      else ins_tree (link t1 t2) ts
  else [::t1].

Lemma invar_ins_tree t ts :
  invar_tree t ->
  invar ts ->
  all (fun t' => rank t <= rank t') ts ->
  invar (ins_tree t ts).
Proof.
elim: ts t=>/=.
- by move=>t H _ _; rewrite /invar /= !andbT.
rewrite /invar /= =>t2 ts IH t Ht.
rewrite -andbA; case/and3P=>Ht2 Ha Hp; case/andP=>Hr Has.
case: ltgtP Hr=>//= E _.
- by rewrite Ht Ht2 Ha E.
apply: IH.
- by apply: invar_link.
- by rewrite Ha /=; apply/path_sorted: Hp.
move: Hp; rewrite (path_sortedE lt_trans); case/andP=>+ _.
by rewrite -E all_map =>/sub_all; apply=>z /=; rewrite rank_link.
Qed.

Lemma mset_heap_ins_tree t ts :
  perm_eq (mset_heap (ins_tree t ts)) (mset_tree t ++ mset_heap ts).
Proof.
elim: ts t=>//=t2 ts IH t.
case: ifP=>_ //; apply: perm_trans; first by apply: IH.
by rewrite catA perm_cat2r; apply: mset_link.
Qed.

Lemma ins_tree_rank_bound (t0 : tree T) t ts :
  all (preim rank (> rank t0)) ts ->
  rank t0 < rank t ->
  all (preim rank (> rank t0)) (ins_tree t ts).
Proof.
elim: ts t=>/=.
- by move=>t _; rewrite andbT.
move=>t1 ts IH t; case: ifP=>_ /=.
- by case/andP=>->->->.
case/andP=>_ Ha H2.
apply: IH=>//; rewrite rank_link ltEnat /= ltnS -leEnat.
by apply: ltW.
Qed.

Definition insert (x : T) (ts : heap T) : heap T :=
  ins_tree (Node 0 x [::]) ts.

Lemma invar_insert x t : invar t -> invar (insert x t).
Proof.
move=>H; rewrite /insert; apply: invar_ins_tree=>//=.
by apply/allP.
Qed.

Lemma mset_heap_insert x t :
  perm_eq (mset_heap (insert x t)) (x::mset_heap t).
Proof. by rewrite /insert; apply: mset_heap_ins_tree. Qed.

(* merge *)

Fixpoint merge (h1 : heap T) : heap T -> heap T :=
  if h1 is t1::ts1 then
    let fix merge_h1 (h2 : heap T) :=
      if h2 is t2::ts2 then
        if rank t1 < rank t2 then t1 :: merge ts1 h2
          else if rank t2 < rank t1 then t2 :: merge_h1 ts2
            else ins_tree (link t1 t2) (merge ts1 ts2)
      else h1 in
    merge_h1
  else id.

Lemma merge_rank_bound (t : tree T) (ts1 ts2 : heap T) :
  all (preim rank (> rank t)) ts1 ->
  all (preim rank (> rank t)) ts2 ->
  all (preim rank (> rank t)) (merge ts1 ts2).
Proof.
elim: ts1 ts2=>//= t1 ts1 IH1; elim=>//= t2 ts2 IH2.
case/andP=>Hr1 Ha1; case/andP=>Hr2 Ha2.
case: ltgtP=>_ /=.
- by rewrite Hr1 /=; apply: IH1=>//=; rewrite Hr2 Ha2.
- by rewrite Hr2 /=; apply: IH2=>//; rewrite Hr1 Ha1.
apply: ins_tree_rank_bound; first by apply: IH1.
by rewrite rank_link ltEnat /= ltnS -leEnat; apply: ltW.
Qed.

Lemma invar_merge ts1 ts2 :
  invar ts1 ->
  invar ts2 ->
  invar (merge ts1 ts2).
Proof.
elim: ts1 ts2=>//= t1 ts1 IH1; elim=>//= t2 ts2 IH2.
rewrite !invar_cons; case/and3P=>Ht1 Ha1 H1; case/and3P=>Ht2 Ha2 H2.
case: ltgtP=>Hr12.
- rewrite invar_cons Ht1 /=; apply/andP; split; last first.
  - by apply: IH1=>//; rewrite invar_cons Ht2 Ha2 H2.
  move: Ha1 Ha2; rewrite !all_map => Ha1 Ha2.
  apply: merge_rank_bound=>//=; rewrite Hr12 /=.
  by apply/sub_all/Ha2=>z /= Hz; apply/lt_trans/Hz.
- rewrite invar_cons Ht2 /=; apply/andP; split; last first.
  - by apply: IH2=>//; rewrite invar_cons Ht1 Ha1 H1.
  move: Ha1 Ha2; rewrite !all_map => Ha1 Ha2.
  move: (@merge_rank_bound t2 (t1::ts1) ts2); apply=>//=.
  by rewrite Hr12 /=; apply/sub_all/Ha1=>z /= Hz; apply/lt_trans/Hz.
apply: invar_ins_tree.
- by apply: invar_link.
- by apply: IH1.
move: Ha1 Ha2; rewrite -Hr12 !all_map=>Ha1 Ha2.
move: (merge_rank_bound Ha1 Ha2)=>H.
by apply/sub_all/H=>z /= Hz; rewrite rank_link.
Qed.

Lemma mset_heap_merge ts1 ts2 :
  perm_eq (mset_heap (merge ts1 ts2)) (mset_heap ts1 ++ mset_heap ts2).
Proof.
elim: ts1 ts2=>//= t1 ts1 IH1; elim=>//.
- by rewrite cats0.
move=>t2 ts2 IH2; case: ltgtP=>?.
- rewrite /mset_heap /= -catA perm_cat2l.
  by apply: IH1.
- rewrite /mset_heap /= perm_sym perm_catCA perm_cat2l perm_sym.
  by apply: IH2.
apply: perm_trans; first by apply: mset_heap_ins_tree.
rewrite /mset_heap /= perm_sym perm_catAC -!catA catA.
apply: perm_cat.
- by rewrite perm_sym; apply: mset_link.
by rewrite perm_catC perm_sym; apply: IH1.
Qed.

(* get_min *)

Fixpoint get_min (t : tree T) (h : heap T) : T :=
  if h is t1::ts
   then Order.min (root t) (get_min t1 ts)
   else root t.

Lemma invar_tree_root_min (t : tree T) x :
  invar_tree t ->
  x \in mset_tree t ->
  root t <= x.
Proof.
rewrite /invar_tree; elim/(tree_ind_eq (A:=T)): t x=>r a ts IH x /=.
rewrite inE -andbA; case/and3P=>Hab Hs Hao.
case/orP; first by move/eqP=>->.
case/flattenP=>xs; case/mapP=>t Ht {xs}->Hx.
move/allP: Hab=>/(_ t Ht) Hb.
move/allP: Hao=>/(_ t Ht); case/andP=>Ho Ha.
move: (IH _ Ht x); rewrite Hb Ho /= =>/(_ erefl Hx) Hr.
by apply/le_trans/Hr.
Qed.

Lemma get_min_mset t h x :
  invar_tree t -> all (> rank t) (map rank h) -> invar h ->
  (x \in mset_tree t) || (x \in mset_heap h) ->
  get_min t h <= x.
Proof.
elim: h t=>/=.
- move=>t Ht _ _; rewrite mset_heap_nil in_nil orbF=>Hx.
  by apply: invar_tree_root_min.
move=>t1 ts IH t Ht _.
rewrite invar_cons; case/and3P=>Ht1 Ha1 Hs; rewrite le_minl; case/orP.
- by move=>Hx; rewrite invar_tree_root_min.
rewrite mset_heap_cons mem_cat=>Hx.
by rewrite IH // orbT.
Qed.

Lemma get_min_mem t h :
  (get_min t h \in mset_tree t) || (get_min t h \in mset_heap h).
Proof.
elim: h t=>/=.
- by move=>t; rewrite root_in_mset.
move=>t1 ts IH t; rewrite mset_heap_cons mem_cat minElt; case: ifP=>_.
- by rewrite root_in_mset.
by rewrite IH // orbT.
Qed.

Lemma get_min_min x0 t h :
  invar_tree t -> all (> rank t) (map rank h) -> invar h ->
  get_min t h = mins x0 (mset_tree t ++ mset_heap h).
Proof.
elim: h t=>/=.
- move=>t Ht _ _; rewrite mset_heap_nil cats0.
  apply/eq_mins_iff.
  - by apply: mset_tree_nonempty.
  rewrite root_in_mset andbT; apply/allP=>z Hz.
  by apply: invar_tree_root_min.
move=>t1 ts IH t Ht; case/andP=>Hr Ha.
rewrite invar_cons mset_heap_cons; case/and3P=>Ht1 Ha1 Hs.
rewrite mins_cat; first last.
- by rewrite -mset_heap_cons; apply/mset_heap_empty_iff.
- by exact: mset_tree_nonempty.
rewrite IH // (_ : root t = mins x0 (mset_tree t)) //.
apply/eq_mins_iff; first by exact: mset_tree_nonempty.
rewrite root_in_mset andbT; apply/allP=>z Hz.
by apply: invar_tree_root_min.
Qed.

(* del_min *)

Fixpoint get_min_rest (t : tree T) (h : heap T) : (tree T * heap T) :=
  if h is t1::ts then
    let: (t',ts') := get_min_rest t1 ts in
    if root t <= root t' then (t,t1::ts) else (t',t::ts')
  else (t, [::]).

Definition del_min (h : heap T) : heap T :=
  if h is t::ts then
    let: (Node _ _ ts1, ts2) := get_min_rest t ts in
    merge (rev ts1) ts2
  else [::].

Lemma mset_get_min_rest t h t' h' :
  get_min_rest t h = (t',h') ->
  perm_eq (t::h) (t'::h').
Proof.
elim: h t t' h'=>/=.
- by move=>t t' h'; case=><-<-.
move=>t1 ts IH t t' h'; case Hgmr: (get_min_rest t1 ts)=>[t'' h''].
case: leP=>E; case=>{t'}<-{h'}<-//.
rewrite perm_sym -cat1s -(cat1s t) perm_catCA perm_cons /= perm_sym.
by apply: IH.
Qed.

Lemma invar_get_min_rest t h t' h' :
  get_min_rest t h = (t',h') ->
  invar_tree t -> all (> rank t) (map rank h) -> invar h ->
  invar_tree t' && invar h'.
Proof.
elim: h t t' h'=>/=.
- by move=>t t' h'; case=><-<- ->.
move=>t1 ts IH t t' h'; case Hgmr: (get_min_rest t1 ts)=>[t'' h''].
case: (leP (root t) (root t''))=>E; case=>{t'}<-{h'}<- Ht; case/andP=>Hr Ha.
- by rewrite Ht.
rewrite !invar_cons; case/and3P=>Ht1 Ha1 Hs.
case/andP: (IH _ _ _ Hgmr Ht1 Ha1 Hs)=>->->; rewrite Ht /= andbT.
have: all (preim rank (> rank t)) (t1::ts) by rewrite -all_map /= Hr Ha.
by rewrite (perm_all _ (mset_get_min_rest Hgmr)) /= all_map; case/andP.
Qed.

Lemma get_min_rest_get_min_same_root t h t' h' :
  get_min_rest t h = (t',h') ->
  root t' = get_min t h.
Proof.
elim: h t t' h'=>/=.
- by move=>t t' h'; case=><-.
move=>t1 ts IH t t' h'; case Hgmr: (get_min_rest t1 ts)=>[t'' h''].
case: leP=>E; case=>{t'}<-{h'}_; rewrite -(IH _ _ _ Hgmr); apply/eqP; rewrite eq_sym.
- by rewrite eq_minl.
by rewrite eq_minr; apply: ltW.
Qed.

Lemma invar_del_min ts :
  invar ts -> invar (del_min ts).
Proof.
case: ts=>//=t s; rewrite invar_cons; case/and3P=>Ht Ha Hs.
case Hgmr: (get_min_rest t s)=>[t' h'].
case/andP: (invar_get_min_rest Hgmr Ht Ha Hs); case: {Hgmr}t'=>/=x a ts Ht' Hh.
by apply: invar_merge=>//; apply: (invar_children Ht').
Qed.

Lemma mset_heap_del_min t h :
  perm_eq (mset_heap (t::h)) (get_min t h :: mset_heap (del_min (t::h))).
Proof.
rewrite /=; case Hgmr: (get_min_rest t h)=>[t' h'].
rewrite -(get_min_rest_get_min_same_root Hgmr).
move: (mset_get_min_rest Hgmr)=>/perm_mset_heap Hp.
case: {Hgmr}t' Hp=>r a ts /= Hp; apply: (perm_trans Hp).
rewrite mset_heap_cons /= perm_cons perm_sym.
apply: perm_trans; first by apply: mset_heap_merge.
by rewrite perm_cat2r; exact: mset_heap_rev.
Qed.

Definition get_min' (x0 : T) (h : heap T) : T :=
  if h is t::ts then get_min t ts else x0.

Corollary invar_empty : invar ([::] : heap T).
Proof. by []. Qed.

Corollary mset_empty : mset_heap ([::] : heap T) = [::].
Proof. by []. Qed.

Corollary mset_insert x s :
  invar s -> perm_eq (mset_heap (insert x s)) (x :: mset_heap s).
Proof. by move=>_; exact: mset_heap_insert. Qed.

Corollary invar_del_min_ne ts :
  invar ts -> ~~nilp (mset_heap ts) -> invar (del_min ts).
Proof. by move=>+ _; exact: invar_del_min. Qed.

Corollary mset_del_min x0 s :
  invar s ->
  ~~ nilp (mset_heap s) ->
  perm_eq (mset_heap (del_min s)) (rem (get_min' x0 s) (mset_heap s)).
Proof.
move=>_; case: s=>// t h _.
rewrite -(perm_cons (get_min t h)) perm_sym.
apply: perm_trans; last by apply: mset_heap_del_min.
rewrite /= perm_sym; apply: perm_to_rem.
by rewrite mset_heap_cons mem_cat; exact: get_min_mem.
Qed.

Corollary get_min_min' (s : heap T) (x0 : T) :
  invar s -> get_min' x0 s = mins x0 (mset_heap s).
Proof.
case: s=>//=t h; rewrite invar_cons mset_heap_cons.
by case/and3P=>Ht Ha Hh; apply: get_min_min.
Qed.

Corollary mset_merge s1 s2 :
  invar s1 -> invar s2 ->
  perm_eq (mset_heap (merge s1 s2)) (mset_heap s1 ++ mset_heap s2).
Proof. move=>_ _; exact: mset_heap_merge. Qed.

Definition BHeapPQM :=
  @APQM.make _ _ (heap T)
  [::] insert del_min get_min' merge
  mset_heap invar
  invar_empty mset_empty
  invar_insert mset_insert
  invar_del_min_ne mset_del_min
  get_min_min'
  invar_merge mset_merge.

End PriorityQueueImplementation.

Section RunningTimeAnalysis.
Context {disp : unit} {T : orderType disp}.

Definition T_link (t1 t2 : tree T) : nat := 1.

Fixpoint T_ins_tree (t1 : tree T) (h : heap T) : nat :=
  if h is t2::ts then
    if rank t1 < rank t2
      then 1%N
      else T_link t1 t2 + T_ins_tree (link t1 t2) ts
  else 1.

Definition T_insert (x : T) (ts : heap T) : nat :=
  T_ins_tree (Node 0 x [::]) ts + 1.

Fixpoint T_merge (h1 : heap T) : heap T -> nat :=
  if h1 is t1::ts1 then
    let fix T_merge_h1 (h2 : heap T) :=
      if h2 is t2::ts2 then
        if rank t1 < rank t2 then T_merge ts1 h2
          else if rank t2 < rank t1 then T_merge_h1 ts2
            else T_ins_tree (link t1 t2) (merge ts1 ts2) + T_merge ts1 ts2
      else 1%N in
    T_merge_h1
  else fun=>1%N.

Fixpoint T_get_min (t : tree T) (h : heap T) : nat :=
  if h is t1::ts
   then T_get_min t1 ts + 1
   else 1.

Fixpoint T_get_min_rest (t : tree T) (h : heap T) : nat :=
  if h is t1::ts then
    T_get_min_rest t1 ts + 1
  else 1.

Definition T_rev' {A} (xs : seq A) := T_catrev xs [::].

Definition T_del_min (h : heap T) : nat :=
  if h is t::ts then
    T_get_min_rest t ts +
      let: (Node _ _ ts1, ts2) := get_min_rest t ts in
      T_rev' ts1 + T_merge (rev ts1) ts2 + 1
  else 1.

Lemma T_ins_tree_simple_bound t ts : (T_ins_tree t ts <= size ts + 1)%N.
Proof.
elim: ts t=>//=t1 ts IH t; case: ifP=>//= _.
by rewrite /T_link addnC leq_add2r -addn1; apply: IH.
Qed.

Lemma T_insert_bound x ts :
  invar ts ->
  (T_insert x ts <= trunc_log 2 (size (mset_heap ts) + 1) + 2)%N.
Proof.
move=>Hi; have H: (T_insert x ts <= size ts + 2)%N.
- rewrite /T_insert /= (_ : 2 = 1 + 1) // addnA leq_add2r.
  by apply: T_ins_tree_simple_bound.
apply: (leq_trans H); rewrite leq_add2r.
by apply: size_mset_heap.
Qed.

Lemma T_ins_tree_length t ts:
  T_ins_tree t ts + size (ins_tree t ts) = 2 + size ts.
Proof.
elim: ts t=>//=ts t1 IH t; case: ifP=>//= _.
rewrite /T_link -addnA addnC -(addn1 (size _)) addnA.
by apply/eqP; rewrite eqn_add2r IH.
Qed.

Lemma T_merge_length ts1 ts2 :
  (size (merge ts1 ts2) + T_merge ts1 ts2 <= 2 * (size ts1 + size ts2) + 1)%N.
Proof.
elim: ts1 ts2=>//=.
- by move=>ts2; rewrite leq_add2r add0n; apply: leq_pmull.
move=>t1 ts1 IH1; elim=>//=.
- rewrite leq_add2r addn0 mulnSr.
  apply: leq_ltn_trans; first by apply: (leq_pmull _ (n:=2)).
  by rewrite -[X in (X < _)%N]addn0 ltn_add2l.
move=>t2 ts2 IH2; case: ifP=>/= _.
- rewrite addSn addn1 ltnS; apply: leq_trans; first by apply: IH1.
  by rewrite /= !addnS addSn addn0 ltn_pmul2l.
case: ifP=>/= _.
- rewrite addSn addn1 ltnS; apply: leq_trans; first by apply: IH2.
  by rewrite addn1 !addSn addnS ltn_pmul2l.
rewrite addnCA addnA T_ins_tree_length !addnS addn0 !addSn add0n ltnS.
apply: leq_ltn_trans; first by apply: IH1.
by rewrite -[X in (_ < 2 * X)%N]addn2 !mulnDr ltn_add2l.
Qed.

Lemma T_merge_bound ts1 ts2 :
  invar ts1 -> invar ts2 ->
  (T_merge ts1 ts2 <= 4 * trunc_log 2 (size (mset_heap ts1) + size (mset_heap ts2) + 1) + 1)%N.
Proof.
move=>H1 H2.
have H : (T_merge ts1 ts2 <= 2 * (size ts1) + 2 * (size ts2) + 1)%N.
- rewrite -mulnDr; apply: leq_trans; last by apply: T_merge_length.
  by apply: leq_addl.
apply: (leq_trans H); rewrite leq_add2r.
set n1 := size (mset_heap ts1); set n2 := size (mset_heap ts2).
apply: (leq_trans (n:=2 * trunc_log 2 (n1 + 1) + 2 * trunc_log 2 (n2 + 1))).
- by apply: leq_add; rewrite leq_pmul2l //; apply: size_mset_heap.
rewrite (_ : 4 = 2 + 2) // mulnDl; apply: leq_add; rewrite leq_pmul2l //;
apply: leq_trunc_log; rewrite leq_add2r.
- by apply: leq_addr.
by apply: leq_addl.
Qed.

Lemma T_get_min_estimate t ts : T_get_min t ts = (size ts).+1.
Proof. by elim: ts t=>//=t1 ts -> t; rewrite addn1. Qed.

Lemma T_get_min_bound t ts :
  invar_tree t -> all (> rank t) (map rank ts) -> invar ts ->
  (T_get_min t ts <= trunc_log 2 (size (mset_heap (t::ts)) + 1))%N.
Proof.
move=>Ht Ha Hi; rewrite T_get_min_estimate.
by apply: leq_trans; last by apply: size_mset_heap; rewrite invar_cons Ht Ha Hi.
Qed.

Lemma T_get_min_eq_rest t ts : T_get_min_rest t ts = T_get_min t ts.
Proof. by []. Qed.

Lemma T_del_min_bound ts :
  invar ts ->
  (T_del_min ts <= 6 * trunc_log 2 (size (mset_heap ts) + 1) + 3)%N.
Proof.
rewrite /T_del_min; case: ts=>//=t ts; rewrite invar_cons; case/and3P=>Ht Ha Hi.
case Hgmr: (get_min_rest t ts)=>[t' ts2]; case: t' Hgmr=>r a ts1 Hgmr.
have /andP [/invar_children Hl H'] := invar_get_min_rest Hgmr Ht Ha Hi.
set n := size (mset_heap (t::ts)).
set n1 := size (mset_heap ts1); set n2 := size (mset_heap ts2).
have Hn12 : (n1 + n2 <= n)%N.
- by rewrite /n1 /n2 /n (perm_size (perm_mset_heap (mset_get_min_rest Hgmr)))
    /= /mset_heap size_cat.
rewrite {2}(_ : 3 = 2 + 1) // !addnA leq_add2r
  (_ : 6 = 1 + 1 + 4) // !mulnDl mul1n -3!addnA; apply: leq_add.
- by rewrite T_get_min_eq_rest; apply: T_get_min_bound.
rewrite {4}(_ : 2 = 1 + 1) // 2!addnA addnAC -addnA; apply: leq_add.
- apply: (leq_trans (n := trunc_log 2 (n1 + 1) + 1)).
  - rewrite /T_rev' T_catrev_complexity addn1 ltnS.
    rewrite -size_rev /n1 -(perm_size (mset_heap_rev ts1)).
    by apply: size_mset_heap.
  rewrite leq_add2r; apply: leq_trunc_log; rewrite leq_add2r.
  by apply/leq_trans/Hn12; apply: leq_addr.
apply: (leq_trans (n := 4 * trunc_log 2 (n1 + n2 + 1) + 1)).
- apply/leq_trans; first by apply: T_merge_bound.
  by rewrite (perm_size (mset_heap_rev ts1)).
by rewrite leq_add2r leq_pmul2l //; apply: leq_trunc_log; rewrite leq_add2r.
Qed.

End RunningTimeAnalysis.

Section Exercises.
Context {disp : unit} {T : orderType disp}.

(* Exercise 17.1 *)

Fixpoint nol (n : nat) (t : tree T) : nat := 1. (* FIXME *)

Lemma binom_sum (r n : nat) :
  \sum_(0 <= i < r) 'C(i, n) = 'C(r, n.+1).
Proof.
Admitted.

Lemma nol_binom n t :
  invar_btree t -> nol n t = 'C(rank t, n).
Proof.
Admitted.

(* Exercise 17.2 *)

(* 1. *)

Definition invar_bin (bs : seq nat) : bool := true. (* FIXME *)

Definition num_of (bs : seq nat) : nat := 0. (* FIXME *)

Fixpoint carry (d : nat) (b : seq nat) : seq nat := [::d]. (* FIXME *)

Fixpoint add (b1 : seq nat) : seq nat -> seq nat := id. (* FIXME *)

(* 2. *)

Lemma correct_add b1 b2 :
  invar_bin b1 -> invar_bin b2 ->
  num_of (add b1 b2) == num_of b1 + num_of b2.
Proof.
Admitted.

(* 3. *)

Fixpoint T_carry (d : nat) (b : seq nat) : nat := 1. (* FIXME *)

Fixpoint T_add (b1 : seq nat) : seq nat -> nat := fun=>1%N. (* FIXME *)

End Exercises.