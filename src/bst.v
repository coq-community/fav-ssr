From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype choice ssrnat seq order path.
From favssr Require Import prelude bintree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Intro.
Context {disp : unit} {T : orderType disp}.

Fixpoint bst (t : tree T) : bool :=
  if t is Node l a r
    then [&& all (< a) (inorder l), all (> a) (inorder r), bst l & bst r]
    else true.

(* not needed *)
Lemma bst_uniq (t : tree T) : bst t -> uniq (inorder t).
Proof.
elim: t=>//=l IHl a r IHr /and4P [Hal Har /IHl Hl /IHr Hr].
rewrite cat_uniq cons_uniq Hl Hr /= andbT negb_or.
do !(apply/andP; split).
- apply/count_memPn; rewrite -(count_pred0 (inorder l)).
  apply/eq_in_count=>z; move/allP: Hal=>/(_ z) /[apply] /=.
  by rewrite lt_neqAle =>/andP [/negbTE].
- rewrite -all_predC.
  apply/sub_all/Har=>z Hz /=.
  apply/count_memPn; rewrite -(count_pred0 (inorder l)).
  apply/eq_in_count=>x; move/allP: Hal=>/(_ x) /[apply] /= Hx.
  by move: (lt_trans Hx Hz); rewrite lt_neqAle =>/andP [/negbTE].
apply/count_memPn; rewrite -(count_pred0 (inorder r)).
apply/eq_in_count=>z; move/allP: Har=>/(_ z) /[apply] /=.
by rewrite lt_neqAle =>/andP [/negbTE]; rewrite eq_sym.
Qed.

(* Exercise 5.1 *)

Fixpoint nodes {A} (t : tree A) : seq (tree A * A * tree A) := [::]. (* FIXME *)

Definition bst_nodes (t : tree T) : bool :=
  all (fun '(l,a,r) => true) (nodes t). (* FIXME *)

Lemma bst_bst_nodes t : bst t = bst_nodes t.
Proof.
Admitted.

End Intro.

Module ASet.
Structure ASet (disp : unit) (T : orderType disp): Type :=
  make {tp :> Type;
        empty : tp;
        insert : T -> tp -> tp;
        delete : T -> tp -> tp;
        isin : tp -> T -> bool}.

End ASet.

Section Unbalanced.
Context {disp : unit} {T : orderType disp}.

Variant cmp_val := LT | EQ | GT.

Definition cmp (x y : T) : cmp_val :=
  if x < y then LT else if x == y then EQ else GT.

Variant cmp_spec (x y : T) : cmp_val -> cmp_val -> bool -> bool -> bool -> bool -> Set :=
  | CmpLess  of x < y : cmp_spec x y LT GT true  false false false
  | CmpEq    of x = y : cmp_spec x y EQ EQ false true  true  false
  | CmpGreat of x > y : cmp_spec x y GT LT false false false true.

Lemma cmpE (x y : T) : cmp_spec x y (cmp x y) (cmp y x) (x < y) (x == y) (y == x) (y < x).
Proof. by rewrite /cmp; case: ltgtP=>H; constructor. Qed.

Fixpoint isin (t : tree T) x : bool :=
  if t is Node l a r
    then match cmp x a with
         | LT => isin l x
         | EQ => true
         | GT => isin r x
         end
  else false.

Fixpoint insert x (t : tree T) : tree T :=
  if t is Node l a r
    then match cmp x a with
         | LT => Node (insert x l) a r
         | EQ => Node l a r
         | GT => Node l a (insert x r)
         end
  else Node leaf x leaf.

(* deletion by replacing *)

Fixpoint split_min (l : tree T) (a : T) (r : tree T) : T * tree T :=
  if l is Node ll al rl then
    let: (x, l') := split_min ll al rl in
      (x, Node l' a r)
    else (a, r).

Lemma inorder_split_min (l r t : tree T) a x :
  split_min l a r = (x, t) ->
  x :: inorder t = inorder l ++ a :: inorder r.
Proof.
elim: l a r t=>/= [|ll IHl al rl _] a r t; first by case=>->->.
case Hsm: (split_min ll al rl)=>[x0 l'][Hx <-] /=.
rewrite {}Hx in Hsm; rewrite -cat_cons.
by rewrite (IHl _ _ _ Hsm).
Qed.

Fixpoint delete x (t : tree T) : tree T :=
  if t is Node l a r
    then match cmp x a with
           | LT => Node (delete x l) a r
           | EQ => if r is Node lr ar rr
                     then let: (a', r') := split_min lr ar rr in
                          Node l a' r'
                     else l
           | GT => Node l a (delete x r)
         end
  else leaf.

Definition UASet := ASet.make leaf insert delete isin.

(* deletion by joining *)

Equations join (t1 t2 : tree T) : tree T :=
join t              Leaf           => t;
join Leaf           t              => t;
join (Node l1 a r1) (Node l2 b r2) =>
  if join r1 l2 is Node l3 c r3
    then Node (Node l1 a l3) c (Node r3 b r2)
    else Node l1 a (Node leaf b r2).

Lemma join_characteristic l r : inorder (join l r) = inorder l ++ inorder r.
Proof.
funelim (join l r); simp join=>//=; first by rewrite cats0.
case H2: (join r1 l2)=>/=[|l3 c r3]; rewrite {}H2 /= in H.
- by rewrite -catA cat_cons catA -H.
by rewrite -!catA cat_cons -(cat_cons c) catA H -!catA !cat_cons.
Qed.

Fixpoint delete2 x (t : tree T) : tree T :=
  if t is Node l a r
    then match cmp x a with
           | LT => Node (delete2 x l) a r
           | EQ => join l r
           | GT => Node l a (delete2 x r)
         end
  else leaf.

Equations join0 (t1 t2 : tree T) : tree T :=
join0 t              Leaf           => t;
join0 Leaf           t              => t;
join0 (Node l1 a r1) (Node l2 b r2) => Node l1 a (Node (join0 r1 l2) b r2).

(* Exercise 5.2 *)

Lemma join_behaves l r : (height (join l r) <= maxn (height l) (height r) + 1)%N.
Proof.
Admitted.

Definition ub (l r : tree T) : nat := 0%N. (* FIXME *)

Lemma join0_misbehaves l r : (height (join0 l r) <= ub l r)%N.
Proof.
Admitted.

Lemma join0_exact_complete l r :
  complete l -> complete r ->
  height (join0 l r) = ub l r.
Proof.
Admitted.

End Unbalanced.

Section Correctness.
Context {disp : unit} {T : orderType disp}.

(* Exercise 5.3 *)

Lemma inorder_empty : inorder (@Leaf T) = [::].
Proof.
Admitted.

Lemma inorder_insert x (t : tree T) :
  bst t ->
  perm_eq (inorder (insert x t))
          (if x \in inorder t then inorder t else x :: inorder t).
Proof.
Admitted.

Lemma inorder_delete x (t : tree T) :
  bst t ->
  perm_eq (inorder (delete x t))
          (filter (predC1 x) (inorder t)).
Proof.
Admitted.

Lemma inorder_isin (t : tree T) :
  bst t ->
  isin t =i inorder t.
Proof.
Admitted.

Lemma bst_empty : bst (@Leaf T).
Proof.
Admitted.

Lemma bst_insert x (t : tree T) : bst t -> bst (insert x t).
Proof.
Admitted.

(* the following two lemmas might be useful for delete *)
Lemma split_min_all (l r t : tree T) a x (p : pred T) :
  split_min l a r = (x, t) ->
  all p (inorder l) -> p a -> all p (inorder r) ->
  (p x) && all p (inorder t).
Proof.
Admitted.

Lemma bst_split_min (l r t : tree T) a x :
  split_min l a r = (x, t) ->
  all (< a) (inorder l) -> all (> a) (inorder r) ->
  bst l -> bst r ->
  [&& x <= a, all (> x) (inorder t) & bst t].
Proof.
Admitted.

Lemma bst_delete x (t : tree T) : bst t -> bst (delete x t).
Proof.
Admitted.

End Correctness.

Section CorrectnessProofs.
Context {disp : unit} {T : orderType disp}.

(* sorted list library *)

Fixpoint ins_list (x : T) (xs : seq T) : seq T :=
  if xs is a::xs' then
    if x < a
      then x :: a :: xs'
      else if x == a then a :: xs'
        else a :: ins_list x xs'
  else [::x].

Fixpoint del_list (x : T) (xs : seq T) : seq T :=
  if xs is a :: xs' then
    if x == a then xs'
      else a :: del_list x xs'
  else [::].

Lemma inorder_ins_list x xs :
  sorted <%O xs ->
  perm_eq (ins_list x xs)
          (if x \in xs then xs else x :: xs).
Proof.
elim: xs=>//=a xs IH Hp.
case: ifP.
- move/[dup]=>Hxa; rewrite inE lt_neqAle =>/andP [/negbTE -> _] /=.
  move: IH; case: ifP=>//.
  move: (order_path_min lt_trans Hp) =>/allP/[apply] Hax.
  by move: (lt_asym x a); rewrite Hxa Hax.
move/negbT; rewrite inE -leNgt=>Hax; case: ifP=>//=.
move/negbT=>Hxa; move/path_sorted: Hp=>/IH.
case: ifP=>H; first by rewrite perm_cons.
by move=>H1; rewrite perm_sym -cat1s -(cat1s a) perm_catCA /= perm_cons perm_sym.
Qed.

Lemma ins_list_sorted x xs :
  sorted <%O xs -> sorted <%O (ins_list x xs).
Proof.
elim: xs=>//=a xs IH H.
case: ifP=>/=; first by move=>->.
move/negbT; rewrite -leNgt=>Hax.
case: ifP=>//= Hxa.
move: Hax; rewrite le_eqVlt eq_sym Hxa /= => {Hxa}Hax.
move/path_sorted: (H)=>/[dup] Hs /IH H'.
rewrite path_min_sorted {H'}//.
move: (order_path_min lt_trans H)=>Ha.
rewrite (perm_all _ (inorder_ins_list _ Hs)); case: ifP=>//= _.
by rewrite Hax.
Qed.

Lemma del_nop y xs :
  path <%O y xs -> del_list y xs = xs.
Proof.
elim: xs=>//=x xs IH /andP [H1 H2].
move: (H1); rewrite lt_neqAle=>/andP [/negbTE -> _].
by rewrite IH //; apply/(path_le lt_trans)/H2.
Qed.

Lemma inorder_del_list x xs :
  sorted <%O xs ->
  perm_eq (del_list x xs)
          (filter (predC1 x) xs).
Proof.
elim: xs=>//=a xs IH Hp.
move/path_sorted: (Hp)=>/IH {IH}H.
case: ifP.
- move/eqP=>E; move: H; rewrite E eq_refl /=.
  by apply/perm_trans; rewrite perm_sym del_nop.
by move/negbT=>Hx; rewrite eq_sym Hx perm_cons.
Qed.

Lemma del_list_sorted x xs :
  sorted <%O xs -> sorted <%O (del_list x xs).
Proof.
elim: xs=>//=a xs IH H.
move/path_sorted: (H)=>/[dup] H1 /IH {IH}H2.
case: ifP=>//= /negbT Hxa.
rewrite path_min_sorted //.
move: (order_path_min lt_trans H)=>Ha.
rewrite (perm_all _ (inorder_del_list _ H1)) all_filter.
by apply/sub_all/Ha=>z /= ->; exact: implybT.
Qed.

Lemma sorted_cat_cons_cat (l r : seq T) x :
  sorted <%O (l ++ x :: r) = sorted <%O (l ++ [::x]) && sorted <%O (x::r).
Proof.
apply/eqP/bool_eq_iff; split.
- by move/[dup]/cat_sorted2=>->; rewrite -cat1s catA =>/cat_sorted2 ->.
case/andP=>/= + H; rewrite cats1.
case: l=>//=a l; rewrite rcons_path=>/andP [H1 H2].
by rewrite cat_path /= H1 H2.
Qed.

Lemma inslist_sorted_cat_cons_cat (xs ys : seq T) x a :
  sorted <%O (xs ++ [::a]) ->
  ins_list x (xs ++ a :: ys) = if x < a then ins_list x xs ++ a :: ys
                                        else xs ++ ins_list x (a :: ys).
Proof.
elim: xs=>/=; first by move=>_; case: ifP.
move=>y xs + H.
move: (H); move/(order_path_min lt_trans).
rewrite all_cat /= andbT =>/andP [Hxs Hya].
case: ifP.
- move=>Ha; case: ifP=>// /negbT Hy.
  move=>IH; case: ifP=>//= /negbT He.
  by rewrite IH //; apply: (path_sorted H).
move=>/negbT Ha; case: ifP; first by move=>Ha'; rewrite Ha' in Ha.
move=>_; case: ifP.
- move/eqP=>{Ha}->; case: ifP=>/=.
  - by rewrite ltNge le_eqVlt Hya orbT.
  move/negbT; rewrite -leNgt=>_; case: ifP=>// _.
  by move=>->//; apply: (path_sorted H).
move/negbT=>Ha'; move: Ha; rewrite lt_neqAle Ha' /= -ltNge=>{Ha'}Hx.
case: ifP.
- move=>Hy _; move: (lt_trans Hy Hya).
  by rewrite ltNge le_eqVlt Hx orbT.
move/negbT=>Hy; case: ifP.
- move/eqP=>He; rewrite He in Hx; move: Hx.
  by rewrite ltNge le_eqVlt Hya orbT.
by move/eqP=>_ ->//; apply: (path_sorted H).
Qed.

Lemma dellist_sorted_cat_cons_cat (xs ys : seq T) x a :
  sorted <%O (xs ++ a :: ys) ->
  del_list x (xs ++ a :: ys) = if x < a then del_list x xs ++ a :: ys
                                        else xs ++ del_list x (a :: ys).
Proof.
elim: xs=>/=.
- move=>H; case: ifP.
  - by move/eqP=>->; rewrite ltxx.
  move/negbT=>_; case: ifP=>// Hx.
  by rewrite del_nop //; apply/(path_le lt_trans)/H.
move=>y xs + H.
move: (H); move/(order_path_min lt_trans).
rewrite all_cat /= =>/and3P [Hxs Hya Hys].
case: ifP.
- move=>Ha; case: ifP=>// /negbT Hy.
  by move=>-> //; apply: (path_sorted H).
move=>/negbT Ha; case: ifP.
- move/eqP=>{Ha}->; case: ifP=>/=.
  - by move/eqP=>Hay; rewrite Hay ltxx in Hya.
  by move=>_ ->//; apply: (path_sorted H).
move/negbT=>Ha'; move: Ha; rewrite lt_neqAle Ha' /= -ltNge=>{Ha'}Hx.
case: ifP.
- move/eqP=>He; rewrite He in Hx; move: Hx.
  by rewrite ltNge le_eqVlt Hya orbT.
by move/negbT=>_ -> //; apply: (path_sorted H).
Qed.

(* BST via sorted lists *)

Definition bst_list (t : tree T) : bool := sorted <%O (inorder t).

Lemma bst_to_list (t : tree T) :
  bst t <-> bst_list t.
Proof.
rewrite /bst_list; elim: t=>//=l IHl a r IHr.
rewrite sorted_cat_cons_cat /= cats1 (sorted_rconsE lt_trans) (path_sortedE lt_trans) -andbA.
split; case/and4P.
- by move=>->->/IHl->/IHr->.
by move=>->/IHl->->/IHr->.
Qed.

(* mapping to lists *)

Lemma inorder_insert_list x t :
  bst_list t ->
  inorder (insert x t) = ins_list x (inorder t).
Proof.
rewrite /bst_list /=; elim: t=>//=l IHl a r IHr.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite inslist_sorted_cat_cons_cat //.
case: cmpE=>Hx /=.
- case: ltgtP Hx=>//_ _; rewrite IHr //.
  by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
- by rewrite Hx ltxx eq_refl.
by rewrite IHl // (cat_sorted2 H1).
Qed.

Lemma inorder_delete_list x t :
  bst_list t ->
  inorder (delete x t) = del_list x (inorder t).
Proof.
rewrite /bst_list /=; elim: t=>//=l IHl a r IHr /[dup] H.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite dellist_sorted_cat_cons_cat //.
case: cmpE=>Hx /=.
- case: ltgtP Hx=>// _ _; rewrite IHr //.
  by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
- move/eqP: Hx; case: ltgtP=>//_ _.
  case: {IHr H H2}r=>//=; first by rewrite cats0.
  move=>lr ar rr.
  case Hsm: (split_min lr ar rr)=>[x' l'] /=.
  by rewrite (inorder_split_min Hsm).
rewrite IHl //.
by rewrite (cat_sorted2 H1).
Qed.

Lemma inorder_isin_list (t : tree T) :
  bst_list t ->
  isin t =i inorder t.
Proof.
rewrite /bst_list /= => + x; elim: t=>//=l IHl a r IHr.
rewrite -topredE /= in IHl; rewrite -topredE /= in IHr.
rewrite -topredE /= mem_cat inE sorted_cat_cons_cat=>/andP [H1 H2].
case: cmpE=>Hx /=; rewrite ?orbT //.
- rewrite IHr; last by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
  move: H1; rewrite cats1 (sorted_rconsE lt_trans); case/andP=>Ha _.
  suff: x \notin inorder l by move/negbTE=>->.
  by apply: (all_notin Ha)=>/=; rewrite -leNgt; apply: ltW.
rewrite IHl; last by rewrite (cat_sorted2 H1).
move: H2=>/= /(order_path_min lt_trans)=>Ha.
suff: x \notin inorder r by move/negbTE=>->/=; rewrite orbF.
by apply: (all_notin Ha)=>/=; rewrite -leNgt; apply: ltW.
Qed.

Definition LASet := ASet.make [::] ins_list del_list (@mem_seq T).

End CorrectnessProofs.

Section TreeRotations.
Context {disp : unit} {T : orderType disp}.

Fixpoint is_list (t : tree T) : bool :=
  if t is Node l _ r then ~~ is_node l && is_list r else true.

Fixpoint rlen (t : tree T) : nat :=
  if t is Node _ _ r then (rlen r).+1 else 0.

Lemma rlen_le_size t : (rlen t <= size_tree t)%N.
Proof.
elim: t=>//= l _ _ r IHr.
by rewrite addn1 ltnS; apply/(leq_trans IHr)/leq_addl.
Qed.

Equations? list_of (t : tree T) : tree T by wf (2 * size_tree t - rlen t) lt :=
list_of (Node (Node ll a rl) b r) => list_of (Node ll a (Node rl b r));
list_of (Node           Leaf a r) => Node leaf a (list_of r);
list_of  Leaf                     => leaf.
Proof.
all: apply: ssrnat.ltP.
- rewrite add0n mulnDr muln1 {3}(_ : 2 = 1 + 1) // addnA addn1 subSS -addnBAC ?addn1 //.
  by apply/leq_trans/leq_pmull=>//; exact: rlen_le_size.
rewrite (@addnAC (size_tree rl)) !addnA subnS ltn_predL subn_gt0 mulnDr muln1
  {2}(_ : 2 = 1 + 1) // addnA addn1 ltnS addn1 ltnS mul2n.
apply: leq_trans; first by exact: rlen_le_size.
by rewrite doubleD -(@addnn (size_tree r)) addnA; apply: leq_addl.
Qed.

Lemma is_list_rot t : is_list (list_of t).
Proof. by funelim (list_of t). Qed.

Lemma inorder_rot t : inorder (list_of t) = inorder t.
Proof. by funelim (list_of t)=>//=; rewrite H //= -catA. Qed.

Variant dir := L | R.

Definition pos := seq dir.

Equations? rotR_poss (t : tree T) : seq pos by wf (2 * size_tree t - rlen t) lt :=
rotR_poss (Node (Node ll a rl) b r) => [::] :: rotR_poss (Node ll a (Node rl b r));
rotR_poss (Node Leaf a r)           => map (cons R) (rotR_poss r);
rotR_poss  Leaf                     => [::].
Proof.  (* identical to above *)
all: apply: ssrnat.ltP.
- rewrite add0n mulnDr muln1 {3}(_ : 2 = 1 + 1) // addnA addn1 subSS -addnBAC ?addn1 //.
  by apply/leq_trans/leq_pmull=>//; exact: rlen_le_size.
rewrite (@addnAC (size_tree rl)) !addnA subnS ltn_predL subn_gt0 mulnDr muln1
  {2}(_ : 2 = 1 + 1) // addnA addn1 ltnS addn1 ltnS mul2n.
apply: leq_trans; first by exact: rlen_le_size.
by rewrite doubleD -(@addnn (size_tree r)) addnA; apply: leq_addl.
Qed.

Equations apply_at (f : tree T -> tree T) (p : pos) (t : tree T) : tree T :=
apply_at f [::]      t            => f t;
apply_at f ds        Leaf         => leaf;
apply_at f (L :: ds) (Node l a r) => Node (apply_at f ds l) a r;
apply_at f (R :: ds) (Node l a r) => Node l a (apply_at f ds r).

Fixpoint apply_ats (f : tree T -> tree T) (ps : seq pos) (t : tree T) : tree T :=
  if ps is p :: ps' then apply_ats f ps' (apply_at f p t) else t.

Equations rotR (t : tree T) : tree T :=
rotR (Node (Node ll a rl) b r) => Node ll a (Node rl b r);
rotR  t                        => t.

Equations rotL (t : tree T) : tree T :=
rotL (Node ll a (Node rl b r)) => Node (Node ll a rl) b r;
rotL  t                        => t.

Definition rotRs := apply_ats rotR.
Definition rotLs := apply_ats rotL.

Lemma apply_ats_map_R f ps l a r :
  apply_ats f (map (cons R) ps) (Node l a r) = Node l a (apply_ats f ps r).
Proof. by elim: ps r=>//= p ps IH r; simp apply_at. Qed.

Lemma inorder_rotRs_poss t : inorder (rotRs (rotR_poss t) t) = inorder t.
Proof.
funelim (rotR_poss t)=>//=; rewrite /rotRs /= in H *.
- by rewrite apply_ats_map_R /= H.
by simp apply_at rotR; rewrite H -catA.
Qed.

Lemma is_list_rotRs t : is_list (rotRs (rotR_poss t) t).
Proof.
by funelim (rotR_poss t)=>//; rewrite /rotRs apply_ats_map_R.
Qed.

Lemma length_rotRs_poss t : size (rotR_poss t) = size_tree t - rlen t.
Proof.
funelim (rotR_poss t)=>//=.
- by rewrite size_map add0n addn1 subSS.
rewrite H /= addn1 subSS subnSK; last first.
- by rewrite !addnA addn1 ltnS; apply: leq_trans; [exact: rlen_le_size | apply: leq_addl].
by rewrite [in RHS]addn1 subSS addnAC !addnA.
Qed.

Lemma size_rlen_better_ub t : (size_tree t - rlen t <= (size_tree t).-1)%N.
Proof.
by case: t=>//= l _ r; rewrite -subn1 leq_sub2lE // addn1.
Qed.

Lemma apply_ats_append f ps1 ps2 t :
  apply_ats f (ps1 ++ ps2) t = apply_ats f ps2 (apply_ats f ps1 t).
Proof. by elim: ps1 t=>/=. Qed.

Lemma rot_id t : rotLs (rev (rotR_poss t)) (rotRs (rotR_poss t) t) = t.
Proof.
funelim (rotR_poss t)=>//=; rewrite /rotLs /rotRs in H *.
- by rewrite apply_ats_map_R -map_rev apply_ats_map_R H.
rewrite rev_cons -cat1s -cats1 !apply_ats_append /=.
by simp apply_at; rewrite H; simp rotL.
Qed.

Lemma inorder_nil (t : tree T) : inorder t = [::] -> t = leaf.
Proof.
case: t=>//= l a r.
by move/(f_equal size)=>/=; rewrite size_cat /= addnS.
Qed.

Lemma is_list_inorder_same t1 t2 :
  is_list t1 -> is_list t2 -> inorder t1 = inorder t2 -> t1 = t2.
Proof.
elim: t1 t2=>/= [t2 _ _| l _ a r IHr t2].
- case: t2=>//= l2 a2 r2.
  by move/(f_equal size)=>/=; rewrite size_cat /= addnS.
case/andP=>/not_node_leaf {l}-> Hr; case: t2=>//= l2 a2 r2.
case/andP=>/not_node_leaf {l2}-> Hr2 /= [->] H2.
by rewrite (IHr r2 Hr Hr2 H2).
Qed.

Corollary tree_to_tree_rotations t1 t2 :
  inorder t1 = inorder t2 ->
  rotLs (rev (rotR_poss t2)) (rotRs (rotR_poss t1) t1) = t2.
Proof.
move=>E.
have H : rotRs (rotR_poss t1) t1 = rotRs (rotR_poss t2) t2.
- apply: is_list_inorder_same; try by apply: is_list_rotRs.
  by rewrite !inorder_rotRs_poss.
move/(f_equal (rotLs (rev (rotR_poss t2)))): H=>->.
by apply: rot_id.
Qed.

(* Exercise 5.4 *)

Equations? count_rots (t : tree T) : nat by wf (2 * size_tree t - rlen t) lt :=
count_rots t => 0. (* FIXME *)
Proof.
Qed.

Lemma count_rots_correct t : count_rots t = size_tree t - rlen t.
Proof.
Admitted.

(* Exercise 5.5 *)

Lemma rotRs_induction t :
  exists2 ps, is_list (rotRs ps t) & inorder (rotRs ps t) = inorder t.
Proof.
Admitted.

End TreeRotations.

(* Exercise 5.6 *)

Lemma rotRs_max :
  exists (t : tree nat) ps, is_list (rotRs ps t) /\ size (rotR_poss t) < size ps.
Proof.
Admitted.

Section Augmented.
Context {disp : unit} {T : orderType disp} {A : Type}.
Implicit Types (t : tree (T*A)).

Fixpoint isin_a t x : bool :=
  if t is Node l (a,_) r
    then match cmp x a with
           | LT => isin_a l x
           | EQ => true
           | GT => isin_a r x
         end
  else false.

Fixpoint bst_a t : bool :=
  if t is Node l (a, _) r
    then [&& all (< a) (inorder_a l), all (> a) (inorder_a r), bst_a l & bst_a r]
    else true.

(* not needed *)
Lemma bst_a_uniq t : bst_a t -> uniq (inorder_a t).
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

Definition bst_list_a t : bool := sorted <%O (inorder_a t).

Lemma bst_to_list_a t :
  bst_a t <-> bst_list_a t.
Proof.
rewrite /bst_list_a /=; elim: t=>//=l IHl [a b] r IHr.
rewrite sorted_cat_cons_cat /= cats1 (sorted_rconsE lt_trans) (path_sortedE lt_trans) -andbA.
split; case/and4P.
- by move=>->->/IHl->/IHr->.
by move=>->/IHl->->/IHr->.
Qed.

Lemma inorder_isin_list_a t :
  bst_list_a t ->
  isin_a t =i inorder_a t.
Proof.
move/bst_to_list_a=>+ x; elim: t=>//= l IHl [a c] r IHr.
case/and4P=>Hal Har /IHl {IHl}Hl /IHr {IHr}Hr.
rewrite -topredE /= in Hl; rewrite -topredE /= in Hr.
rewrite -topredE /= mem_cat inE; case: cmpE=>Hx /=; rewrite ?orbT //.
- suff: x \notin inorder_a l by move/negbTE=>->.
  by apply: (all_notin Hal)=>/=; rewrite -leNgt; apply: ltW.
suff: x \notin inorder_a r by move/negbTE=>->/=; rewrite orbF.
by apply: (all_notin Har)=>/=; rewrite -leNgt; apply: ltW.
Qed.

End Augmented.

Section IntervalTrees.
Context {disp : unit} {T : orderType disp}.

(* intervals *)

Structure ivl : Type := Interval {ival :> T * T; _ : ival.1 <= ival.2}.

Canonical interval_subType := Eval hnf in [subType for ival].

Definition interval_eqMixin := Eval hnf in [eqMixin of ivl by <:].
Canonical interval_eqType := Eval hnf in EqType ivl interval_eqMixin.
Definition interval_choiceMixin := [choiceMixin of ivl by <:].
Canonical interval_choiceType := Eval hnf in ChoiceType ivl interval_choiceMixin.

Definition low: ivl -> T := fst \o ival.
Definition high: ivl -> T := snd \o ival.

Lemma xivl_eqE x y : (x == y) = (low x == low y) && (high x == high y).
Proof.
by rewrite /low /high -val_eqE
  (surjective_pairing (val x)) (surjective_pairing (val y)) xpair_eqE.
Qed.

Definition lt_ivl x y := (low x < low y) || (low x == low y) && (high x < high y).
Definition le_ivl x y := (low x < low y) || (low x == low y) && (high x <= high y).

Fact lt_def_ivl : forall x y, lt_ivl x y = (y != x) && (le_ivl x y).
Proof.
move=>x y; rewrite /lt_ivl /le_ivl.
case H: (y==x)=>/=.
- by move/eqP: H=>->; rewrite !ltxx andbF.
suff: (low x != low y) || (high x != high y).
- case/orP; first by move/negbTE=>->.
  by rewrite (lt_neqAle (high _))=>->.
move/negbT: H; rewrite -negb_and; apply: contra.
by rewrite -xivl_eqE eq_sym.
Qed.

Fact refl_ivl : reflexive le_ivl.
Proof. by move=>x; rewrite /le_ivl ltxx eq_refl lexx. Qed.

Fact anti_ivl : antisymmetric le_ivl.
Proof.
move=>x y; rewrite /le_ivl =>/andP [].
case/orP=>[H1|/andP [/eqP H11 H21]]; case/orP=>[H2|/andP [/eqP H12 H22]].
- by move: (lt_asym (low x) (low y)); rewrite H1 H2.
- by rewrite H12 ltxx in H1.
- by rewrite H11 ltxx in H2.
apply/val_inj.
move: {H12}H11 H21 H22; case: x =>[[x1 x2] /= Hx]; case: y =>[[y1 y2] /= Hy].
rewrite /low /high /= => -> H1 H2.
by move: (eq_le x2 y2); rewrite H1 H2 /= =>/eqP ->.
Qed.

Fact trans_ivl : transitive le_ivl.
Proof.
move=>x y z; rewrite /le_ivl.
case/orP=>[H1|/andP [/eqP H11 H21]]; case/orP=>[H2|/andP [/eqP H12 H22]].
- by move: (lt_trans H1 H2)=>->.
- by rewrite -H12 H1.
- by rewrite H11 H2.
rewrite H11 H12 ltxx eq_refl /=.
by apply/le_trans/H22.
Qed.

Definition ivl_porderMixin : lePOrderMixin interval_eqType :=
  LePOrderMixin lt_def_ivl refl_ivl anti_ivl trans_ivl.
Canonical ivl_porderType := Eval hnf in POrderType tt ivl ivl_porderMixin.

Fact total_ivl : total le_ivl.
Proof.
move=>x y; rewrite /le_ivl.
case: (ltgtP (low x) (low y))=>//= _.
by apply: le_total.
Qed.

Definition ivl_totalPOrderMixin :
  totalPOrderMixin ivl_porderType := total_ivl.
Canonical ivl_latticeType :=
  Eval hnf in LatticeType ivl ivl_totalPOrderMixin.
Canonical ivl_distrLatticeType :=
  Eval hnf in DistrLatticeType ivl ivl_totalPOrderMixin.
Canonical ivl_orderType :=
  Eval hnf in OrderType ivl ivl_totalPOrderMixin.

Definition overlap (x y : ivl) := (low y <= high x) && (low x <= high y).

Lemma overlapC x y : overlap x y = overlap y x.
Proof. by rewrite /overlap andbC. Qed.

Definition has_overlap (s : seq ivl) y := has (overlap^~ y) s.

Lemma le_low x y : x <= y -> low x <= low y.
Proof.
rewrite {1}/Order.le /= /le_ivl (le_eqVlt (low _)).
by case/orP; [move=>->; rewrite orbT|case/andP=>->].
Qed.

(* interval trees = trees of intervals augmented with maximal values *)

Definition ivl_tree := tree (ivl * T).

(* TODO construct a proper bLattice? *)
Variables (x0 : T) (lmin : left_id x0 Order.max).

Lemma rmin : right_id x0 Order.max.
Proof. by move=>x; rewrite maxC lmin. Qed.

Definition max3 (m : T) (a : ivl) (n : T) : T :=
  Order.max (high a) (Order.max m n).

Definition max_hi : ivl_tree -> T := b_val x0.

Definition inv_max_hi : ivl_tree -> bool := invar_f x0 max3.

Lemma max_hi_max t x :
  inv_max_hi t -> x \in inorder_a t -> high x <= max_hi t.
Proof.
elim: t=>/=; first by rewrite in_nil.
move=>l IHl [a m] r IHr /and3P [/eqP -> /IHl Hl /IHr Hr] {IHl IHr}.
rewrite mem_cat inE /max3; case/or3P.
- move/Hl=>H.
  apply/(le_trans H)/(le_trans (y:=Order.max (max_hi l) (max_hi r)));
  by rewrite le_maxr lexx ?orbT.
- by move/eqP=>->; rewrite le_maxr lexx.
move/Hr=>H.
apply/(le_trans H)/(le_trans (y:=Order.max (max_hi l) (max_hi r)));
by rewrite le_maxr lexx ?orbT.
Qed.

Lemma max_hi_mem t :
  inv_max_hi t -> is_node t ->
  has (fun a => high a == max_hi t) (inorder_a t).
Proof.
elim: t=>//= l IHl [a m] r IHr /and3P [/eqP E /IHl Hl /IHr Hr] {IHl IHr} _.
rewrite has_cat /=.
case: r E Hr=>/=; case: l Hl=>/=; rewrite /max3.
- by move=>_ + _; rewrite lmin rmin =>->; rewrite eq_refl.
- move=>ll [al ml] lr H; rewrite orbF rmin /Order.max; case: ifP=>_ -> _;
  by rewrite ?H // eq_refl orbT.
- move=>_ rl [ar mr] rr; rewrite lmin /Order.max=>+ H; case: ifP=>_ ->;
  by rewrite ?eq_refl // H // orbT.
move=>ll [al ml] lr Hl rl [ar mr] rr; rewrite /Order.max; case: ifP=>_.
- case: ifP=>_-> Hr; last by rewrite Hl.
  by rewrite Hr // !orbT.
by move=>->_; rewrite eq_refl /= orbT.
Qed.

(* sets of intervals *)

Definition node_i : ivl_tree -> ivl -> ivl_tree -> ivl_tree :=
  node_f x0 max3.

Fixpoint insert_i x (t : ivl_tree) : ivl_tree :=
  if t is Node l (a,m) r
    then match cmp x a with
           | LT => node_i (insert_i x l) a r
           | EQ => Node l (a,m) r
           | GT => node_i l a (insert_i x r)
         end
  else Node leaf (x, high x) leaf.

Fixpoint split_min_i (l : ivl_tree) (a : ivl) (r : ivl_tree) : ivl * ivl_tree :=
  if l is Node ll (al, _) rl then
    let: (x, l') := split_min_i ll al rl in
        (x, node_i l' a r)
    else (a, r).

Lemma inorder_ivl_split_min (l r t : ivl_tree) a x :
  split_min_i l a r = (x, t) ->
  x :: inorder_a t = inorder_a l ++ a :: inorder_a r.
Proof.
elim: l a r t=>/= [|ll IHl [al _] rl _] a r t; first by case=>->->.
case Hsm: (split_min_i ll al rl)=>[x' l'][Hx <-] /=.
rewrite {}Hx in Hsm; rewrite -cat_cons.
by rewrite (IHl _ _ _ Hsm).
Qed.

Fixpoint delete_i x (t : ivl_tree) : ivl_tree :=
  if t is Node l (a,_) r
    then match cmp x a with
           | LT => node_i (delete_i x l) a r
           | EQ => if r is Node lr (ar,_) rr
                     then let: (a', r') := split_min_i lr ar rr in
                          node_i l a' r'
                     else l
           | GT => node_i l a (delete_i x r)
         end
  else leaf.

(* functional correctness *)

Lemma inorder_ivl_insert_list x t :
  bst_list_a t ->
  inorder_a (insert_i x t) = ins_list x (inorder_a t).
Proof.
rewrite /bst_list_a; elim: t=>//=l IHl [a m] r IHr.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite inslist_sorted_cat_cons_cat //.
case: cmpE=>Hx /=.
- case: ltgtP Hx=>//_ _; rewrite IHr //.
  by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
- by move/eqP: Hx; case: ltgtP.
rewrite IHl //.
by rewrite (cat_sorted2 H1).
Qed.

Lemma inorder_ivl_delete_list x t :
  bst_list_a t ->
  inorder_a (delete_i x t) = del_list x (inorder_a t).
Proof.
rewrite /bst_list_a; elim: t=>//=l IHl [a m] r IHr /[dup] H.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite dellist_sorted_cat_cons_cat //.
case: cmpE=>Hx /=.
- case: ltgtP Hx=>//_ _; rewrite IHr //.
  by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
- rewrite Hx eq_refl.
  case: {IHr H H2}r=>//=; first by rewrite cats0.
  move=>lr [ar _] rr.
  case Hsm: (split_min_i lr ar rr)=>[x' l'] /=.
  by rewrite (inorder_ivl_split_min Hsm).
rewrite IHl //.
by rewrite (cat_sorted2 H1).
Qed.

Lemma inv_max_hi_insert x t :
  inv_max_hi t -> inv_max_hi (insert_i x t).
Proof.
elim: t=>/=; first by rewrite /max3 lmin rmin eq_refl.
move=>l IHl [a m] r IHr /and3P [/eqP E Hl Hr].
move:(IHl Hl)=>{}IHl; move:(IHr Hr)=>{}IHr.
by case: cmpE=>/=; rewrite ?E eq_refl ?Hl ?Hr ?IHl ?IHr.
Qed.

Lemma inv_max_split_min (l r t : ivl_tree) a x :
  split_min_i l a r = (x, t) ->
  inv_max_hi l -> inv_max_hi r ->
  inv_max_hi t.
Proof.
elim: l a r t=>/= [|ll IHl [al ml] rl _] a r t; first by case=>_->.
case Hsm: (split_min_i ll al rl)=>[x' l'] [Hx <-] /=; rewrite {}Hx in Hsm.
case/and3P=>_ Hll Hrl ->; rewrite eq_refl andbT /=.
by rewrite (IHl _ _ _ Hsm Hll Hrl).
Qed.

Lemma inv_max_hi_delete x t :
  inv_max_hi t -> inv_max_hi (delete_i x t).
Proof.
elim: t=>//=.
move=>l IHl [a m] r IHr /and3P [/eqP E Hl Hr].
move:(IHl Hl)=>{}IHl; move:(IHr Hr)=>{}IHr.
case: cmpE=>_ /=.
- by rewrite eq_refl Hl IHr.
- case: {E IHr}r Hr=>//= lr [ar mr] rr.
  case/and3P=>_ Hlr Hrr.
  case Hsm: (split_min_i lr ar rr)=>[x' l'] /=.
  by rewrite eq_refl Hl /=; apply: (inv_max_split_min Hsm).
by rewrite eq_refl IHl Hr.
Qed.

(* top-level correctness *)

Definition invar t := inv_max_hi t && bst_list_a t.

Corollary inorder_ivl_insert_list_set x (t : ivl_tree) :
  invar t ->
  perm_eq (inorder_a (insert_i x t))
          (if x \in inorder_a t then inorder_a t else x :: inorder_a t).
Proof.
rewrite /invar =>/andP [_ Hs].
rewrite inorder_ivl_insert_list //.
by apply: inorder_ins_list.
Qed.

Corollary inorder_ivl_delete_list_set x (t : ivl_tree) :
  invar t ->
  perm_eq (inorder_a (delete_i x t))
          (filter (predC1 x) (inorder_a t)).
Proof.
rewrite /invar =>/andP [_ Hs].
rewrite inorder_ivl_delete_list //.
by apply: inorder_del_list.
Qed.

Corollary invar_insert x (t : ivl_tree) :
  invar t -> invar (insert_i x t).
Proof.
rewrite /invar /bst_list_a =>/andP [Hi Hs].
rewrite inv_max_hi_insert //= inorder_ivl_insert_list //.
by apply: ins_list_sorted.
Qed.

Corollary invar_delete x (t : ivl_tree) :
  invar t -> invar (delete_i x t).
Proof.
rewrite /invar /bst_list_a =>/andP [Hi Hs].
rewrite inv_max_hi_delete //= inorder_ivl_delete_list //.
by apply: del_list_sorted.
Qed.

(* searching for an overlapping interval *)

Fixpoint search (t : ivl_tree) (x : ivl) : bool :=
  if t is Node l (a,_) r then
    if overlap x a then true
      else if is_node l && (low x <= max_hi l)
        then search l x else search r x
    else false.

Lemma search_correct t x :
  invar t -> search t x = has_overlap (inorder_a t) x.
Proof.
rewrite /invar /bst_list_a; elim: t=>//=.
move=>l IHl [a _] r IHr /andP [/and3P [_ Hl Hr] Hs].
rewrite /has_overlap has_cat /= overlapC.
case: ifP=>/=; first by rewrite orbT.
move=>_; case: ifP.
- case/andP=>Hnl H2.
  rewrite IHl /has_overlap; last by rewrite Hl (cat_sorted2 Hs).
  case Hol: (has (overlap^~ x) (inorder_a l))=>//=; symmetry; apply/negbTE.
  case/hasP: (max_hi_mem Hl Hnl)=>/= p Hp /eqP Ep; rewrite -{}Ep in H2.
  move/negbT: Hol; rewrite -all_predC=>/allP /(_ _ Hp) /=.
  rewrite {1}/overlap negb_and H2 /= -ltNge => Hxp.
  apply/hasPn=>rp Hrp; rewrite /overlap negb_and -!ltNge.
  apply/orP; right; apply: (lt_le_trans Hxp).
  move: Hs; rewrite (sorted_pairwise lt_trans) pairwise_cat =>/and3P [+ _ _].
  rewrite allrel_consr=>/andP [_ /allP /(_ _ Hp) /= /allP /(_ _ Hrp)].
  by move/ltW/le_low.
rewrite IHr /has_overlap; last by rewrite -cat1s catA in Hs; rewrite Hr (cat_sorted2 Hs).
move/negbT; rewrite negb_and; case/orP; first by move/not_node_leaf=>->.
rewrite -ltNge=>Hlx.
suff: ~~has (overlap^~ x) (inorder_a l) by move/negbTE=>->.
apply/hasPn=>/= lp Hlp; rewrite /overlap negb_and -!ltNge; apply/orP; left.
by apply/le_lt_trans/Hlx/max_hi_max.
Qed.

(* Exercise 5.7 *)

Definition in_ivl (x : T) (iv : ivl) : bool := low iv <= x <= high iv.

Fixpoint search1 (t : ivl_tree) (x : T) : bool := false. (* FIXME *)

Lemma search1_correct t x :
  invar t -> search1 t x = has (in_ivl x) (inorder_a t).
Proof.
Admitted.

End IntervalTrees.