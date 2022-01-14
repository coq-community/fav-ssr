From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq order path.
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

(* Exercise 5.1 *)

Fixpoint nodes {A} (t : tree A) : seq (tree A * A * tree A) := [::]. (* FIXME *)

Definition bst_nodes (t : tree T) : bool :=
  all (fun '(l,a,r) => true) (nodes t). (* FIXME *)

Lemma bst_bst_nodes t : bst t = bst_nodes t.
Proof.
Admitted.

End Intro.

Module ASet.
Record ASet (disp : unit) (T : orderType disp): Type :=
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

Lemma cmp_lt x y : cmp x y = LT -> x < y.
Proof. by rewrite /cmp; case: ltP=>//; case: eqP. Qed.

Lemma cmp_eq x y : cmp x y = EQ -> x == y.
Proof. by rewrite /cmp; case: ltP=>//; case: eqP. Qed.

Lemma cmp_gt x y : cmp x y = GT -> y < x.
Proof.
rewrite /cmp; case: ltP=>//; case: ifP=>//.
by rewrite lt_neqAle eq_sym=>->->.
Qed.

Definition empty : tree T := @Leaf T.

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
  else Node (@Leaf T) x (@Leaf T).

Fixpoint split_min (l : tree T) (a : T) (r : tree T) : T * tree T :=
  if l is Node ll al rl then
    let '(x, l') := split_min ll al rl in
        (x, Node l' a r)
    else (a, r).

Lemma inorder_split_min (l r t : tree T) a x :
  split_min l a r = (x, t) ->
  x :: inorder t = inorder l ++ a :: inorder r.
Proof.
elim: l a r t=>/=; first by move=>a r t; case=>->->.
move=>ll IHl al rl _ a r t.
case Hsm: (split_min ll al rl)=>[x0 l'] [Hx <-] /=.
rewrite {}Hx in Hsm; rewrite -cat_cons.
by rewrite (IHl _ _ _ Hsm).
Qed.

Fixpoint delete x (t : tree T) : tree T :=
  if t is Node l a r
    then match cmp x a with
           | LT => Node (delete x l) a r
           | EQ => if r is Node lr ar rr
                     then let '(a', r') := split_min lr ar rr in
                          Node l a' r'
                     else l
           | GT => Node l a (delete x r)
         end
  else @Leaf T.

Definition UASet := ASet.make empty insert delete isin.

Equations join (t1 t2 : tree T) : tree T :=
join t              Leaf           => t;
join Leaf           t              => t;
join (Node l1 a r1) (Node l2 b r2) =>
  if join r1 l2 is Node l3 c r3
    then Node (Node l1 a l3) c (Node r3 b r2)
    else Node l1 a (Node (@Leaf T) b r2).

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
  else @Leaf T.

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

Lemma inorder_empty : inorder (@empty _ T) = [::].
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

Lemma inorder_isin x (t : tree T) :
  bst t ->
  isin t x = (x \in inorder t).
Proof.
Admitted.

Lemma bst_empty : bst (@empty _ T).
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

Definition bst_list (t : tree T) : bool := sorted <%O (inorder t).

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

Lemma del_nop y xs :
  path <%O y xs -> del_list y xs = xs.
Proof.
elim: xs=>//=x xs IH /andP [H1 H2].
move: (H1); rewrite lt_neqAle=>/andP [/negbTE -> _].
by rewrite IH //; apply/(path_le lt_trans)/H2.
Qed.

Lemma sorted_cat_cons_cat (l r : seq T) x :
  sorted <%O (l ++ x :: r) = sorted <%O (l ++ [::x]) && sorted <%O (x::r).
Proof.
apply/eqP/bool_eq_iff; split.
- by move/[dup]/cat_sorted2=>->; rewrite -cat1s catA => /cat_sorted2 ->.
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
rewrite all_cat /= andbT => /andP [Hxs Hya].
case: ifP.
- move=>Ha; case: ifP=>// /negbT Hy.
  move=>IH; case: ifP=>//= /negbT He.
  by rewrite IH // -(path_min_sorted (x:=y)) // all_cat /= Hxs Hya.
move=>/negbT Ha; case: ifP; first by move=>Ha'; rewrite Ha' in Ha.
move=>_; case: ifP.
- move/eqP=>{Ha}->; case: ifP=>/=.
  - by rewrite ltNge le_eqVlt Hya orbT.
  move/negbT; rewrite -leNgt=>_; case: ifP=>// _ IH.
  by rewrite IH // -(path_min_sorted (x:=y)) // all_cat /= andbT Hxs Hya.
move/negbT=>Ha'; move: Ha; rewrite lt_neqAle Ha' /= -ltNge=>{Ha'}Hx.
case: ifP.
- move=>Hy _; move: (lt_trans Hy Hya).
  by rewrite ltNge le_eqVlt Hx orbT.
move/negbT=>Hy; case: ifP.
- move/eqP=>He; rewrite He in Hx; move: Hx.
  by rewrite ltNge le_eqVlt Hya orbT.
by move/eqP=>He IH; rewrite IH // -(path_min_sorted (x:=y)) // all_cat /= Hxs Hya.
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
rewrite all_cat /= => /and3P [Hxs Hya Hys].
case: ifP.
- move=>Ha; case: ifP=>// /negbT Hy.
  by move=>IH; rewrite IH // -(path_min_sorted (x:=y)) // all_cat /= Hxs Hya.
move=>/negbT Ha; case: ifP.
- move/eqP=>{Ha}->; case: ifP=>/=.
  - by move/eqP=>Hay; rewrite Hay ltxx in Hya.
  by move=>_ IH; rewrite IH // -(path_min_sorted (x:=y)) // all_cat /= Hxs Hya.
move/negbT=>Ha'; move: Ha; rewrite lt_neqAle Ha' /= -ltNge=>{Ha'}Hx.
case: ifP.
- move/eqP=>He; rewrite He in Hx; move: Hx.
  by rewrite ltNge le_eqVlt Hya orbT.
by move/negbT=>Hxy IH; rewrite IH // -(path_min_sorted (x:=y)) // all_cat /= Hxs Hya.
Qed.

Lemma inorder_insert_list x t :
  bst_list t ->
  inorder (insert x t) = ins_list x (inorder t).
Proof.
rewrite /bst_list /=.
elim: t=>//=l IHl a r IHr.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite inslist_sorted_cat_cons_cat //.
case Hc: (cmp x a)=>/=.
- move/cmp_lt: Hc=>->; rewrite IHl //.
  by rewrite (cat_sorted2 H1).
- by move/cmp_eq: Hc=>/eqP ->; rewrite ltxx eq_refl.
move/cmp_gt: Hc=>/[dup] Hx.
rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
rewrite IHr //.
by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
Qed.

Lemma inorder_delete_list x t :
  bst_list t ->
  inorder (delete x t) = del_list x (inorder t).
Proof.
rewrite /bst_list /=.
elim: t=>//=l IHl a r IHr /[dup] H.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite dellist_sorted_cat_cons_cat //.
case Hc: (cmp x a)=>/=.
- move/cmp_lt: Hc=>->; rewrite IHl //.
  by rewrite (cat_sorted2 H1).
- move/cmp_eq: Hc=>/eqP ->; rewrite ltxx eq_refl.
  case: {IHr H H2}r=>//=; first by rewrite cats0.
  move=>lr ar rr.
  case Hsm: (split_min lr ar rr)=>[x' l'] /=.
  by rewrite (inorder_split_min Hsm).
move/cmp_gt: Hc=>/[dup] Hx.
rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
rewrite IHr //.
by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
Qed.

Lemma inorder_isin_list x (t : tree T) :
  bst_list t ->
  isin t x = (x \in inorder t).
Proof.
rewrite /bst_list /=.
elim: t=>//=l IHl a r IHr.
rewrite mem_cat inE sorted_cat_cons_cat=>/andP [H1 H2].
case Hc: (cmp x a)=>/=.
- move/cmp_lt: Hc=>Hx; rewrite IHl; last by rewrite (cat_sorted2 H1).
  have ->: (x==a)=false by move: Hx; rewrite lt_neqAle=>/andP [/negbTE].
  have ->: x \in inorder r = false; last by rewrite /= orbF.
  apply/negbTE/count_memPn; rewrite -(count_pred0 (inorder r)).
  apply/eq_in_count=>z; move: H2=>/= /(order_path_min lt_trans)/allP/(_ z)/[apply] Hz.
  by move: (lt_trans Hx Hz); rewrite lt_neqAle eq_sym=>/andP [/negbTE].
- by move/cmp_eq: Hc=>/eqP->; rewrite eq_refl /= orbT.
move/cmp_gt: Hc=>Hx; rewrite IHr; last first.
- by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
have ->: (x==a)=false by move: Hx; rewrite lt_neqAle eq_sym=>/andP [/negbTE].
suff: x \in inorder l = false by move=>->.
apply/negbTE/count_memPn; rewrite -(count_pred0 (inorder l)).
apply/eq_in_count=>z /=.
move: H1; rewrite (sorted_pairwise lt_trans) pairwise_cat /= allrel1r andbT.
case/andP=>+ _ => /allP/(_ z)/[apply] Hz.
by move: (lt_trans Hz Hx); rewrite lt_neqAle eq_sym=>/andP [/negbTE].
Qed.

End CorrectnessProofs.