From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype order seq.
From favssr Require Import prelude bintree braun priority.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Implementation.
Context {disp : Order.disp_t} {T : orderType disp}.

Fixpoint insert (a : T) (t : tree T) : tree T :=
  if t is Node l x r then
    if a < x then Node (insert x r) a l
             else Node (insert a r) x l
  else Node leaf a leaf.

Fixpoint del_left (l : tree T) (x : T) (r : tree T) : T * tree T :=
  if l is Node ll xl rl then
    let: (y, l') := del_left ll xl rl in
    (y, Node r x l')
  else (x, r).

Equations? sift_down (l : tree T) (a : T) (r : tree T) : tree T
  by wf (size_tree l + size_tree r) lt :=
(* Braun property guarantees r = Leaf *)
sift_down Leaf a _ => Node leaf a leaf;
(* Braun property guarantees l1 = r1 = Leaf *)
sift_down (Node _ x _) a Leaf =>
  if a <= x then Node (Node leaf x leaf) a leaf
            else Node (Node leaf a leaf) x leaf;
sift_down (Node l1 x1 r1) a (Node l2 x2 r2) =>
  let t1 := Node l1 x1 r1 in
  let t2 := Node l2 x2 r2 in
  if (a <= x1) && (a <= x2)
    then Node t1 a t2
    else if x1 <= x2
           then Node (sift_down l1 a r1) x1 t2
           else Node t1 x2 (sift_down l2 a r2).
Proof.
all: apply: ssrnat.ltP.
- by apply: ltn_addr; rewrite addn1.
by apply: ltn_addl; rewrite addn1.
Qed.

Definition del_min (t : tree T) : tree T :=
  if t is Node l x r then
    if l is Node ll al rl then
      let: (y, l') := del_left ll al rl in
      sift_down r y l'
    else leaf
  else leaf.

End Implementation.

Section Correctness.
Context {disp : Order.disp_t} {T : orderType disp}.

Lemma size_insert (x : T) t : size_tree (insert x t) = size_tree t + 1.
Proof.
elim: t x=>//= l _ a r IHr x; case: ifP=>/= _;
by rewrite {}IHr -addnA addnCA !addnA.
Qed.

Lemma perm_insert (x : T) t : perm_eq (mset_tree (insert x t)) (x :: mset_tree t).
Proof.
elim: t x=>//= l _ a r IHr x; case: ifP=>/= _.
- by rewrite perm_cons perm_sym -cat1s catA perm_catAC perm_cat2r /= perm_sym.
by rewrite perm_sym -cat1s -(cat1s a) perm_catCA perm_cons catA
  perm_catAC perm_cat2r /= perm_sym.
Qed.

Lemma braun_insert (x : T) t :
  braun t -> braun (insert x t).
Proof.
elim: t x=>//= l _ a r IHr x /and3P [E Hl /IHr Hr] {IHr}.
by case: ifP=>/= _; rewrite size_insert Hl Hr /= andbT;
case/orP: E=>/eqP->; rewrite eq_refl //= orbT.
Qed.

Lemma heap_insert (x : T) t : heap t -> heap (insert x t).
Proof.
elim: t x=>//= l _ a r IHr x /and3P [].
rewrite all_cat; case/andP=>Hal Har Hl /IHr Hr {IHr}.
case: ifP=>/=; rewrite Hl Hr /= andbT all_cat.
- move=>Hxa; rewrite (perm_all _ (perm_pre_in _))
    (perm_all _ (perm_insert a r)) /= (ltW Hxa) /=.
  apply/andP; split.
  - rewrite -(perm_all _ (perm_pre_in _)).
    by apply/sub_all/Har=>z Hz; apply/ltW/lt_le_trans/Hz.
  by apply/sub_all/Hal=>z Hz; apply/ltW/lt_le_trans/Hz.
move/negbT; rewrite -leNgt=>Hax.
by rewrite (perm_all _ (perm_pre_in _)) (perm_all _ (perm_insert x r)) /=
  Hax -(perm_all _ (perm_pre_in _)) Har Hal.
Qed.

Lemma del_left_mset_plus (l : tree T) a r x t :
  del_left l a r = (x,t) ->
  perm_eq (a :: mset_tree l ++ mset_tree r) (x :: mset_tree t).
Proof.
elim: l a r t=>/= [|ll IHl al rl _] a r t; first by case=>->->.
case Hdl: (del_left ll al rl)=>[y l'][Hx {t}<-] /=; rewrite {y}Hx in Hdl.
rewrite perm_sym -cat1s -cat_cons perm_catCA /= perm_cons perm_sym
  -cat_cons perm_catC perm_cat2l.
by apply: IHl.
Qed.

Lemma del_left_mset (l : tree T) a r x t :
  del_left l a r = (x,t) ->
  let mt := a :: mset_tree l ++ mset_tree r in
  x \in mt /\ perm_eq (mset_tree t) (rem x mt).
Proof.
move/del_left_mset_plus=>/=.
rewrite perm_sym=>/[dup] H /perm_mem=>/(_ x).
rewrite inE eq_refl => /= Hi; symmetry in Hi; rewrite Hi; split=>//.
rewrite -(perm_cons x); move/permPl: H=>->; case: ifP; first by move/eqP=>->.
by move=>Hax; move/perm_to_rem/permPl: Hi=>-> /=; rewrite {}Hax.
Qed.

(* TODO move to prelude *)
Lemma all_subset {A: eqType} a (s1 s2 : seq A) :
  {subset s1 <= s2} -> all a s2 -> all a s1.
Proof. by move=>Hs /allP Ha2; apply/allP=>x Hx; apply/Ha2/Hs. Qed.

Lemma del_left_heap (l : tree T) a r x t :
  del_left l a r = (x,t) ->
  all (>= a) (inorder l ++ inorder r) -> heap l -> heap r ->
  heap t.
Proof.
elim: l a r t=>/= [|ll IHl al rl _] a r t; first by case=>_->.
case Hdl: (del_left ll al rl)=>[y l'][Hx {t}<-] /=; rewrite {y}Hx in Hdl.
move=>H /and3P [Ha Hll Hrl] Hr; rewrite Hr /=.
apply/andP; split; last by apply: (IHl _ _ _ Hdl).
move: H; rewrite !all_cat /= -!andbA; case/and4P=>Hal Haa Harl -> /=.
case/del_left_mset: Hdl=>Hi Hp.
rewrite (perm_all _ (perm_pre_in _)) ((perm_all _ Hp)).
apply: all_subset; first by exact: mem_rem.
by rewrite /= all_cat Haa -!(perm_all _ (perm_pre_in _)) Hal Harl.
Qed.

Lemma del_left_size (l : tree T) a r x t :
  del_left l a r = (x,t) ->
  size_tree l + size_tree r = size_tree t.
Proof.
elim: l a r t=>/= [|ll IHl al rl _] a r t; first by case=>_->.
case Hdl: (del_left ll al rl)=>[y l'][Hx {t}<-] /=; rewrite {y}Hx in Hdl.
by rewrite (IHl _ _ _ Hdl) addnC addnA.
Qed.

Lemma del_left_braun (l : tree T) a r x t :
  del_left l a r = (x,t) ->
  (size_tree l == size_tree r) || (size_tree l == size_tree r + 1) ->
  braun l -> braun r ->
  braun t.
Proof.
elim: l a r t=>/= [|ll IHl al rl _] a r t; first by case=>_->.
case Hdl: (del_left ll al rl)=>[y l'][Hx {t}<-] /=; rewrite {y}Hx in Hdl.
move=>E1 /and3P [E2 Hll Hrl] -> /=.
rewrite -(del_left_size Hdl); apply/andP; split; last by apply: (IHl _ _ _ Hdl).
case/orP: E1; rewrite eq_sym; first by move=>->; rewrite orbT.
by rewrite eqn_add2r=>->.
Qed.

Lemma size_sift_down (l : tree T) a r :
  (size_tree l == size_tree r) || (size_tree l == size_tree r + 1) ->
  braun l -> braun r ->
  size_tree (sift_down l a r) = size_tree l + size_tree r + 1.
Proof.
funelim (sift_down l a r); simp sift_down=>/=.
- by case/orP; [move/eqP=><- | rewrite addn1].
- case/orP; first by rewrite addn1.
  rewrite eqn_add2r addn_eq0; case/andP=>/eqP->/eqP->/= _ _.
  by case: ifP.
move=>_; case/and3P=>E1 Hl1 Hr1; case/and3P=>E2 Hl2 Hr2.
by case: ifP=>// _; case: ifP=>/= _; [rewrite H | rewrite H0].
Qed.

Lemma braun_sift_down (l : tree T) a r :
  (size_tree l == size_tree r) || (size_tree l == size_tree r + 1) ->
  braun l -> braun r ->
  braun (sift_down l a r).
Proof.
funelim (sift_down l a r)=> //=; simp sift_down=>/=.
- by move=>_ _ _; case: ifP.
rewrite !eqn_add2r=>E; case/and3P=>E1 Hl1 Hr1; case/and3P=>E2 Hl2 Hr2.
case: ifP=>/=.
- by rewrite !eqn_add2r E E1 Hl1 Hr1 E2 Hl2 Hr2.
move=>_; case: ifP=>_ /=; rewrite size_sift_down // !eqn_add2r {}E /=.
- by rewrite H // E2 Hl2 Hr2.
by rewrite E1 Hl1 Hr1 H0.
Qed.

Lemma mset_sift_down (l : tree T) a r :
  (size_tree l == size_tree r) || (size_tree l == size_tree r + 1) ->
  braun l -> braun r ->
  perm_eq (mset_tree (sift_down l a r)) (a :: mset_tree l ++ mset_tree r).
Proof.
funelim (sift_down l a r); simp sift_down=>/=.
- case/orP; last by rewrite addn1.
  by rewrite eq_sym=>/eqP/size0leaf->.
- case/orP; first by rewrite addn1.
  rewrite eqn_add2r addn_eq0; case/andP=>/eqP/size0leaf->/eqP/size0leaf->/= _ _.
  by case: ifP=>//= _; rewrite -cat1s perm_catC.
move=>_; case/and3P=>E1 Hl1 Hr1; case/and3P=>E2 Hl2 Hr2.
case: ifP=>// _; case: ifP=>/= _.
- rewrite -!cat_cons perm_cat2r /= perm_sym -cat1s -(cat1s x1)
    perm_catCA perm_cons /= perm_sym.
  by apply: H.
rewrite -cat1s -cat_cons perm_catCA perm_sym -cat1s -cat_cons perm_catCA perm_cat2l
   -(cat1s x2) perm_catCA perm_cons /= perm_sym.
by apply: H0.
Qed.

Lemma heap_sift_down (l : tree T) a r :
  (size_tree l == size_tree r) || (size_tree l == size_tree r + 1) ->
  braun l -> braun r ->
  heap l -> heap r ->
  heap (sift_down l a r).
Proof.
funelim (sift_down l a r)=> //=; simp sift_down=>/=.
- case/orP; first by rewrite addn1.
  rewrite eqn_add2r addn_eq0; case/andP=>/eqP/size0leaf->/eqP/size0leaf->/= _ _ _ _.
  by case: ifP=>/=; rewrite !andbT // =>/negbT; rewrite -ltNge=>/ltW.
rewrite !all_cat -!andbA; rewrite !eqn_add2r=>E.
case/and3P=>E1 Hl1 Hr1; case/and3P=>E2 Hl2 Hr2.
case/and4P=>Hal1 Har1 Hhl1 Hhr1; case/and4P=>Hal2 Har2 Hhl2 Hhr2.
case: ifP=>/=.
- case/andP=>Hax1 Hax2; rewrite !all_cat /= -!andbA Hax1 Hax2 Hal1 Har1
    Hhl1 Hhr1 Hal2 Har2 Hhl2 Hhr2 /= andbT.
  apply/and4P; split.
  - by apply/sub_all/Hal1=>z Hz; apply/le_trans/Hz.
  - by apply/sub_all/Har1=>z Hz; apply/le_trans/Hz.
  - by apply/sub_all/Hal2=>z Hz; apply/le_trans/Hz.
  by apply/sub_all/Har2=>z Hz; apply/le_trans/Hz.
move/negbT; rewrite negb_and -!ltNge=>Ha12.
case: ifP=>/=; rewrite !all_cat /= -!andbA.
- move=>Hx12; rewrite Hx12 Hal2 Har2 Hhl2 Hhr2 /= andbT.
  apply/and4P; split.
  - rewrite (perm_all _ (perm_pre_in _))
     (perm_all _ (mset_sift_down _ E1 Hl1 Hr1)) /= all_cat
     -!(perm_all _ (perm_pre_in _)) Hal1 Har1 /= andbT.
    case/orP: Ha12; first by move/ltW.
    by move=>Hx2; apply/ltW/le_lt_trans/Hx2.
  - by apply/sub_all/Hal2=>z Hz; apply/le_trans/Hz.
  - by apply/sub_all/Har2=>z Hz; apply/le_trans/Hz.
  by apply: H.
move/negbT; rewrite -ltNge=>Ha21.
rewrite (ltW Ha21) Hal1 Har1 Hhl1 Hhr1 /=.
apply/and4P; split.
- by apply/sub_all/Hal1=>z Hz; apply/ltW/lt_le_trans/Hz.
- by apply/sub_all/Har1=>z Hz; apply/ltW/lt_le_trans/Hz.
- rewrite (perm_all _ (perm_pre_in _))
   (perm_all _ (mset_sift_down _ E2 Hl2 Hr2)) /= all_cat
   -!(perm_all _ (perm_pre_in _)) Hal2 Har2 /= andbT.
  case/orP: Ha12; last by move/ltW.
  by move=>Hx1; apply/ltW/lt_trans/Hx1.
by apply: H0.
Qed.

Lemma braun_del_min (t : tree T) : braun t -> braun (del_min t).
Proof.
case: t=>//=; case=>//=ll al rl _ r; rewrite -!andbA eqn_add2r.
case/and5P=>E El Hll Hrl Hr; case Hdl: (del_left ll al rl)=>[y l'].
apply: braun_sift_down=>//.
- by rewrite -(del_left_size Hdl) eq_sym orbC eq_sym.
by apply: (del_left_braun Hdl).
Qed.

Lemma heap_del_min (t : tree T) :
  braun t -> heap t -> heap (del_min t).
Proof.
case: t=>//=; case=>//= ll al rl a r; rewrite !all_cat /= -!andbA eqn_add2r.
case/and5P=>E El Hbll Hbrl Hbr; case/and9P=>_ _ _ _ Halll Halrl Hhll Hhrl Hhr.
case Hdl: (del_left ll al rl)=>[y l'].
apply: heap_sift_down=>//.
- by rewrite -(del_left_size Hdl) eq_sym orbC eq_sym.
- by apply: (del_left_braun Hdl).
by apply: (del_left_heap Hdl)=>//; rewrite all_cat Halll Halrl.
Qed.

Lemma size_del_min (t : tree T) :
  braun t -> size_tree (del_min t) = (size_tree t).-1.
Proof.
case: t=>//=; case=>/=[|ll al rl] _ r.
- by case/andP; case/orP; [move/eqP=><- | rewrite addn1].
rewrite -!andbA eqn_add2r.
case/and5P=>E El Hll Hrl Hr; case Hdl: (del_left ll al rl)=>[y l'].
rewrite size_sift_down //; first last.
- by apply: (del_left_braun Hdl).
- by rewrite -(del_left_size Hdl) eq_sym orbC eq_sym.
by rewrite (del_left_size Hdl) [in RHS]addn1 /= -addnA addnC.
Qed.

Lemma mset_del_min x0 (t : tree T) :
  braun t -> is_node t ->
  perm_eq (mset_tree (del_min t)) (rem (get_min x0 t) (mset_tree t)).
Proof.
case: t=>//=; case=>/= [|ll al rl] a r; rewrite eq_refl.
- case/andP; case/orP; last by rewrite addn1.
  by rewrite eq_sym=>/eqP/size0leaf->.
rewrite -!andbA eqn_add2r; case/and5P=>E El Hll Hrl Hr _.
case Hdl: (del_left ll al rl)=>[y l'].
have H1: (size_tree r == size_tree l') || (size_tree r == size_tree l' + 1).
- by rewrite -(del_left_size Hdl) eq_sym orbC eq_sym.
have H2: braun l' by apply: (del_left_braun Hdl).
move/permPl: (@mset_sift_down r y l' H1 Hr H2)=>->.
rewrite -cat1s catA perm_catAC -cat_cons perm_cat2r /= perm_sym.
by apply: del_left_mset_plus.
Qed.

Definition invar (t : tree T) : bool := braun t && heap t.

Corollary invar_leaf : invar leaf.
Proof. by []. Qed.

Corollary invar_insert x t :
  invar t -> invar (insert x t).
Proof. by rewrite /invar; case/andP=>/(braun_insert x)-> /(heap_insert x)->. Qed.

Corollary perm_insert' x t :
  invar t ->
  perm_eq (mset_tree (insert x t)) (x :: mset_tree t).
Proof. by move=>_; exact: perm_insert. Qed.

Corollary invar_del_min t :
  invar t -> ~~ nilp (mset_tree t) -> invar (del_min t).
Proof.
rewrite /invar; case/andP=>Hb Hh _; apply/andP; split.
- by apply: braun_del_min.
by apply: heap_del_min.
Qed.

Corollary perm_del_min x0 t :
  invar t ->
  ~~ nilp (mset_tree t) ->
  perm_eq (mset_tree (del_min t)) (rem (get_min x0 t) (mset_tree t)).
Proof.
rewrite /invar; case/andP=>Hb _ Hn.
by apply: mset_del_min=>//; case: {Hb}t Hn.
Qed.

Corollary mins_getmin' t x0 :
  invar t ->
  get_min x0 t = mins x0 (mset_tree t).
Proof. by rewrite /invar; case/andP=>_; exact: mins_getmin_heap. Qed.

Definition BraunPQ :=
  @APQ.make _ _ (tree T)
    leaf insert del_min get_min
    mset_tree invar
    invar_leaf mset_empty
    invar_insert perm_insert'
    invar_del_min perm_del_min
    mins_getmin'.

End Correctness.
