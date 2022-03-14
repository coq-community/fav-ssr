From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat ssrint ssralg ssrnum order seq path.
From favssr Require Import prelude bintree bst adt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Intro.
Context {A : Type}.

Definition tree_ht A := tree (A * nat).

Definition ht (t : tree_ht A) : nat :=
  if t is Node _ (_, n) _ then n else 0.

Definition node (l : tree_ht A) (a : A) (r : tree_ht A) : tree_ht A :=
  Node l (a, maxn (ht l) (ht r) + 1) r.

Fixpoint avl (t : tree_ht A) : bool :=
  if t is Node l (_, n) r
    then [&& `|height l - height r| <= 1%N, n == maxn (height l) (height r) + 1, avl l & avl r]
    else true.

Lemma avl_ind (P : tree_ht A -> Prop) :
  P (Leaf (A*nat)) ->
  (forall l a r,
   `|height l - height r| <= 1%N ->
   avl l -> avl r ->
   P l -> P r ->
   P (Node l (a,maxn (height l) (height r) + 1) r)) ->
  forall t, avl t -> P t.
Proof.
move=>Pl Pn; elim=>//= l IHl [a n] r IHr /and4P [D /eqP -> Hcl Hcr].
by apply: Pn=>//; [apply: IHl| apply: IHr].
Qed.

Lemma ht_height (t : tree_ht A) : avl t -> ht t = height t.
Proof. by case: t=>//=l [a x] r /and4P [_ /eqP E _ _]. Qed.

(* TODO: move to bintree? *)
Inductive non_empty_if (b : bool) (t : tree_ht A) : Type :=
| Nd l a n r : t = Node l (a,n) r -> b -> non_empty_if b t
| Def : ~~ b -> non_empty_if b t.

Lemma ne_hplus2 (t1 t2 : tree_ht A) : non_empty_if (ht t1 == ht t2 + 2) t1.
Proof.
case: eqP; last by move=>_; apply: Def.
case: t1=>/=; first by rewrite addn2.
by move=>l [a n] r _; apply: Nd.
Qed.

Lemma ne_hgt (t1 t2 : tree_ht A) : non_empty_if (ht t2 < ht t1)%N t1.
Proof.
case: ltnP; last by move=>_; apply: Def.
by case: t1=>//= l [a n] r _; apply: Nd.
Qed.

End Intro.

Arguments avl_ind [A P].

(* TODO: move to prelude? *)
(* distance helpers *)

Lemma dist_leq (a b c : nat) :
  (`|a - b| <= c -> (a <= b <= a + c) || (b <= a <= b + c))%N.
Proof.
case/orP: (leq_total a b)=>/[dup] Hab =>[/distnEr|/distnEl] ->;
rewrite Hab leq_subLR=>->//=.
by rewrite orbT.
Qed.

Corollary dist_leqL (a b c : nat) :
  (`|a - b| <= c -> a <= b -> b <= a + c)%N.
Proof.
move/dist_leq; rewrite (leqNgt b a) ltn_neqAle.
move/[swap]=>->; rewrite andbT /=; case/orP=>//.
by case/andP=>/negbNE/eqP->.
Qed.

Corollary dist_leqR (a b c : nat) :
  (`|a - b| <= c -> b <= a -> a <= b + c)%N.
Proof.
move/dist_leq; rewrite (leqNgt a b) ltn_neqAle.
move/[swap]=>->; rewrite andbT /=; case/orP=>//.
by case/andP=>/negbNE/eqP->.
Qed.

Lemma distn_Dl n m : `|(n + m) - n| = m.
Proof.
have/distnEl->: (n <= n + m)%N by apply: leq_addr.
by rewrite -addnBAC // subnn.
Qed.

Corollary distn_Dr (n m : nat) : `|n - (n + m)| = m.
Proof. by rewrite distnC; apply: distn_Dl. Qed.

Lemma leq_dist n m p :
  (n <= m + p -> m <= n + p -> `|n - m| <= p)%N.
Proof.
move=>Hn Hm.
by case/orP: (leq_total n m)=>[/distnEr|/distnEl]->; rewrite leq_subLR.
Qed.

Section LogarithmicHeight.
Context {A : Type}.

Equations? fib (n: nat) : nat by wf n lt :=
fib 0 => 0;
fib 1 => 1;
fib (n.+2) => fib (n + 1) + fib n.
Proof. by apply: ssrnat.ltP; rewrite addn1. Qed.

Lemma fib_monotone : {homo fib : x y / (x <= y)%N}.
Proof.
apply: (homo_leq leqnn leq_trans)=>n.
funelim (fib n); simp fib=>//.
by apply: leq_add.
Qed.

Lemma avl_fib (t : tree_ht A) : avl t -> (fib (height t + 2) <= size1_tree t)%N.
Proof.
elim/avl_ind=>{t}//=l _ r H Hal Har Hl Hr.
case: (leqP (height l) (height r))=>Hlr; rewrite addn2; simp fib.
- rewrite addnC; apply: leq_add; last by rewrite -addnA.
  apply/leq_trans/Hl/fib_monotone; rewrite (_ : 2 = 1 + 1) // addnA leq_add2r.
  by apply: dist_leqL.
apply: leq_add; first by rewrite -addnA.
apply/leq_trans/Hr/fib_monotone; rewrite (_ : 2 = 1 + 1) // addnA leq_add2r.
by apply: dist_leqR=>//; apply: ltnW.
Qed.

Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.

Variable C : numClosedFieldType.
Definition phi : C := (1 + sqrtC 5%:R) / 2%:R.

Lemma phi_sq : phi ^+ 2 = phi + 1.
Proof.
rewrite /phi expr_div_n sqrrD expr1n sqrtCK mul1r addrAC expr2.
rewrite -(natrD _ 1) (_ : (1+5=(2+1)*2)%N) // natrM -(mulr_natr (sqrtC 5%:R)).
rewrite -mulrDl -mulf_div divff; last by rewrite pnatr_eq0.
rewrite mulr1 natrD -addrA [in LHS]mulrDl divff; last by rewrite pnatr_eq0.
by rewrite addrC.
Qed.

Lemma fib_bound n : phi ^+ n <= (fib (n + 2)) %:R.
Proof.
funelim (fib n); simp fib=>//.
- rewrite add0n; simp fib=>//; rewrite addn0 expr1 addn1 /phi.
  rewrite -(@ler_pmul2r _ 2%:R) // mulfVK; last by rewrite pnatr_eq0.
  rewrite -natrM (_ : (2*2 = 1+3)%N) // natrD mulr1n ler_add2l.
  rewrite -(@ler_pexpn2r _ 2) //; first last.
  - by rewrite nnegrE.
  - by rewrite nnegrE sqrtC_ge0; apply: ler0n.
  by rewrite sqrtCK expr2 -natrM ler_nat.
rewrite -addn2 (addn2 (n + 2)); simp fib.
rewrite exprD phi_sq mulrDr mulr1 natrD.
by apply: ler_add=>//; move: H; rewrite exprD expr1 -!addnA.
Qed.

Corollary height_bound (t : tree_ht A) : avl t -> phi ^+ (height t) <= (size1_tree t)%:R.
Proof.
move/avl_fib=>H; apply: le_trans; first by apply: fib_bound.
by rewrite ler_nat.
Qed.

(* ssrnum doesn't have general logarithms *)
(* they exist in mathcomp-analysis but it doesn't look worth it *)

(* Corollary height_bound_ln t : avl t -> height t <= (1 / ln phi) * ln (size_tree1 t). *)

End LogarithmicHeight.

Section SetImplementation.
Context {disp : unit} {T : orderType disp}.

(* rebalancing *)

Definition balL {A} (ab : tree_ht A) (u : A) (c : tree_ht A) : tree_ht A :=
  match ne_hplus2 ab c with
  | Nd a v _ b _ _ =>
      match ne_hgt b a with
      | Nd b1 w _ b2 _ _ => node (node a v b1) w (node b2 u c)
      | Def _            => node a v (node b u c)
      end
  | Def _ => node ab u c
  end.

Definition balR {A} (a : tree_ht A) (u : A) (bc : tree_ht A) : tree_ht A :=
  match ne_hplus2 bc a with
  | Nd b v _ c _ _ =>
      match ne_hgt b c with
      | Nd b1 w _ b2 _ _ => node (node a u b1) w (node b2 v c)
      | Def _            => node (node a u b) v c
      end
  | Def _ => node a u bc
  end.

(* h bal = h c + 3 only when h a = h b = h c + 1 *)
Lemma height_balL {A} (l : tree_ht A) a r :
  avl l -> avl r -> height l = height r + 2 ->
  (height (balL l a r) == height r + 2) || (height (balL l a r) == height r + 3).
Proof.
move=>Hl Hr E; rewrite /balL.
case (ne_hplus2 l r)=>[al vl xl bl|] /=; last by rewrite !ht_height // E eq_refl.
move=>El _; move/eqP: E; rewrite {l}El /= in Hl *;
rewrite {1}(_ : 2 = 1+1) // {1}addnA eqn_add2r => /eqP E.
case/and4P: Hl=>Habl _ Hal Hbl.
case (ne_hgt bl al)=>[bl1 wl nl bl2|] /=; rewrite !ht_height //; last first.
- rewrite -leqNgt=>/[dup] Hbal /maxn_idPr.
  rewrite maxnC => Em; rewrite {}Em in E; rewrite E -addn_maxl maxnCA maxnn.
  move: (dist_leqR Habl Hbal)=>/[dup] {}Habl; rewrite E leq_add2r=>/maxn_idPl->.
  rewrite leq_eqVlt {2}addn1 ltnS E in Habl.
  case/orP: Habl; first by rewrite eqn_add2r =>/eqP->; rewrite -addnA eq_refl.
  move=>Habl; have /eqP->: height bl == height al by rewrite eqn_leq Hbal E.
  by rewrite E -2!addnA eq_refl orbT.
move/[swap]/[dup] => Habl' /ltnW {Hal Hbl} /(dist_leqL Habl) {Habl}.
rewrite leq_eqVlt {2}addn1 ltnS leqNgt {}Habl' orbF =>Ehbl Ebl.
rewrite {bl}Ebl /= in Ehbl E *; move: Ehbl.
rewrite eqn_add2r=>/eqP Ehal; rewrite -{}Ehal in E *; rewrite -addn_maxl.
set h1 := height bl1 in E *; set h2 := height bl2 in E *.
have {E}<-: maxn h1 h2 = height r.
- by move: E; rewrite maxn_addr !addn1 =>/succn_inj.
by rewrite (maxnAC h1 h2 h1) maxnn (maxnCA h2 h1 h2) !maxnn -addnA eq_refl.
Qed.

Lemma height_balR {A} (l : tree_ht A) a r :
  avl l -> avl r -> height r = height l + 2 ->
  (height (balR l a r) == height l + 2) || (height (balR l a r) == height l + 3).
Proof.
move=>Hl Hr E; rewrite /balR.
case (ne_hplus2 r l)=>[br vr xr cr|] /=; last by rewrite !ht_height // E eq_refl.
move=>Er; move/eqP: E; rewrite {r}Er /= in Hr *;
rewrite {1}(_ : 2 = 1+1) // {1}addnA eqn_add2r => /eqP E _.
case/and4P: Hr=>Hbcr _ Hbr Hcr.
case (ne_hgt br cr)=>[br1 wr nr br2|] /=; rewrite !ht_height //; last first.
- rewrite -leqNgt=>/[dup] Hcbr /maxn_idPr Em; rewrite {}Em in E.
  rewrite E -addn_maxl maxnAC maxnn.
  move: (dist_leqL Hbcr Hcbr)=>/[dup] {Hbcr}Hcbr'; rewrite E leq_add2r=>/maxn_idPr->.
  rewrite leq_eqVlt {2}addn1 ltnS E in Hcbr'.
  case/orP: Hcbr'; first by rewrite eqn_add2r =>/eqP->; rewrite -addnA eq_refl.
  move=>Hlbr; have /eqP->: height br == height cr by rewrite eqn_leq Hcbr E.
  by rewrite E -2!addnA eq_refl orbT.
move/[swap]/[dup] => Hcbr' /ltnW {Hbr Hcr} /(dist_leqR Hbcr) {Hbcr}.
rewrite leq_eqVlt {2}addn1 ltnS leqNgt {}Hcbr' orbF=>Ehbr Ebr.
rewrite {br}Ebr /= in Ehbr E *; move: Ehbr.
rewrite eqn_add2r=>/eqP Ehcr; rewrite -{}Ehcr in E *; rewrite -addn_maxl.
set h1 := height br1 in E *; set h2 := height br2 in E *.
have {E}<-: maxn h1 h2 = height l.
- by move: E; rewrite maxn_addl !addn1 =>/succn_inj.
by rewrite (maxnAC h1 h2 h1) maxnn (maxnCA h2 h1 h2) !maxnn -addnA eq_refl.
Qed.

Lemma height_balL2 {A} (l : tree_ht A) a r :
  avl l -> avl r -> height l != height r + 2 ->
  height (balL l a r) = maxn (height l) (height r) + 1.
Proof.
move=>Hl Hr E; rewrite /balL.
case (ne_hplus2 l r)=>[al vl xl bl _|_] //=.
by rewrite !ht_height //; move/negbTE: E=>->.
Qed.

Lemma height_balR2 {A} (l : tree_ht A) a r :
  avl l -> avl r -> height r != height l + 2 ->
  height (balR l a r) = maxn (height l) (height r) + 1.
Proof.
move=>Hl Hr E; rewrite /balR.
case (ne_hplus2 r l)=>[al vl xl bl _|_] //=.
by rewrite !ht_height //; move/negbTE: E=>->.
Qed.

Lemma avl_balL {A} (l : tree_ht A) a r :
  avl l -> avl r -> (height r - 1 <= height l <= height r + 2)%N ->
  avl (balL l a r).
Proof.
move=>Hl Hr I; rewrite /balL.
case (ne_hplus2 l r)=>[al vl xl bl|] /=; last first.
- rewrite Hl Hr !ht_height // eq_refl /= andbT => N.
  case/andP: I; rewrite leq_subLR addnC=>Hrl.
  rewrite leq_eqVlt; move/negbTE: N=>->/=; rewrite (_ : 2= 1+1) // addnA addn1 ltnS.
  rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite addn1 distSn.
  by rewrite addn1 ltnS => /distnEr ->; rewrite leEnat leq_subLR.
rewrite !ht_height // => {I}El; rewrite {l}El /= in Hl *.
rewrite (_ : 2= 1+1) // addnA eqn_add2r => /eqP E.
case/and4P: Hl=>Habl _ Hal Hbl.
case (ne_hgt bl al)=>[bl1 wl nl bl2|] /=; last first.
- rewrite !ht_height // !eq_refl Hr Hal Hbl /= andbT.
  rewrite -leqNgt =>/[dup] Hbal /maxn_idPr; rewrite maxnC =>Em; rewrite {}Em in E.
  move: (dist_leqR Habl Hbal); rewrite E leq_add2r=>/[dup] {}Habl /maxn_idPl->.
  by rewrite distnDr distnC andbb (distnEl Habl) leEnat leq_subLR -E.
rewrite ht_height // ht_height // => /[swap]/[dup] Habl' /ltnW /(dist_leqL Habl) {Habl}.
rewrite leq_eqVlt {2}addn1 ltnS leqNgt {}Habl' orbF =>Ehbl Ebl.
rewrite {bl}Ebl /= in Hbl Ehbl E *; case/and4P: Hbl=>D12 _ Hbl1 Hbl2.
rewrite !ht_height // !eq_refl {}Hal {}Hbl1 {}Hbl2 {}Hr -!andbA /= andbT distnDr.
move: Ehbl; rewrite eqn_add2r=>/eqP Ehal; rewrite -{}Ehal in E *.
set h1 := height bl1 in D12 E *; set h2 := height bl2 in D12 E *.
have {E}<-: maxn h1 h2 = height r.
- by move: E; rewrite maxn_addr !addn1 =>/succn_inj.
rewrite (maxnAC h1 h2 h1) maxnn (maxnCA h2 h1 h2) maxnn distnn /=.
by rewrite /maxn; case: ifP=>_; rewrite distnn distnC ?andbT.
Qed.

Lemma avl_balR {A} (l : tree_ht A) a r :
  avl l -> avl r -> (height l - 1 <= height r <= height l + 2)%N ->
  avl (balR l a r).
Proof.
move=>Hl Hr I; rewrite /balR.
case (ne_hplus2 r l)=>[br vr xr cr|] /=; last first.
- rewrite Hl Hr !ht_height // eq_refl /= andbT => N.
  case/andP: I; rewrite leq_subLR addnC=>Hrl.
  rewrite leq_eqVlt; move/negbTE: N=>->/=; rewrite (_ : 2= 1+1) // addnA addn1 ltnS.
  rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite addn1 distnS.
  by rewrite addn1 ltnS => /distnEl ->; rewrite leEnat leq_subLR.
rewrite !ht_height // => {I}Er; rewrite {r}Er /= in Hr *.
rewrite (_ : 2= 1+1) // addnA eqn_add2r => /eqP E.
case/and4P: Hr=>Hbcr _ Hbr Hcr.
case (ne_hgt br cr)=>[br1 wr nr br2|] /=; last first.
- rewrite !ht_height // !eq_refl Hl Hbr Hcr /= !andbT.
  rewrite -leqNgt =>/[dup] Hcbr /maxn_idPr Em; rewrite {}Em in E.
  move: (dist_leqL Hbcr Hcbr); rewrite E leq_add2r=>/[dup] {}Hbcr /maxn_idPr->.
  by rewrite distnDr distnC andbb (distnEr Hbcr) leEnat leq_subLR -E.
rewrite ht_height // ht_height // => /[swap]/[dup] Hcbr /ltnW /(dist_leqR Hbcr) {Hbcr}.
rewrite leq_eqVlt {2}addn1 ltnS leqNgt {}Hcbr orbF =>Ehbr Ebr.
rewrite {br}Ebr /= in Hbr Ehbr E *; case/and4P: Hbr=>D12 _ Hbr1 Hbr2.
rewrite !ht_height // !eq_refl {}Hl {}Hbr1 {}Hbr2 {}Hcr -!andbA /= andbT distnDr.
move: Ehbr; rewrite eqn_add2r=>/eqP Ehcr; rewrite -{}Ehcr in E *.
set h1 := height br1 in D12 E *; set h2 := height br2 in D12 E *.
have {E}<-: maxn h1 h2 = height l.
- by move: E; rewrite maxn_addl !addn1 =>/succn_inj.
rewrite (maxnAC h1 h2 h1) maxnn (maxnCA h2 h1 h2) maxnn distnn /=.
by rewrite /maxn; case: ifP=>_; rewrite distnn distnC ?andbT.
Qed.

(* insertion *)

Fixpoint insert (x : T) (t : tree_ht T) : tree_ht T :=
  if t is Node l (a,n) r then
    match cmp x a with
    | LT => balL (insert x l) a r
    | EQ => Node l (a,n) r
    | GT => balR l a (insert x r)
    end
    else Node empty_a (x,1%N) empty_a.

Theorem avl_insert x t :
  avl t ->
  avl (insert x t) && ((height (insert x t) == height t) || (height (insert x t) == height t + 1)).
Proof.
elim/avl_ind=>//=l a r H Hal Har /andP [Hail IHl] /andP [Hair IHr].
case: (cmp x a)=>/=.
- apply/andP; split.
  - apply: avl_balL=>//; rewrite leq_subLR addnC.
    case/dist_leq/orP: H=>/andP [H1 H2]; case/orP: IHl=>/eqP->.
    - by rewrite H2 /=; apply/(leq_trans H1)/leq_addr.
    - apply/andP; split; first by apply/(leq_trans H2)/leq_addr.
      by rewrite (_ : 2= 1+1) // addnA leq_add2r; apply/(leq_trans H1)/leq_addr.
    - apply/andP; split; first by apply/(leq_trans H1)/leq_addr.
      by rewrite (_ : 2= 1+1) // addnA; apply/(leq_trans H2)/leq_addr.
    apply/andP; split; first by rewrite -addnA; apply/(leq_trans H1)/leq_addr.
    by rewrite (_ : 2= 1+1) // addnA leq_add2r.
  case/boolP: (height (insert x l) == height r + 2)=>Hil; last first.
  - move: (height_balL2 a Hail Har Hil)=>->.
    case/orP: IHl=>/eqP->; first by rewrite eq_refl.
    case/dist_leq/orP: H=>/andP [H1 H2].
    - move/maxn_idPl: (H2)=>->; move/maxn_idPr: (H1)=>->; rewrite !eqn_add2r.
      move: H2; rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite eq_refl.
      rewrite addn1 ltnS => Hrl; suff: height l == height r by move=>->; rewrite orbT.
      by rewrite eqn_leq H1 Hrl.
    have/maxn_idPl->: (height r <= height l + 1)%N by apply/(leq_trans H1)/leq_addr.
    by move/maxn_idPl: H1=>->; rewrite eq_refl orbT.
  rewrite (eqP Hil) in IHl; case/orP: IHl.
  - by move=>/eqP Ehl; move: H; rewrite -{}Ehl distn_Dl.
  rewrite (_: 2= 1+1) // addnA eqn_add2r =>/eqP<-; rewrite maxn_addl.
  by case/orP: (height_balL a Hail Har (eqP Hil))=>/eqP->; rewrite -!addnA eq_refl ?orbT.
- by rewrite H Hal Har eq_refl.
apply/andP; split.
- apply: avl_balR=>//; rewrite leq_subLR addnC.
  case/dist_leq/orP: H=>/andP [H1 H2]; case/orP: IHr=>/eqP->.
  - apply/andP; split; first by apply/(leq_trans H1)/leq_addr.
    by rewrite (_ : 2= 1+1) // addnA; apply/(leq_trans H2)/leq_addr.
  - apply/andP; split; first by rewrite -addnA; apply/(leq_trans H1)/leq_addr.
    by rewrite (_ : 2= 1+1) // addnA leq_add2r.
  - by rewrite H2 /=; apply/(leq_trans H1)/leq_addr.
  apply/andP; split; first by apply/(leq_trans H2)/leq_addr.
  by rewrite (_ : 2= 1+1) // addnA leq_add2r; apply/(leq_trans H1)/leq_addr.
case/boolP: (height (insert x r) == height l + 2)=>Hir; last first.
- move: (height_balR2 a Hal Hair Hir)=>->.
  case/orP: IHr=>/eqP->; first by rewrite eq_refl.
  case/dist_leq/orP: H=>/andP [H1 H2].
  - have/maxn_idPr->: (height l <= height r + 1)%N by apply/(leq_trans H1)/leq_addr.
    by move/maxn_idPr: H1=>->; rewrite eq_refl orbT.
  move/maxn_idPr: (H2)=>->; move/maxn_idPl: (H1)=>->; rewrite !eqn_add2r.
  move: H2; rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite eq_refl.
  rewrite addn1 ltnS => Hrl; suff: height r == height l by move=>->; rewrite orbT.
  by rewrite eqn_leq H1 Hrl.
rewrite (eqP Hir) in IHr; case/orP: IHr.
- by move=>/eqP Ehr; move: H; rewrite -{}Ehr distn_Dr.
rewrite (_: 2= 1+1) // addnA eqn_add2r =>/eqP<-; rewrite maxn_addr.
by case/orP: (height_balR a Hal Hair (eqP Hir))=>/eqP->; rewrite -!addnA eq_refl ?orbT.
Qed.

(* deletion by replacing *)

Fixpoint split_max (l : tree_ht T) (a : T) (r : tree_ht T) : (tree_ht T * T) :=
   if r is Node lr (ar, _) rr then
       let: (r', a') := split_max lr ar rr in
       (balL l a r', a')
     else (l, a).

Fixpoint delete (x : T) (t : tree_ht T) : tree_ht T :=
  if t is Node l (a, _) r then
    match cmp x a with
    | LT => balR (delete x l) a r
    | EQ => if l is Node ll (al, _) rl then
                let: (l', a') := split_max ll al rl in
                balR l' a' r
              else r
    | GT => balL l a (delete x r)
    end
  else empty_a.

Lemma avl_split_max l a r t x :
  split_max l a r = (t, x) ->
  `|height l - height r| <= 1%N -> avl l -> avl r ->
  avl t && ((height t == maxn (height l) (height r)) || (height t == maxn (height l) (height r) + 1)).
Proof.
elim: r l a t=>/=[|lr _ [ar nr] rr IHr] l a t; first by case=><- _; rewrite maxn0 eq_refl /= => _ ->.
case Hsm: (split_max lr ar rr)=>[r' a'][<- E]; rewrite {}E in Hsm.
move=>E Hl /and4P [Hr Er Hlr Hrr]; case/andP: (IHr _ _ _ Hsm Hr Hlr Hrr)=>Hr' E'.
apply/andP; split.
- apply: avl_balL=>//; rewrite leq_subLR.
  case/orP: E'=>/eqP E'; rewrite -{}E' in E; case/dist_leq/orP: E=>/andP [H1 H2].
  - rewrite leq_add2r in H2; apply/andP; split; first by apply: (leq_trans H2); apply: leq_addl.
    by rewrite (_: 2= 1+1) // addnA; apply: (leq_trans H1); apply: leq_addr.
  - rewrite -addnA in H2; rewrite H2 andbT.
    apply: leq_trans; first by apply: (leq_addr 1).
    by apply: (leq_trans H1); apply: leq_addl.
  - by rewrite addnC H2 /=; apply: (leq_trans H1); apply: leq_addr.
  apply/andP; split; first by apply: (leq_trans H1); apply: leq_addl.
  by rewrite (_: 2= 1+1) // addnA; apply: (leq_trans H2); apply: leq_addr.
case/boolP: (height l == height r' + 2)=>Hlr'; last first.
- move: (height_balL2 a Hl Hr' Hlr')=>->.
  case/orP: E'=>/eqP E'; last by rewrite -E' eq_refl orbT.
  rewrite -{}E' in E *.
  case/dist_leq/orP: E=>/andP [H1 H2].
  - rewrite leq_add2r in H2.
    move/maxn_idPr: (H1)=>->; move/maxn_idPl: (H2)=>->; rewrite !eqn_add2r.
    move: H1; rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite eq_refl orbT.
    rewrite addn1 ltnS => H1; suff: height l == height r' by move=>->.
    by rewrite eqn_leq H1 H2.
  move: H2; rewrite -addnA leq_eqVlt; move/negbTE: Hlr'=>-> /=; rewrite addnA addn1 ltnS => H2.
  have /eqP->: height l == height r' + 1 by rewrite eqn_leq H1 H2.
  by rewrite maxnn maxn_addl eq_refl orbT.
case/orP: E'=>/eqP<-; rewrite (eqP Hlr') addn_maxl;
case/orP: (height_balL a Hl Hr' (eqP Hlr'))=>/eqP->;
set n := height r'; apply/orP.
- by left; rewrite eq_sym; apply/eqP/maxn_idPl; rewrite (_: 2= 1+1) // addnA; apply: leq_addr.
- by right; rewrite eq_sym -addnA; apply/eqP/maxn_idPl; rewrite -addnA [X in (_ <= X)%N]addnA; apply: leq_addr.
- by left; rewrite eq_sym; apply/eqP/maxn_idPl; apply: leq_addr.
by right; rewrite eq_sym -addnA; apply/eqP/maxn_idPl; rewrite (addnC 2 1%N) addnA; apply: leq_addr.
Qed.

Theorem avl_delete x t :
  avl t ->
  avl (delete x t) && ((height t == height (delete x t)) || (height t == height (delete x t) + 1)).
Proof.
elim/avl_ind=>//=l a r H Hal Har /andP [Hail IHl] /andP [Hair IHr].
case: (cmp x a)=>/=.
- apply/andP; split.
  - apply: avl_balR=>//; rewrite leq_subLR addnC.
    case/dist_leq/orP: H=>/andP [H1 H2]; case/orP: IHl=>/eqP E'.
    - rewrite -E'; apply/andP; split; first by apply/(leq_trans H1)/leq_addr.
      by rewrite (_ : 2= 1+1) // addnA; apply/(leq_trans H2)/leq_addr.
    - apply/andP; split; last by rewrite (_ : 2= 1+1) // addnA -E'.
      by rewrite -(leq_add2r 1) -E' -addnA; apply/(leq_trans H1)/leq_addr.
    - by rewrite -E' H2 /=; apply/(leq_trans H1)/leq_addr.
    apply/andP; split; last by rewrite (_ : 2= 1+1) // addnA -E'; apply/(leq_trans H1)/leq_addr.
    by rewrite -(leq_add2r 1) -E'; apply/(leq_trans H2)/leq_addr.
  case/boolP: (height r == height (delete x l) + 2)=>Hil; last first.
  - move: (height_balR2 a Hail Har Hil)=>->.
    rewrite !addn_maxl; case/orP: IHl=>/eqP<-; first by rewrite eq_refl.
    rewrite -!addn_maxl.
    case/dist_leq/orP: H=>/andP [H1 H2].
    - have/maxn_idPr->: (height l <= height r + 1)%N by apply/(leq_trans H1)/leq_addr.
      by move/maxn_idPr: H1=>->; rewrite eq_refl.
    move/maxn_idPl: (H1)=>->; move/maxn_idPr: (H2)=>->; rewrite !eqn_add2r.
    move: H2; rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite eq_refl orbT.
    rewrite addn1 ltnS => Hlr; suff: height l == height r by move=>->.
    by rewrite eqn_leq H1 Hlr.
  case/orP: (height_balR a Hail Har (eqP Hil))=>/eqP->;
  case/orP: IHl=>/eqP ->; rewrite (eqP Hil);
  set d := height (delete x l); apply/orP.
  - by right; rewrite eqn_add2r maxn_addr eq_refl.
  - by right; rewrite eqn_add2r; apply/eqP/maxn_idPr; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
  - by left; rewrite (_ : 3= 2+1) // addnA eqn_add2r maxn_addr eq_refl.
  by left; rewrite (_ : 3= 2+1) // addnA eqn_add2r; apply/eqP/maxn_idPr; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
- case: {Hail IHl}l H Hal=>/=; first by rewrite Har max0n eq_refl orbT.
  move=>ll [al nl] rl H /and4P [Hl El Hall Harl].
  case Hsm: (split_max ll al rl)=>[l' a'].
  case/andP: (avl_split_max Hsm Hl Hall Harl)=>Hal' Hl'.
  apply/andP; split.
  - apply: avl_balR=>//; rewrite leq_subLR addnC.
    case/dist_leq/orP: H=>/andP [H1 H2]; case/orP: Hl'=>/eqP E';
    rewrite -{}E' in H1 H2.
    - rewrite -addnA in H2; rewrite H2 andbT.
      by rewrite -(leq_add2r 1); apply/(leq_trans H1); rewrite -addnA; apply: leq_addr.
    - apply/andP; split; first by apply/(leq_trans H1)/leq_addr.
      by rewrite (_ : 2= 1+1) // addnA; apply/(leq_trans H2)/leq_addr.
    - apply/andP; split; last by rewrite (_ : 2= 1+1) // addnA; apply/(leq_trans H1)/leq_addr.
      by rewrite -(leq_add2r 1); apply/(leq_trans H2)/leq_addr.
    by rewrite H2 /=; apply/(leq_trans H1)/leq_addr.
  case/boolP: (height r == height l' + 2)=>Hrl'; last first.
  - move: (height_balR2 a' Hal' Har Hrl')=>->.
    case/orP: Hl'=>/eqP E'; rewrite -{}E' in H *; last by rewrite eq_refl.
    case/dist_leq/orP: H=>/andP [H1 H2].
    - have/maxn_idPr->: (height l' <= height r)%N by apply/leq_trans/H1/leq_addr.
      by move/maxn_idPr: H1=>->; rewrite eq_refl.
    move/maxn_idPl: (H1)=>->.
    rewrite leq_add2r in H2; move/maxn_idPr: (H2)=>->; rewrite !eqn_add2r.
    move: H1; rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite eq_refl.
    rewrite addn1 ltnS => {}Hrl'; suff: height l' == height r by move=>->; rewrite orbT.
    by rewrite eqn_leq H2 Hrl'.
  case/orP: Hl'=>/eqP E'; rewrite -{}E' (eqP Hrl') in H *; last by move: H; rewrite distn_Dr.
  case/orP: (height_balR a' Hal' Har (eqP Hrl'))=>/eqP->; apply/orP.
  - right; rewrite eqn_add2r; apply/eqP/maxn_idPr; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
  by left; rewrite (_ : 3= 2+1) // addnA eqn_add2r; apply/eqP/maxn_idPr; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
apply/andP; split.
- apply: avl_balL=>//; rewrite leq_subLR addnC.
  case/dist_leq/orP: H=>/andP [H1 H2]; case/orP: IHr=>/eqP E'.
  - by rewrite -E' H2 /=; apply/(leq_trans H1)/leq_addr.
  - apply/andP; split; last by rewrite (_ : 2= 1+1) // addnA -E'; apply/(leq_trans H1)/leq_addr.
    by rewrite -(leq_add2r 1) -E'; apply/(leq_trans H2)/leq_addr.
  - rewrite -E'; apply/andP; split; first by apply/(leq_trans H1)/leq_addr.
    by rewrite (_ : 2= 1+1) // addnA; apply/(leq_trans H2)/leq_addr.
  apply/andP; split; last by rewrite (_ : 2= 1+1) // addnA -E' H2.
  by rewrite -(leq_add2r 1) -E' -addnA; apply/(leq_trans H1)/leq_addr.
case/boolP: (height l == height (delete x r) + 2)=>Hlr; last first.
- move: (height_balL2 a Hal Hair Hlr)=>->.
  rewrite !addn_maxl; case/orP: IHr=>/eqP<-; first by rewrite eq_refl.
  rewrite -!addn_maxl.
  case/dist_leq/orP: H=>/andP [H1 H2].
  - move/maxn_idPr: (H1)=>->; move/maxn_idPl: (H2)=>->; rewrite !eqn_add2r.
    move: H2; rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite eq_refl orbT.
    rewrite addn1 ltnS => {}Hlr; suff: height r == height l by move=>->.
    by rewrite eqn_leq H1 Hlr.
  have/maxn_idPl->: (height r <= height l + 1)%N by apply/(leq_trans H1)/leq_addr.
  by move/maxn_idPl: H1=>->; rewrite eq_refl.
case/orP: (height_balL a Hal Hair (eqP Hlr))=>/eqP->;
case/orP: IHr=>/eqP ->; rewrite (eqP Hlr);
set d := height (delete x r); apply/orP.
- by right; rewrite eqn_add2r maxn_addl eq_refl.
- by right; rewrite eqn_add2r; apply/eqP/maxn_idPl; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
- by left; rewrite (_ : 3= 2+1) // addnA eqn_add2r maxn_addl eq_refl.
by left; rewrite (_ : 3= 2+1) // addnA eqn_add2r; apply/eqP/maxn_idPl; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
Qed.

(* correctness via sorted lists *)

Lemma inorder_balL {A} (l : tree_ht A) a r :
  inorder_a (balL l a r) = inorder_a l ++ a :: inorder_a r.
Proof.
rewrite /balL.
case (ne_hplus2 l r)=>// al vl xl bl {l}->/= _.
case (ne_hgt bl al)=>[bl1 wl nl bl2|] /=; last by rewrite -catA.
by move=>{bl}->/= _; rewrite -!catA !cat_cons -catA.
Qed.

Lemma inorder_balR {A} (l : tree_ht A) a r :
  inorder_a (balR l a r) = inorder_a l ++ a :: inorder_a r.
Proof.
rewrite /balR.
case (ne_hplus2 r l)=>// br vr xr cr {r}->/= _.
case (ne_hgt br cr)=>[br1 wr nr br2|] /=; last by rewrite -catA.
by move=>{br}->/= _; rewrite -!catA !cat_cons.
Qed.

Lemma inorder_split_max l a r t x :
  split_max l a r = (t, x) ->
  inorder_a t ++ [:: x] = inorder_a l ++ a :: inorder_a r.
Proof.
elim: r l a t=>/= [|lr _ [ar nr] rr IHr] l a t; first by case=>->->.
case Hsm: (split_max lr ar rr)=>[r' a'][<- Hx] /=; rewrite {}Hx in Hsm.
by rewrite inorder_balL -(IHr _ _ _ Hsm) -catA.
Qed.

Definition bst_list (t : tree_ht T) : bool := sorted <%O (inorder_a t).

Theorem inorder_insert x t :
  bst_list t ->
  inorder_a (insert x t) = ins_list x (inorder_a t).
Proof.
rewrite /bst_list; elim: t=>//=l IHl [a n] r IHr.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite inslist_sorted_cat_cons_cat //.
case Hc: (cmp x a)=>/=.
- by move/cmp_lt: Hc=>->; rewrite inorder_balL IHl // (cat_sorted2 H1).
- by move/cmp_eq: Hc=>/eqP->; rewrite ltxx eq_refl.
move/cmp_gt: Hc=>/[dup] Hx.
rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
rewrite -cat1s in H2.
by rewrite inorder_balR IHr // (cat_sorted2 H2).
Qed.

Theorem inorder_delete x t :
  bst_list t ->
  inorder_a (delete x t) = del_list x (inorder_a t).
Proof.
rewrite /bst_list /=; elim: t=>//=l IHl [a c] r IHr /[dup] H.
rewrite sorted_cat_cons_cat=>/andP [H1 H2].
rewrite dellist_sorted_cat_cons_cat //.
case Hc: (cmp x a)=>/=.
- by move/cmp_lt: Hc=>->; rewrite inorder_balR IHl // (cat_sorted2 H1).
- move/cmp_eq: Hc=>/eqP ->; rewrite ltxx eq_refl.
  case: {H H1 IHl}l=>//= ll [al nl] rl.
  case Hsm: (split_max ll al rl)=>[a' r'] /=.
  move: (inorder_split_max Hsm)=>Esm.
  by rewrite inorder_balR -Esm -catA.
move/cmp_gt: Hc=>/[dup] Hx.
rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
rewrite -cat1s in H2.
by rewrite inorder_balL IHr // (cat_sorted2 H2).
Qed.

(* TODO holds for all augmented trees (i.e. copied from RBT), move to bintree? *)

Lemma inorder_isin_list x t :
  bst_list t ->
  isin_a t x = (x \in inorder_a t).
Proof.
rewrite /bst_list /=; elim: t=>//= l IHl [a c] r IHr.
rewrite mem_cat inE sorted_cat_cons_cat=>/andP [H1 H2].
case Hc: (cmp x a)=>/=.
- move/cmp_lt: Hc=>Hx; rewrite IHl; last by rewrite (cat_sorted2 H1).
  have ->: (x==a)=false by move: Hx; rewrite lt_neqAle=>/andP [/negbTE].
  have ->: x \in inorder_a r = false; last by rewrite /= orbF.
  apply/negbTE/count_memPn; rewrite -(count_pred0 (inorder_a r)).
  apply/eq_in_count=>z; move: H2=>/= /(order_path_min lt_trans)/allP/(_ z)/[apply] Hz.
  by move: (lt_trans Hx Hz); rewrite lt_neqAle eq_sym=>/andP [/negbTE].
- by move/cmp_eq: Hc=>/eqP->; rewrite eq_refl /= orbT.
move/cmp_gt: Hc=>Hx; rewrite IHr; last first.
- by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
have ->: (x==a)=false by move: Hx; rewrite lt_neqAle eq_sym=>/andP [/negbTE].
suff: x \in inorder_a l = false by move=>->.
apply/negbTE/count_memPn; rewrite -(count_pred0 (inorder_a l)).
apply/eq_in_count=>z /=.
move: H1; rewrite (sorted_pairwise lt_trans) pairwise_cat /= allrel1r andbT.
case/andP=>+ _ =>/allP/(_ z)/[apply] Hz.
by move: (lt_trans Hz Hx); rewrite lt_neqAle eq_sym=>/andP [/negbTE].
Qed.

(* corollaries *)

Definition invariant t := bst_list t && avl t.

Corollary inorder_insert_list x t :
  invariant t ->
  perm_eq (inorder_a (insert x t))
          (if x \in inorder_a t then inorder_a t else x :: inorder_a t).
Proof.
rewrite /invariant /bst_list => /andP [H1 _].
by rewrite inorder_insert //; apply: inorder_ins_list.
Qed.

Corollary inorder_delete_list x t :
  invariant t ->
  perm_eq (inorder_a (delete x t))
          (filter (predC1 x) (inorder_a t)).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
by rewrite inorder_delete //; apply: inorder_del_list.
Qed.

Corollary invariant_empty : invariant empty_a.
Proof. by []. Qed.

Corollary invariant_insert x t :
  invariant t -> invariant (insert x t).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
apply/andP; split; last by case/andP: (avl_insert x H2).
by rewrite inorder_insert //; apply: ins_list_sorted.
Qed.

Corollary invariant_delete x t :
  invariant t -> invariant (delete x t).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
apply/andP; split; last by case/andP: (avl_delete x H2).
by rewrite inorder_delete //; apply: del_list_sorted.
Qed.

Lemma inv_isin_list x t :
  invariant t ->
  isin_a t x = (x \in inorder_a t).
Proof. by rewrite /invariant => /andP [H1 _]; apply: inorder_isin_list. Qed.

Definition SetAVL :=
  @ASetM.make _ _ (tree_ht T)
    empty_a insert delete isin_a
    inorder_a invariant
    invariant_empty erefl
    invariant_insert inorder_insert_list
    invariant_delete inorder_delete_list
    inv_isin_list.

End SetImplementation.

Section Exercises.

(* Exercise 9.1 *)

Lemma height_bound' {A} (t : tree_ht A) :
  avl t ->
  (2^ (height t)./2 <= size1_tree t)%N.
Proof.
Admitted.

(* Exercise 9.2 *)

Equations? fibt (n : nat) : tree unit by wf n lt :=
fibt 0 => Leaf _;
fibt 1 => Node (Leaf _) tt (Leaf _);
fibt (n.+2) => Node (fibt (n + 1)) tt (fibt n).
Proof. by apply: ssrnat.ltP; rewrite addn1. Qed.

Fixpoint avl0 {A} (t : tree A) : bool :=
  if t is Node l _ r
    then [&& `|height l - height r| <= 1%N, avl0 l & avl0 r]
    else true.

Lemma avl0_fibt n : avl0 (fibt n).
Proof.
Admitted.

Lemma fibt_size n : size1_tree (fibt n) = fib (n + 2).
Proof.
Admitted.

Lemma fibt_minimal {A} (t : tree_ht A) :
  avl t ->
  (size1_tree (fibt (height t)) <= size1_tree t)%N.
Proof.
Admitted.

(* Exercise 9.3 *)

Lemma acomplete_avl {A} (t : tree A) : acomplete t -> avl0 t.
Proof.
Admitted.

(* Exercise 9.4 *)
Variable (m : nat) (mnz : (0 < m)%N).

(* height-balanced tree *)

(* IMPLEMENT *)

(* Exercise 9.5 *)

Definition avl_of_list {A} (xs : seq A) : tree_ht A := empty_a (* FIXME *).

(* order preservation *)

Theorem inorder_aol {A} (xs : seq A) : inorder_a (avl_of_list xs) = xs.
Proof.
Admitted.

(* AVL invariant *)

Theorem avl_aol {S : eqType} (xs : seq S) : avl (avl_of_list xs).
Proof.
Admitted.

End Exercises.

Section Optimization.
Context {disp : unit} {T : orderType disp}.

Variant bal := Lh | Bal | Rh.

Definition eqbal (b1 b2 : bal) :=
  match b1, b2 with
  | Lh, Lh => true
  | Bal, Bal => true
  | Rh, Rh => true
  | _, _ => false
  end.

Lemma eqbalP : Equality.axiom eqbal.
Proof. by move; case; case; constructor. Qed.

Canonical bal_eqMixin := EqMixin eqbalP.
Canonical bal_eqType := Eval hnf in EqType bal bal_eqMixin.

Definition tree_bal A := tree (A * bal).

Definition bal_inv (x : nat) (b : bal) (y : nat) : bool :=
  match b with
  | Lh => x == y + 1
  | Bal => y == x
  | Rh => y == x + 1
  end.

Fixpoint avl_b {A} (t : tree_bal A) : bool :=
  if t is Node l (_, b) r then
    [&& bal_inv (height l) b (height r), avl_b l & avl_b r]
    else true.

Lemma avl_b_ind {A} (P : tree_bal A -> Prop) :
  P (Leaf (A*bal)) ->
  (forall l a b r,
   bal_inv (height l) b (height r) ->
   avl_b l -> avl_b r ->
   P l -> P r ->
   P (Node l (a,b) r)) ->
  forall t, avl_b t -> P t.
Proof.
move=>Pl Pn; elim=>//= l IHl [a n] r IHr /and3P [H Hal Har].
by apply: Pn=>//; [apply: IHl| apply: IHr].
Qed.

Arguments avl_b_ind [A P].

Definition is_bal {A} (t : tree_bal A) : bool :=
  if t is Node _ (_, b) _ then b == Bal else false.

Definition incr {A} (t t' : tree_bal A) : bool :=
  ~~ is_node t || (is_bal t && ~~ is_bal t').

(* since we don't have height~balance factor link available in the computational code, *)
(* we add unused cases for pattern-matches *)

Definition rot2 {A} (a : tree_bal A) (x : A) (b : tree_bal A) (z : A) (c : tree_bal A) : tree_bal A :=
  match b with
  | Node b1 (y, bb) b2 =>
    let bb1 := if bb == Rh then Lh else Bal in
    let bb2 := if bb == Lh then Rh else Bal in
    Node (Node a (x, bb1) b1) (y, Bal) (Node b2 (z, bb2) c)
  | Leaf => empty_a
  end.

(* TODO split out internal matches and formulate helper lemmas in their terms *)

Definition balL_b {A} (ab : tree_bal A) (z : A) (bb : bal) (c : tree_bal A) : tree_bal A :=
  match bb with
  | Lh => match ab with
          | Node a (x, Lh) b => Node a (x, Bal) (Node b (z, Bal) c)
          | Node a (x, Bal) b => Node a (x, Rh) (Node b (z, Lh) c)
          | Node a (x, Rh) b => rot2 a x b z c
          | Leaf => empty_a
          end
  | Bal => Node ab (z, Lh) c
  | Rh => Node ab (z, Bal) c
  end.

Definition balR_b {A} (a : tree_bal A) (x : A) (bb : bal) (bc : tree_bal A) : tree_bal A :=
  match bb with
  | Lh => Node a (x, Bal) bc
  | Bal => Node a (x, Rh) bc
  | Rh => match bc with
          | Node b (z, Lh) c => rot2 a x b z c
          | Node b (z, Bal) c => Node (Node a (x, Rh) b) (z, Lh) c
          | Node b (z, Rh) c => Node (Node a (x, Bal) b) (z, Bal) c
          | Leaf => empty_a
          end
  end.

Fixpoint insert_b (x : T) (t : tree_bal T) : tree_bal T :=
  if t is Node l (a, b) r
    then match cmp x a with
         | LT => let l' := insert_b x l in
                 if incr l l' then balL_b l' a b r else Node l' (a, b) r
         | EQ => Node l (a, b) r
         | GT => let r' := insert_b x r in
                 if incr r r' then balR_b l a b r' else Node l (a, b) r'
         end
    else Node empty_a (x, Bal) empty_a.

Definition decr {A} (t t' : tree_bal A) : bool :=
  is_node t && (~~ is_node t' || ((~~ is_bal t) && is_bal t')).

Fixpoint split_max_b {A} (l : tree_bal A) (a : A) (ba : bal) (r : tree_bal A) : tree_bal A * A :=
  if r is Node lr (ar, br) rr
    then let: (r', a') := split_max_b lr ar br rr in
         let t' := if decr r r' then balL_b l a ba r' else Node l (a, ba) r' in
         (t', a')
    else (l, a).

Fixpoint delete_b (x : T) (t : tree_bal T) : tree_bal T :=
  if t is Node l (a, ba) r
    then match cmp x a with
         | LT => let l' := delete_b x l in
                 if decr l l' then balR_b l' a ba r else Node l' (a, ba) r
         | EQ => if l is Node ll (al, bl) rl then
                   let: (l', a') := split_max_b ll al bl rl in
                   if decr l l' then balR_b l' a' ba r
                                else Node l' (a', ba) r
                   else r
         | GT => let r' := delete_b x r in
                 if decr r r' then balL_b l a ba r' else Node l (a, ba) r'
         end
    else empty_a.

Lemma avl_insert_b x t :
  avl_b t ->
  avl_b (insert_b x t) && (height (insert_b x t) == height t + incr t (insert_b x t)).
Proof.
elim/avl_b_ind=>//= l a b r E Hl Hr /andP [Hal Hhl] /andP [Har Hhr].
case: (cmp x a)=>/=.
- (* x < a *)
  case: ifP=>/=; last first.
  - move=>Hi; case: b E=>/=; move/eqP: Hhl=>->/eqP->;
    by rewrite Hi !addn0 Hal Hr !eq_refl.
  (* incr l insert *)
  move=>Hi; rewrite Hi in Hhl.
  case: b E=>/eqP E /=.
  - (* b = Lh *)
    case E': (insert_b x l) Hi => [|li [ai bi] ri]/=.
    - (* insert = Leaf, impossible *)
      by move: Hhl; rewrite E' addn0 E addn1.
    (* insert = Node *)
    move: Hal Hhl; rewrite {}E' E /= maxn_addl addn0; case: bi=>/=.
    - (* bi = Lh *)
      case/and3P=>/eqP->->->/=.
      by rewrite maxn_addl !eqn_add2r=>/eqP<-; rewrite !maxnn Hr !eq_refl.
    - (* bi = Bal *)
      case: {Hl}l E; rewrite /incr /=; first by rewrite addn1.
      by move=>????; rewrite andbF.
    (* bi = Rh *)
    case/and3P; case: ri=>/=; first by rewrite addn1; move/eqP.
    move=>lri [ari bri] rri /=; rewrite eqn_add2r /bal_inv =>/eqP <- ->.
    case: bri=>/= /and3P [/eqP->->->] /=.
    - (* bri = Lh *)
      rewrite -!addn_maxl maxn_addl -addn_maxl maxn_addr !eqn_add2r =>/eqP <-.
      by rewrite maxn_addr !maxnn Hr !eq_refl.
    - (* bri = Bal *)
      by rewrite !maxnn maxn_addr !eqn_add2r=>/eqP<-; rewrite !maxnn Hr !eq_refl.
    (* bri = Rh *)
    by rewrite !maxn_addr maxn_addl !eqn_add2r=>/eqP<-; rewrite !maxnn Hr !eq_refl.
  - (* b = Bal *)
    by rewrite Hal Hr; move/eqP: Hhl=>->; rewrite E maxnn maxn_addl !eq_refl.
  (* b = Rh *)
  by rewrite Hal Hr; move/eqP: Hhl=>->; rewrite E maxnn addn0 maxn_addr !eq_refl.
- (* x == a *)
  by rewrite Hl Hr /= andbT; case: b E=>/= /eqP->; rewrite addn0 !eq_refl.
(* x > a *)
case: ifP=>/=; last first.
- move=>Hi; case: b E=>/=; move/eqP: Hhr=>->/eqP->;
  by rewrite Hi !addn0 Har Hl !eq_refl.
(* incr r insert *)
move=>Hi; case: b E=>/eqP E /=.
- (* b = Lh *)
  by rewrite Har Hl; move/eqP: Hhr=>->; rewrite Hi E maxnn addn0 maxn_addl !eq_refl.
- (* b = Bal *)
  by rewrite Har Hl; move/eqP: Hhr=>->; rewrite Hi E maxnn maxn_addr !eq_refl.
(* b = Rh *)
case E': (insert_b x r)=> [|li [ai bi] ri]/=.
- (* insert = Leaf, impossible *)
  move: Hhr; rewrite E' /=; case: (incr _ _)=>/= /eqP; first by rewrite addn1.
  by rewrite addn0 E addn1.
(* insert = Node *)
move: Hi Har Hhr; rewrite {}E' E=>/=.
rewrite maxn_addr addn0; case: bi=>/=.
- (* bi = Lh *)
  move=>->; case/and3P; case: li=>/=; first by rewrite addn1; move/eqP.
  move=>lli [ali bli] rli /=; rewrite eqn_add2r /bal_inv =>/eqP <- /[swap] ->.
  case: bli=>/= /and3P [/eqP->->->] /=.
  - (* bli = Lh *)
    by rewrite !maxn_addl maxn_addr -addn_maxl !eqn_add2r =>/eqP=><-; rewrite !maxnn Hl !eq_refl.
  - (* bli = Bal *)
    by rewrite !maxnn maxn_addl !eqn_add2r =>/eqP<-; rewrite !maxnn Hl !eq_refl.
  (* bli = Rh *)
  rewrite maxn_addl maxn_addr -!addn_maxl !eqn_add2r=>/eqP<-.
  by rewrite maxn_addl !maxnn Hl !eq_refl.
- (* bi = Bal, impossible *)
  case: {Hr}r E; rewrite /incr /=; first by rewrite addn1.
  by move=>????; rewrite andbF.
(* bi = Rh *)
move=>->; case/and3P=>/eqP->->->/=.
by rewrite !eqn_add2r maxn_addr eqn_add2r=>/eqP<-; rewrite !maxnn Hl !eq_refl.
Qed.

Lemma avl_balL_b_decr {A} (l : tree_bal A) a b r t :
  avl_b l -> avl_b r -> bal_inv (height l) b (height r + 1) ->
  avl_b (balL_b l a b r) && (maxn (height l) (height r + 1) + 1 == height (balL_b l a b r) +
                                                                   decr (Node l (a, b) t) (balL_b l a b r)).
Proof.
move=>Hl Hr; case: b=>/=.
- case: l Hl=>/=; first by move=>_ /eqP; rewrite addn1.
  move=>ll [al bl] rl /and3P [Hbl Hall Harl].
  rewrite eqn_add2r => /[dup] H' /eqP ->; rewrite -addn_maxl maxn_addl.
  case: bl Hbl=>/=; move: (H')=>/[swap]/eqP->.
  - rewrite maxn_addl !eqn_add2r=>/eqP->.
    by rewrite !maxnn !eq_refl Hall Harl Hr.
  - rewrite maxnn addn0 !eqn_add2r=>/eqP->.
    by rewrite -addn_maxl maxn_addl maxn_addr !eq_refl Hall Harl Hr.
  rewrite maxn_addr eqn_add2r =>/eqP H''.
  case: rl Harl H'=>/=.
  - by move=>_; rewrite maxn0 H'' -{1}(addn0 (height _)) eqn_add2l.
  move=>lrl [arl brl] rrl=>/= /and3P [Hlrl -> ->].
  case: brl Hlrl=>/=.
  - move/eqP->; rewrite maxn_addl H''.
    case: (ltngtP (height r) (height rrl + 1 + 1))=>_;
      try by rewrite -{1}(addn0 (height _)) eqn_add2l.
    by rewrite eqn_add2r=>/eqP<-; rewrite maxn_addr !maxnn !eq_refl Hall Hr.
  - move/eqP->; rewrite maxnn H''.
    case: (ltngtP (height r) (height lrl + 1))=>_;
      try by rewrite -{1}(addn0 (height _)) eqn_add2l.
    by rewrite eqn_add2r=>/eqP->; rewrite !maxnn !eq_refl Hall Hr.
  move/eqP->; rewrite maxn_addr H''.
  case: (ltngtP (height r) (height lrl + 1 + 1))=>_;
    try by rewrite -{1}(addn0 (height _)) eqn_add2l.
  by rewrite eqn_add2r=>/eqP<-; rewrite maxn_addl !maxnn !eq_refl Hall Hr.
- by move/eqP <-; rewrite maxn_addl maxnn addn0 !eq_refl Hl Hr.
by rewrite eqn_add2r=>/eqP->; rewrite maxn_addr maxnn !eq_refl Hl Hr.
Qed.

Lemma avl_split_max_b {A} (l : tree_bal A) a b r t x :
  split_max_b l a b r = (t, x) ->
  bal_inv (height l) b (height r) -> avl_b l -> avl_b r ->
  avl_b t && (maxn (height l) (height r) + 1 == height t + decr (Node l (a,b) r) t).
Proof.
elim: r l a b t=>/= [|lr _ [ar br] rr IHr] l a b t.
- case=><- _; rewrite maxn0 => H /[dup] E -> _ /=.
  case: b H=>/=; rewrite /decr /=.
  - rewrite add0n=>/[dup] H /eqP ->; rewrite eqn_add2l eq_sym eqb1.
    case: l E H=>//= l [z b] r.
    rewrite -{2}(add0n 1%N) eqn_add2r; case: b=>//=; case/and3P=>/eqP->_ _.
    - by rewrite maxn_addl addn1=>/eqP.
    by rewrite maxn_addr addn1=>/eqP.
  - by rewrite eq_sym=>/heightE->.
  by rewrite addn1=>/eqP.
case Hsm: (split_max_b lr ar br rr)=>[r' a']; case=><- E; rewrite {}E in Hsm.
move=>H Hl /and3P [Hbr Hlr Hrr].
case/andP: (IHr _ _ _ _ Hsm Hbr Hlr Hrr)=>Har' Hh.
case: ifP=>/= Hd; rewrite Hd /= in Hh.
- rewrite /bal_inv /= in H; rewrite (eqP Hh) in H *.
  by apply: avl_balL_b_decr.
by case: b H=>/=; rewrite (eqP Hh) addn0=>/eqP->; rewrite addn0 !eq_refl Hl Har'.
Qed.

Lemma avl_delete_b x t :
  avl_b t ->
  avl_b (delete_b x t) && (height t == height (delete_b x t) + decr t (delete_b x t)).
Proof.
elim/avl_b_ind=>//=l a b r E Hl Hr /andP [Hal Hhl] /andP [Har Hhr].
case: (cmp x a)=>/=.
- (* x < a *)
  case: ifP=>/=; last first.
  - by move=>Hi; case: b E=>/=; move/eqP: Hhl=>->;
    rewrite Hi !addn0=>/eqP->; rewrite Hal Hr !eq_refl.
  (* decr l delete *)
  move=>Hi; rewrite Hi /= in Hhl; case: b E=>E /=.
  - (* b = Lh *)
    rewrite Hal Hr; move: Hhl; rewrite (eqP E) eqn_add2r=>/eqP<-.
    by rewrite maxnn maxn_addl !eq_refl.
  - (* b = Bal *)
    rewrite Hal Hr; move: Hhl; rewrite (eqP E) maxnn =>/eqP->.
    by rewrite maxn_addr addn0 !eq_refl.
  (* b = Rh *)
  case: {Har Hhr}r Hr E=>/=; first by rewrite addn1.
  move=>lr [ar br] rr /=; case/and3P; case: br=>/=.
  - case: lr=>/=; first by rewrite addn1=>/eqP.
    move=>llr [alr blr] rlr /=; rewrite eqn_add2r=>Hrr; case: blr=>/=.
    - rewrite -(eqP Hrr); case/and3P =>/eqP-> Hallr Harlr Harr; move/eqP: Hhl=>->.
      rewrite !maxn_addl !eqn_add2r=>/eqP <-.
      by rewrite !maxn_addr !maxnn !eq_refl Hal Hallr Harlr Harr.
    - rewrite -(eqP Hrr); case/and3P=>/eqP-> Hallr Harlr Harr; move/eqP: Hhl=>->.
      rewrite maxn_addl !maxnn !eqn_add2r=>/eqP <-.
      by rewrite maxn_addr !maxnn !eq_refl Hal Hallr Harlr Harr.
    rewrite -(eqP Hrr); case/and3P =>/eqP-> Hallr Harlr Harr; move/eqP: Hhl=>->.
    rewrite !maxn_addl !maxn_addr !eqn_add2r=>/eqP <-.
    by rewrite !maxn_addr !maxn_addl !maxnn !eq_refl Hal Hallr Harlr Harr.
  - move/eqP=>-> Halr Harr; rewrite (eqP Hhl) maxnn !eqn_add2r =>/eqP->.
    by rewrite !maxn_addr maxn_addl addn0 !eq_refl Hal Halr Harr.
  move/eqP=>-> Halr Harr; rewrite (eqP Hhl) maxn_addr !eqn_add2r =>/eqP <-.
  by rewrite !maxnn maxn_addr !eq_refl Hal Halr Harr.
- (* x == a *)
  case: {Hal Hhl} l Hl E=>/=.
  - move=>_; case: b=>/=; rewrite /decr /=.
    - by rewrite addn1 => /eqP.
    - by move/heightE=>->.
    rewrite add0n max0n Hr => H /=; rewrite eqn_add2l.
    case: {Har Hhr}r Hr H=>//=lr [ar br] rr /=.
    rewrite -{2}(add0n 1%N) eqn_add2r; case: br=>//=; case/and3P=>/eqP=>->_ _.
    - by rewrite maxn_addl addn1=>/eqP.
    by rewrite maxn_addr addn1=>/eqP.
  move=>ll [al bl] rl=>/and3P [Hb Hall Harl] Hbl.
  case Hsm: (split_max_b ll al bl rl)=>[l' a'].
  case/andP: (avl_split_max_b Hsm Hb Hall Harl)=>Hal'; case: ifP=>/= Hd.
  - rewrite eqn_add2r => /eqP E'; move: Hbl; rewrite E'; case: b=>/=.
    - by rewrite eqn_add2r=>/eqP->; rewrite maxn_addl maxnn !eq_refl Hal' Hr.
    - by move/eqP=>->; rewrite maxn_addr maxnn addn0 !eq_refl Hal' Hr.
    case: {Har Hhr}r Hr=>/=; first by rewrite addn1=>/eqP.
    move=>lr [ar br] rr; rewrite eqn_add2r=>/and3P [H'' Halr Harr] E''.
    case: br H'' =>/=.
    - case: lr Halr E''=>/=; first by move=>_ _; rewrite addn1=>/eqP.
      move=>llr [alr blr] rlr; case: blr=>/= /and3P [/eqP-> Hallr Harlr].
      - rewrite maxn_addl !eqn_add2r=>/[swap]/eqP<-.
        rewrite maxn_addl eqn_add2r=>/eqP<-.
        by rewrite !maxn_addr !maxnn !eq_refl Hal' Hallr Harlr Harr.
      - rewrite maxnn !eqn_add2r=>/[swap]/eqP->.
        rewrite maxn_addl maxnn eqn_add2r=>/eqP->.
        by rewrite !maxnn maxn_addr !eq_refl Hal' Hallr Harlr Harr.
      rewrite maxn_addr !eqn_add2r=>/[swap]/eqP<-.
      rewrite maxn_addl eqn_add2r=>/eqP<-.
      by rewrite maxn_addl maxn_addr !maxnn !eq_refl Hal' Hallr Harlr Harr.
    - move: E''=>/[swap]/eqP->; rewrite maxnn=>/eqP->.
      by rewrite !maxn_addr maxn_addl addn0 !eq_refl Hal' Halr Harr.
    move: E''=>/[swap]/eqP->; rewrite maxn_addr !eqn_add2r=>/eqP->.
    by rewrite !maxnn maxn_addr !eq_refl Hal' Halr Harr.
  by rewrite addn0 Hal' Hr; move: Hbl=>/[swap]/eqP->-> /=; case: b=>/=; rewrite addn0.
(* x > a *)
case: ifP=>/=; last first.
- by move=>Hi; case: b E=>/=; move/eqP: Hhr=>->;
  rewrite Hi !addn0=>/eqP->; rewrite Har Hl !eq_refl.
(* decr l delete *)
move=>Hi; rewrite Hi /= in Hhr; case: b E=>E /=.
- (* b = Lh *)
  case: {Hal Hhl}l Hl E=>/=; first by rewrite addn1.
  move=>ll [al bl] rl /=; case/and3P; case: bl=>/=.
  - move/eqP=>-> Hall Harl; rewrite (eqP Hhr) maxn_addl !eqn_add2r =>/eqP <-.
    by rewrite !maxnn maxn_addl !eq_refl Har Hall Harl.
  - move/eqP=>-> Hall Harl; rewrite (eqP Hhr) maxnn !eqn_add2r =>/eqP->.
    by rewrite !maxn_addl maxn_addr addn0 !eq_refl Har Hall Harl.
  case: rl=>/=; first by rewrite addn1=>/eqP.
  move=>lrl [arl brl] rrl /=; rewrite eqn_add2r=>Hll Hall; case: brl=>/=.
  - rewrite -(eqP Hll); case/and3P=>/eqP-> Halrl Harrl.
    rewrite maxn_addl maxn_addr !eqn_add2r; move/eqP: Hhr=>->.
    rewrite !eqn_add2r =>/eqP <-.
    by rewrite !maxn_addr maxn_addl !maxnn !eq_refl Hall Halrl Harrl Har.
  - rewrite -(eqP Hll); case/and3P=>/eqP-> Halrl Harrl.
    rewrite maxnn maxn_addr !eqn_add2r; move/eqP: Hhr=>->.
    rewrite !eqn_add2r =>/eqP <-.
    by rewrite maxn_addl !maxnn !eq_refl Hall Halrl Harrl Har.
  rewrite -(eqP Hll); case/and3P=>/eqP-> Halrl Harrl.
  rewrite !maxn_addr maxn_addl !eqn_add2r; move/eqP: Hhr=>->.
  rewrite !eqn_add2r =>/eqP <-.
  by rewrite maxn_addl !maxnn !eq_refl Hall Halrl Harrl Har.
- (* b = Bal *)
  rewrite Har Hl; move: Hhr; rewrite (eqP E) maxnn =>/eqP->.
  by rewrite maxn_addl addn0 !eq_refl.
(* b = Rh *)
rewrite Har Hl; move: Hhr; rewrite (eqP E) eqn_add2r=>/eqP<-.
by rewrite maxnn maxn_addr !eq_refl.
Qed.

End Optimization.

Section Exercises2.

(* Exercise 9.6 *)

Fixpoint debal {A} (t : tree_bal A) : tree_ht A :=
  if t is Node l (a, _) r
    then Node (debal l) (a, maxn (height l) (height r) + 1) (debal r)
    else empty_a.

Lemma avl_b_avl {A} (t : tree_bal A) : avl_b t -> avl (debal t).
Proof.
Admitted.

Fixpoint debal2 {A} (t : tree_bal A) : tree_ht A := empty_a. (* FIXME *)

Lemma avl_debal_eq {A} (t : tree_bal A) : avl_b t -> debal2 t = debal t.
Proof.
Admitted.

(* Exercise 9.7 *)

Context {disp : unit} {T : orderType disp}.

Inductive tree4 A := Leaf
                   | Lh4 of (tree4 A) & A & (tree4 A)
                   | Bal4 of (tree4 A) & A & (tree4 A)
                   | Rh4 of (tree4 A) & A & (tree4 A).

(* IMPLEMENT *)

End Exercises2.
