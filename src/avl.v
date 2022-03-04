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

Lemma ht_height (t : tree_ht A) : avl t -> ht t = height t.
Proof. by case: t=>//=l [a x] r /and4P [_ /eqP E _ _]. Qed.

End Intro.

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
elim: t=>//= l IHl [_ n] r IHr /and4P [H _ /IHl Hl /IHr Hr] {IHl IHr}.
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

Inductive non_empty_if (b : bool) (t : tree_ht T) : Type :=
| Nd l a n r : t = Node l (a,n) r -> b -> non_empty_if b t
| Def : ~~ b -> non_empty_if b t.

Lemma ne_hplus2 (t1 t2 : tree_ht T) : non_empty_if (ht t1 == ht t2 + 2) t1.
Proof.
case: eqP; last by move=>_; apply: Def.
case: t1=>/=; first by rewrite addn2.
by move=>l [a n] r _; apply: Nd.
Qed.

Lemma ne_hgt (t1 t2 : tree_ht T) : non_empty_if (ht t2 < ht t1)%N t1.
Proof.
case: ltnP; last by move=>_; apply: Def.
by case: t1=>//= l [a n] r _; apply: Nd.
Qed.

Definition balL (ab : tree_ht T) (u : T) (c : tree_ht T) : tree_ht T :=
  match ne_hplus2 ab c with
  | Nd a v _ b _ _ =>
      match ne_hgt b a with
      | Nd b1 w _ b2 _ _ => node (node a v b1) w (node b2 u c)
      | Def _            => node a v (node b u c)
      end
  | Def _ => node ab u c
  end.

Definition balR (a : tree_ht T) (u : T) (bc : tree_ht T) : tree_ht T :=
  match ne_hplus2 bc a with
  | Nd b v _ c _ _ =>
      match ne_hgt b c with
      | Nd b1 w _ b2 _ _ => node (node a u b1) w (node b2 v c)
      | Def _            => node (node a u b) v c
      end
  | Def _ => node a u bc
  end.

Lemma height_balL l a r :
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
- move: E; move/maxn_idPr: (leq_addr 1 (maxn h1 h2))=>->.
  by rewrite !addn1 =>/succn_inj.
by rewrite (maxnAC h1 h2 h1) maxnn (maxnCA h2 h1 h2) !maxnn -addnA eq_refl.
Qed.

Lemma height_balR l a r :
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
- move: E; move/maxn_idPl: (leq_addr 1 (maxn h1 h2))=>->.
  by rewrite !addn1 =>/succn_inj.
by rewrite (maxnAC h1 h2 h1) maxnn (maxnCA h2 h1 h2) !maxnn -addnA eq_refl.
Qed.

Lemma height_balL2 l a r :
  avl l -> avl r -> height l != height r + 2 ->
  height (balL l a r) = maxn (height l) (height r) + 1.
Proof.
move=>Hl Hr E; rewrite /balL.
case (ne_hplus2 l r)=>[al vl xl bl _|_] //=.
by rewrite !ht_height //; move/negbTE: E=>->.
Qed.

Lemma height_balR2 l a r :
  avl l -> avl r -> height r != height l + 2 ->
  height (balR l a r) = maxn (height l) (height r) + 1.
Proof.
move=>Hl Hr E; rewrite /balR.
case (ne_hplus2 r l)=>[al vl xl bl _|_] //=.
by rewrite !ht_height //; move/negbTE: E=>->.
Qed.

Lemma avl_balL l a r :
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
- move: E; move/maxn_idPr: (leq_addr 1 (maxn h1 h2))=>->.
  by rewrite !addn1 =>/succn_inj.
rewrite (maxnAC h1 h2 h1) maxnn (maxnCA h2 h1 h2) maxnn distnn /=.
by rewrite /maxn; case: ifP=>_; rewrite distnn distnC ?andbT.
Qed.

Lemma avl_balR l a r :
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
- move: E; move/maxn_idPl: (leq_addr 1 (maxn h1 h2))=>->.
  by rewrite !addn1 =>/succn_inj.
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
elim: t=>//=l IHl [a n] r IHr /and4P [H E Hal Har].
case/IHl/andP: (Hal)=>Hail {}IHl; case/IHr/andP: (Har)=>Hair {}IHr.
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
    move/maxn_idPl: (H1)=>->; have: (height r <= height l + 1)%N by apply/(leq_trans H1)/leq_addr.
    by move/maxn_idPl=>->; rewrite eq_refl orbT.
  rewrite (eqP Hil) in IHl; case/orP: IHl.
  - move=>/eqP Ehl; move: H; rewrite -{}Ehl.
    have/distnEl->: (height r <= height r + 2)%N by apply: leq_addr.
    by rewrite -addnBAC // subnn.
  rewrite (_: 2= 1+1) // addnA eqn_add2r =>/eqP<-.
  have/maxn_idPl->: (height r <= height r + 1)%N by apply: leq_addr.
  by case/orP: (height_balL a Hail Har (eqP Hil))=>/eqP->; rewrite -!addnA eq_refl ?orbT.
- by rewrite H E Hal Har eq_refl.
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
  - move/maxn_idPr: (H1)=>->; have: (height l <= height r + 1)%N by apply/(leq_trans H1)/leq_addr.
    by move/maxn_idPr=>->; rewrite eq_refl orbT.
  move/maxn_idPr: (H2)=>->; move/maxn_idPl: (H1)=>->; rewrite !eqn_add2r.
  move: H2; rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite eq_refl.
  rewrite addn1 ltnS => Hrl; suff: height r == height l by move=>->; rewrite orbT.
  by rewrite eqn_leq H1 Hrl.
rewrite (eqP Hir) in IHr; case/orP: IHr.
- move=>/eqP Ehr; move: H; rewrite -{}Ehr.
  have/distnEr->: (height l <= height l + 2)%N by apply: leq_addr.
  by rewrite -addnBAC // subnn.
rewrite (_: 2= 1+1) // addnA eqn_add2r =>/eqP<-.
have/maxn_idPr->: (height l <= height l + 1)%N by apply: leq_addr.
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
  rewrite maxnn; have/maxn_idPl->: (height r' <= height r' + 1)%N by apply: leq_addr.
  by rewrite eq_refl orbT.
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
elim: t=>//=l IHl [a n] r IHr /and4P [H E Hal Har].
case/IHl/andP: (Hal)=>Hail {}IHl; case/IHr/andP: (Har)=>Hair {}IHr.
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
    - move/maxn_idPr: (H1)=>->; have/maxn_idPr->: (height l <= height r + 1)%N by apply/(leq_trans H1)/leq_addr.
      by rewrite eq_refl.
    move/maxn_idPl: (H1)=>->; move/maxn_idPr: (H2)=>->; rewrite !eqn_add2r.
    move: H2; rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite eq_refl orbT.
    rewrite addn1 ltnS => Hlr; suff: height l == height r by move=>->.
    by rewrite eqn_leq H1 Hlr.
  case/orP: (height_balR a Hail Har (eqP Hil))=>/eqP->;
  case/orP: IHl=>/eqP ->; rewrite (eqP Hil);
  set d := height (delete x l); apply/orP.
  - by right; rewrite eqn_add2r; apply/eqP/maxn_idPr; apply: leq_addr.
  - by right; rewrite eqn_add2r; apply/eqP/maxn_idPr; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
  - by left; rewrite (_ : 3= 2+1) // addnA eqn_add2r; apply/eqP/maxn_idPr/leq_addr.
  by left; rewrite (_ : 3= 2+1) // addnA eqn_add2r; apply/eqP/maxn_idPr; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
- case: {Hail IHl}l H E Hal=>/=; first by move=>_ _ _; rewrite Har max0n eq_refl orbT.
  move=>ll [al nl] rl H E /and4P [Hl El Hall Harl].
  case Hsm: (split_max ll al rl)=>[l' a'].
  case/andP: (avl_split_max Hsm Hl Hall Harl)=>Hal' Hl'.
  apply/andP; split.
  - apply: avl_balR=>//; rewrite leq_subLR addnC.
    case/dist_leq/orP: H=>/andP [H1 H2]; case/orP: Hl'=>/eqP E';
    rewrite -{}E' in H1 H2.
    - rewrite -addnA in H2; rewrite H2 andbT.
      rewrite -(leq_add2r 1); apply/(leq_trans H1); rewrite -addnA; apply: leq_addr.
    - apply/andP; split; first by apply/(leq_trans H1)/leq_addr.
      by rewrite (_ : 2= 1+1) // addnA; apply/(leq_trans H2)/leq_addr.
    - apply/andP; split; last by rewrite (_ : 2= 1+1) // addnA; apply/(leq_trans H1)/leq_addr.
      by rewrite -(leq_add2r 1); apply/(leq_trans H2)/leq_addr.
    by rewrite H2 /=; apply/(leq_trans H1)/leq_addr.
  case/boolP: (height r == height l' + 2)=>Hrl'; last first.
  - move: (height_balR2 a' Hal' Har Hrl')=>->.
    case/orP: Hl'=>/eqP E'; rewrite -{}E' in H *; last by rewrite eq_refl.
    case/dist_leq/orP: H=>/andP [H1 H2].
    - move/maxn_idPr: (H1)=>->; have/maxn_idPr->: (height l' <= height r)%N by apply/leq_trans/H1/leq_addr.
      by rewrite eq_refl.
    move/maxn_idPl: (H1)=>->.
    rewrite leq_add2r in H2; move/maxn_idPr: (H2)=>->; rewrite !eqn_add2r.
    move: H1; rewrite leq_eqVlt; case/orP; first by move/eqP=>->; rewrite eq_refl.
    rewrite addn1 ltnS => {}Hrl'; suff: height l' == height r by move=>->; rewrite orbT.
    by rewrite eqn_leq H2 Hrl'.
  case/orP: Hl'=>/eqP E'; rewrite -{}E' (eqP Hrl') in H *; last first.
  - move: H; have/distnEr->: (height l' <= height l' + 2)%N by apply: leq_addr.
    by rewrite -addnBAC // subnn.
  case/orP: (height_balR a' Hal' Har (eqP Hrl'))=>/eqP->; apply/orP.
  - by right; rewrite eqn_add2r; apply/eqP/maxn_idPr; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
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
  move/maxn_idPl: (H1)=>->; have/maxn_idPl->: (height r <= height l + 1)%N by apply/(leq_trans H1)/leq_addr.
  by rewrite eq_refl.
case/orP: (height_balL a Hal Hair (eqP Hlr))=>/eqP->;
case/orP: IHr=>/eqP ->; rewrite (eqP Hlr);
set d := height (delete x r); apply/orP.
- by right; rewrite eqn_add2r; apply/eqP/maxn_idPl; apply: leq_addr.
- by right; rewrite eqn_add2r; apply/eqP/maxn_idPl; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
- by left; rewrite (_ : 3= 2+1) // addnA eqn_add2r; apply/eqP/maxn_idPl/leq_addr.
by left; rewrite (_ : 3= 2+1) // addnA eqn_add2r; apply/eqP/maxn_idPl; rewrite (_ : 2= 1+1) // addnA; apply: leq_addr.
Qed.

(* correctness via sorted lists *)

Lemma inorder_balL l a r :
  inorder_a (balL l a r) = inorder_a l ++ a :: inorder_a r.
Proof.
rewrite /balL.
case (ne_hplus2 l r)=>// al vl xl bl {l}->/= _.
case (ne_hgt bl al)=>[bl1 wl nl bl2|] /=; last by rewrite -catA.
by move=>{bl}->/= _; rewrite -!catA !cat_cons -catA.
Qed.

Lemma inorder_balR l a r :
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
