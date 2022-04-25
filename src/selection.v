From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path order bigop div ssrnum ssralg ssrint prime.
From favssr Require Import prelude sorting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Intro.
Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys : seq T) (k : nat).
Variable x0 : T.

Definition is_selection x k xs :=
  ((count (< x) xs <= k) && (count (> x) xs < size xs - k))%N.

Lemma selection_uniq k xs x y :
  k < size xs ->
  is_selection x k xs -> is_selection y k xs -> x = y.
Proof.
move=>Hk /andP [Hxl Hxg] /andP [Hyl Hyg]; apply/eqP; case/boolP: (_ == _) =>// Hn.
rewrite -(ltnn (size xs)) -{2}(subnKC (n:=size _) (m:=k)); last by apply: ltnW.
case/orP: (lt_total Hn)=>Hxy.
- rewrite -{1}(count_predC (<= x)).
  apply: leq_ltn_add; last by rewrite (eq_count (a2 := >x)) // =>z /=; rewrite ltNge.
  by apply/leq_trans/Hyl/sub_count=>z /= Hz; apply/le_lt_trans/Hxy.
rewrite -{1}(count_predC (<= y)).
apply: leq_ltn_add; last by rewrite (eq_count (a2 := >y)) // =>z /=; rewrite ltNge.
by apply/leq_trans/Hxl/sub_count=>z /= Hz; apply/le_lt_trans/Hxy.
Qed.

Definition select k xs : T := nth x0 (sort <=%O xs) k.

Lemma is_selection_sorted_nth xs k :
  (k < size xs)%N ->
  sorted <=%O xs ->
  is_selection (nth x0 xs k) k xs.
Proof.
elim: xs k=>//=x xs IH k Hk Hp; rewrite /is_selection; case: k Hk=>/= [_|k].
- rewrite ltxx !add0n subn0 leqn0 ltnS count_size andbT.
  rewrite -size_filter -all_pred0 all_filter (eq_all (a2 := >= x)).
  - by apply/le_path_min: Hp.
  by move=>z /=; rewrite implybF leNgt.
rewrite ltnS=>Hk.
move: Hp; rewrite le_path_sortedE=>/andP [Ha Hs].
case/andP: (IH _ Hk Hs)=> {IH} H1 H2; apply/andP; split.
- by rewrite -addn1 addnC; apply: leq_add=>//; case: (_ < _).
rewrite subSS ltNge.
suff : x <= nth x0 xs k by move=>->.
by move/all_nthP: Ha; apply.
Qed.

Lemma is_selection_select k xs :
  k < size xs -> is_selection (select k xs) k xs.
Proof.
move=>Hk; rewrite /select /is_selection.
move/permPl: (perm_sort <=%O xs)=>/[dup] Hp /permP Hc.
rewrite -!Hc -(perm_size Hp) in Hk *.
by apply: is_selection_sorted_nth.
Qed.

Lemma perm_sort_eq xs ys : perm_eq xs ys -> sort <=%O xs = sort <=%O ys.
Proof. by apply: perm_sort_leP. Qed.

Lemma perm_select_eq xs ys k : perm_eq xs ys -> select k xs = select k ys.
Proof. by rewrite /select=>/perm_sort_eq ->. Qed.

Lemma sort_cat xs ys :
  allrel <=%O xs ys ->
  sort <=%O (xs ++ ys) = sort <=%O xs ++ sort <=%O ys.
Proof.
move=>Ha; apply: le_sorted_eq=>//; last first.
- by rewrite perm_sort; apply: perm_cat; rewrite perm_sym perm_sort.
rewrite -(allrel_merge (leT := <=%O)).
- by apply: (merge_sorted le_total); exact: sort_le_sorted.
by apply/allrelP=>y z; rewrite !mem_sort=>Hy Hz; move/allrelP: Ha; apply.
Qed.

Lemma selection_mem s k xs :
  (k < size xs)%N -> is_selection s k xs ->
  s \in xs.
Proof.
move=>Hk Hs; move: (is_selection_select Hk)=>Hsel.
rewrite (selection_uniq Hk Hs Hsel) /select (perm_mem (s2:=sort <=%O xs)) ?mem_nth //.
- by rewrite size_sort.
by rewrite perm_sym perm_sort.
Qed.

(* Exercise 3.1 *)

Definition select0 xs := x0. (* FIXME *)

Lemma select0_select xs : xs != [::] -> select0 xs = select 0 xs.
Proof.
Admitted.

(* Exercise 3.2 *)

Definition select1 xs := x0. (* FIXME *)

(* Exercise 3.3.1 *)

Definition select_fixed k xs := x0. (* FIXME *)

Lemma select_fixed_select k xs :
  (* k < size xs -> *)   (* this typically won't be needed because nth is total via x0 *)
  select_fixed k xs = select k xs.
Proof.
Admitted.

(* Exercise 3.3.2 *)

Lemma select1_fixed xs : select1 xs = select_fixed 1 xs.
Proof.
Admitted.

(* Exercise 3.3.3 *)

Definition T_select_fixed k xs : nat := 1%N. (* FIXME *)

(* FIXME replace these with concrete numbers *)
Parameters (c1 c2 c3 c4 : nat).

Lemma T_select_fixed_kn k xs :
  T_select_fixed k xs <= c1*k*size xs + c2*size xs + c3*k + c4.
Proof.
Admitted.

End Intro.

Section IntroInt.

Open Scope ring_scope.
Import intZmod.
Import Num.Theory.
Import GRing.Theory.

Variable x0 : int.

(* Exercise 3.4 *)

Lemma select_uniq k i (xs : seq int) :
  (k < size xs)%N -> (i < size xs)%N -> uniq xs ->
  exists z, let xs' := set_nth x0 xs i z in
    uniq xs' /\ select x0 k xs' != select x0 k xs.
Proof.
Admitted.

End IntroInt.

Section DivideAndConquer.

Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys zs : seq T) (k : nat).
Variable x0 : T.

Lemma select_cat k ys zs :
  (* k < size ys + size zs -> *)  (* unnecessary *)
  allrel <=%O ys zs ->
  select x0 k (ys ++ zs) =
    if k < size ys then select x0 k ys else select x0 (k - size ys) zs.
Proof. by move=>Ha; rewrite /select sort_cat // nth_cat size_sort. Qed.

Lemma select_recurrence k x xs :
  (*k < size xs ->*)  (* unnecessary *)
  select x0 k xs =
    let '(ls, es, gs) := partition3 x xs in
    if k < size ls then select x0 k ls
      else if k < size ls + size es then x
        else select x0 (k - size ls - size es) gs.
Proof.
move H: (partition3 x xs)=>[[ls es] gs].
rewrite /partition3 in H; case: H=>Hl He Hg.
have /(perm_select_eq x0 k)-> : perm_eq xs (ls ++ es ++ gs).
- rewrite -Hl -He -Hg -(perm_filterC (<x)) perm_cat2l -(perm_filterC (>x)) perm_catC.
  apply: perm_cat; apply/permP=>p; rewrite !count_filter; apply: eq_count=>a /=;
  by case: ltgtP=>/= _; rewrite ?andbT ?andbF.
rewrite !select_cat; first last.
- apply/allrelP=>y z; rewrite -Hl -He -Hg mem_cat !mem_filter /= =>/andP [Hyx _] /orP; case; case/andP.
  - by move/eqP=>-> _; apply: ltW.
  by move=>Hxz _; apply/ltW/lt_trans/Hxz.
- apply/allrelP=>y z; rewrite -He -Hg !mem_filter /= =>/andP [/eqP -> _] /andP [Hxz _].
  by apply: ltW.
case: ifP=>// /negbT; rewrite -leNgt=>Hlk.
have {Hlk}Hkm : (k - size ls < size es) = (k < size ls + size es).
- rewrite ltEnat /= -[in LHS](ltn_add2r (size ls)) -addnBn.
  suff : size ls - k = 0 by move=>->; rewrite addn0 addnC.
  by apply/eqP; rewrite subn_eq0.
rewrite Hkm; case: ifP=>// Hkle; rewrite {}Hkle ltEnat /= in Hkm.
rewrite /select.
have /all_pred1P-> : all (pred1 x) (sort <=%O es).
- rewrite (perm_all (s2:=es)); last by rewrite (perm_sort <=%O es).
  by apply/all_filterP; rewrite -He filter_id.
by rewrite size_sort nth_nseq Hkm.
Qed.

Definition median (xs : seq T) : T :=
  select x0 (size xs).-1./2 xs.

Lemma median_mem xs : (0 < size xs)%N -> median xs \in xs.
Proof.
move=>Hn.
have /[dup] H: ((size xs).-1./2 < size xs)%N.
- apply/leq_ltn_trans; first by exact: half_le.
  by rewrite ltn_predL.
move/(selection_mem x0); apply.
by apply: is_selection_select.
Qed.

(* Exercise 3.5 *)

Definition reduce_select_median k xs := xs. (* FIXME *)

Lemma reduce_select_prop k xs : k < size xs ->
  reduce_select_median k xs != [::] /\
  median (reduce_select_median k xs) = select x0 k xs.
Proof.
Admitted.

End DivideAndConquer.

Section MedianOfMedians.

Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys zs : seq T) (k : nat).
Variable x0 : T.

Lemma median_bound xs : (0 < size xs)%N ->
  ((count (< median x0 xs) xs <= (size xs).-1./2) &&
   (count (> median x0 xs) xs <= uphalf (size xs).-1))%N.
Proof.
move=>Hs.
have : ((size xs).-1./2 < size xs)%N.
- apply/leq_ltn_trans; first by exact: half_le.
  by rewrite ltn_predL.
move/(is_selection_select x0)=>/andP [->].
set n := size xs in Hs *.
rewrite (_ : n - (n.-1)./2 = (uphalf n.-1).+1) //.
rewrite -{1}(prednK Hs) -addn1 -addnBAC; last by apply: half_le.
by rewrite half_subn addn1.
Qed.

(* TODO use reshape instead? *)
Equations chop (n : nat) xs : seq (seq T) :=
chop 0 _    => [::];
chop _ [::] => [::];
chop n xs   => take n xs :: chop n (drop n xs).

Lemma chop_nil n : chop n [::] = [::].
Proof. by case: n. Qed.

Lemma chop1 n xs ys : (0 < n)%N -> size xs = n -> chop n (xs ++ ys) = xs :: chop n ys.
Proof.
case: n=>// n _.
case: xs=>//= h t /eqP; rewrite eqSS=>/eqP Hn.
by simp chop=>/=; rewrite take_cat drop_cat Hn ltnn subnn take0 drop0 cats0.
Qed.

Lemma chop_cat n k xs ys :
  (0 < n)%N ->
  size xs = n * k -> chop n (xs++ys) = chop n xs ++ chop n ys.
Proof.
move=>Hn; elim: k xs.
- move=>xs.
  rewrite muln0=>/size0nil->/=.
  by simp chop; rewrite chop_nil.
move=>k IH xs Hx.
rewrite -(cat_take_drop n xs) -catA.
have Ht : size (take n xs) = n.
- rewrite size_take Hx.
  case: {IH Hx}k; first by rewrite muln1 ltnn.
  by move=>k; rewrite -(addn1 k.+1) mulnDr muln1 -{1}(add0n n) ltn_add2r muln_gt0 Hn.
rewrite chop1 // [in RHS]chop1 // (IH (drop n xs)) //.
by rewrite size_drop Hx -addn1 mulnDr muln1 -addnBA // subnn addn0.
Qed.

Lemma chop_ge_length_eq n xs :
  (0 < size xs <= n)%N -> chop n xs = [::xs].
Proof.
case: xs=>//=x xs; case: n=>//= n.
rewrite ltnS=>Hk; simp chop=>/=.
by rewrite take_oversize // drop_oversize.
Qed.

Lemma chop_flattenK n (xs : seq (seq T)) :
  (0 < n)%N -> (forall x, x \in xs -> size x = n) -> chop n (flatten xs) = xs.
Proof.
move=>Hn; elim: xs=>/=; first by rewrite chop_nil.
move=>xs xxs IH H; rewrite chop1 //; last by apply: H; rewrite inE eq_refl.
by rewrite IH // =>x Hx; apply: H; rewrite inE Hx orbT.
Qed.

Lemma chop_flatten_eq n xs :
  0 < n -> xs = flatten (chop n xs).
Proof.
funelim (chop n xs)=>//; simp chop=>/= /H /= {}H.
by rewrite -{1}(cat_take_drop n.+1 (s::l)) /= -cat_cons {1}H.
Qed.

Lemma chop_mem_size n xs s :
  0 < n -> s \in chop n xs ->
  0 < size s <= n.
Proof.
funelim (chop n xs)=>//; simp chop=>/= /(H s0) /= {}H.
rewrite inE=>/orP; case=>// /eqP=>-> /=.
rewrite size_take -/(minn _ _) leEnat ltnS.
by exact: geq_minl.
Qed.

Lemma chop_count_le n xs s a :
  0 < n -> s \in chop n xs ->
  (count a s <= n)%N.
Proof.
move=>Hn Hx.
have/andP [_ H2] := chop_mem_size Hn Hx.
by apply/leq_trans/H2/count_size.
Qed.

Lemma chop_size n xs :
  0 < n -> size (chop n xs) = up_div (size xs) n.
Proof.
funelim (chop n xs)=>// /H /= {H}IH.
case/boolP: (n <= size l)%N; last first.
- rewrite -ltnNge=>Hk; move: (ltn_trans Hk (ltnSn n))=>{}Hk.
  by rewrite chop_ge_length_eq //= up_divS divn_small.
simp chop=>/= Hk; have ->: (size l).+1 = n.+1 + size (drop n l).
- by rewrite -{1}(cat_take_drop n l) size_cat size_takel.
rewrite IH addSn up_divS; congr S.
rewrite divnD // divn_small // modn_small // add0n.
by rewrite -{3}[in RHS](addn0 n) ltn_add2l lt0n.
Qed.

Definition mom xs :=
  median x0 (map (median x0) (chop 5 xs)).

Lemma mom_mem xs : (0 < size xs)%N -> mom xs \in xs.
Proof.
move=>Hn; rewrite /mom.
suff: {subset [seq median x0 i | i <- chop 5 xs] <= xs}.
- apply; apply: median_mem.
  by rewrite size_map chop_size //; apply: up_div_gt0.
move=>_ /mapP /= [s Hs ->].
have H5 : 0 < 5 by [].
case/andP: (chop_mem_size H5 Hs)=>Hs' _.
rewrite (chop_flatten_eq xs H5).
by apply/flattenP; exists s=>//; apply: median_mem.
Qed.

Definition chop_lt xs :=
  filter (fun ys => median x0 ys < mom xs) (chop 5 xs).
Definition chop_gt xs :=
  filter (fun ys => median x0 ys > mom xs) (chop 5 xs).
Definition chop_eq xs :=
  filter (fun ys => median x0 ys == mom xs) (chop 5 xs).

Lemma chops_eq xs :
  perm_eq (chop 5 xs) (chop_lt xs ++ chop_eq xs ++ chop_gt xs).
Proof.
rewrite -(perm_filterC (fun ys => median x0 ys < mom xs)) perm_cat2l
  -(perm_filterC (fun ys => median x0 ys == mom xs)).
apply: perm_cat; apply/permP=>a; rewrite !count_filter; apply: eq_count=>z /=.
- rewrite -leNgt le_eqVlt; case: eqP; last by rewrite andbF.
  by move=>->; rewrite eq_refl ltxx !andbT.
by rewrite -leNgt lt_neqAle eq_sym andbA.
Qed.

Lemma chop_ltgt_bound xs : (0 < size xs)%N ->
  ((size (chop_lt xs) <= (up_div (size xs) 5).-1./2) &&
  (size (chop_gt xs) <= uphalf (up_div (size xs) 5).-1))%N.
Proof.
move=>Hs; rewrite -chop_size // !size_filter /mom.
have : (0 < size (chop 5 xs))%N.
- by rewrite chop_size //; apply: up_div_gt0.
move: (median_bound (xs:=map (median x0) (chop 5 xs))).
by rewrite size_map=>/[apply]/andP []; rewrite !count_map=>->->.
Qed.

Lemma chop_ge_mom_lt xs x :
  x \in chop_eq xs ++ chop_gt xs ->
  (count (< mom xs) x <= 2)%N.
Proof.
rewrite mem_cat !mem_filter -andb_orl =>/andP [Hm Hx].
have/andP [H1 H2] : 0 < size x <= 5 by apply: (chop_mem_size _ Hx).
apply (leq_trans (n:=count (< median x0 x) x)).
- apply: sub_count=>y /= /lt_le_trans; apply.
  by rewrite le_eqVlt eq_sym.
apply: (leq_trans (n:=(size x).-1./2)); first by case/andP: (median_bound H1).
by rewrite (_ : 2 = 5./2) //; apply/half_leq/leq_trans/H2/leq_pred.
Qed.

Lemma chop_le_mom_gt xs x :
  x \in chop_lt xs ++ chop_eq xs ->
  (count (> mom xs) x <= 2)%N.
Proof.
rewrite mem_cat !mem_filter -andb_orl =>/andP [Hm Hx].
have/andP [H1 H2] : 0 < size x <= 5 by apply: (chop_mem_size _ Hx).
apply (leq_trans (n:=count (> median x0 x) x)).
- apply: sub_count=>y /= /le_lt_trans; apply.
  by rewrite le_eqVlt orbC.
apply: (leq_trans (n:=uphalf (size x).-1)); first by case/andP: (median_bound H1).
rewrite (_ : 2 = uphalf (5.-1)) //.
apply: uphalf_leq; rewrite -(leq_add2r 1) !addn1 /=.
by apply/leq_trans/H2; rewrite ltn_predL.
Qed.

Lemma up_div71 n : (0 < n)%N ->
  (3 * ((up_div n 5).-1)./2 + 2 * up_div n 5 <= up_div (7 * n) 10 + 1)%N.
Proof.
move=>Hn.
rewrite up_div_div //=; case: n Hn=>//= n _.
rewrite -(addn1 n) -(addn1 (n %/ 5)) !mulnDr !muln1 addnA.
rewrite up_div_div; last by apply/leq_trans/leq_addl.
rewrite -[X in (_ <= X + 1)%N]addn1 -[X in (_ <= X)%N]addnA leq_add2r.
rewrite -subn1 -addnBA // (_ : 7 - 1 = 6) //.
rewrite divnD // (divn_small (isT : 6 < 10)) (modn_small (isT : 6 < 10)) addn0.
rewrite {2}(_ : 10 = 4 + 6) // leq_add2r -divn2.
case: (edivnP n 5)=>/= q r {n}-> Hr; rewrite divnMDl // (divn_small Hr) addn0.
rewrite (_ : 10 = 2 * 5) // mulnDr mulnA divnD // modnD // divnMr // -muln_modl.
case: (edivnP q 2)=>/= u v {q}-> Hv; rewrite divnMDl // (divn_small Hv) addn0.
rewrite (mulnC 2 5) // !mulnDr !mulnA divnD // modnD // mulnK // modnMl add0n.
rewrite (_ : 5 * 2 = 10) // addnA mulnAC -mulnDl (_ : 3+2*2 = 7) // -4!addnA.
by rewrite {u}leq_add2l; case: v Hv=>//=; case.
Qed.

Lemma up_div73 n : (0 < n)%N ->
  (3 * uphalf (up_div n 5).-1 + 2 * up_div n 5 <= up_div (7 * n) 10 + 3)%N.
Proof.
move=>Hn.
rewrite uphalf_half up_div_div //=; case: n Hn=>//= n _.
rewrite -(addn1 n) -(addn1 (n %/ 5)) !mulnDr !muln1 addnA.
rewrite up_div_div; last by apply/leq_trans/leq_addl.
rewrite -[X in (_ <= X + 3)%N]addn1 -[X in (_ <= X)%N]addnA.
rewrite (_ : 1 + 3 = 2 + 2) // addnA leq_add2r.
rewrite -subn1 -addnBA // (_ : 7 - 1 = 6) //.
rewrite divnD // (divn_small (isT : 6 < 10)) (modn_small (isT : 6 < 10)).
rewrite {2}(_ : 10 = 4 + 6) // leq_add2r -divn2.
case: (edivnP n 5)=>/= q r {n}-> Hr; rewrite divnMDl // (divn_small Hr) !addn0.
rewrite (_ : 10 = 2 * 5) // mulnDr mulnA divnD // modnD // divnMr // -muln_modl.
case: (edivnP q 2)=>/= u v {q}-> Hv; rewrite divnMDl // (divn_small Hv) addn0.
rewrite oddD oddM andbF /= -addnA addnC.
rewrite (mulnC 2 5) // !mulnDr !mulnA divnD // modnD // mulnK // modnMl add0n.
rewrite (_ : 5 * 2 = 10) // addnA mulnAC -mulnDl (_ : 3+2*2 = 7) // -6!addnA.
rewrite {u}leq_add2l; case: v Hv=>//=; case=>//= _.
by rewrite !addnA [X in (_ <= X)%N]addnC.
Qed.

Lemma mom_pivot_bound xs :
  (count (< mom xs) xs <= up_div (7*size xs) 10 + 1) &&
  (count (> mom xs) xs <= up_div (7*size xs) 10 + 3).
Proof.
case/boolP: (size xs == 0); first by move/eqP/size0nil=>->.
rewrite -lt0n =>/[dup] Hs /chop_ltgt_bound/andP [L1 L2].
have Hc := chops_eq xs.
have H1 := perm_map (count (< mom xs)) Hc.
have H2 := perm_map (count (> mom xs)) Hc; rewrite catA in H2.
rewrite {2 5}(chop_flatten_eq xs (isT : 0 < 5)) !count_flatten !sumnE.
rewrite {H1}(perm_big _ H1) {H2}(perm_big _ H2); rewrite perm_sym in Hc.
apply/andP; split; rewrite map_cat big_cat /= !big_map.
- apply/leq_trans/up_div71=>//.
  apply: (leq_trans (n:=5*size (chop_lt xs) + 2*size (chop_eq xs ++ chop_gt xs))).
  - apply: leq_add;
    rewrite -iter_addn_0 -count_predT -big_const_seq
      big_seq_cond [X in (_ <= X)%N]big_seq_cond;
    apply: leq_sum=>i; rewrite andbT; last by apply: chop_ge_mom_lt.
    by rewrite mem_filter =>/andP [_] /chop_count_le; apply.
  rewrite {1}(_ : 5 = 3 + 2) // mulnDl -addnA -mulnDr size_cat addnA.
  rewrite -!size_cat -catA; rewrite (perm_size Hc) chop_size //.
  by rewrite leq_add2r leq_pmul2l.
apply/leq_trans/up_div73=>//.
apply: (leq_trans (n:=2*size (chop_lt xs ++ chop_eq xs) + 5*size (chop_gt xs))).
- apply: leq_add;
  rewrite -iter_addn_0 -count_predT -big_const_seq
    big_seq_cond [X in (_ <= X)%N]big_seq_cond;
  apply: leq_sum=>i; rewrite andbT; first by apply: chop_le_mom_gt.
  by rewrite mem_filter =>/andP [_] /chop_count_le; apply.
rewrite addnC {1}(_ : 5 = 3 + 2) // mulnDl addnAC -addnA -mulnDr size_cat.
rewrite -!size_cat -catA; rewrite (perm_size Hc) chop_size //.
by rewrite leq_add2r leq_pmul2l.
Qed.

End MedianOfMedians.

Section SelectionInLinearTime.
Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys zs : seq T) (k : nat).
Variable x0 : T.

(* Bove-Capretta method to the rescue *)

Inductive mom_select_grph : nat -> seq T -> T -> Prop :=
| mom_select_gt k xs : size xs <= 20 -> mom_select_grph k xs (select x0 k xs)
| mom_select_le_1 k xs M ls es gs res:
    size xs > 20 ->
    mom_select_grph ((up_div (size xs) 5).-1./2)
                     (map (median x0) (chop 5 xs))
                     M ->
    (ls, es, gs) = partition3 M xs ->
    k < size ls ->
    mom_select_grph k ls res ->
    mom_select_grph k xs res
| mom_select_le_2 k xs M ls es gs :
    size xs > 20 ->
    mom_select_grph ((up_div (size xs) 5).-1./2)
                     (map (median x0) (chop 5 xs))
                     M ->
    (ls, es, gs) = partition3 M xs ->
    size ls <= k < size ls + size es ->
    mom_select_grph k xs M
| mom_select_le_3 k xs M ls es gs res :
    size xs > 20 ->
    mom_select_grph ((up_div (size xs) 5).-1./2)
                     (map (median x0) (chop 5 xs))
                     M ->
    (ls, es, gs) = partition3 M xs ->
    k >= size ls + size es ->
    mom_select_grph (k - size ls - size es) gs res ->
    mom_select_grph k xs res.

Lemma mom_select_spec k xs r : mom_select_grph k xs r -> r = select x0 k xs.
Proof.
elim=>//= {}k {}xs M ls es gs => [res||res] Hs _;
set ms := [seq median _ i | i <- chop 5 xs];
rewrite (_ : up_div (size xs) 5 = size ms); try by [rewrite size_map chop_size];
rewrite -/(median _ ms) -/(mom _ xs)=>->; case=>Hl He Hg Hk;
rewrite (select_recurrence x0 k (mom x0 xs) xs) /= -Hl -He -Hg.
- by move=>_ ->; rewrite Hk.
- by case/andP: Hk; rewrite leNgt=>/negbTE->->.
move=>_->.
have -> : (k < size ls) = false.
- apply/negbTE; rewrite -leNgt; apply/le_trans/Hk.
  by rewrite leEnat; apply: leq_addr.
by move: Hk; rewrite leNgt=>/negbTE->.
Qed.

Equations? mom_select_exists k xs : {t | mom_select_grph k xs t} by wf (size xs) lt :=
mom_select_exists k xs with inspect (20 < size xs) := {
  | true eqn: Hn with mom_select_exists ((up_div (size xs) 5).-1./2)
                                         (map (median x0) (chop 5 xs)) => {
    | @exist M fM with inspect (partition3 M xs) => {
      | (ls, es, gs) eqn: eq with inspect (k < size ls) => {
        | true eqn: Hk1 =>
            let '(exist r fR) := mom_select_exists k ls in
            (exist _ r _)
        | false eqn: Hk1 with inspect (k < size ls + size es) => {
          | true eqn: Hk2 => exist _ M _
          | false eqn: Hk2 =>
              let '(exist r fR) := mom_select_exists (k - size ls - size es) gs in
              (exist _ r _)
    } } } }
  | false eqn: Hn => exist _ (select x0 k xs) _
  }.
Proof.
1,2,5: apply: ssrnat.ltP.
  (* list of chopped medians is smaller than xs *)
- rewrite size_map chop_size //.
  by apply: up_div_lt=>//; apply/ltn_trans/Hn.
  (* ls is smaller than xs *)
- rewrite size_filter (mom_select_spec fM).
  set ms := [seq median _ i | i <- chop 5 xs].
  rewrite (_ : up_div (size xs) 5 = size ms); last by rewrite size_map chop_size.
  rewrite -/(median _ ms) -/(mom _ xs).
  rewrite -(count_predC (< mom x0 xs)) -{1}(addn0 (count _ xs)) ltn_add2l -has_count.
  apply/hasP; exists (mom x0 xs)=>/=; last by rewrite ltxx.
  by apply: mom_mem; apply/ltn_trans/Hn.
  (* gs is smaller than xs *)
- rewrite size_filter (mom_select_spec fM).
  set ms := [seq median _ i | i <- chop 5 xs].
  rewrite (_ : up_div (size xs) 5 = size ms); last by rewrite size_map chop_size.
  rewrite -/(median _ ms) -/(mom _ xs).
  rewrite -(count_predC (> mom x0 xs)) -{1}(addn0 (count _ xs)) ltn_add2l -has_count.
  apply/hasP; exists (mom x0 xs)=>/=; last by rewrite ltxx.
  by apply: mom_mem; apply/ltn_trans/Hn.
  (* recursive call when k < size ls *)
- by apply: (mom_select_le_1 Hn fM _ Hk1 fR).
  (* recursive call when size ls <= k < size ls + size es *)
- apply: (mom_select_le_2 Hn fM)=>//.
  by rewrite Hk2 andbT leNgt Hk1.
  (* recursive call when size ls + size es <= k *)
- apply: (mom_select_le_3 Hn fM)=>//.
  by rewrite leNgt Hk2.
(* size xs <= 20, fall back to select k xs *)
by apply: mom_select_gt; rewrite leNgt Hn.
Defined.

Definition mom_select k xs := sval (mom_select_exists k xs).

Lemma mom_select_correct k xs : mom_select k xs = select x0 k xs.
Proof. by rewrite /mom_select; case: mom_select_exists=>r /= /mom_select_spec. Qed.

Corollary is_selection_mom_select k xs :
  k < size xs -> is_selection (mom_select k xs) k xs.
Proof. by rewrite mom_select_correct; apply: is_selection_select. Qed.

(* Exercise 3.6 *)

End SelectionInLinearTime.

Section TimeFunctions.
Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys zs : seq T) (k : nat).
Variable x0 : T.

(* TODO move to prelude *)
Equations T_nth xs (n : nat) : nat :=
T_nth _         0     => 1;
T_nth [::]      _     => 1;
T_nth (_ :: xs) (S n) => T_nth xs n.

Lemma T_nth_leq xs n : (T_nth xs n <= (size xs).+1)%N.
Proof.
funelim (T_nth xs n)=>//=; simp T_nth=>//.
by apply: (leq_trans H).
Qed.

Fixpoint T_takedrop xs n : nat :=
  if xs is _ :: xs'
    then if n is n'.+1 then (T_takedrop xs' n').+1 else 1
    else 1.

Lemma T_takedrop_comp n xs : T_takedrop xs n = (minn n (size xs)).+1.
Proof.
elim: xs n=>/=[n|_ xs IH n]; first by rewrite minn0.
case: n=>[|n]; first by rewrite !min0n.
by rewrite IH minnSS.
Qed.

Equations T_chop (n : nat) xs : nat :=
T_chop 0 _    => 1;
T_chop _ [::] => 1;
T_chop n xs   => (T_takedrop xs n).*2 + T_chop n (drop n xs) + 1.

Lemma T_chop_leq n xs : (T_chop n xs <= (5 * size xs) + 1)%N.
Proof.
funelim (T_chop n xs)=>//=; simp T_chop=>/=; first by apply: leq_addl.
rewrite /= size_drop mulnBr in H.
rewrite T_takedrop_comp addnAC.
case: (ltnP n (size l))=>Hn; rewrite -addn2 -muln2; last first.
- rewrite drop_oversize //; simp T_chop.
  rewrite mulnC mulnDr -2!addnA (_ : 2*2+(1+1)=6) //.
  by rewrite mulnSr -addnA leq_add2r leq_mul2r orbT.
rewrite -[X in (_ <= X)%N]add0n -{4}(subnn (5*n)) addnA.
rewrite addnBAC // (mulnS 5) [X in (_ <= (X - _) + _)%N]addnA.
rewrite -addnBA; last by rewrite leq_pmul2l // ltnW.
rewrite -[X in (_ <= X)%N]addnA; apply: leq_add=>//.
by rewrite mulnC mulnDr -addnA leq_add2r leq_mul2r orbT.
Qed.

(* TODO this is probably not ideal since we have a naive definition of partition3 via filters *)
Fixpoint T_partition3 xs : nat :=
  if xs is _ :: ys then (T_partition3 ys).+1 else 1.

Lemma T_partition3_eq xs : T_partition3 xs = size xs + 1.
Proof. by elim: xs=>//= _ xs ->. Qed.

(* TODO technically we use mergesort from mathcomp in select *)
Definition T_slow_select k xs : nat :=
  T_isort xs + T_nth (sort <=%O xs) k + 1.

Lemma T_slow_select_leq k xs : (T_slow_select k xs <= (size xs)^2 + 3 * size xs + 3)%N.
Proof.
rewrite /T_slow_select {2}(_ : 3 = 2+1) // addnA leq_add2r.
apply: (leq_trans (n:=(size xs).+1 ^2 + (size xs).+1)).
- apply: leq_add; first by exact: T_isort_size.
  by rewrite -(size_sort <=%O); exact: T_nth_leq.
rewrite -addn1 sqrnD muln1 exp1n -3!addnA leq_add2l.
by rewrite addnC addnA -{2}(mul1n (size xs)) -mulnDl -addnA.
Qed.

Definition T_slow_median xs : nat :=
  T_slow_select ((size xs).-1./2) xs + 1.

Lemma T_slow_median_leq xs : (T_slow_median xs <= (size xs)^2 + 3 * size xs + 4)%N.
Proof.
rewrite /T_slow_median (_ : 4 = 3+1) // addnA leq_add2r.
by apply: T_slow_select_leq.
Qed.

Equations? T_mom_select (k : nat) xs : nat by wf (size xs) lt :=
T_mom_select k xs with inspect (20 < size xs)%N => {
  | true eqn: Hn with inspect (chop 5 xs) => {
    | xss eqn: Hx with inspect (map (median x0) xss) => {
      | ms eqn: Hm with inspect (((size xs + 4) %/ 5).-1./2) => {
        | idx eqn: Hi with inspect (partition3 (mom_select x0 idx ms) xs) := {
          | (ls, es, gs) eqn: H2 =>
             T_mom_select idx ms + T_chop 5 xs + T_mapfilter T_slow_median xss +
             T_partition3 xs + size ls + size es + 3 +
             (if k < size ls then T_mom_select k ls
                else if k < size ls + size es then 0
                       else T_mom_select (k - size ls - size es) gs)
        }}}}
  | false eqn: Hn => T_slow_select k xs
  }.
Proof.
all: apply: ssrnat.ltP.
  (* xss is smaller than xs *)
- rewrite size_map chop_size //.
  by apply: up_div_lt=>//; apply/ltn_trans/Hn.
  (* ls is smaller than xs *)
- rewrite size_filter mom_select_correct.
  set ms := [seq median _ i | i <- chop 5 xs].
  rewrite (_ : (size xs + 4) %/ 5 = size ms); last first.
  - by rewrite size_map chop_size // up_div_divDP.
  rewrite -/(median _ ms) -/(mom _ xs).
  rewrite -(count_predC (< mom x0 xs)) -{1}(addn0 (count _ xs)) ltn_add2l -has_count.
  apply/hasP; exists (mom x0 xs)=>/=; last by rewrite ltxx.
  by apply: mom_mem; apply/ltn_trans/Hn.
  (* gs is smaller than xs *)
rewrite size_filter mom_select_correct.
set ms := [seq median _ i | i <- chop 5 xs].
rewrite (_ : (size xs + 4) %/ 5 = size ms); last first.
- by rewrite size_map chop_size // up_div_divDP.
rewrite -/(median _ ms) -/(mom _ xs).
rewrite -(count_predC (> mom x0 xs)) -{1}(addn0 (count _ xs)) ltn_add2l -has_count.
apply/hasP; exists (mom x0 xs)=>/=; last by rewrite ltxx.
by apply: mom_mem; apply/ltn_trans/Hn.
Defined.

(* We get a slightly different bounding function:
   the book has .. +17*n + 50. This shouldn't change the result.
  *)
Equations? T_mom_select_upper (n : nat) : nat by wf n lt :=
T_mom_select_upper n with inspect (20 < n)%N => {
  | true eqn: H => T_mom_select_upper (up_div n 5) +
                   T_mom_select_upper (up_div (7*n) 10 + 3) + 16*n + 51
  | false eqn: H => 463
}.
Proof.
all: apply: ssrnat.ltP.
- by apply: up_div_lt=>//; apply/ltn_trans/H.
have {H}Hn : n = n-21+21 by rewrite addnBAC // addnK.
rewrite {}Hn; set m := n-21.
rewrite {2}(_ : 21 = 18+3) // mulnDr addnA ltn_add2r.
rewrite (_ : 7*21 = 146+1) // addnA addn1 up_divS.
rewrite divnD // (_ : 146%/10 = 14) // (_ : 146%%10 = 6) //.
rewrite {3}(_ : 9 = 3+6) // ltn_add2r addnAC -[X in (X < _)%N]addn1.
rewrite -addnA (_ : 14+1 = 15) // (_ : 18 = 3+15) // addnA ltn_add2r.
case: (edivnP m 10)=>q r -> /= Hr.
rewrite mulnDr mulnA divnMDl // modnMDl (mulnC _ 10).
rewrite {3}(_ : 10 = 7+3) // mulnDl -3!addnA ltn_add2l.
apply: (leq_trans (n:=r+3)); last by apply: leq_addl.
by do 10!(case: r Hr=>//= r Hr).
Defined.

(* TODO prove via homo_leq? *)
Lemma T_mom_select_upper_mono :
  {homo T_mom_select_upper : n m / (n <= m)%N}.
Proof.
move=>n m Hnm.
funelim (T_mom_select_upper n); funelim (T_mom_select_upper m)=>//; first 1 last.
- move/negbT: {H0}H; rewrite -leqNgt=>H.
  by move: (leq_ltn_trans H H1); rewrite ltnNge Hnm.
- rewrite -2!addnA; apply/leq_trans/leq_addr.
  by apply: (H0 0 _ _ (up_div n 5)).
rewrite leq_add2r; apply: leq_add; last by rewrite leq_pmul2l.
apply: leq_add.
- by apply/H4/leq_up_div2r.
apply/H5; rewrite leq_add2r.
by apply: leq_up_div2r; rewrite leq_pmul2l.
Qed.

Lemma T_mom_select_bound k xs :
  (T_mom_select k xs <= T_mom_select_upper (size xs))%N.
Proof.
apply_funelim (T_mom_select k xs).
- move=>{}k {}xs Hn _.
  funelim (T_mom_select_upper (size xs)); first by rewrite H in Hn.
  apply: leq_trans; first by exact: T_slow_select_leq.
  move/negbT: Hn; rewrite -ltnNge ltnS => Hn.
  rewrite (_ : 463 = 460+3) // leq_add2r (_ : 460 = 20^2+3*20) //.
  by apply: leq_add; [rewrite leq_sqr | rewrite leq_pmul2l].
move=>{}k {}xs idx Hi xss ms ls es gs H2 Hm Hx Hn Hi1 Hi2 Hi3 _ _ _ _ _.
funelim (T_mom_select_upper (size xs)); last by rewrite H in Hn.
clear H H0 H1 H2.
set xss := chop 5 xs in Hi1 Hi2 Hi3 *.
set ms := map (median x0) xss in Hi1 Hi2 Hi3 *.
set idx := (((size xs + 4) %/ 5).-1./2) in Hi1 Hi2 Hi3 *.
set ls := [seq x <- xs | (< mom_select x0 idx ms) x] in Hi2 Hi3 *.
set es := [seq x <- xs | pred1 (mom_select x0 idx ms) x] in Hi3 *.
set gs := [seq x <- xs | mom_select x0 idx ms < x] in Hi3 *.
rewrite size_map chop_size // in Hi1; rewrite -8!addnA; apply: leq_add=>//.
rewrite (_ : 16*size xs + 51 = (5*size xs + 1) + (11*size xs + 50)); last first.
- rewrite {1}(_ : 16 = 5+11) // mulnDl addnAC (_ : 51 = 1+50) //.
  by rewrite addnA -addnA (addnC _ 50).
rewrite [X in (_ <= X)%N]addnC -[X in (_ <= X)%N]addnA.
apply: leq_add; first by exact: T_chop_leq.
rewrite T_partition3_eq !addnA; apply: leq_add; last first.
- have /andP [Hl Hg] := (mom_pivot_bound x0 xs).
  have Hms : (size xs + 4) %/ 5 = size ms.
  - by rewrite size_map chop_size // up_div_divDP.
  case: ifP=>Hk.
  - apply/(leq_trans Hi2)/T_mom_select_upper_mono.
    rewrite size_filter mom_select_correct /idx Hms
      -/(median _ ms) -/(mom _ xs).
    by apply/(leq_trans Hl); rewrite leq_add2l.
  case: ifP=>// Hk2.
  apply/(leq_trans Hi3)/T_mom_select_upper_mono.
  by rewrite size_filter mom_select_correct /idx Hms.
rewrite T_mapfilter_size chop_size // -5!addnA.
have Hs: (\sum_(x <- xss) T_slow_median x <= 44 * up_div (size xs) 5)%N.
- rewrite -chop_size // -/xss -sumn_nseq sumnE big_nseq -count_predT -big_const_seq /=.
  rewrite !big_seq; apply: leq_sum=>/= i Hi.
  case/andP: (chop_mem_size (isT : 0 < 5) Hi)=>Hs1 Hs2.
  apply: leq_trans; first by exact: T_slow_median_leq.
  rewrite (_ : 44 = 40+4) // leq_add2r (_ : 40 = 5^2+3*5) //.
  by apply: leq_add; [rewrite leq_exp2r | rewrite leq_pmul2l].
apply: (leq_trans (n:=45*up_div (size xs) 5 + 2*size xs + 5)).
- rewrite -[X in (_ <= X)%N]addnA; apply: leq_add.
  - by rewrite (_ : 45 = 44+1) // mulnDl mul1n leq_add2r.
  rewrite addnC mul2n -addnn -!addnA (_ : 3+1 = 4) // leq_add2l.
  rewrite addnC -!addnA (_ : 4+1 = 5) // addnA leq_add2r.
  rewrite !size_filter -count_predUI addnC /=.
  suff : (count (predI (<%O^~ (mom_select x0 idx ms)) (eq_op^~ (mom_select x0 idx ms))) xs = 0%N).
  - by move=>->; rewrite add0n; apply: count_size.
  rewrite -(count_pred0 xs); apply: eq_count=>x /=.
  by rewrite lt_neqAle andbC andbA andbN.
rewrite (_ : 50 = 45+5) // addnA leq_add2r [X in (_ <= X)%N]addnC.
rewrite {3}(_ : 11 = 9+2) // mulnDl addnA leq_add2r.
rewrite (_ : 45=9*5) // mulnAC -mulnA; apply: (leq_trans (n:=9 * (size xs + 5))).
- rewrite leq_pmul2l //; apply: leq_up_div.
by rewrite mulnDr addnC.
Qed.

(* Exercise 3.7 *)

Definition f (n : nat) : seq nat := [::]. (* FIXME *)

Lemma f_increasing n : (size (f n) < size (f n.+1))%N.
Proof.
Admitted.

Lemma f_property n : (10 * count (> mom 0%N (f n)) (f n) > 7 * size (f n))%N.
Proof.
Admitted.

End TimeFunctions.

Section AkraBazziLight.

(* TODO *)

(* Exercise 3.8 *)

End AkraBazziLight.
