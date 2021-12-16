From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path order bigop div ssrnum ssralg ssrint.
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
  { z | let xs' := set_nth x0 xs i z in
        uniq xs' /\ select x0 k xs' != select x0 k xs }.
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
Proof.
move=>Ha; rewrite /select.
have -> : sort <=%O (ys ++ zs) = sort <=%O ys ++ sort <=%O zs.
- apply: le_sorted_eq=>//; last first.
  - by rewrite perm_sort; apply: perm_cat; rewrite perm_sym perm_sort.
  rewrite -(allrel_merge (leT := <=%O)).
  - by apply: (merge_sorted le_total); exact: sort_le_sorted.
  by apply/allrelP=>y z; rewrite !mem_sort=>Hy Hz; move/allrelP: Ha; apply.
by rewrite nth_cat size_sort.
Qed.

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
  apply: perm_cat; apply/permP=>p; rewrite !count_filter; apply: eq_count=>a /=.
  - by rewrite -!leNgt -andbA -eq_le.
  by case: (p a)=>//=; rewrite -leNgt le_eqVlt; case: leP=>//= _; rewrite orbT.
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
rewrite Hkm; case: ifP=>// Hkle; rewrite /select.
have /all_pred1P-> : all (pred1 x) (sort <=%O es).
- rewrite (perm_all (s2:=es)); last by rewrite (perm_sort <=%O es).
  by rewrite -He all_filter; apply/allP=>y _ /=; apply/implyP.
rewrite {}Hkle ltEnat /= in Hkm.
by rewrite nth_nseq size_sort Hkm.
Qed.

Definition median (xs : seq T) : T :=
  select x0 (size xs).-1./2 xs.

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

Equations chop (n : nat) (xs : seq T) : seq (seq T) :=
chop 0 _    => [::];
chop _ [::] => [::];
chop n xs   => take n xs :: chop n (drop n xs).

Lemma chop_ge_length_eq n xs : (0 < size xs <= n)%N -> chop n xs = [::xs].
Proof.
case: xs=>//=x xs; case: n=>//= n.
rewrite ltnS=>Hk; simp chop=>/=.
by rewrite take_oversize // drop_oversize.
Qed.

Lemma chop_flatten_eq n xs : 0 < n -> xs = flatten (chop n xs).
Proof.
funelim (chop n xs)=>//; simp chop=>/= /H /= {}H.
by rewrite -{1}(cat_take_drop n.+1 (s::l)) /= -cat_cons {1}H.
Qed.

Lemma chop_mem_size n xs s : 0 < n -> s \in chop n xs -> 0 < size s <= n.
Proof.
funelim (chop n xs)=>//; simp chop=>/= /(H s0) /= {}H.
rewrite inE=>/orP; case=>// /eqP=>-> /=.
rewrite size_take -/(minn _ _) leEnat ltnS.
by exact: geq_minl.
Qed.

Lemma chop_count_le n xs s a : 0 < n -> s \in chop n xs -> (count a s <= n)%N.
Proof.
move=>Hn Hx.
have/andP [_ H2] := chop_mem_size Hn Hx.
by apply/leq_trans/H2/count_size.
Qed.

Lemma chop_size n xs : 0 < n -> size (chop n xs) = div_up (size xs) n.
Proof.
funelim (chop n xs)=>// /H /= {H}IH.
case/boolP: (n <= size l)%N; last first.
- rewrite -ltnNge=>Hk; move: (ltn_trans Hk (ltnSn n))=>{}Hk.
  by rewrite chop_ge_length_eq //= div_upS // divn_small.
simp chop=>/= Hk; have ->: (size l).+1 = n.+1 + size (drop n l).
- by rewrite -{1}(cat_take_drop n l) size_cat size_takel.
rewrite IH addSn div_upS //; congr S.
rewrite divnD // divn_small // modn_small // add0n.
by rewrite -{3}[in RHS](addn0 n) ltn_add2l lt0n.
Qed.

Definition mom xs := median x0 (map (median x0) (chop 5 xs)).

Definition chop_lt xs :=
  filter (fun ys => median x0 ys < mom xs) (chop 5 xs).
Definition chop_gt xs :=
  filter (fun ys => median x0 ys > mom xs) (chop 5 xs).
Definition chop_eq xs :=
  filter (fun ys => median x0 ys == mom xs) (chop 5 xs).

Lemma chops_eq xs : perm_eq (chop 5 xs) (chop_lt xs ++ chop_eq xs ++ chop_gt xs).
Proof.
rewrite -(perm_filterC (fun ys => median x0 ys < mom xs)) perm_cat2l
  -(perm_filterC (fun ys => median x0 ys == mom xs)).
apply: perm_cat; apply/permP=>a; rewrite !count_filter; apply: eq_count=>z /=.
- rewrite -leNgt le_eqVlt; case: eqP; last by rewrite andbF.
  by move=>->; rewrite eq_refl ltxx !andbT.
by rewrite -leNgt lt_neqAle eq_sym andbA.
Qed.

Lemma chop_ltgt_bound xs : (0 < size xs)%N ->
  ((size (chop_lt xs) <= (div_up (size xs) 5).-1./2) &&
   (size (chop_gt xs) <= uphalf (div_up (size xs) 5).-1))%N.
Proof.
move=>Hs; rewrite -chop_size // !size_filter /mom.
have : (0 < size (chop 5 xs))%N.
- by rewrite chop_size //; apply: div_up_gt0.
move: (median_bound (xs:=map (median x0) (chop 5 xs))).
by rewrite size_map=>/[apply]/andP []; rewrite !count_map=>->->.
Qed.

Lemma chop_ge_mom_lt xs x : x \in chop_eq xs ++ chop_gt xs -> (count (< mom xs) x <= 2)%N.
Proof.
rewrite mem_cat !mem_filter -andb_orl =>/andP [Hm Hx].
have/andP [H1 H2] : 0 < size x <= 5 by apply: (chop_mem_size _ Hx).
apply (leq_trans (n:=count (< median x0 x) x)).
- apply: sub_count=>y /= /lt_le_trans; apply.
  by rewrite le_eqVlt eq_sym.
apply: (leq_trans (n:=(size x).-1./2)); first by case/andP: (median_bound H1).
by rewrite (_ : 2 = 5./2) //; apply/half_leq/leq_trans/H2/leq_pred.
Qed.

Lemma chop_le_mom_gt xs x : x \in chop_lt xs ++ chop_eq xs -> (count (> mom xs) x <= 2)%N.
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

Lemma div_up71 n : (0 < n)%N ->
  (3 * ((div_up n 5).-1)./2 + 2 * div_up n 5 <= div_up (7 * n) 10 + 1)%N.
Proof.
move=>Hn.
rewrite div_up_div //=; case: n Hn=>//= n _.
rewrite -(addn1 n) -(addn1 (n %/ 5)) !mulnDr !muln1 addnA.
rewrite div_up_div; last by apply/ltn_leq_trans/leq_addl.
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

Lemma div_up73 n : (0 < n)%N ->
  (3 * uphalf (div_up n 5).-1 + 2 * div_up n 5 <= div_up (7 * n) 10 + 3)%N.
Proof.
move=>Hn.
rewrite uphalf_half div_up_div //=; case: n Hn=>//= n _.
rewrite -(addn1 n) -(addn1 (n %/ 5)) !mulnDr !muln1 addnA.
rewrite div_up_div; last by apply/ltn_leq_trans/leq_addl.
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

Lemma mom_pivot_bound_lt xs : count (< mom xs) xs <= div_up (7*size xs) 10 + 1.
Proof.
rewrite {2}(chop_flatten_eq xs (isT : 0 < 5)) count_flatten sumnE.
have Hc := chops_eq xs.
have H := perm_map (count (< mom xs)) Hc; rewrite perm_sym in Hc.
rewrite {H}(perm_big _ H) map_cat big_cat /= !big_map.
apply: (leq_trans (n:=5*size (chop_lt xs) + 2*size (chop_eq xs ++ chop_gt xs))).
- apply: leq_add;
  rewrite -iter_addn_0 -count_predT -big_const_seq
  big_seq_cond [X in (_ <= X)%N]big_seq_cond;
  apply: leq_sum=>i; rewrite andbT; last by apply: chop_ge_mom_lt.
  by rewrite mem_filter =>/andP [_] /chop_count_le; apply.
rewrite {1}(_ : 5 = 3 + 2) // mulnDl -addnA -mulnDr size_cat addnA.
rewrite -!size_cat -catA; rewrite (perm_size Hc) chop_size //.
case/boolP: (size xs == 0); first by move/eqP/size0nil=>->.
rewrite -lt0n =>/[dup] Hs /chop_ltgt_bound/andP [+ _].
set n := size xs in Hs *.
rewrite -(leq_pmul2l (isT : 0 < 3))
  -(@leq_add2r (2 * div_up n 5))=>/leq_trans; apply.
by apply: div_up71.
Qed.

Lemma mom_pivot_bound_gt xs : count (> mom xs) xs <= div_up (7*size xs) 10 + 3.
Proof.
rewrite {2}(chop_flatten_eq xs (isT : 0 < 5)) count_flatten sumnE.
have Hc := chops_eq xs.
have H := perm_map (count (> mom xs)) Hc; rewrite perm_sym in Hc.
rewrite {H}(perm_big _ H) catA map_cat big_cat /= !big_map.
apply: (leq_trans (n:=2*size (chop_lt xs ++ chop_eq xs) + 5*size (chop_gt xs))).
- apply: leq_add;
  rewrite -iter_addn_0 -count_predT -big_const_seq
    big_seq_cond [X in (_ <= X)%N]big_seq_cond;
  apply: leq_sum=>i; rewrite andbT; first by apply: chop_le_mom_gt.
  by rewrite mem_filter =>/andP [_] /chop_count_le; apply.
rewrite addnC {1}(_ : 5 = 3 + 2) // mulnDl addnAC -addnA -mulnDr size_cat.
rewrite -!size_cat -catA; rewrite (perm_size Hc) chop_size //.
case/boolP: (size xs == 0); first by move/eqP/size0nil=>->.
rewrite -lt0n =>/[dup] Hs /chop_ltgt_bound/andP [_].
set n := size xs in Hs *.
rewrite -(leq_pmul2l (isT : 0 < 3))
  -(@leq_add2r (2 * div_up n 5))=>/leq_trans; apply.
by apply: div_up73.
Qed.

End MedianOfMedians.
