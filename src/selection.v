From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path order ssrnum ssralg ssrint.
From favssr Require Import prelude.
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
Proof. by rewrite /select => /perm_sort_eq ->. Qed.

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
