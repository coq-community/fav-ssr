From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path order.
From favssr Require Import prelude.

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
  - by move: (order_path_min le_trans Hp).
  by move=>z /=; rewrite implybF leNgt.
rewrite ltnS=>Hk.
move: Hp; rewrite (path_sortedE le_trans)=>/andP [Ha Hs].
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
Proof. by apply: (perm_sortP le_total le_trans le_anti). Qed.

Lemma perm_select_eq xs ys k : perm_eq xs ys -> select k xs = select k ys.
Proof. by move=>H; rewrite /select (perm_sort_eq _ ys). Qed.

End Intro.
