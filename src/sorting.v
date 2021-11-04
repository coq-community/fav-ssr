From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path order bigop.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

(* inspect idiom so we can expand let-bound vars in proofs *)

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a erefl.

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

Section InsertionSort.
Context {disp : unit} {T : orderType disp}.

(* Definition *)

Fixpoint insort (x : T) xs :=
  if xs is y :: xs' then
    if x <= y then x :: y :: xs' else y :: insort x xs'
    else [:: x].

Fixpoint isort xs :=
  if xs is x :: xs' then insort x (isort xs') else [::].

(* Functional Correctness *)

Lemma perm_insort x xs : perm_eq (insort x xs) (x :: xs).
Proof.
elim: xs=>//= y xs IH; case: (_ <= _)=>//.
rewrite -(perm_cons y) in IH.
apply: perm_trans; first by exact: IH.
by apply/permP=>/=?; rewrite addnCA.
Qed.

Lemma perm_isort xs : perm_eq (isort xs) xs.
Proof.
elim: xs=>//= x xs IH.
apply: perm_trans; first by apply: perm_insort.
by rewrite perm_cons.
Qed.

Lemma sorted_insort a xs : sorted <=%O (insort a xs) = sorted <=%O xs.
Proof.
elim: xs=>//= x xs IH.
case H: (_ <= _)=>/=; first by rewrite H.
rewrite !path_sortedE; try by exact: le_trans.
rewrite (perm_all _ (perm_insort _ _)) /= IH.
suff: x <= a by move=>->.
by case/orP: (le_total a x)=>//; rewrite H.
Qed.

Lemma sorted_isort xs : sorted <=%O (isort xs).
Proof. by elim: xs=>//= x xs; rewrite sorted_insort. Qed.

(* Time complexity *)

Fixpoint T_insort (x : T) (xs : seq T) : nat :=
  if xs is y :: xs' then
    (if x <= y then 0 else T_insort x xs').+1
    else 1.

Fixpoint T_isort xs : nat :=
  if xs is x :: xs' then (T_isort xs' + T_insort x (isort xs')).+1 else 1.

Lemma T_insort_size x xs : T_insort x xs <= (size xs).+1.
Proof.
elim: xs=>//=y xs IH.
by case: (x <= y).
Qed.

(* This seems to be unused *)
Lemma size_insort x xs: size (insort x xs) = (size xs).+1.
Proof. by move/perm_size: (perm_insort x xs). Qed.

Lemma size_isort xs : size (isort xs) = size xs.
Proof. by move/perm_size: (perm_isort xs). Qed.

Lemma T_isort_size xs : T_isort xs <= (size xs).+1 ^ 2.
Proof.
elim: xs=>// x xs IH.
rewrite -addn1 sqrnD /= -addn1 -!addnA.
apply: leq_add=>//; rewrite exp1n muln1 addnC leq_add2l.
apply: leq_trans; first by exact: T_insort_size.
by rewrite size_isort; apply: leq_pmull.
Qed.

(* Exercise 2.1 *)

Lemma isort_beh (f : seq T -> seq T) xs :
  perm_eq (f xs) xs -> sorted <=%O (f xs) -> f xs = isort xs.
Proof.
Admitted.

(* Exercise 2.2.1 *)

Lemma T_isort_optimal xs : sorted <=%O xs -> T_isort xs = (2 * size xs).+1.
Proof.
Admitted.

End InsertionSort.

Section InsertionSortNat.

(* this might come in handy *)
Lemma uphalf_addn n m : uphalf n + uphalf m = odd n && odd m + uphalf (n + m).
Proof.
rewrite !uphalf_half halfD oddD.
by case: (odd n); case: (odd m)=>//=; rewrite addnCA.
Qed.

(* Exercise 2.2.2 *)
Lemma T_isort_worst n : T_isort (rev (iota 0 n)) = uphalf ((n.+1)*(n.+2)).
Proof.
Admitted.

End InsertionSortNat.

Section QuickSort.
Context {disp : unit} {T : orderType disp}.

(* Definition *)

Equations? quicksort (xs : seq T) : seq T by wf (size xs) lt :=
quicksort [::]    => [::];
quicksort (x::xs) => quicksort (filter (< x) xs) ++ [:: x] ++
                     quicksort (filter (>= x) xs).
Proof.
- by rewrite size_filter /=; apply/ssrnat.ltP/count_size.
by rewrite size_filter /=; apply/ssrnat.ltP/count_size.
Qed.

(* Functional Correctness *)

Lemma perm_quicksort xs : perm_eq (quicksort xs) xs.
Proof.
apply_funelim (quicksort xs)=>//=x {}xs Hl Hg.
rewrite perm_catC cat_cons perm_cons perm_sym -(perm_filterC (>= x)) perm_sym.
apply: perm_cat=>//.
rewrite (eq_in_filter (a2 := < x)) //= =>y _.
by rewrite ltNge.
Qed.

Lemma sorted_quicksort xs : sorted <=%O (quicksort xs).
Proof.
apply_funelim (quicksort xs)=>//= x {}xs Hl Hg.
have Hx : sorted <=%O [:: x] by [].
move: (merge_sorted le_total Hx Hg)=>{Hx}/=.
rewrite allrel_merge; last first.
- by rewrite allrel1l (perm_all _ (perm_quicksort _)) filter_all.
move/(merge_sorted le_total Hl); rewrite allrel_merge //=.
apply/allrelP=>y z.
rewrite (perm_mem (perm_quicksort _) y) inE
  (perm_mem (perm_quicksort _) z) !mem_filter /=.
case/andP=>Hy _; case/orP=>[/eqP ->|/andP [Hz _]];
rewrite le_eqVlt; apply/orP; right=>//.
by apply/lt_le_trans/Hz.
Qed.

(* Exercise 2.3 *)

Equations? quicksort2 (xs ys : seq T) : seq T by wf (size xs) lt :=
quicksort2 xs ys => ys. (* FIXME *)
Proof.
Qed.

Lemma quick2_quick xs ys : quicksort2 xs ys = quicksort xs ++ ys.
Proof.
Admitted.

(* Exercise 2.4 *)

Definition partition3 (x : T) (xs : seq T) : seq T * seq T * seq T :=
  (filter (< x) xs, filter (pred1 x) xs, filter (> x) xs).

Equations? quicksort3 (xs : seq T) : seq T by wf (size xs) lt :=
quicksort3 [::]    => [::];
quicksort3 (x::xs) with inspect (partition3 x xs) => {
  | (ls, es, gs) eqn: eq => quicksort3 ls ++ x :: es ++ quicksort3 gs
}.
Proof.
- by apply/ssrnat.ltP; rewrite size_filter; apply: count_size.
by apply/ssrnat.ltP; rewrite size_filter; apply: count_size.
Qed.

(* this is the main part *)
Lemma quick_filter_ge x xs :
  quicksort (filter (>= x) xs) = filter (pred1 x) xs ++ quicksort (filter (> x) xs).
Proof.
Admitted.

Lemma quick3_quick xs : quicksort3 xs = quicksort xs.
Proof.
Admitted.

(* Exercise 2.5.1 *)

Fixpoint T_filter {A} (ta : A -> nat) (s : seq A) : nat :=
  if s is x :: s' then ta x + T_filter ta s' + 1 else 1.

Lemma T_filter_size {A} (xs : seq A) ta :
  T_filter ta xs = \sum_(x<-xs) (ta x) + size xs + 1.
Proof.
elim: xs=>/=; first by rewrite big_nil.
by move=>x xs ->; rewrite big_cons -(addn1 (size _)) !addnA.
Qed.

Equations? T_quicksort (xs : seq T) : nat by wf (size xs) lt :=
T_quicksort [::]    => 1;
T_quicksort (x::xs) => T_quicksort (filter (< x) xs) +
                       T_quicksort (filter (>= x) xs) +
                       2 * T_filter (fun => 1%N) xs + 1.
Proof.
- by apply/ssrnat.ltP; rewrite size_filter; apply: count_size.
by apply/ssrnat.ltP; rewrite size_filter; apply: count_size.
Qed.

(* FIXME replace these with concrete numbers *)
Parameters (a b c : nat).

Lemma quicksort_quadratic xs : sorted <=%O xs -> T_quicksort xs = a * size xs ^ 2 + b * size xs + c.
Proof.
Admitted.

(* Exercise 2.5.2 *)

Lemma quicksort_worst xs : T_quicksort xs <= a * size xs ^ 2 + b * size xs + c.
Proof.
Admitted.

End QuickSort.

Section TopDownMergeSort.
Context {disp : unit} {T : orderType disp}.

(* reusing `merge` from mathcomp.path *)

Lemma half_le n : (n./2 <= n)%N.
Proof.
elim: n=>//= n IH; rewrite uphalf_half -addn1 (addnC _ 1%N).
by apply: leq_add=>//; apply: leq_b1.
Qed.

Equations? msort (xs : seq T) : seq T by wf (size xs) lt :=
msort [::]  => [::];
msort [::x] => [::x];
msort xs    => let n := size xs in
               merge <=%O (msort (take n./2 xs))
                          (msort (drop n./2 xs)).
Proof.
- by apply/ssrnat.ltP; rewrite size_take /= !ltnS !half_le.
by apply/ssrnat.ltP; rewrite size_drop /= /leq subSS subnAC subnn.
Qed.

(* Functional Correctness *)

Lemma perm_msort xs : perm_eq (msort xs) xs.
Proof.
funelim (msort xs)=>//=.
rewrite perm_merge -{3}(cat_take_drop (size l)./2 (s0::l)) -cat_cons.
by apply: perm_cat.
Qed.

Lemma sorted_msort xs : sorted <=%O (msort xs).
Proof. by funelim (msort xs)=>//=; apply: merge_sorted. Qed.

(* Running Time Analysis *)

Fixpoint C_merge (s1 : seq T) :=
  if s1 is x1 :: s1' then
    let fix C_merge_s1 (s2 : seq T) :=
      if s2 is x2 :: s2' then
        (if x1 <= x2 then C_merge s1' s2 else C_merge_s1 s2').+1
      else 0 in
    C_merge_s1
  else fun => 0.

Equations? C_msort (xs : seq T) : nat by wf (size xs) lt :=
C_msort [::]  => 0;
C_msort [::x] => 0;
C_msort xs    => let n := (size xs) in
                 let ys := take n./2 xs in
                 let zs := drop n./2 xs in
                 C_msort ys + C_msort zs + C_merge (msort ys) (msort zs).
Proof.
- by apply/ssrnat.ltP; rewrite size_take /= !ltnS !half_le.
by apply/ssrnat.ltP; rewrite size_drop /= /leq subSS subnAC subnn.
Qed.

Lemma C_merge_leq xs ys : (C_merge xs ys <= size xs + size ys)%N.
Proof.
elim: xs ys=>//= x xs IH1; elim=>//= y ys IH2.
case: ifP=>_.
- rewrite -addn1 -!(addn1 (size _)) addnA leq_add2r addnAC.
  apply: leq_trans; first by apply: IH1.
  by rewrite addn1 addnS.
by rewrite addnS ltnS; apply: IH2.
Qed.

Lemma size1 {A} (xs : seq A) : size xs = 1%N -> {x : A | xs = [::x]}.
Proof. by case: xs=>// x; case=>//= _; exists x. Qed.

Lemma size_gt {A} (xs : seq A) : (size xs > 1)%N -> {x : A & {y : A & {ys : seq A & xs = [:: x, y & ys]}}}.
Proof. by case: xs=>// x; case=>//= y ys _; exists x,y,ys. Qed.

Lemma half_subn n : n - n./2 = uphalf n.
Proof.
have {1}-> : n = n./2 + uphalf n by rewrite uphalf_half addnCA addnn odd_double_half.
by rewrite -addnBAC // subnn.
Qed.

Lemma C_msort_leq xs k: size xs = 2^k -> (C_msort xs <= k * 2^k)%N.
Proof.
elim: k xs=>/=.
- by move=>xs; rewrite expn0 =>/size1 [x] ->; simp C_msort.
move=>k IH xs H.
have Hs1 : (size xs > 1)%N by rewrite H -{1}(expn0 2); apply: ltn_exp2l.
case: (size_gt _ Hs1)=> x[y][ys] He; rewrite He /= in H *; simp C_msort=>/=.
have Hp : (size ys)./2.+1 = ((size ys).+2)./2 by rewrite -addn2 halfD andbF /= addn1.
have Ht : size (x :: take (size ys)./2 (y :: ys)) = 2^k.
- by rewrite /= size_take /= ltnS half_le Hp H expnS mul2n half_double.
have Hd : size (drop (size ys)./2 (y :: ys)) = 2^k.
- rewrite size_drop /= subSn; last by apply: half_le.
  rewrite half_subn uphalf_half -addnS Hp H expnS mul2n half_double.
  have -> : odd (size ys) = odd (size ys).+2 by rewrite -addn2 oddD addbF.
  by rewrite H oddX.
apply: leq_trans;
  first by exact: (leq_add (leq_add (IH _ Ht) (IH _ Hd)) (C_merge_leq _ _)).
rewrite !(perm_size (perm_msort _)) Ht Hd.
by rewrite !addnn -!muln2 -mulnA -!expnSr -{3}(addn1 k) mulnDl mul1n.
Qed.

(* Exercise 2.6 *)

Fixpoint halve {A: Type} (xs ys zs : seq A) : seq A * seq A :=
  ([::],[::]). (* FIXME *)

Equations? msort2 (xs : seq T) : seq T by wf (size xs) lt :=
msort2 [::]  => [::];
msort2 [::x] => [::x];
msort2 xs with inspect (halve xs [::] [::]) := {
  | (ys1, ys2) eqn: eq => merge <=%O (msort2 ys1) (msort2 ys2)
}.
Proof.
(* FIXME *)
- by apply/ssrnat.ltP.
by apply/ssrnat.ltP.
Qed.

Lemma perm_msort2 xs : perm_eq (msort2 xs) xs.
Proof.
Admitted.

Lemma sorted_msort2 xs : sorted <=%O (msort2 xs).
Proof.
Admitted.

End TopDownMergeSort.

Section BottomUpMergeSort.
Context {disp : unit} {T : orderType disp}.

Equations merge_adj (xss : seq (seq T)) : seq (seq T) :=
merge_adj [::]          => [::];
merge_adj [::xs]        => [::xs];
merge_adj (xs::ys::zss) => merge <=%O xs ys :: merge_adj zss.

Lemma size_merge_adj xss : size (merge_adj xss) = uphalf (size xss).
Proof. by funelim (merge_adj xss)=>//=; congr S. Qed.

Lemma uphalf_le n : (uphalf n <= n)%N.
Proof. by case: n=>//= n; rewrite ltnS; apply: half_le. Qed.

Equations? merge_all (xss : seq (seq T)) : seq T by wf (size xss) lt :=
merge_all [::]   => [::];
merge_all [::xs] => xs;
merge_all xss    => merge_all (merge_adj xss).
Proof.
by apply/ssrnat.ltP; rewrite size_merge_adj /= !ltnS; apply: uphalf_le.
Qed.

Definition msort_bu (xs : seq T) : seq T :=
  merge_all (map (fun x => [::x]) xs).

(* Functional Correctness *)

Lemma perm_merge_adj xss : perm_eq (flatten (merge_adj xss)) (flatten xss).
Proof.
funelim (merge_adj xss)=>//=.
rewrite catA; apply: perm_cat=>//.
by rewrite perm_merge.
Qed.

Lemma perm_merge_all xss : perm_eq (merge_all xss) (flatten xss).
Proof.
funelim (merge_all xss)=>//=; first by rewrite cats0.
by apply/(perm_trans H)/perm_merge_adj.
Qed.

Lemma perm_msort_bu xs : perm_eq (msort_bu xs) xs.
Proof.
rewrite /msort_bu; apply: (perm_trans (perm_merge_all _)).
by rewrite flatten_map1 map_id.
Qed.

Lemma sorted_merge_adj xss :
  all (sorted <=%O) xss -> all (sorted <=%O) (merge_adj xss).
Proof.
funelim (merge_adj xss)=>//= /and3P [Hs1 Hs2] /H ->; rewrite andbT.
by apply: merge_sorted.
Qed.

Lemma sorted_merge_all xss :
  all (sorted <=%O) xss -> sorted <=%O (merge_all xss).
Proof.
funelim (merge_all xss)=>//=; first by rewrite andbT.
move: H; simp merge_adj=>/= H.
case/and3P=>Hs1 Hs2 Hs; apply/H/andP.
by split; [apply: merge_sorted | apply: sorted_merge_adj].
Qed.

Lemma sorted_msort_bu xs : sorted <=%O (msort_bu xs).
Proof.
rewrite /msort_bu; apply: sorted_merge_all; rewrite all_map.
by elim: xs.
Qed.

(* Running Time Analysis *)

End BottomUpMergeSort.
