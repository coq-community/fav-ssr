From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path order bigop prime.
From favssr Require Import prelude.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section InsertionSort.
Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys : seq T).

(* Definition *)

Fixpoint insort x xs :=
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
rewrite !le_path_sortedE (perm_all _ (perm_insort _ _)) /= IH.
suff: x <= a by move=>->.
by rewrite leNgt lt_neqAle H andbF.
Qed.

Lemma sorted_isort xs : sorted <=%O (isort xs).
Proof. by elim: xs=>//= x xs; rewrite sorted_insort. Qed.

(* Time complexity *)

Fixpoint T_insort x xs : nat :=
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
Lemma size_insort x xs : size (insort x xs) = (size xs).+1.
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

(* uphalf_addn from prelude might come in handy here *)
(* Exercise 2.2.2 *)
Lemma T_isort_worst n : T_isort (rev (iota 0 n)) = uphalf ((n.+1)*(n.+2)).
Proof.
Admitted.

End InsertionSortNat.

Section QuickSort.
Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys : seq T).

(* Definition *)

Equations? quicksort xs : seq T by wf (size xs) lt :=
quicksort [::]    => [::];
quicksort (x::xs) => quicksort (filter (< x) xs) ++ [:: x] ++
                     quicksort (filter (>= x) xs).
Proof. all: by rewrite size_filter /=; apply/ssrnat.ltP/count_size. Qed.

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

Equations? quicksort2 xs ys : seq T by wf (size xs) lt :=
quicksort2 xs ys => ys. (* FIXME *)
Proof.
Qed.

Lemma quick2_quick xs ys : quicksort2 xs ys = quicksort xs ++ ys.
Proof.
Admitted.

(* Exercise 2.4 *)

(* TODO rewrite in one pass? *)
Definition partition3 x xs : seq T * seq T * seq T :=
  (filter (< x) xs, filter (pred1 x) xs, filter (> x) xs).

Equations? quicksort3 xs : seq T by wf (size xs) lt :=
quicksort3 [::]    => [::];
quicksort3 (x::xs) with inspect (partition3 x xs) => {
  | (ls, es, gs) eqn: eq => quicksort3 ls ++ x :: es ++ quicksort3 gs
}.
Proof. all: by apply/ssrnat.ltP; rewrite size_filter; apply: count_size. Qed.

(* this is the main part *)
Lemma quick_filter_ge x xs :
  quicksort (filter (>= x) xs) = filter (pred1 x) xs ++ quicksort (filter (> x) xs).
Proof.
Admitted.

Lemma quick3_quick xs : quicksort3 xs = quicksort xs.
Proof.
Admitted.

(* Exercise 2.5.1 *)

(* TODO move to basics? *)
Fixpoint T_mapfilter {A} (ta : A -> nat) (s : seq A) : nat :=
  if s is x :: s' then ta x + T_mapfilter ta s' + 1 else 1.

Lemma T_mapfilter_size {A} (xs : seq A) ta :
  T_mapfilter ta xs = \sum_(x<-xs) (ta x) + size xs + 1.
Proof.
elim: xs=>/=; first by rewrite big_nil.
by move=>x xs ->; rewrite big_cons -(addn1 (size _)) !addnA.
Qed.

Equations? T_quicksort xs : nat by wf (size xs) lt :=
T_quicksort [::]    => 1;
T_quicksort (x::xs) => T_quicksort (filter (< x) xs) +
                       T_quicksort (filter (>= x) xs) +
                       2 * T_mapfilter (fun => 1%N) xs + 1.
Proof. all: by apply/ssrnat.ltP; rewrite size_filter; apply: count_size. Qed.

(* FIXME replace these with concrete numbers *)
Parameters (a b c : nat).

Lemma quicksort_quadratic xs :
  sorted <=%O xs -> T_quicksort xs = a * size xs ^ 2 + b * size xs + c.
Proof.
Admitted.

(* Exercise 2.5.2 *)

Lemma quicksort_worst xs :
  T_quicksort xs <= a * size xs ^ 2 + b * size xs + c.
Proof.
Admitted.

End QuickSort.

Section TopDownMergeSort.
Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys : seq T).

(* reusing `merge` from mathcomp.path *)

Equations? msort xs : seq T by wf (size xs) lt :=
msort [::]  => [::];
msort [::x] => [::x];
msort xs    => let n := size xs in
               merge <=%O (msort (take n./2 xs))
                          (msort (drop n./2 xs)).
Proof.
all: apply/ssrnat.ltP.
- by rewrite size_take /= !ltnS !half_le.
by rewrite size_drop /= /leq subSS subnAC subnn.
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

Fixpoint C_merge xs :=
  if xs is x :: xs' then
    let fix C_merge_xs ys :=
      if ys is y :: ys' then
        (if x <= y then C_merge xs' ys else C_merge_xs ys').+1
      else 0 in
    C_merge_xs
  else fun => 0.

Equations? C_msort xs : nat by wf (size xs) lt :=
C_msort [::]  => 0;
C_msort [::x] => 0;
C_msort xs    => let n := (size xs) in
                 let ys := take n./2 xs in
                 let zs := drop n./2 xs in
                 C_msort ys + C_msort zs + C_merge (msort ys) (msort zs).
Proof.
all: apply/ssrnat.ltP.
- by rewrite size_take /= !ltnS !half_le.
by rewrite size_drop /= /leq subSS subnAC subnn.
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

Lemma C_msort_leq xs k: size xs = 2^k -> (C_msort xs <= k * 2^k)%N.
Proof.
elim: k xs=>/=.
- by move=>xs; rewrite expn0 =>/size1 [x] ->; simp C_msort.
move=>k IH xs H.
have Hs1 : (size xs > 1)%N by rewrite H -{1}(expn0 2); apply: ltn_exp2l.
case: (size2 Hs1)=> x[y][ys] He; rewrite He /= in H *; simp C_msort=>/=.
have Hp : (size ys)./2.+1 = ((size ys).+2)./2 by rewrite -addn2 halfD andbF /= addn1.
have Ht : size (x :: take (size ys)./2 (y :: ys)) = 2^k.
- by rewrite /= size_take /= ltnS half_le Hp H expnS mul2n half_double.
have Hd : size (drop (size ys)./2 (y :: ys)) = 2^k.
- rewrite size_drop /= subSn; last by apply: half_le.
  by rewrite half_subn uphalf_half -addnS Hp H expnS mul2n half_double odd2 H oddX.
apply: leq_trans;
  first by exact: (leq_add (leq_add (IH _ Ht) (IH _ Hd)) (C_merge_leq _ _)).
rewrite !(perm_size (perm_msort _)) Ht Hd.
by rewrite !addnn -!muln2 -mulnA -!expnSr -{3}(addn1 k) mulnDl mul1n.
Qed.

(* Exercise 2.6 *)

Fixpoint halve {A: Type} (xs ys zs : seq A) : seq A * seq A :=
  ([::],[::]). (* FIXME *)

Equations? msort2 xs : seq T by wf (size xs) lt :=
msort2 [::]  => [::];
msort2 [::x] => [::x];
msort2 xs with inspect (halve xs [::] [::]) := {
  | (ys1, ys2) eqn: eq => merge <=%O (msort2 ys1) (msort2 ys2)
}.
Proof.
all: apply/ssrnat.ltP.
(* FIXME *)
- by [].
by [].
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
Implicit Types (xs ys : seq T).

Equations merge_adj : seq (seq T) -> seq (seq T) :=
merge_adj [::]          => [::];
merge_adj [::xs]        => [::xs];
merge_adj (xs::ys::zss) => merge <=%O xs ys :: merge_adj zss.

Lemma size_merge_adj xss : size (merge_adj xss) = uphalf (size xss).
Proof. by funelim (merge_adj xss)=>//=; congr S. Qed.

Equations? merge_all (xss : seq (seq T)) : seq T by wf (size xss) lt :=
merge_all [::]   => [::];
merge_all [::xs] => xs;
merge_all xss    => merge_all (merge_adj xss).
Proof. by apply/ssrnat.ltP; rewrite size_merge_adj /= !ltnS; apply: uphalf_le. Qed.

Definition msort_bu xs : seq T :=
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

Equations C_merge_adj : seq (seq T) -> nat :=
C_merge_adj [::]          => 0;
C_merge_adj [::xs]        => 0;
C_merge_adj (xs::ys::zss) => C_merge xs ys + C_merge_adj zss.

Equations? C_merge_all (xss : seq (seq T)) : nat by wf (size xss) lt :=
C_merge_all [::]   => 0;
C_merge_all [::xs] => 0;
C_merge_all xss    => C_merge_adj xss + C_merge_all (merge_adj xss).
Proof. by apply/ssrnat.ltP; rewrite size_merge_adj /= !ltnS; apply: uphalf_le. Qed.

Definition C_msort_bu xs : nat :=
  C_merge_all (map (fun x => [::x]) xs).

Lemma merge_adj_sizes xss m :
  ~~ odd (size xss) -> all (fun xs => size xs == m) xss ->
  all (fun xs => size xs == m.*2) (merge_adj xss).
Proof.
funelim (merge_adj xss)=>//=; rewrite negbK=>Ho /and3P [/eqP Hx /eqP Hy Ha]; apply/andP.
split; last by rewrite (H _ Ho Ha).
by rewrite size_merge size_cat Hx Hy addnn.
Qed.

Lemma C_merge_adj_leq xss m :
  all (fun xs => size xs == m) xss -> C_merge_adj xss <= m * size xss.
Proof.
funelim (C_merge_adj xss)=>//= /and3P [/eqP Hx /eqP Hy Ha].
rewrite -add2n mulnDr muln2 -addnn; apply/leq_add/H=>//.
by rewrite -{1}Hx -Hy; apply: C_merge_leq.
Qed.

Lemma C_merge_all_leq xss m k :
  all (fun xs => size xs == m) xss -> size xss = 2 ^ k ->
  C_merge_all xss <= m * k * 2^k.
Proof.
funelim (C_merge_all xss)=>//= /and3P [/eqP Hx /eqP Hy Ha] Hs.
move: H; simp merge_adj C_merge_adj=>/= H. (* slow for some reason *)
have [k0 Hk] : { k0 | k = k0.+1 } by move: Hs; case: k=>//=k0 _; exists k0.
have He : ~~ odd (size l1) by rewrite odd2 Hs oddX Hk.
rewrite Hk expnS mulnS mulnDl in Hs *; apply: leq_add.
- rewrite -Hs -addn2 mulnDr addnC.
  apply: leq_add; first by apply: C_merge_adj_leq.
  by rewrite muln2 -addnn -{1}Hx -Hy; apply: C_merge_leq.
rewrite mulnCA !mulnA mul2n; apply: H.
- apply/andP; split; last by apply: merge_adj_sizes.
  by rewrite size_merge size_cat Hx Hy addnn.
apply/eqP; rewrite size_merge_adj -addn1 -(eqn_pmul2r (m:=2)) // mulnDl muln2.
have -> : (uphalf (size l1)).*2 = size l1
  by rewrite -[in RHS](odd_double_half (size l1)) uphalf_half (negbTE He).
by rewrite addn2 mulnC Hs.
Qed.

Lemma C_msort_bu_leq xs k : size xs = 2^k -> C_msort_bu xs <= k * 2^k.
Proof.
move=>H; rewrite -(mul1n (_ * _)) mulnA; apply: C_merge_all_leq.
- by rewrite all_map; elim: {H}xs.
by rewrite size_map.
Qed.

End BottomUpMergeSort.

Section NaturalMergeSort.
Context {disp : unit} {T : orderType disp}.
Implicit Types (xs ys : seq T) (xss : seq (seq T)).

Fixpoint runs_fix a xs : seq (seq T) :=
  if xs is b::bs
    then if b < a then desc b [:: a] bs else asc b (cons a) bs
    else [::[::a]]
with asc x (xd : seq T -> seq T) ys : seq (seq T) :=
  if ys is y::ys'
    then if x <= y then asc y (xd \o cons x) ys' else xd [::x] :: runs_fix y ys'
    else [:: xd [::x]]
with desc x xs ys : seq (seq T) :=
  if ys is y::ys'
     then if y < x then desc y (x :: xs) ys' else (x :: xs) :: runs_fix y ys'
     else [:: (x :: xs)].

Definition runs xs : seq (seq T) :=
  if xs is x::xs' then runs_fix x xs' else [::].

Definition nmsort xs := merge_all (runs xs).

(* Functional Correctness *)

Definition is_dlist (xd : seq T -> seq T) :=
  forall ps qs, xd (ps ++ qs) = xd ps ++ qs.

Lemma perm_runs_asc_desc x xs ys xd :
     perm_eq (flatten (runs_fix x ys)) (x :: ys)
  /\ perm_eq (flatten (desc x xs ys)) (x::xs ++ ys)
  /\ (is_dlist xd ->
       perm_eq (flatten (asc x xd ys)) (x :: xd [::] ++ ys)).
Proof.
elim: ys x xs xd=>/=.
- move=>x xs xd; do!split=>//.
  by move=>H; move: (H [::] [::x])=>/=; rewrite !cats0=>->; rewrite perm_catC.
move=>b bs IH x xs xd; do!split.
- case: ifP=>_.
  - apply: perm_trans; first by case: (IH b [::x] xd)=>_ [+ _]; apply.
    by move: (perm_catCA [::b] [::x] bs)=>/=->.
  apply: perm_trans; first by case: (IH b [::x] (cons x))=>_ [_] /=; apply.
  by move: (perm_catCA [::b] [::x] bs)=>/=->.
- case: ifP=>_.
  - apply: perm_trans; first by case: (IH b (x::xs) xd)=>_ [+ _]; apply.
    by move: (perm_catCA [::b] (x::xs) bs)=>/=->.
  rewrite /= -!cat_cons perm_cat2l.
  by case: (IH b xs xd)=>+ _; apply.
move=>H; case: ifP=>_.
- apply: perm_trans.
  - case: (IH b xs (xd \o cons x))=>_ [_] /=; apply=>ps qs.
    by rewrite /= -cat_cons; apply: H.
  move: (H [::] [::x])=>/=->; move: (perm_catCA [::b] (xd [::] ++ [::x]) bs)=>/=->.
  by rewrite -cat_cons perm_cat2r perm_catC.
move: (H [::] [::x])=>/=->; rewrite -cat_cons.
apply: perm_cat; first by rewrite perm_catC.
by case: (IH b xs xd)=>+ _; apply.
Qed.

Lemma perm_runs xs : perm_eq (flatten (runs xs)) xs.
Proof.
case: xs=>//=x xs.
by case: (perm_runs_asc_desc x [::] xs id).
Qed.

Lemma perm_nmsort xs : perm_eq (nmsort xs) xs.
Proof.
rewrite /nmsort; apply/perm_trans/perm_runs.
by apply: perm_merge_all.
Qed.

Lemma sorted_runs_asc_desc x xs ys xd :
     all (sorted <=%O) (runs_fix x ys)
  /\ (sorted <=%O xs -> all (>= x) xs -> all (sorted <=%O) (desc x xs ys))
  /\ (is_dlist xd -> sorted <=%O (xd [::]) -> all (<= x) (xd [::]) ->
      all (sorted <=%O) (asc x xd ys)).
Proof.
elim: ys x xs xd=>/=.
- move=>x xs xd; do!split.
  - by move=>Hs Ha; rewrite andbT le_path_sortedE; apply/andP.
  move=>Hd Hs Ha; rewrite andbT; move: (Hd [::] [::x])=>/=->.
  rewrite cats1; apply: sorted_rcons=>//; exact: le_trans.
move=>b ys IH x xs xd; do!split.
- case: ifP=>Ho.
  - case: (IH b [::x] id)=>_ [+ _]; apply=>//.
    by rewrite all_seq1 le_eqVlt Ho orbT.
  case: (IH b xs (cons x))=>_ [_]; apply=>//.
  by rewrite all_seq1 /= leNgt; apply/negbT.
- move=>Hs Ha; case: ifP=>Ho /=.
  - case: (IH b (x::xs) id)=>_ [+ _]; apply=>/=.
    - by rewrite le_path_sortedE; apply/andP.
    rewrite le_eqVlt Ho orbT /=; apply/sub_all/Ha=>z.
    by apply/le_trans; rewrite le_eqVlt Ho orbT.
  rewrite le_path_sortedE Ha Hs /=.
  by case: (IH b xs xd)=>+ _; apply.
move=>Hd Hs Ha; case: ifP=>Ho /=.
- case: (IH b xs (xd \o cons x))=>_ [_] /=; apply.
  - by move=>ps qs /=; rewrite -cat_cons; apply: Hd.
  - move: (Hd [::] [::x])=>/=->.
    by rewrite cats1; apply: sorted_rcons=>//; exact: le_trans.
  move: (Hd [::] [::x])=>/=->.
  rewrite cats1 all_rcons /= Ho /=.
  by apply/sub_all/Ha=>z /= Hx; apply/le_trans/Ho.
apply/andP; split.
- move: (Hd [::] [::x])=>/=->.
  by rewrite cats1; apply: sorted_rcons=>//; exact: le_trans.
by case: (IH b xs id)=>+ _; apply.
Qed.

Lemma sorted_runs xs : all (sorted <=%O) (runs xs).
Proof. by case: xs=>//=x xs; case: (sorted_runs_asc_desc x [::] xs id). Qed.

Lemma sorted_nmsort xs : sorted <=%O (nmsort xs).
Proof. by rewrite /nmsort; apply/sorted_merge_all/sorted_runs. Qed.

(* Running Time Analysis *)

Fixpoint C_runs_fix a xs : nat :=
  if xs is b::bs
    then (if b < a then C_desc b bs else C_asc b bs).+1
    else 0
with C_asc a xs : nat :=
  if xs is b::bs
    then (if a <= b then C_asc b bs else C_runs_fix b bs).+1
    else 0
with C_desc a xs : nat :=
  if xs is b::bs
     then (if b < a then C_desc b bs else C_runs_fix b bs).+1
     else 0.

Definition C_runs xs : nat :=
  if xs is x::xs' then C_runs_fix x xs' else 0.

Definition C_nmsort xs : nat :=
  C_runs xs + C_merge_all (runs xs).

Lemma C_merge_adj_flat xss : C_merge_adj xss <= size (flatten xss).
Proof.
funelim (C_merge_adj xss)=>//=; rewrite catA !size_cat.
by apply: leq_add=>//; apply: C_merge_leq.
Qed.

Lemma merge_adj_flat xss :
  size (flatten (merge_adj xss)) = size (flatten xss).
Proof.
funelim (merge_adj xss)=>//=.
by rewrite catA !size_cat H size_merge size_cat.
Qed.

Lemma C_merge_adj_log2 xss :
  C_merge_all xss <= size (flatten xss) * up_log 2 (size xss).
Proof.
funelim (C_merge_all xss)=>//=; move: H; simp C_merge_adj merge_adj.
rewrite /= !size_cat merge_adj_flat size_merge_adj size_merge size_cat =>IH.
rewrite up_log2S //= mulnS !addnA; apply: leq_add=>//.
by apply/leq_add/C_merge_adj_flat/C_merge_leq.
Qed.

Lemma size_runs_asc_desc x xs ys xd :
      size (flatten (runs_fix x ys)) = (size ys).+1
  /\  size (flatten (desc x xs ys)) = (size xs + size ys).+1
  /\ (is_dlist xd ->
      size (flatten (asc x xd ys)) = (size (xd [::]) + size ys).+1).
Proof.
elim: ys x xs xd=>/=.
- move=>x xs xd; do!split; first by rewrite cats0 addn0.
  by move=>H; move: (H [::] [::x])=>/=; rewrite !cats0=>->; rewrite size_cat addn0 /= addn1.
move=>b bs IH x xs xd; do!split.
- case: ifP=>_.
  - by case: (IH b [::x] id)=>_ [+ _]; rewrite /= addnC addn1.
  case: (IH b [::x] (cons x))=>_ [_] /=; rewrite /= addnC addn1; apply.
  by move=>??; rewrite cat_cons.
- case: ifP=>_ /=.
  - by case: (IH b (x::xs) id)=>_ [+ _]; rewrite /= addSnnS.
  by case: (IH b xs xd)=>+ _; rewrite size_cat=>->.
move=>H; case: ifP=>_ /=.
- case: (IH b xs (xd \o cons x))=>_ [_] /=.
  move: (H [::] [::x])=>/=->; rewrite size_cat /= addnAC -addnA addn1; apply.
  by move=>?? /=; rewrite -cat_cons; apply: H.
move: (H [::] [::x])=>/=->; rewrite !size_cat /=.
by case: (IH b xs xd)=>+ _; rewrite addnAC addn1=>->.
Qed.

Lemma size_runs xs : size (flatten (runs xs)) = size xs.
Proof. by case: xs=>//=x xs; case: (size_runs_asc_desc x [::] xs id). Qed.

Lemma size_runs_asc_desc_leq x xs ys xd :
      (size (runs_fix x ys) <= (size ys).+1)%N
  /\  (size (desc x xs ys) <= (size ys).+1)%N
  /\ (is_dlist xd ->
      (size (asc x xd ys) <= (size ys).+1)%N).
Proof.
elim: ys x xs xd=>//= b bs IH x xs xd; do!split.
- case: ifP=>_.
  - by apply: leqW; case: (IH b [::x] id)=>_ [+ _].
  apply: leqW; case: (IH b [::x] (cons x))=>_ [_]; apply.
  by move=>??; rewrite cat_cons.
- case: ifP=>_ /=.
  - by apply: leqW; case: (IH b (x::xs) id)=>_ [+ _].
  by rewrite ltnS; case: (IH b xs xd)=>+ _ /=.
move=>H; case: ifP=>_ /=.
- apply: leqW; case: (IH b xs (xd \o cons x))=>_ [_] /=; apply.
  by move=>?? /=; rewrite -cat_cons; apply: H.
by rewrite ltnS; case: (IH b xs xd)=>+ _.
Qed.

Lemma size_runs_leq xs : (size (runs xs) <= size xs)%N.
Proof. by case: xs=>//=x xs; case: (size_runs_asc_desc_leq x [::] xs id). Qed.

Lemma C_size_runs_asc_desc_leq x ys :
     (C_runs_fix x ys <= size ys)%N
  /\ (C_desc x ys <= size ys)%N
  /\ (C_asc x ys <= size ys)%N.
Proof.
elim: ys x=>//=b bs IH x.
by do!split; case: ifP=>_; rewrite ltnS; case: (IH b)=>+ [].
Qed.

Lemma C_size_runs_leq xs : (C_runs xs <= (size xs).-1)%N.
Proof. by case: xs=>//=x xs; case: (C_size_runs_asc_desc_leq x xs). Qed.

Lemma C_merge_runs_leq xs n :
  size xs = n -> (C_merge_all (runs xs) <= n * up_log 2 n)%N.
Proof.
move=>H; apply: leq_trans; first by apply: C_merge_adj_log2.
rewrite size_runs H leq_mul2l; apply/orP.
case: n H=>[H|n H]; first by left.
right; apply: leq_up_log; rewrite -H.
by apply: size_runs_leq.
Qed.

Lemma C_nmsort_leq xs n :
  size xs = n -> (C_nmsort xs <= n + n * up_log 2 n)%N.
Proof.
move=>H; rewrite /C_nmsort; apply/leq_add/C_merge_runs_leq=>//.
apply: leq_trans; first by apply: C_size_runs_leq.
by rewrite H; exact: leq_pred.
Qed.

End NaturalMergeSort.

Section Stability.
Context {disp : unit} {T : eqType} {K : orderType disp}.
Implicit Types (xs ys : seq T).

(* Definition *)

Fixpoint insort_key (f : T -> K) x xs : seq T :=
  if xs is y :: xs' then
    if f x <= f y then x :: y :: xs' else y :: insort_key f x xs'
    else [:: x].

Fixpoint isort_key f xs :=
  if xs is x :: xs' then insort_key f x (isort_key f xs') else [::].

Lemma perm_insort_key f x xs : perm_eq (insort_key f x xs) (x :: xs).
Proof.
elim: xs=>//= y xs IH; case: (_ <= _)=>//.
rewrite -(perm_cons y) in IH.
apply: perm_trans; first by exact: IH.
by apply/permP=>/=?; rewrite addnCA.
Qed.

Lemma perm_isort_key f xs : perm_eq (isort_key f xs) xs.
Proof.
elim: xs=>//= x xs IH.
apply: perm_trans; first by apply: perm_insort_key.
by rewrite perm_cons.
Qed.

Lemma sorted_insort_key f a xs :
  sorted <=%O (map f (insort_key f a xs)) = sorted <=%O (map f xs).
Proof.
elim: xs=>//= x xs IH.
case H: (_ <= _)=>/=; first by rewrite H.
rewrite !le_path_sortedE !all_map (perm_all _ (perm_insort_key _ _ _)) /= IH.
suff: f x <= f a by move=>->.
by rewrite leNgt lt_neqAle H andbF.
Qed.

Lemma sorted_isort_key f xs : sorted <=%O (map f (isort_key f xs)).
Proof. by elim: xs=>//=x xs; rewrite sorted_insort_key. Qed.

Lemma insort_key_cons f a xs :
  all (fun x => f a <= f x) xs -> insort_key f a xs = a :: xs.
Proof. by case: xs=>//=x xs /andP [-> _]. Qed.

Lemma filter_not_insort_key (p : pred T) f x xs :
  ~~ p x -> filter p (insort_key f x xs) = filter p xs.
Proof.
move/negbTE=>Hp; elim: xs=>/=; first by rewrite Hp.
move=>y xs IH; case: ifP=>_ /=; first by rewrite Hp.
by rewrite IH.
Qed.

Lemma filter_insort_key (p : pred T) f x xs :
  sorted <=%O (map f xs) -> p x ->
  filter p (insort_key f x xs) = insort_key f x (filter p xs).
Proof.
move/[swap]=>Hp; elim: xs=>/=; first by rewrite Hp.
move=>y xs IH; rewrite le_path_sortedE =>/andP [Ha Hs].
case: ifP=>Hf /=.
- rewrite Hp; case: ifP=>/=; first by rewrite Hf.
  rewrite insort_key_cons // all_filter.
  rewrite all_map in Ha; apply/sub_all/Ha.
  by move=>z /= Hf2; apply/implyP=>_; apply/le_trans/Hf2.
by case: ifP=>/=; rewrite (IH Hs) // Hf.
Qed.

Lemma isort_key_stable f k xs :
  filter (fun y => f y == k) (isort_key f xs) = filter (fun y => f y == k) xs.
Proof.
elim: xs=>//=x xs IH; case: ifP; last first.
- by move/negbT=>Hk; rewrite filter_not_insort_key.
move=>Hk; rewrite filter_insort_key //; last by apply: sorted_isort_key.
rewrite IH insort_key_cons // all_filter (eq_in_all (a2:=predT)) ?all_predT //.
by move=>z _ /=; apply/implyP; move/eqP: Hk=>->/eqP->.
Qed.

End Stability.
