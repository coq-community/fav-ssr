From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path order.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section InsertionSort.
Context {disp : unit} {T : orderType disp}.

(* Definition *)

Fixpoint insort (x : T) xs :=
  if xs is y :: xs' then
    if  x <= y then x :: y :: xs' else y :: insort x xs'
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
by case: (odd n); case: (odd m)=>//=; rewrite addnCA -addnA ?(add1n, add0n).
Qed.

(* Exercise 2.2.2 *)
Lemma T_isort_worst n : T_isort (rev (iota 0 n)) = uphalf ((n.+1)*(n.+2)).
Proof.
Admitted.

End InsertionSortNat.
