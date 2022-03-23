From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype order ssrnat seq path.
From favssr Require Import prelude bst adt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Inductive tree23 A := Leaf
                    | Node2 of (tree23 A) & A & (tree23 A)
                    | Node3 of (tree23 A) & A & (tree23 A) & A & (tree23 A).

Definition empty {A} : tree23 A := @Leaf A.

(* dependent helper for irrefutable pattern matching *)
Inductive non_empty23_if {A} (b : bool) (t : tree23 A) : Type :=
| Nd2 l x r     : t = Node2 l x r     -> b -> non_empty23_if b t
| Nd3 l x m y r : t = Node3 l x m y r -> b -> non_empty23_if b t
| Def           :                     ~~ b -> non_empty23_if b t.

Section Intro.
Context {A : Type}.

Fixpoint inorder23 (t : tree23 A) : seq A :=
  match t with
  | Leaf => [::]
  | Node2 l a r => inorder23 l ++ [::a] ++ inorder23 r
  | Node3 l a m b r => inorder23 l ++ [::a] ++ inorder23 m ++ [::b] ++ inorder23 r
  end.

(* number of nodes *)
Fixpoint size23 (t : tree23 A) : nat :=
  match t with
  | Leaf => 0
  | Node2 l _ r => size23 l + size23 r + 1
  | Node3 l _ m _ r => size23 l + size23 m + size23 r + 1
  end.

Fixpoint height23 (t : tree23 A) : nat :=
  match t with
  | Leaf => 0
  | Node2 l _ r => maxn (height23 l) (height23 r) + 1
  | Node3 l _ m _ r => maxn (height23 l) (maxn (height23 m) (height23 r)) + 1
  end.

Lemma ne_hgt23 (t1 t2 : tree23 A) : non_empty23_if (height23 t1 < height23 t2)%N t2.
Proof.
case: ltnP; last by move=>_; apply: Def.
case: t2=>//=.
- by move=>l a r _; apply: Nd2.
by move=>l a m b r _; apply: Nd3.
Qed.

Lemma height_empty t : height23 t == 0 -> t = empty.
Proof.
case: t=>//=.
- by move=>l a r; rewrite addn1.
by move=>l a m b r; rewrite addn1.
Qed.

Fixpoint complete23 (t : tree23 A) : bool :=
  match t with
  | Leaf => true
  | Node2 l _ r => [&& height23 l == height23 r, complete23 l & complete23 r]
  | Node3 l _ m _ r => [&& height23 l == height23 m, height23 m == height23 r,
                           complete23 l, complete23 m & complete23 r]
  end.

Lemma complete_size23 t : complete23 t -> 2^height23 t <= size23 t + 1.
Proof.
elim: t=>//=.
- move=>l IHl _ r IHr /and3P [/eqP H /IHl Hl /IHr Hr].
  rewrite H in Hl *; rewrite maxnn expnD expn1 muln2 -addnn.
  by rewrite addnAC -addnA; apply: leq_add.
move=>l IHl _ m IHm _ r IHr /and5P [/eqP H1 /eqP H2 /IHl Hl /IHm Hm /IHr Hr].
rewrite H1 H2 in Hl Hm *; rewrite !maxnn expnD expn1 muln2 -addnn.
rewrite addnAC -3!addnA; apply: leq_trans; first by apply: (leq_add Hm Hr).
by rewrite -addnA; apply: leq_addl.
Qed.

(* a helper induction principle to simplify proofs a bit *)
Lemma complete23_ind (P : tree23 A -> Prop) :
  P (Leaf A) ->
  (forall l a r,
   height23 l == height23 r -> complete23 l -> complete23 r ->
   P l -> P r ->
   P (Node2 l a r)) ->
  (forall l a m b r,
   height23 l == height23 m -> height23 m == height23 r ->
   complete23 l -> complete23 m -> complete23 r ->
   P l -> P m -> P r -> P (Node3 l a m b r)) ->
  forall t, complete23 t -> P t.
Proof.
move=>Pl P2 P3; elim=>//=.
- move=>l IHl a r IHr /and3P [E Hl Hr].
  by apply: P2=>//; [apply: IHl | apply: IHr].
move=>l IHl a m IHm b r IHr /and5P [E1 E2 Hl Hm Hr].
by apply: P3=>//; [apply: IHl | apply: IHm | apply: IHr].
Qed.

End Intro.

Arguments complete23_ind [A P].

Section EqType.
Context {T : eqType}.

Fixpoint eqtree23 (t1 t2 : tree23 T) :=
  match t1, t2 with
  | Leaf, Leaf => true
  | Node2 l1 x1 r1, Node2 l2 x2 r2 =>
      [&& x1 == x2, eqtree23 l1 l2 & eqtree23 r1 r2]
  | Node3 l1 x1 m1 y1 r1, Node3 l2 x2 m2 y2 r2 =>
      [&& x1 == x2, y1 == y2, eqtree23 l1 l2, eqtree23 m1 m2 & eqtree23 r1 r2]
  | _, _ => false
  end.

Lemma eqtree23P : Equality.axiom eqtree23.
Proof.
move; elim=>[|l1 IHl x1 r1 IHr|l1 IHl x1 m1 IHm y1 r1 IHr]
  [|l2 x2 r2|l2 x2 m2 y2 r2] /=; try by constructor.
- have [<-/=|neqx] := x1 =P x2; last by apply: ReflectF; case.
  apply: (iffP andP).
  - by case=>/IHl->/IHr->.
  by case=><-<-; split; [apply/IHl|apply/IHr].
have [<-/=|neqx] := x1 =P x2; have [<-/=|neqy] := y1 =P y2; try by apply: ReflectF; case.
apply: (iffP and3P).
- by case=>/IHl->/IHm->/IHr->.
by case=><-<-<-; split; [apply/IHl|apply/IHm|apply/IHr].
Qed.

Canonical tree23_eqMixin := EqMixin eqtree23P.
Canonical tree23_eqType := Eval hnf in EqType (tree23 T) tree23_eqMixin.

End EqType.

(* Exercise 7.1 *)

Fixpoint maxt (h : nat) : tree23 unit := empty. (* FIXME *)

Lemma maxt_size n : size23 (maxt n) = (3^n - 1)./2.
Proof.
Admitted.

Lemma tree23_bound {A} (t : tree23 A) : (size23 t <= (3^(height23 t) - 1)./2)%N.
Proof.
Admitted.

Section SetImplementation.
Context {disp : unit} {T : orderType disp}.

Fixpoint isin23 (t : tree23 T) x : bool :=
  match t with
  | Leaf => false
  | Node2 l a r => match cmp x a with
                   | LT => isin23 l x
                   | EQ => true
                   | GT => isin23 r x
                   end
  | Node3 l a m b r => match cmp x a with
                       | LT => isin23 l x
                       | EQ => true
                       | GT => match cmp x b with
                               | LT => isin23 m x
                               | EQ => true
                               | GT => isin23 r x
                               end
                       end
  end.

Variant upI A := TI of (tree23 A)
               | OF of (tree23 A) & A & (tree23 A).

Definition treeI {A} (r : upI A) : tree23 A :=
  match r with
    | TI t => t
    | OF l a r => Node2 l a r
  end.

Fixpoint ins (x : T) (t : tree23 T) : upI T :=
  match t with
    | Leaf => OF empty x empty
    | Node2 l a r =>
      match cmp x a with
      | LT =>
        match ins x l with
        | TI l'      => TI (Node2 l' a r)
        | OF l1 b l2 => TI (Node3 l1 b l2 a r)
        end
      | EQ => TI (Node2 l a r)
      | GT =>
        match ins x r with
        | TI r'      => TI (Node2 l a r')
        | OF r1 b r2 => TI (Node3 l a r1 b r2)
        end
      end
    | Node3 l a m b r =>
      match cmp x a with
      | LT =>
        match ins x l with
        | TI l'      => TI (Node3 l' a m b r)
        | OF l1 c l2 => OF (Node2 l1 c l2) a (Node2 m b r)
        end
      | EQ => TI (Node3 l a m b r)
      | GT =>
        match cmp x b with
        | LT =>
          match ins x m with
          | TI m'      => TI (Node3 l a m' b r)
          | OF m1 c m2 => OF (Node2 l a m1) c (Node2 m2 b r)
          end
        | EQ => TI (Node3 l a m b r)
        | GT =>
          match ins x r with
          | TI r'      => TI (Node3 l a m b r')
          | OF r1 c r2 => OF (Node2 l a m) b (Node2 r1 c r2)
          end
        end
      end
  end.

Definition insert (x : T) (t : tree23 T) : tree23 T :=
  treeI (ins x t).

(* non empty tree23 *)
Variant n23 A := N2 of (tree23 A) & A & (tree23 A)
               | N3 of (tree23 A) & A & (tree23 A) & A & (tree23 A).

Definition embed {A} (n : n23 A) : tree23 A :=
  match n with
  | N2 l a r => Node2 l a r
  | N3 l a m b r => Node3 l a m b r
  end.

Definition lift {A} (t : tree23 A) : option (n23 A) :=
  match t with
  | Leaf => None
  | Node2 l a r => Some (N2 l a r)
  | Node3 l a m b r => Some (N3 l a m b r)
  end.

Definition inordern23 {A} (n : n23 A) : seq A :=
  match n with
  | N2 l a r => inorder23 l ++ [::a] ++ inorder23 r
  | N3 l a m b r => inorder23 l ++ [::a] ++ inorder23 m ++ [::b] ++ inorder23 r
  end.

Lemma inorder_embed {A} (t : n23 A) : inordern23 t = inorder23 (embed t).
Proof. by case: t. Qed.

Lemma inorder_lift {A} (t : tree23 A) (n : n23 A) :
  lift t = Some n -> inorder23 t = inordern23 n.
Proof.
case: t=>//=.
- by move=>l a r; case=><-.
by move=>l a m b r; case=><-.
Qed.

Definition heightn23 {A} (n : n23 A) : nat :=
  match n with
  | N2 l _ r => maxn (height23 l) (height23 r) + 1
  | N3 l _ m _ r => maxn (height23 l) (maxn (height23 m) (height23 r)) + 1
  end.

Lemma height_embed {A} (t : n23 A) : heightn23 t = height23 (embed t).
Proof. by case: t. Qed.

Lemma height_lift {A} (t : tree23 A) (n : n23 A) :
  lift t = Some n -> height23 t = heightn23 n.
Proof.
case: t=>//=.
- by move=>l a r; case=><-.
by move=>l a m b r; case=><-.
Qed.

Definition completen23 {A} (n : n23 A) :=
  match n with
  | N2 l _ r => [&& height23 l == height23 r, complete23 l & complete23 r]
  | N3 l _ m _ r => [&& height23 l == height23 m, height23 m == height23 r,
                             complete23 l, complete23 m & complete23 r]
  end.

Lemma complete_embed {A} (t : n23 A) : completen23 t = complete23 (embed t).
Proof. by case: t. Qed.

Lemma complete_lift {A} (t : tree23 A) (n : n23 A) :
  lift t = Some n -> complete23 t = completen23 n.
Proof.
case: t=>//=.
- by move=>l a r; case=><-.
by move=>l a m b r; case=><-.
Qed.

Variant upD A := TD of (tree23 A)
               | UF of (tree23 A).

Definition treeD {A} (r : upD A) : tree23 A :=
  match r with
  | TD t => t
  | UF t => t
  end.

Definition node21 {A} (u1 : upD A) (a : A) (n2 : n23 A) : upD A :=
  match u1 with
    | TD t1 => TD (Node2 t1 a (embed n2))
    | UF t1 =>
      match n2 with
      | N2 t2 b t3      => UF (Node3 t1 a t2 b t3)
      | N3 t2 b t3 c t4 => TD (Node2 (Node2 t1 a t2) b (Node2 t3 c t4))
      end
  end.

Definition node22 {A} (n1 : n23 A) (a : A) (u2 : upD A) : upD A :=
  match u2 with
    | TD t2 => TD (Node2 (embed n1) a t2)
    | UF t' =>
      match n1 with
      | N2 t1 b t2      => UF (Node3 t1 b t2 a t')
      | N3 t1 b t2 c t3 => TD (Node2 (Node2 t1 b t2) c (Node2 t3 a t'))
      end
  end.

Definition node31 {A} (u1 : upD A) (a : A) (n2 : n23 A) (z : A) (t' : tree23 A) : upD A :=
  match u1 with
    | TD t1 => TD (Node3 t1 a (embed n2) z t')
    | UF t1 =>
      match n2 with
      | N2 t2 b t3      => TD (Node2 (Node3 t1 a t2 b t3) z t')
      | N3 t2 b t3 c t4 => TD (Node3 (Node2 t1 a t2) b (Node2 t3 c t4) z t')
      end
  end.

Definition node32 {A} (t1 : tree23 A) (a : A) (u2 : upD A) (b : A) (n3 : n23 A) : upD A :=
  match u2 with
    | TD t2 => TD (Node3 t1 a t2 b (embed n3))
    | UF t2 =>
      match n3 with
      | N2 t3 c t4      => TD (Node2 t1 a (Node3 t2 b t3 c t4))
      | N3 t3 c t4 d t5 => TD (Node3 t1 a (Node2 t2 b t3) c (Node2 t4 d t5))
      end
  end.

Definition node33 {A} (t1 : tree23 A) (a : A) (n2 : n23 A) (z : A) (u3 : upD A) : upD A :=
  match u3 with
    | TD t' => TD (Node3 t1 a (embed n2) z t')
    | UF t' =>
      match n2 with
      | N2 t2 b t3      => TD (Node2 t1 a (Node3 t2 b t3 z t'))
      | N3 t2 b t3 c t4 => TD (Node3 t1 a (Node2 t2 b t3) c (Node2 t4 z t'))
      end
  end.

Fixpoint split_min2 {A} (l : tree23 A) (a : A) (r : tree23 A) : A * upD A :=
  let: def := (a, UF empty) in
  match lift r with
  | None => def
  | Some r' =>
    match l with
    | Leaf => def
    | Node2 ll al rl => let: (x, l') := split_min2 ll al rl in
                        (x, node21 l' a r')
    | Node3 ll al ml bl rl => let: (x, l') := split_min3 ll al ml bl rl in
                              (x, node21 l' a r')
    end
  end
with split_min3 {A} (l : tree23 A) (a : A) (m : tree23 A) (b : A) (r : tree23 A) : A * upD A :=
  let: def := (a, TD (Node2 empty b empty))
  in match lift m with
  | None => def
  | Some m' =>
    match l with
    | Leaf => def
    | Node2 ll al rl => let: (x, l') := split_min2 ll al rl in
                        (x, node31 l' a m' b r)
    | Node3 ll al ml bl rl => let: (x, l') := split_min3 ll al ml bl rl in
                              (x, node31 l' a m' b r)
    end
  end.

Definition split_min {A} (n : n23 A) : A * upD A :=
  match n with
  | N2 l a r => split_min2 l a r
  | N3 l a m b r => split_min3 l a m b r
  end.

Fixpoint del (x : T) (t : tree23 T) : upD T :=
  match t with
  | Leaf => TD empty
  | Node2 l a r =>
    let def := if x == a then UF empty
                 else TD (Node2 empty a empty)
    in match lift l with
       | None => def
       | Some l0 =>
         match lift r with
         | None => def
         | Some r0 =>
           match cmp x a with
           | LT => node21 (del x l) a r0
           | EQ => let: (a', r') := split_min r0
                   in node22 l0 a' r'
           | GT => node22 l0 a (del x r)
           end
         end
       end
  | Node3 l a m b r =>
    let def := TD (if x == a
                     then Node2 empty b empty
                     else if x == b
                            then Node2 empty a empty
                            else Node3 empty a empty b empty)
    in match lift m with
       | None => def
       | Some m0 =>
         match lift r with
         | None => def
         | Some r0 =>
           match cmp x a with
           | LT => node31 (del x l) a m0 b r
           | EQ => let: (a', m') := split_min m0 in
                   node32 l a' m' b r0
           | GT => match cmp x b with
                   | LT => node32 l a (del x m) b r0
                   | EQ => let: (b', r') := split_min r0 in
                           node33 l a m0 b' r'
                   | GT => node33 l a m0 b (del x r)
                   end
           end
         end
       end
  end.

Definition delete (x : T) (t : tree23 T) : tree23 T :=
  treeD (del x t).

End SetImplementation.

Section PreservationOfCompleteness.
Context {disp : unit} {T : orderType disp}.

Definition hI {A} (u : upI A) : nat :=
  match u with
  | TI t => height23 t
  | OF l _ _ => height23 l
  end.

Lemma complete_ins (x : T) t :
  complete23 t ->
  complete23 (treeI (ins x t)) && (hI (ins x t) == height23 t).
Proof.
elim/complete23_ind=>{t}//=.
- move=>l a r /eqP E Hcl Hcr /andP [Hl1 /eqP Hl2] /andP [Hr1 /eqP Hr2].
  case: (cmp x a)=>/=.
  - case Hxl: (ins x l)=>[t|tl ta tm] /=; rewrite {}Hxl /= in Hl1 Hl2.
    - by rewrite Hl2 E Hl1 Hcr !eq_refl.
    by case/and3P: Hl1=>/eqP<- ->->; rewrite Hl2 E Hcr !maxnn !eq_refl.
  - by rewrite E Hcl Hcr !eq_refl.
  - case Hxr: (ins x r)=>[t|tl ta tm] /=; rewrite {}Hxr /= in Hr1 Hr2.
    - by rewrite Hr2 E Hr1 Hcl !eq_refl.
    by case/and3P: Hr1=>/eqP<- ->->; rewrite Hr2 E Hcl !maxnn !eq_refl.
move=>l a m b r /eqP E1 /eqP E2 Hcl Hcm Hcr /andP [Hl1 /eqP Hl2] /andP [Hm1 /eqP Hm2] /andP [Hr1 /eqP Hr2].
case: (cmp x a)=>/=.
- case Hxl: (ins x l)=>[t|tl ta tm] /=; rewrite {}Hxl /= in Hl1 Hl2.
  - by rewrite Hl2 E1 E2 Hl1 Hcm Hcr !eq_refl.
  by case/and3P: Hl1=>/eqP<- ->->; rewrite Hl2 E1 E2 Hcm Hcr !maxnn !eq_refl.
- by rewrite E1 E2 Hcl Hcm Hcr !eq_refl.
case Hxb: (cmp x b)=>/=.
- case Hxm: (ins x m)=>[t|tl ta tm] /=; rewrite {}Hxm /= in Hm1 Hm2.
  - by rewrite Hm2 E1 E2 Hcl Hm1 Hcr !eq_refl.
  by case/and3P: Hm1=>/eqP<- ->->; rewrite Hm2 E1 E2 Hcl Hcr !maxnn !eq_refl.
- by rewrite E1 E2 Hcl Hcm Hcr !eq_refl.
case Hxr: (ins x r)=>[t|tl ta tm] /=; rewrite {}Hxr /= in Hr1 Hr2.
- by rewrite Hr2 E1 E2 Hcl Hcm Hr1 !eq_refl.
by case/and3P: Hr1=>/eqP<- ->->; rewrite Hr2 E1 E2 Hcl Hcm !maxnn !eq_refl.
Qed.

Lemma complete_insert x (t : tree23 T) : complete23 t -> complete23 (insert x t).
Proof. by case/(complete_ins x)/andP. Qed.

Definition hD {A} (u : upD A) : nat :=
  match u with
  | TD t => height23 t
  | UF t => height23 t + 1
  end.

Lemma hD21 {A} (l' : upD A) a r :
  hD (node21 l' a r) = maxn (hD l') (heightn23 r) + 1.
Proof.
case: l'=>/= t; first by rewrite height_embed.
case: r=>/=.
- by move=>l _ r; rewrite addn_maxl.
by move=>l _ m _ r; rewrite !addn_maxl !maxnA.
Qed.

Lemma hD22 {A} (l : n23 A) a r' :
  hD (node22 l a r') = maxn (heightn23 l) (hD r') + 1.
Proof.
case: r'=>/= t; first by rewrite height_embed.
case: l=>/=.
- by move=>l _ r; rewrite !addn_maxl maxnA.
by move=>l _ m _ r; rewrite !addn_maxl !maxnA.
Qed.

Lemma hD31 {A} (l' : upD A) a m b r :
  hD (node31 l' a m b r) = maxn (hD l') (maxn (heightn23 m) (height23 r)) + 1.
Proof.
case: l'=>/= t; first by rewrite height_embed.
case: m=>/=.
- by move=>lm _ rm; rewrite !addn_maxl !maxnA.
by move=>lm _ mm _ rm; rewrite !addn_maxl !maxnA.
Qed.

Lemma hD32 {A} (l : tree23 A) a m' b r :
  hD (node32 l a m' b r) = maxn (height23 l) (maxn (hD m') (heightn23 r)) + 1.
Proof.
case: m'=>/= t; first by rewrite height_embed.
case: r=>/=.
- by move=>lr _ rr; rewrite !addn_maxl !maxnA.
by move=>lr _ mr _ rr; rewrite !addn_maxl !maxnA.
Qed.

Lemma hD33 {A} (l : tree23 A) a m b r' :
  hD (node33 l a m b r') = maxn (height23 l) (maxn (heightn23 m) (hD r')) + 1.
Proof.
case: r'=>/= t; first by rewrite height_embed.
case: m=>/=.
- by move=>lm _ rm; rewrite !addn_maxl !maxnA.
by move=>lm _ mm _ rm; rewrite !addn_maxl !maxnA.
Qed.

Lemma complete21 {A} (l' : upD A) a r :
  hD l' = heightn23 r ->
  complete23 (treeD l') ->
  completen23 r ->
  complete23 (treeD (node21 l' a r)).
Proof.
case: l'=>/= t.
- by rewrite height_embed complete_embed=>->->->; rewrite eq_refl.
case: r=>/=.
- move=>l _ r; rewrite !addn1 =>/succn_inj ->-> /and3P [/eqP ->->->].
  by rewrite maxnn eq_refl.
move=>l _ m _ r; rewrite !addn1 =>/succn_inj ->-> /and5P [/eqP -> /eqP ->->->->].
by rewrite !maxnn !eq_refl.
Qed.

Lemma complete22 {A} (l : n23 A) a r' :
  heightn23 l = hD r' ->
  completen23 l ->
  complete23 (treeD r') ->
  complete23 (treeD (node22 l a r')).
Proof.
case: r'=>/= t.
- by rewrite height_embed complete_embed=>->->->; rewrite eq_refl.
case: l=>/=.
- move=>l _ r; rewrite !addn1 =>/succn_inj <- /and3P [/eqP ->->->] ->.
  by rewrite maxnn eq_refl.
move=>l _ m _ r; rewrite !addn1 =>/succn_inj <- /and5P [/eqP -> /eqP ->->->->] ->.
by rewrite !maxnn !eq_refl.
Qed.

Lemma complete31 {A} (l' : upD A) a m b r :
  hD l' = heightn23 m ->
  heightn23 m = height23 r ->
  complete23 (treeD l') ->
  completen23 m ->
  complete23 r ->
  complete23 (treeD (node31 l' a m b r)).
Proof.
case: l'=>/= t.
- by rewrite height_embed complete_embed=>->->->->->; rewrite eq_refl.
case: m=>/=.
- move=>lm _ rm; rewrite !addn1 =>/succn_inj -> <- -> /and3P [/eqP ->->->] ->.
  by rewrite !maxnn !eq_refl.
move=>lm _ mm _ rm; rewrite !addn1 =>/succn_inj -> <- -> /and5P [/eqP -> /eqP ->->->] ->->.
by rewrite !maxnn !eq_refl.
Qed.

Lemma complete32 {A} (l : tree23 A) a m' b r :
  height23 l = hD m' ->
  hD m' = heightn23 r ->
  complete23 l ->
  complete23 (treeD m') ->
  completen23 r ->
  complete23 (treeD (node32 l a m' b r)).
Proof.
case: m'=>/= t.
- by rewrite height_embed complete_embed=>->->->->->; rewrite eq_refl.
case: r=>/=.
- move=>lm _ rm ->; rewrite !addn1 =>/succn_inj ->->-> /and3P [/eqP ->->->].
  by rewrite !maxnn !eq_refl.
move=>lm _ mm _ rm ->; rewrite !addn1 =>/succn_inj ->->-> /and5P [/eqP -> /eqP ->->->] ->.
by rewrite !maxnn !eq_refl.
Qed.

Lemma complete33 {A} (l : tree23 A) a m b r' :
  height23 l = heightn23 m ->
  heightn23 m = hD r' ->
  complete23 l ->
  completen23 m ->
  complete23 (treeD r') ->
  complete23 (treeD (node33 l a m b r')).
Proof.
case: r'=>/= t.
- by rewrite height_embed complete_embed=>->->->->->; rewrite eq_refl.
case: m=>/=.
- move=>lm _ rm ->; rewrite !addn1 =>/succn_inj <- -> /and3P [/eqP ->->->] ->.
  by rewrite !maxnn !eq_refl.
move=>lm _ mm _ rm ->; rewrite !addn1 =>/succn_inj <- -> /and5P [/eqP -> /eqP ->->->] ->->.
by rewrite !maxnn !eq_refl.
Qed.

Lemma split_min_hD2 {A} (l : tree23 A) a r x t':
  split_min2 l a r = (x, t') ->
  height23 l = height23 r -> complete23 l -> complete23 r ->
  hD t' = maxn (height23 l) (height23 r) + 1
with split_min_hD3 {A} (l : tree23 A) a m b r x t':
  split_min3 l a m b r = (x, t') ->
  height23 l = height23 m -> height23 m = height23 r ->
  complete23 l -> complete23 m -> complete23 r ->
  hD t' = maxn (height23 l) (maxn (height23 m) (height23 r)) + 1.
Proof.
- elim: l a r t'=>/=.
  - by move=>a r t'; case Hlr: (lift r)=>[t|]; case=>_ <-<-.
  - move=>ll IHl al rl _ a r t'.
    case Hlr: (lift r)=>[t|]; last by case: r Hlr=>//= _ [_ <-] ->.
    case Hsm: (split_min2 ll al rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
    move=>_; case/and3P=>/eqP El Hll Hrl _.
    by rewrite hD21 (IHl _ _ _ Hsm El Hll Hrl) (height_lift Hlr).
  move=>ll _ al ml _ bl rl _ a r t'.
  case Hlr: (lift r)=>[t|]; last by case: r Hlr=>//= _ [_ <-] ->.
  case Hsm: (split_min3 ll al ml bl rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
  move=>_; case/and5P=>/eqP El /eqP Em Hll Hml Hrl _.
  by rewrite hD21 (split_min_hD3 _ _ _ _ _ _ _ _ Hsm El Em Hll Hml Hrl) (height_lift Hlr).
elim: l a m b r t'=>/=.
- by move=>a m b r t'; case Hlm: (lift m)=>[t|]; case=>_<-<-<-.
- move=>ll _ al rl _ a m b r t'.
  case Hlm: (lift m)=>[t|]; last by case: m Hlm=>//= _ [_ <-] -> <-.
  case Hsm: (split_min2 ll al rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
  move=>_ _; case/and3P=>/eqP El Hll Hrl _.
  by rewrite hD31 (split_min_hD2 _ _ _ _ _ _ Hsm El Hll Hrl) (height_lift Hlm).
move=>ll IHl al ml _ bl rl _ a m b r t'.
case Hlm: (lift m)=>[t|]; last by case: m Hlm=>//= _ [_ <-] -> <-.
case Hsm: (split_min3 ll al ml bl rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
move=>_ _; case/and5P=>/eqP El /eqP Em Hll Hml Hrl _.
by rewrite hD31 (IHl _ _ _ _ _ Hsm El Em Hll Hml Hrl) (height_lift Hlm).
Qed.

Lemma split_min_completeD2 {A} (l : tree23 A) a r x t' :
  split_min2 l a r = (x, t') ->
  height23 l = height23 r -> complete23 l -> complete23 r ->
  complete23 (treeD t')
with split_min_completeD3 {A} (l : tree23 A) a m b r x t':
  split_min3 l a m b r = (x, t') ->
  height23 l = height23 m -> height23 m = height23 r ->
  complete23 l -> complete23 m -> complete23 r ->
  complete23 (treeD t').
Proof.
- elim: l a r t'=>/=.
  - by move=>a r t'; case Hlr: (lift r)=>[t|]; case=>_ <-.
  - move=>ll IHl al rl _ a r t'.
    case Hlr: (lift r)=>[t|]; last by case: r Hlr=>//= _ [_ <-].
    case Hsm: (split_min2 ll al rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
    move=>H; case/and3P=>/eqP El Hll Hrl Hr.
    apply: complete21.
    by rewrite -(height_lift Hlr) -H (split_min_hD2 Hsm El Hll Hrl).
    - by exact: (IHl _ _ _ Hsm El Hll Hrl).
    by rewrite -(complete_lift Hlr).
  move=>ll _ al ml _ bl rl _ a r t'.
  case Hlr: (lift r)=>[t|]; last by case: r Hlr=>//= _ [_ <-].
  case Hsm: (split_min3 ll al ml bl rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
  move=>H; case/and5P=>/eqP El /eqP Em Hll Hml Hrl Hr.
  apply: complete21.
  - by rewrite -(height_lift Hlr) -H (split_min_hD3 Hsm El Em Hll Hml Hrl).
  - by exact: (split_min_completeD3 _ _ _ _ _ _ _ _ Hsm El Em Hll Hml Hrl).
  by rewrite -(complete_lift Hlr).
elim: l a m b r t'=>/=.
- by move=>a m b r t'; case Hlm: (lift m)=>[t|]; case=>_<-.
- move=>ll _ al rl _ a m b r t'.
  case Hlm: (lift m)=>[t|]; last by case: m Hlm=>//= _ [_ <-].
  case Hsm: (split_min2 ll al rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
  move=>H H'; case/and3P=>/eqP El Hll Hrl Hm Hr.
  apply: complete31=>//.
  - by rewrite -(height_lift Hlm) -H (split_min_hD2 Hsm El Hll Hrl).
  - by rewrite -(height_lift Hlm) H'.
  - by exact: (split_min_completeD2 _ _ _ _ _ _ Hsm El Hll Hrl).
  by rewrite -(complete_lift Hlm).
move=>ll IHl al ml _ bl rl _ a m b r t'.
case Hlm: (lift m)=>[t|]; last by case: m Hlm=>//= _ [_ <-].
case Hsm: (split_min3 ll al ml bl rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
move=>H H'; case/and5P=>/eqP El /eqP Em Hll Hml Hrl Hm Hr.
apply: complete31=>//.
- by rewrite -(height_lift Hlm) -H (split_min_hD3 Hsm El Em Hll Hml Hrl).
- by rewrite -(height_lift Hlm) H'.
- by exact: (IHl _ _ _ _ _ Hsm El Em Hll Hml Hrl).
by rewrite -(complete_lift Hlm).
Qed.

Lemma split_min_hD {A} (t : n23 A) x t' :
  split_min t = (x, t') ->
  completen23 t ->
  hD t' = heightn23 t.
Proof.
case: t=>/=.
- by move=>l a r H /and3P [/eqP E Hl Hr]; apply: (split_min_hD2 H).
by move=>l a m b r H /and5P [/eqP E1 /eqP E2 Hl Hm Hr]; apply: (split_min_hD3 H).
Qed.

Lemma split_min_completeD {A} (t : n23 A) x t' :
  split_min t = (x, t') ->
  completen23 t ->
  complete23 (treeD t').
Proof.
case: t=>/=.
- by move=>l a r H /and3P [/eqP E Hl Hr]; apply: (split_min_completeD2 H).
by move=>l a m b r H /and5P [/eqP E1 /eqP E2 Hl Hm Hr]; apply: (split_min_completeD3 H).
Qed.

Lemma hD_del t (x : T) : complete23 t -> hD (del x t) = height23 t.
Proof.
elim/complete23_ind=>{t}//=.
- move=>l a r /eqP E _ Hr IHl IHr.
  case Hll: (lift l)=>[l'|]; last by case: {IHl}l E Hll=>//=<- _; case: ifP.
  case Hlr: (lift r)=>[r'|]; last by case: {IHr Hr}r E Hlr=>//=-> _; case: ifP.
  case: (cmp x a).
  - by rewrite hD21 IHl (height_lift Hlr).
  - case Hsm: (split_min r')=>[x0 t0].
    rewrite hD22 (height_lift Hll) (height_lift Hlr) (split_min_hD Hsm) //.
    by rewrite -(complete_lift Hlr).
  by rewrite hD22 IHr (height_lift Hll).
move=>l a m b r /eqP E1 /eqP E2 _ Hm Hr IHl IHm IHr.
case Hlm: (lift m)=>[m'|]; last first.
- by case: {IHm Hm}m E1 E2 Hlm=>//= -> <- _; case: ifP=>// _; case: ifP.
case Hlr: (lift r)=>[r'|]; last first.
- by case: {IHr Hr}r E1 E2 Hlr=>//= -> -> _; case: ifP=>// _; case: ifP.
case: (cmp x a).
- by rewrite hD31 IHl (height_lift Hlm).
- case Hsm: (split_min m')=>[x0 t0].
  rewrite hD32 (height_lift Hlm) (height_lift Hlr) (split_min_hD Hsm) //.
  by rewrite -(complete_lift Hlm).
case Hxb: (cmp x b).
- by rewrite hD32 IHm (height_lift Hlr).
- case Hsm: (split_min r')=>[x0 t0].
  rewrite hD33 (height_lift Hlm) (height_lift Hlr) (split_min_hD Hsm) //.
  by rewrite -(complete_lift Hlr).
by rewrite hD33 IHr (height_lift Hlm).
Qed.

Lemma complete_treeD t (x : T) : complete23 t -> complete23 (treeD (del x t)).
Proof.
elim/complete23_ind=>{t}//=.
- move=>l a r /eqP E Hl Hr IHl IHr.
  case Hll: (lift l)=>[l'|]; last by case: ifP.
  case Hlr: (lift r)=>[r'|]; last by case: ifP.
  case: (cmp x a).
  - apply: complete21=>//; last by rewrite -(complete_lift Hlr).
    by rewrite hD_del // -(height_lift Hlr) E.
  - case Hsm: (split_min r')=>[x0 t0].
    apply: complete22.
    - rewrite (split_min_hD Hsm); last by rewrite -(complete_lift Hlr).
      by rewrite -(height_lift Hll) -(height_lift Hlr).
    - by rewrite -(complete_lift Hll).
    by apply: (split_min_completeD Hsm); rewrite -(complete_lift Hlr).
  apply: complete22=>//; last by rewrite -(complete_lift Hll).
  by rewrite hD_del // -(height_lift Hll).
move=>l a m b r /eqP E1 /eqP E2 Hl Hm Hr IHl IHm IHr.
case Hlm: (lift m)=>[m'|]; last by case: ifP=>//= _; case: ifP.
case Hlr: (lift r)=>[r'|]; last by case: ifP=>//= _; case: ifP.
case: (cmp x a).
- apply: complete31=>//; last by rewrite -(complete_lift Hlm).
  - by rewrite hD_del // -(height_lift Hlm) E1.
  by rewrite -(height_lift Hlm) E2.
- case Hsm: (split_min m')=>[x0 t0].
  apply: complete32=>//; last by by rewrite -(complete_lift Hlr).
  - rewrite (split_min_hD Hsm); last by rewrite -(complete_lift Hlm).
    by rewrite -(height_lift Hlm).
  - rewrite (split_min_hD Hsm); last by rewrite -(complete_lift Hlm).
    by rewrite -(height_lift Hlm) -(height_lift Hlr).
  by apply: (split_min_completeD Hsm); rewrite -(complete_lift Hlm).
case Hxb: (cmp x b).
- apply: complete32=>//; first by rewrite hD_del.
  - by rewrite hD_del // -(height_lift Hlr).
  by rewrite -(complete_lift Hlr).
- case Hsm: (split_min r')=>[x0 t0].
  apply: complete33=>//; first by rewrite -(height_lift Hlm).
  - rewrite (split_min_hD Hsm); last by rewrite -(complete_lift Hlr).
    by rewrite -(height_lift Hlm) -(height_lift Hlr).
  - by rewrite -(complete_lift Hlm).
  by apply: (split_min_completeD Hsm); rewrite -(complete_lift Hlr).
apply: complete33=>//; first by rewrite -(height_lift Hlm).
- by rewrite hD_del // -(height_lift Hlm).
by rewrite -(complete_lift Hlm).
Qed.

Lemma complete_delete t (x : T) : complete23 t -> complete23 (delete x t).
Proof. by exact: complete_treeD. Qed.

End PreservationOfCompleteness.

Section FunctionalCorrectness.
Context {disp : unit} {T : orderType disp}.

Definition bst_list (t : tree23 T) : bool := sorted <%O (inorder23 t).

Lemma inorder_insert23 x t :
  bst_list t ->
  inorder23 (insert x t) = ins_list x (inorder23 t).
Proof.
rewrite /bst_list /insert; elim: t=>//=.
- move=>l IHl a r IHr.
  rewrite sorted_cat_cons_cat=>/andP [H1 /path_sorted H2].
  rewrite inslist_sorted_cat_cons_cat //.
  case Hc: (cmp x a)=>/=.
  - move/cmp_lt: Hc=>->.
    by case Hxl: (ins x l)=>[l'|l' a' m'] /=;
    (rewrite -IHl; last by rewrite (cat_sorted2 H1)); rewrite Hxl //= -catA.
  - by move/cmp_eq: Hc=>/eqP ->; rewrite ltxx eq_refl.
  move/cmp_gt: Hc; rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
  by case Hxr: (ins x r)=>[r'|m' b' r'] /=; rewrite -IHr // Hxr.
move=>l IHl a m IHm b r IHr.
rewrite sorted_cat_cons_cat=>/andP [H1 /path_sorted].
rewrite sorted_cat_cons_cat=>/andP [H2 /path_sorted H3].
rewrite inslist_sorted_cat_cons_cat //.
case Hca: (cmp x a)=>/=.
- move/cmp_lt: Hca=>->.
  case Hxl: (ins x l)=>[l'|l' a' r'] /=;
  (rewrite -IHl; last by rewrite (cat_sorted2 H1)); rewrite Hxl //= -catA.
- by move/cmp_eq: Hca=>/eqP ->; rewrite ltxx eq_refl.
move/cmp_gt: Hca; rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
rewrite inslist_sorted_cat_cons_cat //.
case Hcb: (cmp x b)=>/=.
- move/cmp_lt: Hcb=>->.
  by case Hxm: (ins x m) =>[m'|r' c' l'] /=;
  (rewrite -IHm; last by rewrite (cat_sorted2 H2)); rewrite Hxm //= -!catA.
- by move/cmp_eq: Hcb=>/eqP ->; rewrite ltxx eq_refl.
move/cmp_gt: Hcb; rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
by case Hxr: (ins x r)=>[r'|l' c' r'] /=; rewrite -IHr // Hxr //= -catA.
Qed.

Lemma inorderD21 {A} (l' : upD A) a r :
  inorder23 (treeD (node21 l' a r)) = inorder23 (treeD l') ++ a :: inordern23 r.
Proof.
case: l'=>/= t; first by rewrite inorder_embed.
by case: r=>//= l b m c r; rewrite -catA.
Qed.

Lemma inorderD22 {A} (l : n23 A) a r' :
  inorder23 (treeD (node22 l a r')) = inordern23 l ++ a :: inorder23 (treeD r').
Proof.
case: r'=>/= t; first by rewrite inorder_embed.
case: l=>/=.
- by move=>l b r; rewrite -catA.
by move=>l b m c r; rewrite -!catA /= -catA.
Qed.

Lemma inorderD31 {A} (l' : upD A) a m b r :
  inorder23 (treeD (node31 l' a m b r)) = inorder23 (treeD l') ++ a :: inordern23 m ++ b :: inorder23 r.
Proof.
case: l'=>/= t; first by rewrite inorder_embed.
case: m=>/=.
- by move=>lm c rm; rewrite -!catA /= -catA.
by move=>lm c mm d rm; rewrite -!catA /= -catA.
Qed.

Lemma inorderD32 {A} (l : tree23 A) a m' b r :
  inorder23 (treeD (node32 l a m' b r)) = inorder23 l ++ a :: inorder23 (treeD m') ++ b :: inordern23 r.
Proof.
case: m'=>/= t; first by rewrite inorder_embed.
by case: r=>//= lr c mr d rr; rewrite -catA.
Qed.

Lemma inorderD33 {A} (l : tree23 A) a m b r' :
  inorder23 (treeD (node33 l a m b r')) = inorder23 l ++ a :: inordern23 m ++ b :: inorder23 (treeD r').
Proof.
case: r'=>/= t; first by rewrite inorder_embed.
case: m=>/=.
- by move=>lm c rm; rewrite -catA.
by move=>lm c mm d rm; rewrite -!catA /= -catA.
Qed.

Lemma split_minD2 {A} (l : tree23 A) a r x t' :
  split_min2 l a r = (x, t') ->
  height23 l = height23 r -> complete23 l -> complete23 r ->
  x :: inorder23 (treeD t') = inorder23 l ++ a :: inorder23 r
with split_minD3 {A} (l : tree23 A) a m b r x t' :
  split_min3 l a m b r = (x, t') ->
  height23 l = height23 m -> height23 m = height23 r ->
  complete23 l -> complete23 m -> complete23 r ->
  x :: inorder23 (treeD t') = inorder23 l ++ a :: inorder23 m ++ b :: inorder23 r.
Proof.
- elim: l a r t'=>/=.
  - by move=>a r t'; case Hlr: (lift r)=>[t|];
    case=>-> <- /= /eqP; rewrite eq_sym=>/height_empty ->.
  - move=>ll IHl al rl _ a r t'.
    case Hlr: (lift r)=>[t|]; last by case: r Hlr=>//= _ _; rewrite addn1.
    case Hsm: (split_min2 ll al rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
    move=>H; case/and3P=>/eqP El Hll Hrl Hr.
    by rewrite inorderD21 -cat_cons (IHl _ _ _ Hsm El Hll Hrl) (inorder_lift Hlr).
  move=>ll _ al ml _ bl rl _ a r t'.
  case Hlr: (lift r)=>[t|]; last by case: r Hlr=>//= _ _; rewrite addn1.
  case Hsm: (split_min3 ll al ml bl rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
  move=>H; case/and5P=>/eqP El /eqP Em Hll Hml Hrl Hr.
  by rewrite inorderD21 -cat_cons (split_minD3 _ _ _ _ _ _ _ _ Hsm El Em Hll Hml Hrl) (inorder_lift Hlr).
elim: l a m b r t'=>/=.
- by move=>a m b r t'; case Hlm: (lift m)=>[t|];
  case=>-> <- /= /eqP; rewrite eq_sym=>/height_empty -> /= /eqP;
  rewrite eq_sym=>/height_empty ->.
- move=>ll _ al rl _ a m b r t'.
  case Hlm: (lift m)=>[t|]; last by case: m Hlm=>//= _ _; rewrite addn1.
  case Hsm: (split_min2 ll al rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
  move=>H H'; case/and3P=>/eqP El Hll Hrl Hm Hr.
  by rewrite inorderD31 -cat_cons (split_minD2 _ _ _ _ _ _ Hsm El Hll Hrl) (inorder_lift Hlm).
move=>ll IHl al ml _ bl rl _ a m b r t'.
case Hlm: (lift m)=>[t|]; last by case: m Hlm=>//= _ _; rewrite addn1.
case Hsm: (split_min3 ll al ml bl rl)=>[x0 t0][E <-]; rewrite {}E in Hsm.
move=>H H'; case/and5P=>/eqP El /eqP Em Hll Hml Hrl Hm Hr.
by rewrite inorderD31 -cat_cons (IHl _ _ _ _ _ Hsm El Em Hll Hml Hrl) (inorder_lift Hlm).
Qed.

Lemma split_minD {A} (t : n23 A) x t' :
  split_min t = (x,t') ->
  completen23 t ->
  x :: inorder23 (treeD t') = inordern23 t.
Proof.
case: t=>/=.
- by move=>l a r H /and3P [/eqP E Hl Hr]; apply: (split_minD2 H).
by move=>l a m b r H /and5P [/eqP E1 /eqP E2 Hl Hm Hr]; apply: (split_minD3 H).
Qed.

Lemma inorder_delete23 x t :
  complete23 t -> bst_list t ->
  inorder23 (delete x t) = del_list x (inorder23 t).
Proof.
rewrite /bst_list /delete; elim/complete23_ind=>{t}//=.
- move=>l a r /eqP E Hcl Hcr IHl IHr /[dup] H.
  case/cat_sorted2=>H1 /path_sorted H2.
  rewrite dellist_sorted_cat_cons_cat //.
  case Hfl: (lift l)=>[l'|]; last first.
  - case: {H H1 IHl Hcl}l E Hfl =>//= /eqP; rewrite eq_sym => /height_empty -> _.
    case: ifP=>/=; last by rewrite if_same.
    by move/eqP=>->; rewrite ltxx.
  case Hfr: (lift r)=>[r'|]; last first.
  - case: {H H2 IHr Hcr}r E Hfr =>//= /eqP/height_empty -> _.
    case: ifP=>/=; last by rewrite if_same.
    by move/eqP=>->; rewrite ltxx.
  case Hc: (cmp x a)=>/=.
  - by move/cmp_lt: Hc=>->; rewrite inorderD21 (IHl H1) (inorder_lift Hfr).
  - move/cmp_eq: Hc=>/eqP ->; rewrite ltxx eq_refl.
    case Hsm: (split_min r')=>[x0 t0].
    rewrite inorderD22 (split_minD Hsm); last by rewrite -(complete_lift Hfr).
    by rewrite -(inorder_lift Hfl) -(inorder_lift Hfr).
  move/cmp_gt: Hc; rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
  by rewrite inorderD22 (IHr H2) (inorder_lift Hfl).
move=>l a m b r /eqP E1 /eqP E2 Hcl Hcm Hcr IHl IHm IHr /[dup] H.
case/cat_sorted2=>H1 /=; rewrite (path_sortedE lt_trans); case/andP.
rewrite all_cat=>/= /and3P [_ Hab _] /[dup] H0; case/cat_sorted2=>H2 /path_sorted H3.
rewrite dellist_sorted_cat_cons_cat // -/cat.
case Hfm: (lift m)=>[m'|]; last first.
- case: {H H0 H1 H2 IHm Hcm}m E1 E2 Hfm =>//=.
  move/eqP/height_empty => -> /eqP; rewrite eq_sym => /height_empty ->_ /=.
  case: ifP=>/=; first by move/eqP=>->; rewrite ltxx.
  case: ifP=>/=; last by rewrite if_same.
  by move/eqP=>-> _; rewrite ltNge le_eqVlt Hab orbT.
case Hfr: (lift r)=>[r'|]; last first.
- case: {H H0 H3 IHr Hcr}r E2 Hfr =>//= /[dup] Hhm /eqP/height_empty -> _ /=.
  move: E1; rewrite Hhm=>/eqP/height_empty -> /=.
  case: ifP =>/=; first by move/eqP=>->; rewrite ltxx.
  case: ifP=>/=; last by rewrite if_same.
  by move/eqP=>-> _; rewrite ltNge le_eqVlt Hab orbT.
case Hc: (cmp x a)=>/=.
- by move/cmp_lt: Hc=>->; rewrite inorderD31 (IHl H1) (inorder_lift Hfm).
- move/cmp_eq: Hc=>/eqP ->; rewrite ltxx eq_refl.
  case Hsm: (split_min m')=>[x0 t0].
  rewrite inorderD32 -cat_cons (split_minD Hsm); last by rewrite -(complete_lift Hfm).
  by rewrite -(inorder_lift Hfm) -(inorder_lift Hfr).
move/cmp_gt: Hc; rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
rewrite dellist_sorted_cat_cons_cat //.
case Hc': (cmp x b)=>/=.
- by move/cmp_lt: Hc'=>->; rewrite inorderD32 (IHm H2) (inorder_lift Hfr).
- move/cmp_eq: Hc'=>/eqP ->; rewrite ltxx eq_refl.
  case Hsm: (split_min r')=>[x0 t0].
  rewrite inorderD33 (split_minD Hsm); last by rewrite -(complete_lift Hfr).
  by rewrite -(inorder_lift Hfm) -(inorder_lift Hfr).
move/cmp_gt: Hc'; rewrite ltNge le_eqVlt negb_or=>/andP [/negbTE -> /negbTE ->].
by rewrite inorderD33 (IHr H3) (inorder_lift Hfm).
Qed.

Lemma inorder_isin_list (t : tree23 T) :
  bst_list t ->
  isin23 t =i inorder23 t.
Proof.
rewrite /bst_list /= =>+ x; elim: t=>//=.
- move=>l IHl a r IHr.
  rewrite -topredE /= in IHl; rewrite -topredE /= in IHr.
  rewrite -topredE /= mem_cat inE sorted_cat_cons_cat=>/andP [H1 H2].
  case Hc: (cmp x a)=>/=.
  - move/cmp_lt: Hc=>Hx; rewrite IHl; last by rewrite (cat_sorted2 H1).
    have/negbTE->: x!=a by move: Hx; rewrite lt_neqAle; case/andP.
    suff: x \notin inorder23 r by move/negbTE=>->/=; rewrite orbF.
    apply/count_memPn; rewrite -(count_pred0 (inorder23 r)).
    apply/eq_in_count=>z; move: H2=>/= /(order_path_min lt_trans)/allP/(_ z)/[apply] Hz.
    by move: (lt_trans Hx Hz); rewrite lt_neqAle eq_sym=>/andP [/negbTE].
  - by move/cmp_eq: Hc=>/eqP->; rewrite eq_refl /= orbT.
  move/cmp_gt: Hc=>Hx; rewrite IHr; last first.
  - by rewrite -cat1s in H2; rewrite (cat_sorted2 H2).
  have/negbTE->: x!=a by move: Hx; rewrite lt_neqAle eq_sym; case/andP.
  suff: x \notin inorder23 l by move/negbTE=>->.
  apply/count_memPn; rewrite -(count_pred0 (inorder23 l)).
  apply/eq_in_count=>z /=.
  move: H1; rewrite (sorted_pairwise lt_trans) pairwise_cat /= allrel1r andbT.
  case/andP=>+ _ =>/allP/(_ z)/[apply] Hz.
  by move: (lt_trans Hz Hx); rewrite lt_neqAle eq_sym=>/andP [/negbTE].
move=>l IHl a m IHm b r IHr.
rewrite -topredE /= in IHl; rewrite -topredE /= in IHm; rewrite -topredE /= in IHr.
rewrite -topredE /= !(mem_cat, inE) sorted_cat_cons_cat; case/andP=>/=.
rewrite cats1 (sorted_rconsE lt_trans); case/andP => Hal H1.
rewrite (path_sortedE lt_trans); case/andP; rewrite all_cat=>/and3P [Ham Hab Har].
rewrite sorted_cat_cons_cat; case/andP=>/=.
rewrite cats1 (sorted_rconsE lt_trans); case/andP => Hbm H2.
rewrite (path_sortedE lt_trans); case/andP=>Hbr H3.
case Hc: (cmp x a)=>/=.
- move/cmp_lt: Hc=>Hx; rewrite (IHl H1).
  have/negbTE->: x!=a by move: Hx; rewrite lt_neqAle; case/andP.
  have/negbTE->: x \notin inorder23 m.
  - apply/count_memPn; rewrite -(count_pred0 (inorder23 m)).
    apply/eq_in_count=>z /= Hz; move: (allP Ham z Hz) => /(lt_trans Hx).
    by rewrite lt_neqAle eq_sym => /andP [/negbTE].
  have/negbTE->: x!=b by move: (lt_trans Hx Hab); rewrite lt_neqAle; case/andP.
  suff: x \notin inorder23 r by move/negbTE->; rewrite !orbF.
  apply/count_memPn; rewrite -(count_pred0 (inorder23 r)).
  apply/eq_in_count=>z /= Hz; move: (allP Har z Hz) => /(lt_trans Hx).
  by rewrite lt_neqAle eq_sym => /andP [/negbTE].
- by move/cmp_eq: Hc=>/eqP->; rewrite eq_refl /= orbT.
move/cmp_gt: Hc=>Hx; move: (Hx); rewrite lt_neqAle eq_sym=>/andP [/negbTE ->] /= _.
have ->/=: x \in inorder23 l = false.
- apply/negbTE/count_memPn; rewrite -(count_pred0 (inorder23 l)).
  apply/eq_in_count=>z /= Hz; move: (allP Hal z Hz)=>Hza; move: (lt_trans Hza Hx).
  by rewrite lt_neqAle eq_sym => /andP [/negbTE].
case Hc: (cmp x b)=>/=.
- move/cmp_lt: Hc=>Hx'; rewrite (IHm H2).
  have ->: (x==b)=false by move: Hx'; rewrite lt_neqAle=>/andP [/negbTE].
  have ->: x \in inorder23 r = false.
  - apply/negbTE/count_memPn; rewrite -(count_pred0 (inorder23 r)).
    apply/eq_in_count=>z /= Hz; move: (allP Hbr z Hz) => /(lt_trans Hx').
    by rewrite lt_neqAle eq_sym => /andP [/negbTE].
  by rewrite !orbF.
- by move/cmp_eq: Hc=>/eqP->; rewrite eq_refl /= orbT.
move/cmp_gt: Hc=>Hx'; rewrite (IHr H3).
move: (Hx'); rewrite lt_neqAle eq_sym=>/andP [/negbTE ->] /= _.
suff: x \in inorder23 m = false by move=>->.
apply/negbTE/count_memPn; rewrite -(count_pred0 (inorder23 m)).
apply/eq_in_count=>z /= Hz; move: (allP Hbm z Hz)=>Hzb; move: (lt_trans Hzb Hx').
by rewrite lt_neqAle eq_sym => /andP [/negbTE].
Qed.

(* corollaries *)

Definition invariant t := bst_list t && complete23 t.

Corollary inorder_insert_list23 x (t : tree23 T) :
  invariant t ->
  perm_eq (inorder23 (insert x t))
          (if x \in inorder23 t then inorder23 t else x :: inorder23 t).
Proof.
rewrite /invariant /bst_list => /andP [H1 _].
by rewrite inorder_insert23 //; apply: inorder_ins_list.
Qed.

Corollary inorder_delete_list23 x (t : tree23 T) :
  invariant t ->
  perm_eq (inorder23 (delete x t))
          (filter (predC1 x) (inorder23 t)).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
by rewrite inorder_delete23 //; apply: inorder_del_list.
Qed.

Corollary invariant_empty : invariant (@empty T).
Proof. by []. Qed.

Corollary invariant_insert x (t : tree23 T) :
  invariant t -> invariant (insert x t).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
apply/andP; split; last by apply: complete_insert.
by rewrite inorder_insert23 //; apply: ins_list_sorted.
Qed.

Corollary invariant_delete x (t : tree23 T) :
  invariant t -> invariant (delete x t).
Proof.
rewrite /invariant /bst_list => /andP [H1 H2].
apply/andP; split; last by apply: complete_delete.
by rewrite inorder_delete23 //; apply: del_list_sorted.
Qed.

Corollary inv_isin_list (t : tree23 T) :
  invariant t ->
  isin23 t =i inorder23 t.
Proof. by rewrite /invariant => /andP [H1 _]; apply: inorder_isin_list. Qed.

Definition Set23 :=
  @ASetM.make _ _ (tree23 T)
    empty insert delete isin23
    inorder23 invariant
    invariant_empty erefl
    invariant_insert inorder_insert_list23
    invariant_delete inorder_delete_list23
    inv_isin_list.

End FunctionalCorrectness.

Section ConvertingList.
Context {A : eqType}.

Inductive tree23s A := Tr of (tree23 A)
                     | Trs of (tree23 A) & A & (tree23s A).

Fixpoint len (ts : tree23s A) : nat :=
  if ts is Trs _ _ ts then (len ts).+1 else 1.

Fixpoint inorder2 (ts : tree23s A) : seq A :=
  match ts with
  | Tr t => inorder23 t
  | Trs t a ts => inorder23 t ++ a :: inorder2 ts
  end.

Equations join_adj : tree23 A -> A -> tree23s A -> tree23s A :=
join_adj t1 a (Tr  t2)                 => Tr  (Node2 t1 a t2);
join_adj t1 a (Trs t2 b (Tr t3))       => Tr  (Node3 t1 a t2  b  t3);
join_adj t1 a (Trs t2 b (Trs t3 c ts)) => Trs (Node2 t1 a t2) b (join_adj t3 c ts).

Equations? join_all (ts : tree23s A) : tree23 A by wf (len ts) lt :=
join_all (Tr t)       => t;
join_all (Trs t a ts) => join_all (join_adj t a ts).
Proof.
apply: ssrnat.ltP=>{join_all}.
funelim (join_adj t a ts); simp join_adj=>//=.
rewrite -addn1 -[X in (_<=X)%N]addn1 leq_add2r.
by apply/ltn_trans/ltnSn/H.
Qed.

Lemma len_join_all t a ts : (len (join_adj t a ts) <= uphalf (len ts))%N.
Proof. by funelim (join_adj t a ts); simp join_adj. Qed.

Fixpoint leaves (xs : seq A) : tree23s A :=
  if xs is x::xs
    then Trs empty x (leaves xs)
    else Tr empty.

Definition tree23_of_list (xs : seq A) : tree23 A :=
  join_all (leaves xs).

(* Functional correctness *)

Lemma inorder_join_adj t a ts :
  inorder2 (join_adj t a ts) = inorder23 t ++ a :: inorder2 ts.
Proof.
funelim (join_adj t a ts); simp join_adj=>//=.
by rewrite H -catA.
Qed.

Lemma inorder_join_all (ts : tree23s A) :
  inorder23 (join_all ts) = inorder2 ts.
Proof.
funelim (join_all ts); simp join_all=>//=.
by rewrite H inorder_join_adj.
Qed.

Lemma inorder_of_list (xs : seq A) :
  inorder23 (tree23_of_list xs) = xs.
Proof.
rewrite /tree23_of_list inorder_join_all.
by elim: xs=>//=x xs ->.
Qed.

Fixpoint trees (ts : tree23s A) : seq (tree23 A) :=
  match ts with
  | Tr t => [::t]
  | Trs t _ ts => t :: trees ts
  end.

Lemma trees_height t a ts n :
  (forall t', t' \in t :: trees ts -> complete23 t' && (height23 t' == n)) ->
  forall t', t' \in trees (join_adj t a ts) -> complete23 t' && (height23 t' == n.+1).
Proof.
move=>H t'; funelim (join_adj t a ts); simp join_adj=>/=.
- rewrite inE=>/eqP->/=; rewrite -!andbA.
  rewrite /= in H.
  move: (H t1); rewrite inE eq_refl /= =>/(_ erefl); case/andP=>->/eqP->.
  move: (H t2); rewrite !inE eq_refl orbT /= =>/(_ erefl); case/andP=>->/eqP->.
  by rewrite maxnn addn1 !eq_refl.
- rewrite inE=>/eqP->/=; rewrite -!andbA.
  rewrite /= in H.
  move: (H t1); rewrite inE eq_refl /= =>/(_ erefl); case/andP=>->/eqP->.
  move: (H t2); rewrite !inE eq_refl orbT /= =>/(_ erefl); case/andP=>->/eqP->.
  move: (H t3); rewrite !inE eq_refl !orbT /= =>/(_ erefl); case/andP=>->/eqP->.
  by rewrite !maxnn addn1 !eq_refl.
rewrite inE; rewrite /= in H0; case/orP.
- move/eqP=>->/=.
  move: (H0 t1); rewrite inE eq_refl /= =>/(_ erefl); case/andP=>->/eqP->.
  move: (H0 t2); rewrite !inE eq_refl orbT /= =>/(_ erefl); case/andP=>->/eqP->.
  by rewrite maxnn addn1 !eq_refl.
apply: H=>t'' H''; apply: H0.
by rewrite !inE in H'' *; rewrite H'' !orbT.
Qed.

Lemma complete_joinall ts n :
  (forall t', t' \in trees ts -> complete23 t' && (height23 t' == n)) ->
  complete23 (join_all ts).
Proof.
move=>H; funelim (join_all ts).
- rewrite /= in H.
  by move: (H t); rewrite inE eq_refl=>/(_ erefl); case/andP.
by rewrite /= in H0; apply/H/trees_height/H0.
Qed.

Lemma trees_leaves t xs :
  t \in trees (leaves xs) -> complete23 t && (height23 t == 0).
Proof.
elim: xs=>/=; first by rewrite inE=>/eqP->.
by move=>_ xs IH; rewrite inE; case/orP=>// /eqP->.
Qed.

Lemma complete_tree_of_list xs : complete23 (tree23_of_list xs).
Proof. by apply: complete_joinall=>t; apply: trees_leaves. Qed.

(* Running Time Analysis *)

Equations T_join_adj : tree23s A -> nat :=
T_join_adj (Tr  _)                => 1;
T_join_adj (Trs _ _ (Tr _))       => 1;
T_join_adj (Trs _ _ (Trs _ _ ts)) => T_join_adj ts + 1.

Lemma T_join_adj_bound ts : (T_join_adj ts <= uphalf (len ts))%N.
Proof.
rewrite /=.
funelim (T_join_adj ts)=>//=.
rewrite -[X in (_<=X)%N]addn1 leq_add2r.
by apply: (leq_trans H); set n := len ts; elim: n.
Qed.

Equations? T_join_all (ts : tree23s A) : nat by wf (len ts) lt :=
T_join_all (Tr t)       => 1;
T_join_all (Trs t a ts) => T_join_adj ts + T_join_all (join_adj t a ts) + 1.
Proof.
apply: ssrnat.ltP=>{T_join_all}.
funelim (join_adj t a ts); simp join_adj=>//=.
rewrite -addn1 -[X in (_<=X)%N]addn1 leq_add2r.
by apply/ltn_trans/ltnSn/H.
Qed.

Lemma T_join_all_bound ts : (T_join_all ts <= 2*(len ts))%N.
Proof.
funelim (T_join_all ts)=>//=.
apply: (leq_trans (n := (uphalf (len ts) + 2*uphalf (len ts) + 1))).
- rewrite leq_add2r; apply: leq_add; first by exact: T_join_adj_bound.
  by apply: (leq_trans H); rewrite leq_mul2l /=; exact: len_join_all.
rewrite -[X in (_<=2*X)%N]addn1 mulnDr muln1 {3}(_ : 2 = 1+1) // addnA.
rewrite leq_add2r [X in (_<=X+1)%N]mul2n -addnn -addnA.
apply: leq_add; first by exact: uphalf_le.
rewrite uphalf_half mulnDr mul2n mul2n -addnn -addnA odd_double_half addnC leq_add2l.
by case: (odd _).
Qed.

Fixpoint T_leaves (xs : seq A) : nat :=
  if xs is x::xs then (T_leaves xs).+1 else 1%N.

Lemma T_leaves_size xs : T_leaves xs = (size xs).+1.
Proof. by elim: xs=>//=_ xs ->. Qed.

Definition T_tree23_of_list (xs : seq A) : nat :=
  T_leaves xs + T_join_all (leaves xs) + 1.

Lemma T_tree23_of_list_bound xs :
  (T_tree23_of_list xs <= 3 * size xs + 4)%N.
Proof.
rewrite /T_tree23_of_list (_ : 4 = 3 + 1) // addnA leq_add2r.
rewrite T_leaves_size (_ : 3 = 1 + 2) // mulnDl mul1n addnCA 2!addnA.
rewrite [X in (_ <= X + _ + _)%N]addnC addn1 -addnA leq_add2l.
apply: leq_trans; first by apply: T_join_all_bound.
rewrite -{3}(muln1 2) -mulnDr leq_mul2l /=.
by elim: xs.
Qed.

End ConvertingList.
