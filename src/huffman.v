From Equations Require Import Equations.
From Coq Require Import ssreflect ssrbool ssrfun.
From HB Require Import structures.
From mathcomp Require Import eqtype ssrnat seq bigop ssrAC.
From favssr Require Import prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TheImplementation.
Context {A : Type}.

(* TODO most of forest functions (fooF) here can probably be rewritten as maps/folds *)

Inductive tree A := Leaf of nat & A | Node of nat & tree A & tree A.

Definition forest A := seq (tree A).

Definition cachedWeight (t : tree A) : nat :=
  match t with
  | Leaf w _   => w
  | Node w _ _ => w
  end.

Definition uniteTrees (l r : tree A) : tree A :=
  Node (cachedWeight l + cachedWeight r) l r.

Fixpoint insortTree (u : tree A) (ts : forest A) : forest A :=
  if ts is t::s then
    if cachedWeight u <= cachedWeight t
      then u :: t :: s
      else t :: insortTree u s
  else [::u].

Lemma size_insortTree u ts : size (insortTree u ts) = (size ts).+1.
Proof. by elim: ts=>//=t s IH; case: ifP=>//= _; rewrite IH. Qed.

Equations? huffman (t0 : tree A) (ts : forest A) : tree A by wf (size ts) lt :=
huffman t0 [::]         => t0;
huffman _  [::t]        => t;
huffman t0 (t1::t2::ts) => huffman t0 (insortTree (uniteTrees t1 t2) ts).
Proof. by apply: ssrnat.ltP; rewrite size_insortTree. Qed.

End TheImplementation.

Lemma insortTree_notnil {A} (p : tree A) ts:
  ~~ nilp (insortTree p ts).
Proof. by case: ts=>//=t s; case: ifP. Qed.

Section EqTree.
Context {T : eqType}.

Fixpoint eqtree (t1 t2 : tree T) :=
  match t1, t2 with
  | Leaf w1 x1, Leaf w2 x2 => (w1 == w2) && (x1 == x2)
  | Node w1 l1 r1, Node w2 l2 r2 => [&& w1 == w2, eqtree l1 l2 & eqtree r1 r2]
  | _, _ => false
  end.

Lemma eqtreeP : Equality.axiom eqtree.
Proof.
move; elim=>[w1 x1|w1 l1 IHl r1 IHr][w2 x2|w2 l2 r2] /=; try by constructor.
apply: (iffP andP).
- by case=>/eqP->/eqP->.
by case=>->->.
have [<-/=|neqx] := w1 =P w2; last by apply: ReflectF; case.
- apply: (iffP andP).
- by case=>/IHl->/IHr->.
by case=><-<-; split; [apply/IHl|apply/IHr].
Qed.

HB.instance Definition _ := hasDecEq.Build (tree T) eqtreeP.
End EqTree.

Section BasicAuxiliaryFunctions.
Context {A : eqType}.

(* alphabets & intersection *)

Fixpoint alphabet (t : tree A) : pred A :=
  match t with
  | Leaf _ a => pred1 a
  | Node _ l r => [predU (alphabet l) & (alphabet r)]
  end.

Lemma exists_in_alphabet t :
  exists a, a \in alphabet t.
Proof.
elim: t=>/=[_ c|_ l IHl r _].
- by exists c; exact: eq_refl.
by case: IHl=>a Ha; exists a; rewrite !inE Ha.
Qed.

Fixpoint alphabetF (ts : forest A) : pred A :=
  if ts is t::s then [predU (alphabet t) & (alphabetF s)]
    else pred0.

Fixpoint enum (t : tree A) : seq A :=
  match t with
  | Leaf _ a => [::a]
  | Node _ l r => enum l ++ enum r
  end.

Fixpoint enumF (ts : forest A) : seq A :=
  if ts is t::s then enum t ++ enumF s
    else [::].

Lemma alphabet_enum t : alphabet t =i enum t.
Proof.
elim: t=>[w a|w l IHl r IHr] /= z.
- by rewrite in_cons in_nil orbF.
by rewrite !inE mem_cat (IHl z) (IHr z).
Qed.

Lemma alphabet_enumF t : alphabetF t =i enumF t.
Proof.
elim: t=>//=t s IH z.
by rewrite !inE mem_cat alphabet_enum IH.
Qed.

Lemma alphabetF_insortTree (p : tree A) ts :
  alphabetF (insortTree p ts) =i [predU (alphabet p) & (alphabetF ts)].
Proof.
elim: ts=>//=t s IH; case: ifP=>//= _ x.
by rewrite !inE IH !inE orbCA.
Qed.

Definition alpha_intersects p q := has (alphabet p) (enum q).

Definition alpha_intersectsF p qs := has (alphabet p) (enumF qs).

Lemma intersectsC p q : alpha_intersects p q = alpha_intersects q p.
Proof.
rewrite /alpha_intersects; elim: p=>/= _.
- by move=>a; rewrite has_pred1 orbF -(alphabet_enum q).
by move=>l IHl r IHr; rewrite has_predU has_cat IHl IHr.
Qed.

Lemma alpha_not p q :
  ~~ alpha_intersects p q <->
  (forall x, x \in alphabet p -> x \notin alphabet q).
Proof.
split.
- move=>Hi x Hp; apply/negP; rewrite alphabet_enum=>Hq.
  by move/hasPn: Hi=>/(_ x Hq); move: Hp; rewrite -topredE /==>->.
move=>H; rewrite intersectsC /alpha_intersects; apply/hasPn=>z; rewrite -alphabet_enum.
by move/H; rewrite -topredE /=.
Qed.

Lemma alpha_notF p q :
  ~~ alpha_intersectsF p q <->
  (forall x, x \in alphabet p -> x \notin alphabetF q).
Proof.
split.
- move=>Hi x Hp; apply/negP; rewrite alphabet_enumF=>Hq.
  by move/hasPn: Hi =>/(_ x Hq); move: Hp; rewrite -topredE /==>->.
move=>H; rewrite /alpha_intersectsF; apply/hasPn=>z; rewrite -alphabet_enumF=>Hq.
by apply/negP=>/H; rewrite Hq.
Qed.

Lemma alpha_notFC p q :
  ~~ alpha_intersectsF p q <->
  (forall x, x \in alphabetF q -> x \notin alphabet p).
Proof.
split.
- by move=>Hi x; apply/contraL; move: x; apply/alpha_notF.
move=>H; rewrite /alpha_intersectsF; apply/hasPn=>z; rewrite -alphabet_enumF.
by apply: H.
Qed.

Lemma not_intersects p q x :
  ~~ alpha_intersects p q ->
  [\/ (x \in    alphabet p) /\ (x \notin alphabet q)
    , (x \notin alphabet p) /\ (x \in    alphabet q)
    | (x \notin alphabet p) /\ (x \notin alphabet q)
  ].
Proof.
move=>Hi.
case/boolP: (x \in alphabet p)=>Hp; case/boolP: (x \in alphabet q)=>Hq /=; try by constructor.
by move/alpha_not: Hi=>/(_ _ Hp); rewrite Hq.
Qed.

Lemma alpha_intersectsF_cons (p : tree A) q ts :
  alpha_intersectsF p (q::ts) = alpha_intersects p q || alpha_intersectsF p ts.
Proof. by rewrite /alpha_intersects /alpha_intersectsF /= has_cat. Qed.

Lemma alpha_intersectsF_uniteTrees (p : tree A) q ts :
  alpha_intersectsF (uniteTrees p q) ts = alpha_intersectsF p ts || alpha_intersectsF q ts.
Proof. by rewrite /alpha_intersectsF /uniteTrees /= has_predU. Qed.

Lemma intersectsF_insortTree (p : tree A) q ts :
  alpha_intersectsF p (insortTree q ts) = alpha_intersects p q || alpha_intersectsF p ts.
Proof.
rewrite /alpha_intersects /alpha_intersectsF; elim: ts=>/=.
- by rewrite cats0 orbF.
move=>t s IH; case: ifP=>/= _; rewrite !has_cat //.
by rewrite IH orbCA.
Qed.

(* consistency *)

Fixpoint consistent (t : tree A) : bool :=
  if t is Node _ l r
    then [&& ~~ alpha_intersects l r,
             consistent l &
             consistent r]
    else true.

Fixpoint consistentF (ts : forest A) : bool :=
  if ts is t::s
    then [&& ~~ alpha_intersectsF t s,
             consistent t &
             consistentF s]
  else true.

Lemma consistent_ind (P : tree A -> A -> Prop) t a:
  consistent t ->
  (forall w b a, P (Leaf w b) a) ->
  (forall w l r a,
     consistent l -> consistent r ->
     ~~ alpha_intersects l r ->
     a \in alphabet l -> a \notin alphabet r ->
     P l a -> P r a ->
     P (Node w l r) a) ->
  (forall w l r a,
     consistent l -> consistent r ->
     ~~ alpha_intersects l r ->
     a \notin alphabet l -> a \in alphabet r ->
     P l a -> P r a ->
     P (Node w l r) a) ->
  (forall w l r a,
     consistent l -> consistent r ->
     ~~ alpha_intersects l r ->
     a \notin alphabet l -> a \notin alphabet r ->
     P l a -> P r a ->
     P (Node w l r) a) ->
  P t a.
Proof.
move=>Hc H0 Hl Hr Hb; elim: t Hc=>[w b|w l IHl r IHr] /=.
- by move=>_; apply: H0.
case/and3P=>Hi Hcl Hcr.
case: (not_intersects a Hi); case=>Hil Hir.
- by apply: Hl=>//; [apply: IHl|apply: IHr].
- by apply: Hr=>//; [apply: IHl|apply: IHr].
by apply: Hb=>//; [apply: IHl|apply: IHr].
Qed.

Lemma consistentF_insortTree (p : tree A) ts :
  consistentF (insortTree p ts) = consistentF (p::ts).
Proof.
elim: ts=>//=t s IH; case: ifP=>//= _.
rewrite intersectsF_insortTree IH alpha_intersectsF_cons !negb_or intersectsC.
by rewrite !andbA (ACl (1*4*5*2*3*6)%AC).
Qed.

(* tree metrics *)

Fixpoint depth (t : tree A) (a : A) : nat :=
  if t is Node _ l r then
    if a \in alphabet l
      then depth l a + 1
      else if a \in alphabet r
        then depth r a + 1
        else 0
  else 0.

Fixpoint height (t : tree A) : nat :=
  if t is Node _ l r
    then maxn (height l) (height r) + 1
  else 0.

Fixpoint heightF (ts : forest A) : nat :=
  if ts is t::s
    then maxn (height t) (heightF s)
    else 0.

Lemma heightE (t : tree A) : reflect (exists w x, t = Leaf w x) (height t == 0).
Proof.
apply: (iffP idP); last by case=>w[x]->.
case: t=>[w x|w l r] /=; last by rewrite addn1.
by move=>_; exists w, x.
Qed.

Lemma depth_le_height t a :
  depth t a <= height t.
Proof.
elim: t=>//=_ l IHl r IHr; case: ifP=>_.
- by rewrite leq_add2r leq_max IHl.
case: ifP=>_.
- by rewrite leq_add2r leq_max IHr orbT.
by rewrite addn1.
Qed.

Lemma exists_at_height t :
  consistent t -> exists2 a, a \in alphabet t & depth t a = height t.
Proof.
elim: t=>/=[_ a|_ l IHl r IHr].
- move=>_; exists a=>//; apply: eq_refl.
case/and3P=>Hi Hl Hr.
case: (IHl Hl)=>al Hal Hdl.
case: (IHr Hr)=>ar Har Hdr.
case: (leqP (height r) (height l))=>H.
- exists al; rewrite ?inE Hal //.
  by rewrite Hdl.
 exists ar; rewrite ?inE Har; first by rewrite orbT.
 move: Hi; rewrite intersectsC=>/alpha_not/(_ _ Har)/negbTE->.
 by rewrite Hdr.
Qed.

Lemma height_gt0_alphabet_eq t u :
  0 < height t -> consistent t -> alphabet t =i alphabet u ->
  0 < height u.
Proof.
case: t=>//=_ l r _; case/and3P=>Hi Hl Hr.
case: (exists_in_alphabet l)=>b Hb.
case: (exists_in_alphabet r)=>c Hc.
case/boolP: (b==c).
- move/eqP=>E; rewrite -E in Hc.
  by move/alpha_not: Hi=>/(_ _ Hb); rewrite Hc.
move=>Hbc; case: u=>/=[_ a|_ lu ru]; last by rewrite addn1.
move=>H; move: (H b) (H c); rewrite !inE Hb Hc /= orbT => Hba Hca.
symmetry in Hba; move/eqP: Hba=>Hba; rewrite -Hba in Hca.
by symmetry in Hca; move/eqP: Hca=>Hca; rewrite Hca eq_refl in Hbc.
Qed.

Lemma heightF_insortTree (p : tree A) ts :
  heightF (insortTree p ts) = maxn (height p) (heightF ts).
Proof.
elim: ts=>//= t s IH; case: ifP=>//= _.
by rewrite IH maxnCA.
Qed.

Fixpoint freq (t : tree A) (b : A) : nat :=
  match t with
  | Leaf w a => if b == a then w else 0
  | Node _ l r => freq l b + freq r b
  end.

Fixpoint freqF (ts : forest A) (b : A) : nat :=
  if ts is t::s
    then freq t b + freqF s b
    else 0.

Lemma notin_alphabet_freq_0 a t :
  a \notin alphabet t -> freq t a = 0.
Proof.
elim: t=>[w b|_ l IHl r IHr] /=; rewrite !inE.
- by move/negbTE=>->.
by rewrite negb_or; case/andP=>/IHl->/IHr->.
Qed.

Lemma notin_alphabet_freqF_0 a ts :
  a \notin alphabetF ts -> freqF ts a = 0.
Proof.
elim: ts=>//=t s IH; rewrite !inE negb_or.
by case/andP=>/notin_alphabet_freq_0->/IH->.
Qed.

Lemma heightF_0_Leaf_freqF ts a :
  consistentF ts -> heightF ts = 0 -> a \in alphabetF ts ->
  Leaf (freqF ts a) a \in ts.
Proof.
elim: ts=>//=t s IH; case/and3P=>Hi Hct Hcs.
move/eqP; rewrite maxn_eq0; case/andP=>/heightE [w][x] Et /= Hs.
rewrite Et /= in Hi *.
rewrite !inE; case: eqP=>/= [Ea|_].
- move/alpha_notF: Hi=>/=; rewrite -Ea.
  move=>/(_ a); rewrite inE eq_refl=>/(_ erefl) Has _.
  by rewrite notin_alphabet_freqF_0 // addn0 eq_refl.
rewrite add0n=>Has; apply/orP; right; apply: IH=>//.
by apply/eqP.
Qed.

Lemma freqF_insortTree (p : tree A) ts a :
  freqF (insortTree p ts) a = freq p a + freqF ts a.
Proof.
elim: ts=>//=t s IH; case: ifP=>//= _.
by rewrite IH addnCA.
Qed.

Fixpoint weight (t : tree A) : nat :=
  match t with
  | Leaf w _ => w
  | Node _ l r => weight l + weight r
  end.

Lemma height_0_cachedWeight t:
  height t = 0 -> cachedWeight t = weight t.
Proof. by case: t=>//=n l r; rewrite addn1. Qed.

Fixpoint cost (t : tree A) : nat :=
  if t is Node _ l r
    then weight l + cost l + weight r + cost r
  else 0.

(* optimality *)

Definition optimum (t : tree A) : Prop :=
  forall u, consistent u ->
            alphabet t =i alphabet u ->
            freq t =1 freq u ->
            cost t <= cost u.

(* siblings *)

(* weird that equations can't see t is decreasing *)
Equations? sibling (t : tree A) (a : A) : A by wf (height t) lt :=
sibling (Leaf _ _) a => a;
sibling (Node _ (Leaf _ b) (Leaf _ c)) a =>
  if a == b then c else if a == c then b else a;
sibling (Node _ l r) a =>
  if a \in alphabet l then sibling l a
    else if a \in alphabet r then sibling r a
      else a.
Proof.
all: apply: ssrnat.ltP.
- by rewrite addn1.
- by rewrite ltn_add2r max0n addn1.
- by rewrite ltn_add2r leq_max addn1 ltnS leqnn.
by rewrite addn1 ltnS leq_max leqnn orbT.
Qed.

Lemma in_alphabet_sibling t a:
  a \in alphabet t -> sibling t a \in alphabet t.
Proof.
funelim (sibling t a)=>//; simp sibling=>/=; rewrite !inE.
- case/orP=>->; first by rewrite eq_refl orbT.
  by case: ifP=>_; rewrite eq_refl // orbT.
- case/or3P=>E; rewrite !E //= ?orbT.
  - case: ifP; first by move=>->.
    move=>_; apply/orP; right.
    by move: H0=>/=; rewrite !inE; apply; rewrite E.
  case: ifP; first by move=>->.
  move=>_; apply/orP; right.
  by move: H0=>/=; rewrite !inE; apply; rewrite E orbT.
rewrite -orbA; case/or3P=>E; rewrite E /= ?orbT.
- apply/orP; left.
  by move: H=>/=; rewrite !inE; apply; rewrite E.
- apply/orP; left.
  by move: H=>/=; rewrite !inE; apply; rewrite E orbT.
case: ifP.
- move=>Hlr; apply/orP; left.
  by move: H=>/=; rewrite !inE; apply.
by move=>_; rewrite (H0 E) orbT.
Qed.

Lemma notin_alphabet_sibling_id a t :
  a \notin alphabet t -> sibling t a = a.
Proof.
funelim (sibling t a)=>//; simp sibling=>/=; rewrite !inE !negb_or -?andbA.
- by case/andP=>/negbTE->/negbTE->.
- by case/and3P=>/negbTE->/negbTE->/negbTE->.
by case/and3P=>/negbTE->/negbTE->/negbTE->.
Qed.

Corollary sibling_ne_in_alphabet t a :
  sibling t a != a -> sibling t a \in alphabet t.
Proof.
move=>H; apply: in_alphabet_sibling; move: H.
by apply: contraR=>H; apply/eqP/notin_alphabet_sibling_id.
Qed.

Lemma height_gt0_sibling w p q a :
  (0 < height p) || (0 < height q) ->
  sibling (Node w p q) a =
    if a \in alphabet p then sibling p a else sibling q a.
Proof.
case: q=>[wq q|wq ql qr]; case: p=>[wp p|wp pl pr]; simp sibling=>/=.
- by rewrite ltnn.
- by move=>_; rewrite !inE if_same.
- move=>_; rewrite !inE; case: ifP=>//_; case: ifP=>//.
  by move/negbT=>H; rewrite notin_alphabet_sibling_id.
move=>_; rewrite !inE; case: ifP=>//_; case: ifP=>//.
by move/negbT=>H; rewrite notin_alphabet_sibling_id.
Qed.

Lemma sibling_consistent_ind (P : tree A -> A -> Prop) t a :
  consistent t ->
  (forall w b a, P (Leaf w b) a) ->
  (forall w wb b wc c a,
     b != c -> P (Node w (Leaf wb b) (Leaf wc c)) a) ->
  (forall w l r a,
     consistent l -> consistent r ->
     ~~ alpha_intersects l r ->
     (0 < height l) || (0 < height r) ->
     a \in alphabet l -> sibling l a \in alphabet l ->
     a \notin alphabet r -> sibling l a \notin alphabet r ->
     P l a ->
     P (Node w l r) a) ->
  (forall w l r a,
     consistent l -> consistent r ->
     ~~ alpha_intersects l r ->
     (0 < height l) || (0 < height r) ->
     a \notin alphabet l -> sibling r a \notin alphabet l ->
     a \in alphabet r -> sibling r a \in alphabet r ->
     P r a ->
     P (Node w l r) a) ->
  (forall w l r a,
     consistent l -> consistent r ->
     ~~ alpha_intersects l r ->
     (0 < height l) || (0 < height r) ->
     a \notin alphabet l -> a \notin alphabet r ->
     P (Node w l r) a) ->
  P t a.
Proof.
move=>Hc H0 Hn Hl Hr Hb; elim: t Hc=>[w b|w l IHl r IHr] /=.
- by move=>_; apply: H0.
case/and3P=>Hi Hcl Hcr.
case: (posnP (height l + height r)).
- move/eqP; rewrite addn_eq0; case/andP.
  case/heightE=>[wb][b] El; case/heightE=>[wc][c] Er.
  move: Hi; rewrite El Er /alpha_intersects /= orbF eq_sym.
  by apply: Hn.
rewrite addn_gt0=>Hh.
case: (not_intersects a Hi); case=>Hil Hir.
- have Hsl : sibling l a \in alphabet l by apply: in_alphabet_sibling.
  by apply: Hl=>//; [move/alpha_not: Hi; apply |apply: IHl].
- have Hsr : sibling r a \in alphabet r by apply: in_alphabet_sibling.
  apply: Hr=>//; last by apply: IHr.
  by move: Hi; rewrite intersectsC=>/alpha_not; apply.
by apply: Hb.
Qed.

Lemma sibling_sibling_id t a :
  consistent t -> sibling t (sibling t a) = a.
Proof.
move=>H.
apply: (sibling_consistent_ind (P:=fun t a => sibling t (sibling t a) = a))=>{a}//=.
- move=>w wb b wc c a /negbTE Hbc; simp sibling.
  case/boolP: (a==b)=>[/eqP->|/negbTE Hab]; first by rewrite eq_sym Hbc eq_refl.
  case/boolP: (a==c)=>[/eqP->|/negbTE Hac]; first by rewrite eq_refl.
  by rewrite Hab Hac.
- move=>w l r a _ _ _ Hh Hal Hsal _ _ IH.
  by rewrite height_gt0_sibling // height_gt0_sibling // Hal Hsal.
- move=>w l r a _ _ _ Hh /negbTE Hal /negbTE Hsal Har Hsar IH.
  by rewrite height_gt0_sibling // height_gt0_sibling // Hal Hsal.
move=>w l r a _ _ _ Hh Hal Har.
by rewrite !notin_alphabet_sibling_id //= !inE negb_or Hal Har.
Qed.

Corollary sibling_reciprocal t a b :
  consistent t -> sibling t a = b -> sibling t b = a.
Proof. by move=>H <-; apply: sibling_sibling_id. Qed.

Lemma depth_height_sibling_ne t a :
  consistent t -> depth t a = height t -> 0 < height t ->
  a \in alphabet t ->
  sibling t a != a.
Proof.
move=>H.
apply: (sibling_consistent_ind (P:=fun t a => depth t a = height t -> 0 < height t -> a \in alphabet t -> sibling t a != a))=>{a}//=.
- move=>w wb b wc c a Hbc.
  rewrite !inE maxn0 add0n; simp sibling; case: ifP=>/=.
  - by move/eqP=>-> _ _ _; rewrite eq_sym.
  by move=>_; case: ifP=>// /eqP->.
- move=>w l r a _ _ _ Hh Hal _ _ _.
  rewrite height_gt0_sibling // Hal =>IH /eqP; rewrite eqn_add2r=>E _ _.
  apply: IH=>//.
  - case: (leqP (height r) (height l)) E; first by move=>_/eqP.
    by move=>Hlr /eqP Hd; move: (depth_le_height l a); rewrite Hd leqNgt Hlr.
  case: (posnP (height l))=>// El; rewrite El ltnn /= in Hh.
  case/eqP/heightE: El=>[wl][xl]El; rewrite El /= max0n eq_sym in E.
  by move: Hh; move/eqP: E=>->.
- move=>w l r a _ _ _ Hh /negbTE Hal _ Har _.
  rewrite height_gt0_sibling // Hal Har =>IH /eqP; rewrite eqn_add2r=>E _ _.
  apply: IH=>//.
  - case: (leqP (height l) (height r)) E; first by move=>_/eqP.
    by move=>Hrl /eqP Hd; move: (depth_le_height r a); rewrite Hd leqNgt Hrl.
  case: (posnP (height r))=>// Er; rewrite Er ltnn /= orbF in Hh.
  case/eqP/heightE: Er=>[wr][xr]Er; rewrite Er /= maxn0 eq_sym in E.
  by move: Hh; move/eqP: E=>->.
by move=>w l r a _ _ _ _ /negbTE Hal /negbTE Har _ _; rewrite !inE Hal Har.
Qed.

Lemma depth_sibling t a :
  consistent t -> depth t (sibling t a) = depth t a.
Proof.
move=>H.
apply: (sibling_consistent_ind (P:=fun t a => depth t (sibling t a) = depth t a))=>{a}//=.
- move=>w wb b wc c a /negbTE Hbc; simp sibling; rewrite !inE.
  case/boolP: (a==b)=>[_|/negbTE Hab].
  - by rewrite eq_sym Hbc eq_refl.
  case/boolP: (a==c); first by rewrite eq_refl.
  by rewrite Hab =>/negbTE->.
- move=>w l r a _ _ _ Hh Hal Hsal _ _ IH.
  by rewrite height_gt0_sibling // Hal Hsal IH.
- move=>w l r a _ _ _ Hh /negbTE Hal /negbTE Hsal Har Hsar IH.
  by rewrite height_gt0_sibling // Hal Hsal Har Hsar IH.
move=>w l r a _ _ _ Hh Hal Har.
rewrite notin_alphabet_sibling_id; last by rewrite /= !inE negb_or Hal Har.
by rewrite (negbTE Hal) (negbTE Har).
Qed.

End BasicAuxiliaryFunctions.

Arguments consistent_ind [A P].

Section OtherFunctions.
Context {A : eqType}.

(* swapping *)

Fixpoint swapLeaves (t : tree A) (wa : nat) (a : A) (wb : nat) (b : A) : tree A :=
  match t with
  | Leaf wc c =>
      if c == a then Leaf wb b else
        if c == b then Leaf wa a else
          Leaf wc c
  | Node w l r =>
      Node w (swapLeaves l wa a wb b) (swapLeaves r wa a wb b)
  end.

Lemma swapLeaves_id_notin_alphabet t w v a :
  a \notin alphabet t -> swapLeaves t w a v a = t.
Proof.
elim: t=>[n b|n l IHl r IHr] /=; rewrite !inE.
- by rewrite eq_sym=>/negbTE->.
by rewrite negb_or; case/andP=>/IHl->/IHr->.
Qed.

Lemma swapLeaves_id t a :
  consistent t -> swapLeaves t (freq t a) a (freq t a) a = t.
Proof.
(* TODO make nicer? *)
move=>H.
apply: (consistent_ind (P:=fun t a => swapLeaves t (freq t a) a (freq t a) a = t))=>{a}//=.
- by move=>w b a; case: eqP=>//->; rewrite eq_refl.
- move=>w l r a Hcl Hcr Hi Hal Har IHl IHr.
  by rewrite (notin_alphabet_freq_0 Har) addn0 IHl swapLeaves_id_notin_alphabet.
- move=>w l r a Hcl Hcr Hi Hal Har IHl IHr.
  by rewrite (notin_alphabet_freq_0 Hal) add0n IHr swapLeaves_id_notin_alphabet.
move=>w l r a Hcl Hcr Hi Hal Har IHl IHr.
by rewrite (notin_alphabet_freq_0 Hal) (notin_alphabet_freq_0 Har) addn0
  swapLeaves_id_notin_alphabet // swapLeaves_id_notin_alphabet.
Qed.

Lemma alphabet_swapLeaves t wa a wb b :
  alphabet (swapLeaves t wa a wb b) =i
    if a \in alphabet t then
      if b \in alphabet t
        then alphabet t
        else [predU1 b & [predD1 (alphabet t) & a]]
    else
      if b \in alphabet t
        then [predU1 a & [predD1 (alphabet t) & b]]
        else SimplPred (alphabet t).
Proof.
move=>x; elim: t=>/=[w c|w l IHl r IHr]; rewrite !inE.
- case: ifP.
  - move/eqP=><-; rewrite eq_refl /= inE.
    case: ifP; first by move/eqP=>->.
    by move=>_; rewrite !inE andNb orbF.
  rewrite eq_sym=>->; case: ifP.
  - by move/eqP=>->; rewrite eq_refl /= !inE andNb orbF.
  by rewrite eq_sym=>->/=; rewrite inE.
rewrite {}IHl {}IHr.
case/boolP: (a \in alphabet l)=>Hal; case/boolP: (a \in alphabet r)=>Har;
case/boolP: (b \in alphabet l)=>Hbl; case/boolP: (b \in alphabet r)=>Hbr;
rewrite /= !inE //;
case: eqP=>[->|_]; case: eqP=>[->|_] //=;
rewrite ?orbT ?orbF ?Hal ?Hbl ?Har ?Hbr ?orbT //.
- by move/negbTE: Har; rewrite -topredE.
- by move/negbTE: Hal; rewrite -topredE.
- by move/negbTE: Hbr; rewrite -topredE.
by move/negbTE: Hbl; rewrite -topredE.
Qed.

Lemma consistent_swapLeaves t wa a wb b :
  consistent t -> consistent (swapLeaves t wa a wb b).
Proof.
elim: t=>[w c|w l IHl r IHr]/=.
- by move=>_; case: ifP=>//_; case: ifP.
case/and3P=>Hi Hl Hr; rewrite IHl // IHr //= andbT.
apply/alpha_not=>z; rewrite !alphabet_swapLeaves.
case: (not_intersects a Hi)=>[[        Hail /negbTE Hair]
                             |[/negbTE Hail         Hair]
                             |[/negbTE Hail /negbTE Hair]];
case: (not_intersects b Hi)=>[[        Hbil /negbTE Hbir]
                             |[/negbTE Hbil         Hbir]
                             |[/negbTE Hbil /negbTE Hbir]];
rewrite Hail Hair Hbil Hbir ?inE //.
- by move/alpha_not: Hi; apply.
- case: eqP=>[->|_] /=; rewrite negb_or.
  - by rewrite andbT=>_; apply/eqP=>Hba; rewrite Hba Hail in Hbil.
  by case: eqP=>//=_; move/alpha_not: (Hi); apply.
- case: eqP=>[->|_] /=; first by move=>_; move: Hbir; rewrite -topredE /= =>->.
  by case/andP=>_; move/alpha_not: (Hi); apply.
- case: eqP=>[->|_] /=; rewrite negb_or.
  - by rewrite andbT=>_; apply/eqP=>Hab; rewrite Hab Hbil in Hail.
  by case: eqP=>//=_; move/alpha_not: (Hi); apply.
- by move/alpha_not: Hi; apply.
- rewrite negb_or; case: eqP=>[->|_] /=.
  - by move: Hbil; rewrite -topredE /= =>->.
  by case: eqP=>[->|_] //=; move/alpha_not: Hi; apply.
- case: eqP=>[->|_] /=; first by move=>_; move: Hair; rewrite -topredE /= =>->.
  by case: eqP=>//=_; move/alpha_not: (Hi); apply.
- rewrite negb_or; case: eqP=>[->|_] /=.
  - by move: Hail=>/[swap]; rewrite -topredE /= =>->.
  by case: eqP=>[->|_] //=; move/alpha_not: Hi; apply.
by move/alpha_not: Hi; apply.
Qed.

Lemma depth_swapLeaves t wa a wb b c :
  consistent t -> c != a -> c != b ->
  depth (swapLeaves t wa a wb b) c = depth t c.
Proof.
move=>H.
apply: (consistent_ind (P:=fun t c => c != a -> c != b -> depth (swapLeaves t wa a wb b) c = depth t c))=>{c}//=.
- by move=>w d c _ _; case: ifP=>//=_; case: ifP.
- move=>_ l r c _ _ Hi Hcl _ IHl IHr Hca Hcb.
  rewrite !alphabet_swapLeaves Hcl IHl // IHr //.
  case: (not_intersects a Hi)=>[[        Hail /negbTE Hair]
                               |[/negbTE Hail         Hair]
                               |[/negbTE Hail /negbTE Hair]];
  case: (not_intersects b Hi)=>[[        Hbil /negbTE Hbir]
                               |[/negbTE Hbil         Hbir]
                               |[/negbTE Hbil /negbTE Hbir]];
  rewrite Hail Hair Hbil Hbir ?inE ?Hcl ?Hca ?Hcb /= ?orbT //.
  - by move: Hcl; rewrite -topredE /==>->.
  - by move: Hcl; rewrite -topredE /==>->.
  - by move: Hcl; rewrite -topredE /==>->.
  by move: Hcl; rewrite -topredE /==>->.
- move=>_ l r c _ _ Hi /negbTE Hcl Hcr IHl IHr Hca Hcb.
  rewrite !alphabet_swapLeaves Hcl Hcr IHl // IHr //.
  case: (not_intersects a Hi)=>[[        Hail /negbTE Hair]
                               |[/negbTE Hail         Hair]
                               |[/negbTE Hail /negbTE Hair]];
  case: (not_intersects b Hi)=>[[        Hbil /negbTE Hbir]
                               |[/negbTE Hbil         Hbir]
                               |[/negbTE Hbil /negbTE Hbir]];
  rewrite Hail Hair Hbil Hbir ?inE ?Hcl ?Hcr ?Hca ?Hcb /= ?orbT ?andbF ?andbT ?orbF.
  - by move: Hcr; rewrite -topredE /==>->.
  - by rewrite (negbTE Hcb).
  - by rewrite (negbTE Hcb); move: Hcr; rewrite -topredE /==>->.
  - by rewrite (negbTE Hca).
  - by move: Hcl; rewrite -topredE /==>->.
  - by move: Hcl; rewrite -topredE /==>->.
  - by rewrite (negbTE Hca); move: Hcr; rewrite -topredE /==>->.
  - by move: Hcl; rewrite -topredE /==>->.
  by move: Hcl Hcr; rewrite -!topredE /==>->->.
move=>_ l r c _ _ Hi /negbTE Hcl /negbTE Hcr IHl IHr Hca Hcb.
rewrite !alphabet_swapLeaves Hcl Hcr IHl // IHr //.
case: (not_intersects a Hi)=>[[        Hail /negbTE Hair]
                             |[/negbTE Hail         Hair]
                             |[/negbTE Hail /negbTE Hair]];
case: (not_intersects b Hi)=>[[        Hbil /negbTE Hbir]
                             |[/negbTE Hbil         Hbir]
                             |[/negbTE Hbil /negbTE Hbir]];
rewrite Hail Hair Hbil Hbir ?inE ?Hcl ?Hcr ?Hca ?Hcb /= ?andbF ?andbT ?orbF.
- by move: Hcr; rewrite -topredE /==>->.
- by rewrite (negbTE Hcb) (negbTE Hca).
- by rewrite (negbTE Hcb); move: Hcr; rewrite -topredE /==>->.
- by rewrite (negbTE Hca) (negbTE Hcb).
- by move: Hcl; rewrite -topredE /==>->.
- by move: Hcl; rewrite (negbTE Hcb) -topredE /==>->.
- by rewrite (negbTE Hca); move: Hcr; rewrite -topredE /==>->.
- by move: Hcl; rewrite (negbTE Hca) -topredE /==>->.
by move: Hcl Hcr; rewrite -!topredE /==>->->.
Qed.

Lemma height_swapLeaves t wa a wb b :
  height (swapLeaves t wa a wb b) = height t.
Proof.
elim: t=>/=[w c|_ l IHl r IHr]; first by case: ifP=>//_; case: ifP.
by rewrite IHl IHr.
Qed.

Lemma freq_swapLeaves t a b wa wb c :
  consistent t -> a != b ->
  freq (swapLeaves t wa a wb b) c =
    if c == a
      then if b \in alphabet t then wa else 0
      else if c == b then
        if a \in alphabet t then wb else 0
        else freq t c.
Proof.
elim: t=>/=[w d|_ l IHl r IHr].
- rewrite eq_sym=>_ Hba; rewrite !inE; case: eqP=>[->|/eqP Hda] /=.
  - rewrite eq_refl (negbTE Hba).
    case: eqP=>[->|_]; first by rewrite (negbTE Hba).
    by case: ifP=>//->.
  case: eqP=>[->|/eqP Hdb] /=.
  - rewrite eq_refl (eq_sym a b) (negbTE Hba).
    by case: eqP=>//_; case: ifP=>//->.
  move: (Hda); rewrite eq_sym=>/negbTE->.
  move: (Hdb); rewrite eq_sym=>/negbTE->.
  case: eqP=>[->|_]; first by rewrite (negbTE Hda) (negbTE Hdb).
  by rewrite !if_same.
case/and3P=>Hi Hl Hr Hab. rewrite IHl // IHr // !inE.
case: ifP=>_.
- case: (not_intersects b Hi); case=>Hil Hir.
  - by rewrite Hil (negbTE Hir) /= addn0.
  - by rewrite (negbTE Hil) Hir /= add0n.
  by rewrite (negbTE Hil) (negbTE Hir).
case: ifP=>_ //.
case: (not_intersects a Hi); case=>Hil Hir.
- by rewrite Hil (negbTE Hir) /= addn0.
- by rewrite (negbTE Hil) Hir /= add0n.
by rewrite (negbTE Hil) (negbTE Hir).
Qed.

Lemma weight_swapLeaves t a b wa wb :
  consistent t -> a != b ->
  if a \in alphabet t then
    if b \in alphabet t then
      weight (swapLeaves t wa a wb b) + freq t a + freq t b =
        weight t + wa + wb
    else
      weight (swapLeaves t wa a wb b) + freq t a = weight t + wb
  else
    if b \in alphabet t then
      weight (swapLeaves t wa a wb b) + freq t b = weight t + wa
    else
      weight (swapLeaves t wa a wb b) = weight t.
Proof.
move=>H; apply: (consistent_ind (P:=fun t a => a != b -> if a \in alphabet t then if _ then _ = _ else _ else _)) =>{a}//=.
- move=>w c a Hab; rewrite !inE; case: eqP; case: eqP.
  - by move=><- E; rewrite E eq_refl in Hab.
  - by move=>/[swap]<-; rewrite eq_sym eq_refl addnC.
  - by move=><-; rewrite eq_sym eq_refl=>/eqP/negbTE->; rewrite addnC.
  move/eqP/negbTE; rewrite eq_sym=>->.
  by move/eqP/negbTE; rewrite eq_sym=>->.
- move=>_ l r a Hcl Hcr Hi Hal Har IHl IHr Hab; rewrite !inE.
  move: (IHr Hab); move: (IHl Hab).
  rewrite Hal (negbTE Har) (notin_alphabet_freq_0 Har) addn0 /=.
  case: (not_intersects b Hi); case=>Hbl Hbr.
  - rewrite Hbl (negbTE Hbr) (notin_alphabet_freq_0 Hbr) /= =>H0->.
    by rewrite addn0 (ACl ((1*3*4)*2)%AC) /= H0 (ACl (1*4*2*3)%AC).
  - rewrite (negbTE Hbl) (notin_alphabet_freq_0 Hbl) /= Hbr =>H0 H1.
    by rewrite add0n (ACl ((1*3)*(2*4))%AC) /= H0 H1 addnA (ACl (1*3*4*2)%AC).
  rewrite (negbTE Hbl) (negbTE Hbr) /= =>H0->.
  by rewrite addnAC H0 addnAC.
- move=>_ l r a Hcl Hcr Hi Hal Har IHl IHr Hab; rewrite !inE.
  move: (IHr Hab); move: (IHl Hab).
  rewrite (negbTE Hal) Har (notin_alphabet_freq_0 Hal) add0n /=.
  case: (not_intersects b Hi); case=>Hbl Hbr.
  - rewrite Hbl (negbTE Hbr) (notin_alphabet_freq_0 Hbr) /= =>H0 H1.
    by rewrite addn0 (ACl ((1*4)*(2*3))%AC) /= H0 H1 addnA (ACl (1*3*2*4)%AC).
  - rewrite (negbTE Hbl) Hbr (notin_alphabet_freq_0 Hbl) /= =>->H1.
    by rewrite add0n (ACl (1*(2*3*4))%AC) /= H1 !addnA.
  rewrite (negbTE Hbl) (negbTE Hbr) /= =>->H1.
  by rewrite -addnA H1 addnA.
move=>_ l r a Hcl Hcr Hi Hal Har IHl IHr Hab; rewrite !inE.
move: (IHr Hab); move: (IHl Hab); rewrite (negbTE Hal) (negbTE Har) /=.
case: (not_intersects b Hi); case=>Hbl Hbr.
- rewrite Hbl (negbTE Hbr) (notin_alphabet_freq_0 Hbr) /= =>H0->.
  by rewrite addn0 addnAC H0 addnAC.
- rewrite (negbTE Hbl) Hbr (notin_alphabet_freq_0 Hbl) /= =>->H1.
  by rewrite add0n -addnA H1 addnA.
by rewrite (negbTE Hbl) (negbTE Hbr) /= =>->->.
Qed.

Lemma cost_swapLeaves t a b wa wb :
  a != b -> consistent t ->
  if a \in alphabet t then
    if b \in alphabet t then
      cost (swapLeaves t wa a wb b) + freq t a * depth t a + freq t b * depth t b =
        cost t + wa * depth t b + wb * depth t a
    else
      cost (swapLeaves t wa a wb b) + freq t a * depth t a =
        cost t + wb * depth t a
  else
    if b \in alphabet t then
      cost (swapLeaves t wa a wb b) + freq t b * depth t b =
        cost t + wa * depth t b
    else
      cost (swapLeaves t wa a wb b) = cost t.
Proof.
move=>Hab; elim: t=>/=[w c|w l IHl r IHr]; rewrite !inE.
- move=>_; case: eqP; case: eqP.
  - by move=><- E; rewrite E eq_refl in Hab.
  - by move=>/[swap]<-; rewrite eq_sym eq_refl !muln0.
  - by move=><-; rewrite eq_sym eq_refl=>/eqP/negbTE->; rewrite !muln0.
  move/eqP/negbTE; rewrite eq_sym=>->.
  by move/eqP/negbTE; rewrite eq_sym=>->.
case/and3P=>Hi Hcl Hcr; move: (IHr Hcr)=>{IHr}; move: (IHl Hcl)=>{IHl}.
move: (weight_swapLeaves wa wb Hcr Hab); move: (weight_swapLeaves wa wb Hcl Hab).
case: (not_intersects a Hi); case=>Hal Har;
case: (not_intersects b Hi); case=>Hbl Hbr.
- rewrite Hal (negbTE Har) Hbl (negbTE Hbr)
    (notin_alphabet_freq_0 Har)
    (notin_alphabet_freq_0 Hbr) /==>Wl -> Cl ->.
  by rewrite !addn0 !mulnDr !muln1 !addnA (ACl ((1*6*8)*3*(2*5*7)*4)%AC) /=
    Wl Cl !addnA (ACl (1*5*4*8*6*2*7*3)%AC).
- rewrite Hal (negbTE Har) (negbTE Hbl) Hbr
    (notin_alphabet_freq_0 Har)
    (notin_alphabet_freq_0 Hbl) /==>Wl Wr Cl Cr.
  by rewrite addn0 add0n !mulnDr !muln1 !addnA (ACl ((1*6)*(3*8)*(2*5)*(4*7))%AC) /=
    Wl Wr Cl Cr !addnA (ACl (1*5*3*7*8*4*6*2)%AC).
- rewrite Hal (negbTE Har) (negbTE Hbl) (negbTE Hbr)
    (notin_alphabet_freq_0 Har)
    (notin_alphabet_freq_0 Hbl) (notin_alphabet_freq_0 Hbr) /==>Wl -> Cl ->.
  by rewrite addn0 !mulnDr !muln1 !addnA (ACl ((1*6)*(2*5)*3*4)%AC) /=
    Wl Cl !addnA (ACl (1*3*5*6*4*2)%AC).
- rewrite (negbTE Hal) Har Hbl (negbTE Hbr)
    (notin_alphabet_freq_0 Hal)
    (notin_alphabet_freq_0 Hbr) /==>Wl Wr Cl Cr.
  by rewrite addn0 add0n !mulnDr !muln1 !addnA (ACl ((1*8)*(3*6)*(2*7)*(4*5))%AC) /=
    Wl Wr Cl Cr !addnA (ACl (1*5*3*7*6*2*8*4)%AC).
- rewrite (negbTE Hal) Har (negbTE Hbl) Hbr
    (notin_alphabet_freq_0 Hal)
    (notin_alphabet_freq_0 Hbl) /==>-> Wr -> Cr.
  by rewrite !add0n !mulnDr !muln1 !addnA (ACl (1*2*(3*6*8)*(4*5*7))%AC) /=
    Wr Cr !addnA (ACl (1*2*3*6*7*4*8*5)%AC).
- rewrite (negbTE Hal) Har (negbTE Hbl) (negbTE Hbr)
    (notin_alphabet_freq_0 Hal)
    (notin_alphabet_freq_0 Hbl) (notin_alphabet_freq_0 Hbr) /==>-> Wr -> Cr.
  by rewrite add0n !mulnDr !muln1 !addnA (ACl (1*2*(3*6)*(4*5))%AC) /=
    Wr Cr !addnA (ACl (1*2*3*5*6*4)%AC).
- rewrite (negbTE Hal) (negbTE Har) Hbl (negbTE Hbr)
    (notin_alphabet_freq_0 Hal) (notin_alphabet_freq_0 Har)
    (notin_alphabet_freq_0 Hbr) /==>Wl -> Cl ->.
  by rewrite addn0 !mulnDr !muln1 !addnA (ACl ((1*6)*(2*5)*3*4)%AC) /=
    Wl Cl !addnA (ACl (1*3*5*6*4*2)%AC).
- rewrite (negbTE Hal) (negbTE Har) (negbTE Hbl) Hbr
    (notin_alphabet_freq_0 Hal) (notin_alphabet_freq_0 Har)
    (notin_alphabet_freq_0 Hbl) /==>-> Wr -> Cr.
  by rewrite add0n !mulnDr !muln1 !addnA (ACl (1*2*(3*6)*(4*5))%AC) /=
    Wr Cr !addnA (ACl (1*2*3*5*6*4)%AC).
by rewrite (negbTE Hal) (negbTE Har) (negbTE Hbl) (negbTE Hbr)
    (notin_alphabet_freq_0 Hal) (notin_alphabet_freq_0 Har)
    (notin_alphabet_freq_0 Hbl) (notin_alphabet_freq_0 Hbr) /==>->->->->.
Qed.

Lemma sibling_swapLeaves_sibling t wa a ws b :
  consistent t -> sibling t b != b -> a != b ->
  sibling (swapLeaves t wa a ws (sibling t b)) a = b.
Proof.
elim: t=>/=[w c|w l IHl r IHr].
- by move=>_; simp sibling; rewrite eq_refl.
case: (posnP (height l))=>El; case: (posnP (height r))=>Er.
- case/eqP/heightE: El=>[wl][xl]->; case/eqP/heightE: Er=>[wr][xr]-> /=.
  simp sibling; rewrite /alpha_intersects /= orbF andbT =>/negbTE Hrl; case: ifP=>[/eqP->|Hbxl].
  - move=>_; rewrite eq_sym=>/negbTE Haxl.
    rewrite Haxl eq_sym Hrl eq_refl; case: ifP; simp sibling.
    - by rewrite eq_sym=>->; rewrite eq_sym Haxl.
    by move=>_; rewrite eq_sym Haxl eq_refl.
  case: ifP; last by rewrite eq_refl.
  move/eqP=>-> _; rewrite eq_sym=>/negbTE Haxr; rewrite eq_refl Hrl Haxr.
  case: ifP; simp sibling; first by rewrite eq_sym=>->.
  by rewrite eq_refl.
- rewrite height_gt0_sibling; last by rewrite Er orbT.
  case/eqP/heightE: El=>[wl][xl]->/=; rewrite /alpha_intersects /= inE; simp sibling.
  case/andP=>Hxlr Hcr; case: ifP; first by rewrite eq_refl.
  move=>Hbxl Hsrb Hab.
  have Hsab : sibling r b \in alphabet r by apply: sibling_ne_in_alphabet.
  have Hxsb : sibling r b != xl.
  - by rewrite alphabet_enum in Hsab; move/hasPn: Hxlr=>/(_ _ Hsab).
  rewrite height_gt0_sibling; last by rewrite height_swapLeaves Er orbT.
  case/boolP: (xl==a)=>/=.
  - rewrite inE; move/eqP=>{1}<-; rewrite eq_sym (negbTE Hxsb).
    by apply: IHr.
  move=>Haxl; rewrite eq_sym (negbTE Hxsb) /= inE eq_sym (negbTE Haxl).
  by apply: IHr.
- rewrite height_gt0_sibling; last by rewrite El.
  case/eqP/heightE: Er=>[wr][xr]->/=; rewrite /alpha_intersects /= orbF andbT; simp sibling.
  case/andP=>Hlxr Hcl; case: ifP; last by rewrite eq_refl.
  move=>Hbal Hslb Hab.
  have Hsab : sibling l b \in alphabet l by apply: sibling_ne_in_alphabet.
  rewrite height_gt0_sibling; last by rewrite height_swapLeaves El.
  rewrite alphabet_swapLeaves Hsab; case/boolP: (a \in alphabet l)=>/=.
  - by move=>->; apply: IHl.
  by move=>_; rewrite !inE eq_refl /=; apply: IHl.
case/and3P=>Hi Hcl Hcr.
rewrite height_gt0_sibling; last by rewrite El.
case/boolP: (b \in alphabet l)=>Hbal Hsb Hab.
- have Hsab : sibling l b \in alphabet l by apply: sibling_ne_in_alphabet.
  rewrite height_gt0_sibling; last by rewrite height_swapLeaves El.
  rewrite alphabet_swapLeaves Hsab; case/boolP: (a \in alphabet l)=>/=.
  - by move=>->; apply: IHl.
  by move=>_; rewrite !inE eq_refl /=; apply: IHl.
rewrite height_gt0_sibling; last by rewrite height_swapLeaves El.
have Hsab : sibling r b \in alphabet r by apply: sibling_ne_in_alphabet.
move: Hi; rewrite intersectsC=>/alpha_not/(_ _ Hsab)=>Hsab'.
rewrite alphabet_swapLeaves (negbTE Hsab'); case/boolP: (a \in alphabet l)=>/=.
- move=>Hal; rewrite !inE eq_refl /= orbF; case: eqP=>[E|_]; last by apply IHr.
  by rewrite -E Hal in Hsab'.
by rewrite inE=>/negbTE->; apply: IHr.
Qed.

Definition swapSyms (t : tree A) (a b : A) : tree A :=
  swapLeaves t (freq t a) a (freq t b) b.

Corollary swapSyms_id t a :
  consistent t -> swapSyms t a a = t.
Proof. by move=>H; apply: swapLeaves_id. Qed.

Lemma alphabet_swapSyms t a b :
  a \in alphabet t -> b \in alphabet t -> alphabet (swapSyms t a b) =i alphabet t.
Proof.
move=>Ha Hb; rewrite /swapSyms=>x.
by rewrite alphabet_swapLeaves Ha Hb.
Qed.

Lemma consistent_swapSyms t a b :
  consistent t -> consistent (swapSyms t a b).
Proof. by exact: consistent_swapLeaves. Qed.

Lemma depth_swapSyms t c a b :
  consistent t -> c != a -> c != b ->
  depth (swapSyms t a b) c = depth t c.
Proof. by exact: depth_swapLeaves. Qed.

Lemma freq_swapSyms t a b :
  consistent t -> a \in alphabet t -> b \in alphabet t ->
  freq (swapSyms t a b) =1 freq t.
Proof.
move=>Hc Ha Hb; case/boolP: (a == b)=>[/eqP->|Hab] c.
- by rewrite swapSyms_id.
rewrite /swapSyms freq_swapLeaves // Ha Hb.
by case: eqP=>[->|_] //; case: eqP=>[->|_].
Qed.

Lemma cost_swapSyms t a b :
  consistent t -> a \in alphabet t -> b \in alphabet t ->
  cost (swapSyms t a b) + freq t a * depth t a + freq t b * depth t b =
                 cost t + freq t a * depth t b + freq t b * depth t a.
Proof.
case/boolP: (a == b).
- by move/eqP=>->Hc Hb _; rewrite swapSyms_id.
move=>Hab Hc Hat Hbt; rewrite /swapSyms.
by move: (cost_swapLeaves (freq t a) (freq t b) Hab Hc); rewrite Hat Hbt.
Qed.

(* 13.1 *)
Lemma cost_swapSyms_le t a b:
  consistent t -> a \in alphabet t -> b \in alphabet t ->
  freq t a <= freq t b -> depth t a <= depth t b ->
  cost (swapSyms t a b) <= cost t.
Proof.
move=>Ht Ha Hb.
set i := freq t a; set m := depth t a.
set j := freq t b; set n := depth t b.
move=>Hf Hd.
set aabb := i * m + j * n.
set abba := i * n + j * m.
have H1: abba <= aabb.
- rewrite /abba /aabb.
  have : i * m + i * (n - m) + j * m <= i * m + j * m + j * (n - m).
  - by rewrite -!addnA leq_add2l addnC leq_add2l leq_mul2r Hf orbT.
  rewrite !mulnBr addnBCA //; last by rewrite leq_mul2l Hd orbT.
  rewrite subnn addn0 -addnA addnBCA //; last by rewrite leq_mul2l Hd orbT.
  by rewrite subnn addn0.
have H2: cost (swapSyms t a b) + aabb = cost t + abba.
- by rewrite /aabb /abba /i /m /j /n !addnA; apply: cost_swapSyms.
rewrite -(leq_add2r aabb); apply: leq_trans; first by rewrite H2; apply: leqnn.
by rewrite leq_add2l.
Qed.

Corollary sibling_swapSyms_sibling t a b :
  consistent t -> sibling t b != b -> a != b ->
  sibling (swapSyms t a (sibling t b)) a = b.
Proof. by exact: sibling_swapLeaves_sibling. Qed.

Lemma sibling_swapSyms_other_sibling t a b:
  consistent t -> sibling t b != a -> sibling t b != b -> a != b ->
  sibling (swapSyms t a b) (sibling t b) = a.
Proof.
move=>H Ha Hb Hab.
apply: sibling_reciprocal; first by apply: consistent_swapSyms.
rewrite -{1}(sibling_sibling_id (t:=t) b) // sibling_swapSyms_sibling // eq_sym //.
by rewrite sibling_sibling_id.
Qed.

Definition swapFourSyms (t : tree A) (a b c d : A) : tree A :=
  if a == d then swapSyms t b c
    else if b == c then swapSyms t a d
      else swapSyms (swapSyms t a c) b d.

Lemma alphabet_swapFourSyms t a b c d :
  a \in alphabet t -> b \in alphabet t -> c \in alphabet t -> d \in alphabet t ->
  alphabet (swapFourSyms t a b c d) =i alphabet t.
Proof.
move=>Ha Hb Hc Hd; rewrite /swapFourSyms.
case: ifP=>_; first by apply: alphabet_swapSyms.
by case: ifP=>_ z; rewrite !alphabet_swapSyms.
Qed.

Lemma consistent_swapFourSyms t a b c d :
  consistent t -> consistent (swapFourSyms t a b c d).
Proof.
move=>H; rewrite /swapFourSyms.
case: ifP=>_; first by apply: consistent_swapSyms.
by case: ifP=>_; rewrite !consistent_swapSyms.
Qed.

Lemma freq_swapFourSyms t a b c d :
  consistent t ->
  a \in alphabet t -> b \in alphabet t -> c \in alphabet t -> d \in alphabet t ->
  freq (swapFourSyms t a b c d) =1 freq t.
Proof.
move=>H Ha Hb Hc Hd; rewrite /swapFourSyms.
case: ifP=>_; first by apply: freq_swapSyms.
case: ifP=>_; first by apply: freq_swapSyms.
move=>z; rewrite !freq_swapSyms ?alphabet_swapSyms //.
by apply: consistent_swapSyms.
Qed.

Lemma sibling_swapFourSyms t a b c :
  consistent t ->
  a != b -> sibling t c != c ->
  sibling (swapFourSyms t a b c (sibling t c)) a = b.
Proof.
move=>H Hab Hs; case/boolP: ((a != sibling t c) && (b != c)).
- set d := sibling t c in Hs *.
  case/andP=>Had Hbc.
  set s := swapFourSyms t a b c d.
  have Hcs : consistent s by apply: consistent_swapFourSyms.
  apply: sibling_reciprocal=>//.
  have Ed : d = sibling (swapSyms t a c) a.
  - symmetry; rewrite /d -{1}(sibling_sibling_id (t:=t) c) //.
    apply: sibling_swapSyms_sibling=>//.
    by rewrite eq_sym sibling_sibling_id.
  rewrite /s /swapFourSyms (negbTE Had) (negbTE Hbc).
  case/boolP: (a == c)=>[/eqP->|Hac].
  - by rewrite swapSyms_id //; apply: sibling_swapSyms_sibling.
  have {2}<-: sibling (swapSyms t a c) d = a.
  - rewrite /d; apply: sibling_swapSyms_other_sibling=>//.
    by rewrite eq_sym.
  rewrite Ed sibling_sibling_id; last by apply: consistent_swapSyms.
  apply: sibling_swapSyms_sibling.
  - by apply: consistent_swapSyms.
  - by rewrite -Ed eq_sym.
  by rewrite eq_sym.
rewrite /swapFourSyms negb_and.
case/boolP: (a == sibling t c); case/boolP: (b == c)=>//=.
- by move/eqP=>->/eqP Has _; rewrite swapSyms_id // Has sibling_sibling_id.
- move=>Hbc /eqP Has _; rewrite Has; apply: sibling_swapSyms_other_sibling=>//.
  by rewrite -Has.
by move/eqP=>Hbc _ _; rewrite Hbc in Hab *; apply: sibling_swapSyms_sibling.
Qed.

(* merging *)

Equations? mergeSibling (t : tree A) (a : A) : tree A by wf (height t) lt :=
mergeSibling (Leaf wb b) a => Leaf wb b;
mergeSibling (Node w (Leaf wb b) (Leaf wc c)) a =>
  if (a == b) || (a == c)
    then Leaf (wb + wc) a
    else Node w (Leaf wb b) (Leaf wc c);
mergeSibling (Node w l r) a =>
  Node w (mergeSibling l a) (mergeSibling r a).
Proof.
all: apply: ssrnat.ltP.
- by rewrite addn1.
- by rewrite ltn_add2r max0n addn1.
- by rewrite ltn_add2r leq_max addn1 ltnS leqnn.
by rewrite addn1 ltnS leq_max leqnn orbT.
Qed.

Lemma notin_alphabet_mergeSibling_id a t :
  a \notin alphabet t -> mergeSibling t a = t.
Proof.
funelim (mergeSibling t a)=>//; simp mergeSibling=>/=; rewrite !inE.
- by move/negbTE=>->.
- rewrite !negb_or; case/and3P=>Has Hal Har.
  by rewrite H0 //= !inE negb_or Hal Har.
rewrite !negb_or -andbA; case/and3P=>Hap Haq Har.
rewrite H /=; first by rewrite H0.
by rewrite !inE negb_or Hap Haq.
Qed.

Lemma height_gt0_mergeSibling w p q a :
  (0 < height p) || (0 < height q) ->
  mergeSibling (Node w p q) a =
    Node w (mergeSibling p a) (mergeSibling q a).
Proof. by case: q=>[wq q|wq ql qr]; case: p=>[wp p|wp pl pr]; simp mergeSibling. Qed.

Lemma alphabet_mergeSibling t a :
  consistent t -> a \in alphabet t ->
  alphabet (mergeSibling t a) =i [predU1 a & [predD1 (alphabet t) & (sibling t a)]].
Proof.
move=>H; apply: (sibling_consistent_ind (P:=fun t a => a \in alphabet t -> alphabet (mergeSibling t a) =i [predU1 a & [predD1 (alphabet t) & (sibling t a)]])) =>{a}//=.
- move=>w b a; rewrite inE=>/eqP->; simp sibling mergeSibling=>/= z.
  by rewrite !inE; case: eqP.
- move=>w wb b wc c a Hbc; rewrite !inE.
  simp sibling mergeSibling; case/orP=>/eqP->; rewrite eq_refl ?orbT /= => z; rewrite !inE.
  - by case: eqP=>//= _; rewrite andNb.
  by case: eqP=>//= _; rewrite orbF (eq_sym c b) (negbTE Hbc) andNb.
- move=>w l r a _ _ _ Hh Hal _ Har Hsar IH _.
  rewrite height_gt0_mergeSibling //= height_gt0_sibling // Hal
    (notin_alphabet_mergeSibling_id Har) => z.
  by rewrite !inE IH // !inE; case: eqP=>//= _; case: eqP=>//= ->; apply/negbTE.
- move=>w l r a _ _ _ Hh Hal Hsal Har _ IH _.
  rewrite height_gt0_mergeSibling //= height_gt0_sibling // (negbTE Hal)
    (notin_alphabet_mergeSibling_id Hal) => z.
  rewrite !inE IH // !inE; case: eqP=>/= _; first by rewrite orbT.
  by case: eqP=>//=->; rewrite orbF; apply/negbTE.
by move=>w l r a _ _ _ _ Hal Har; rewrite !inE (negbTE Hal) (negbTE Har).
Qed.

Lemma consistent_mergeSibling t a :
  consistent t -> consistent (mergeSibling t a).
Proof.
move=>H; apply: (sibling_consistent_ind (P:=fun t a => consistent (mergeSibling t a))) =>{a}//=.
- move=>w wb b wc c a Hbc; simp mergeSibling; case: ifP=>//= _.
  by rewrite andbT /alpha_intersects /= orbF eq_sym.
- move=>w l r a Hcl Hcr Hi Hh Hal _ Har _ IH.
  rewrite height_gt0_mergeSibling //= (notin_alphabet_mergeSibling_id Har) IH Hcr /= andbT.
  apply/alpha_not=>z; rewrite alphabet_mergeSibling // !inE.
  case: eqP=>[->|_] //=; case/andP=>_.
  by move/alpha_not: Hi; apply.
- move=>w l r a Hcl Hcr Hi Hh Hal _ Har _ IH.
  rewrite height_gt0_mergeSibling //= (notin_alphabet_mergeSibling_id Hal) IH Hcl /= andbT.
  rewrite intersectsC; apply/alpha_not=>z; rewrite alphabet_mergeSibling // !inE.
  case: eqP=>[->|_] //=; case/andP=>_.
  by move: Hi; rewrite intersectsC =>/alpha_not; apply.
move=>w l r a Hcl Hcr Hi Hh Hal Har.
by rewrite height_gt0_mergeSibling //=
  (notin_alphabet_mergeSibling_id Hal) (notin_alphabet_mergeSibling_id Har) Hi Hcl Hcr.
Qed.

Lemma freq_mergeSibling t a z :
  consistent t -> a \in alphabet t -> sibling t a != a ->
  freq (mergeSibling t a) z =
    if z == a then freq t a + freq t (sibling t a)
      else if z == sibling t a
             then 0
             else freq t z.
Proof.
move=>H; apply: (sibling_consistent_ind (P:=fun t a => a \in alphabet t -> sibling t a != a -> freq (mergeSibling t a) z = if z == a then freq t a + freq t (sibling t a) else if z == sibling t a then 0 else freq t z)) =>{a}//=.
- by move=>w b a _; simp sibling; rewrite eq_refl.
- move=>w wb b wc c a Hbc; rewrite !inE.
  simp sibling mergeSibling; case/orP=>/eqP->; rewrite eq_refl /=.
  - move=>_; rewrite (negbTE Hbc) eq_refl (eq_sym c b) (negbTE Hbc) addn0 add0n.
    by case: eqP=>// _; case: eqP.
  rewrite (eq_sym c b) !(negbTE Hbc) /= eq_refl add0n addn0 => _.
  case: eqP; first by rewrite addnC.
  by case: eqP.
- move=>w l r a _ _ _ Hh Hal _ Har Hsar IH _.
  rewrite height_gt0_mergeSibling //= height_gt0_sibling // Hal
    (notin_alphabet_mergeSibling_id Har)
    (notin_alphabet_freq_0 Har) (notin_alphabet_freq_0 Hsar) !addn0 => Hsl.
  rewrite IH //; case: eqP=>[->|_].
  - by rewrite (notin_alphabet_freq_0 Har) addn0.
  by case: eqP=>//->; rewrite (notin_alphabet_freq_0 Hsar).
- move=>w l r a _ _ _ Hh Hal Hsal Har _ IH _.
  rewrite height_gt0_mergeSibling //= height_gt0_sibling // (negbTE Hal)
    (notin_alphabet_mergeSibling_id Hal)
    (notin_alphabet_freq_0 Hal) (notin_alphabet_freq_0 Hsal) !add0n => Hsr.
  rewrite IH //; case: eqP=>[->|_].
  - by rewrite (notin_alphabet_freq_0 Hal) add0n.
  by case: eqP=>//->; rewrite (notin_alphabet_freq_0 Hsal).
by move=>w l r a _ _ _ _ Hal Har; rewrite !inE (negbTE Hal) (negbTE Har).
Qed.

Lemma weight_mergeSibling t a :
  weight (mergeSibling t a) = weight t.
Proof.
funelim (mergeSibling t a)=>//; simp mergeSibling=>/=.
- by case: ifP.
- by rewrite H0.
by rewrite H0 H.
Qed.

(* 13.2 *)
Lemma cost_mergeSibling t a :
  consistent t -> sibling t a != a ->
  cost (mergeSibling t a) + freq t a + freq t (sibling t a) = cost t.
Proof.
move=>H; apply: (sibling_consistent_ind (P:=fun t a => sibling t a != a -> cost (mergeSibling t a) + freq t a + freq t (sibling t a) = cost t)) =>{a}//=.
- by move=>w b a; simp sibling; rewrite eq_refl.
- move=>w wb b wc c a Hbc; simp sibling mergeSibling=>/=; case: ifP=>/=.
  - by move/eqP=>-> Hcb; rewrite eq_sym (negbTE Hcb) eq_refl !addn0 !add0n.
  move/negbT=>Hab; case: ifP=>/=; last by rewrite eq_refl.
  by move/eqP=>->_; rewrite eq_refl (negbTE Hbc) !addn0 !add0n addnC.
- move=>w l r a _ _ _ Hh Hal _ Har Hslar IHl.
  rewrite height_gt0_sibling // height_gt0_mergeSibling //= Hal
    (notin_alphabet_mergeSibling_id Har) weight_mergeSibling
    (notin_alphabet_freq_0 Har) (notin_alphabet_freq_0 Hslar) !addn0
    (ACl (1*(2*5*6)*3*4)%AC) /=.
  by move/IHl=>->.
- move=>w l r a _ _ _ Hh Hal Hslal Har _ IHr.
  rewrite height_gt0_sibling // height_gt0_mergeSibling //= (negbTE Hal)
    (notin_alphabet_mergeSibling_id Hal) weight_mergeSibling
    (notin_alphabet_freq_0 Hal) (notin_alphabet_freq_0 Hslal) !add0n
    (ACl (1*2*3*(4*5*6))%AC) /=.
  by move/IHr=>->.
move=>w l r a _ _ _ Hh Hal Har Hn.
rewrite notin_alphabet_sibling_id /=; last by rewrite !inE negb_or Hal Har.
rewrite notin_alphabet_mergeSibling_id /=; last by rewrite !inE negb_or Hal Har.
by rewrite !notin_alphabet_freq_0 // !addn0.
Qed.

(* splitting *)

Fixpoint splitLeaf (t : tree A) (wa : nat) (a : A) (wb : nat) (b : A) : tree A :=
  match t with
  | Leaf wc c =>
      if c == a then Node wc (Leaf wa a) (Leaf wb b)
                else Leaf wc c
  | Node w l r =>
      Node w (splitLeaf l wa a wb b) (splitLeaf r wa a wb b)
  end.

Fixpoint splitLeafF (ts : forest A) (wa : nat) (a : A) (wb : nat) (b : A) : forest A :=
  if ts is t::s
    then splitLeaf t wa a wb b :: splitLeafF s wa a wb b
    else [::].

Lemma notin_alphabet_splitLeaf_id t a wa b wb :
  a \notin alphabet t -> splitLeaf t wa a wb b = t.
Proof.
elim: t=>/=[w c|w l IHl r IHr]; rewrite !inE.
- by rewrite eq_sym=>/negbTE->.
by rewrite negb_or; case/andP=>/IHl->/IHr->.
Qed.

Lemma notin_alphabet_splitLeafF_id ts wa a wb b :
  a \notin alphabetF ts -> splitLeafF ts wa a wb b = ts.
Proof.
elim: ts=>//=q s IH; rewrite !inE negb_or; case/andP=>Hq Hs.
by rewrite notin_alphabet_splitLeaf_id // IH.
Qed.

Lemma cachedWeight_splitLeaf (t : tree A) wa a wb b :
  cachedWeight (splitLeaf t wa a wb b) = cachedWeight t.
Proof. by case: t=>//=n c; case: ifP. Qed.

Lemma alphabet_splitLeaf t wa a wb b :
  alphabet (splitLeaf t wa a wb b) =i
    if a \in alphabet t then [predU1 b & (alphabet t)] else SimplPred (alphabet t).
Proof.
elim: t=>/= [w c|_ l IHl r IHr] z; rewrite !inE.
- case: ifP; last by rewrite eq_sym=>->/=.
  by move/eqP=>->; rewrite eq_refl !inE orbC.
rewrite {}IHl {}IHr.
case/boolP: (a \in alphabet l)=>Hl; case/boolP: (a \in alphabet r)=>Hr //=;
rewrite !inE; case: eqP=>[->|_] //=.
by rewrite orbT.
Qed.

Lemma consistent_splitLeaf t wa a wb b :
  consistent t -> b \notin alphabet t ->
  consistent (splitLeaf t wa a wb b).
Proof.
elim: t=>/=[w c|_ l IHl r IHr].
- move=>_; rewrite inE=>Hbc; case: ifP=>//=.
  by move/eqP=><-; rewrite andbT /alpha_intersects /= orbF.
case/and3P=>Hi Hcl Hcr; rewrite !inE negb_or; case/andP=>Hbl Hbr.
rewrite IHl // IHr //= andbT.
apply/alpha_not=>z; rewrite !alphabet_splitLeaf.
case: (not_intersects a Hi); case.
- move=>->/negbTE->; rewrite !inE; case: eqP=>[->|_] /=.
  - by move=>_; move: Hbr; rewrite -topredE /=.
  by move/alpha_not: Hi; apply.
- move=>/negbTE->->; rewrite !inE; case: eqP=>[->|_] /=.
  - by move: Hbl; rewrite -topredE /==>/[swap]->.
  by move/alpha_not: Hi; apply.
move=>/negbTE->/negbTE->; rewrite !inE.
by move/alpha_not: Hi; apply.
Qed.

Lemma freq_splitLeaf t wa a wb b z :
  consistent t -> b \notin alphabet t ->
  freq (splitLeaf t wa a wb b) z =
    if a \in alphabet t then
      if z == a then wa else if z == b then wb else freq t z
    else freq t z.
Proof.
move=>H; apply: (consistent_ind (P:=fun t a => b \notin alphabet t -> freq (splitLeaf t wa a wb b) z = if a \in alphabet t then if z == a then wa else if z == b then wb else freq t z else freq t z))=>//={a}.
- move=>w c a; rewrite !inE=>Hbc; case: ifP=>Hca /=.
  - rewrite (eqP Hca) in Hbc *; rewrite eq_refl; case: ifP; last by rewrite add0n.
    by move: Hbc=>/[swap]/eqP->; rewrite eq_sym=>/negbTE->; rewrite addn0.
  by rewrite (eq_sym a c) Hca.
- move=>_ l r a _ _ _ Hal Har IHl IHr; rewrite !inE negb_or; case/andP=>Hbl Hbr.
  rewrite IHl // IHr // Hal (negbTE Har) /=; case: ifP.
  - by move/eqP=>->; rewrite (notin_alphabet_freq_0 Har) addn0.
  move=>_; case: ifP=>// /eqP->.
  by rewrite (notin_alphabet_freq_0 Hbr) addn0.
- move=>_ l r a _ _ _ Hal Har IHl IHr; rewrite !inE negb_or; case/andP=>Hbl Hbr.
  rewrite IHl // IHr // (negbTE Hal) Har /=; case: ifP.
  - by move/eqP=>->; rewrite (notin_alphabet_freq_0 Hal) add0n.
  move=>_; case: ifP=>// /eqP->.
  by rewrite (notin_alphabet_freq_0 Hbl) add0n.
move=>_ l r a _ _ _ Hal Har IHl IHr; rewrite !inE negb_or; case/andP=>Hbl Hbr.
by rewrite IHl // IHr // (negbTE Hal) (negbTE Har).
Qed.

Lemma weight_splitLeaf t a wa b wb :
  consistent t -> a \in alphabet t -> freq t a = wa + wb ->
  weight (splitLeaf t wa a wb b) = weight t.
Proof.
move=>H; apply: (consistent_ind (P:=fun t a => a \in alphabet t -> freq t a = wa + wb -> weight (splitLeaf t wa a wb b) = weight t))=>//={a}.
- by move=>w c a; rewrite inE=>/eqP->; rewrite eq_refl /= =>->.
- move=>_ l r a _ _ _ Hal Har IHl _ _.
  rewrite (notin_alphabet_freq_0 Har) addn0=>Hf.
  by rewrite (notin_alphabet_splitLeaf_id _ _ _ Har) IHl.
- move=>_ l r a _ _ _ Hal Har _ IHr _.
  rewrite (notin_alphabet_freq_0 Hal) add0n=>Hf.
  by rewrite (notin_alphabet_splitLeaf_id _ _ _ Hal) IHr.
by move=>_ l r a _ _ _ /negbTE Hal /negbTE Har _ _; rewrite !inE Hal Har.
Qed.

(* 13.3 *)
Lemma cost_splitLeaf t a wa b wb :
  consistent t -> a \in alphabet t -> freq t a = wa + wb ->
  cost (splitLeaf t wa a wb b) = cost t + wa + wb.
Proof.
move=>H; apply: (consistent_ind (P:=fun t a => a \in alphabet t -> freq t a = wa + wb -> cost (splitLeaf t wa a wb b) = cost t + wa + wb))=>//={a}.
- by move=>w c a; rewrite inE=>/eqP->; rewrite eq_refl /= !addn0 add0n.
- move=>_ l r a Hcl _ _ Hal Har IHl _ _.
  rewrite (notin_alphabet_freq_0 Har) addn0=>Hf.
  by rewrite (notin_alphabet_splitLeaf_id _ _ _ Har) (weight_splitLeaf _ Hcl Hal Hf) IHl //
       !addnA (ACl (1*2*5*6*3*4)%AC).
- move=>_ l r a _ Hcr _ Hal Har _ IHr _.
  rewrite (notin_alphabet_freq_0 Hal) add0n=>Hf.
  by rewrite (notin_alphabet_splitLeaf_id _ _ _ Hal) (weight_splitLeaf _ Hcr Har Hf) IHr //
       !addnA.
by move=>_ l r a _ _ _ /negbTE Hal /negbTE Har _ _; rewrite !inE Hal Har.
Qed.

Lemma splitLeafF_insortTree_in_alphabet (t : tree A) ts wa a wb b :
  a \in alphabet t -> consistent t -> a \notin alphabetF ts -> freq t a = wa + wb ->
  splitLeafF (insortTree t ts) wa a wb b = insortTree (splitLeaf t wa a wb b) ts.
Proof.
move=>Ha Hc + Hf; elim: ts=>//=q s IH; rewrite !inE negb_or; case/andP=>Hq Hs.
rewrite cachedWeight_splitLeaf; case: ifP=>/= _; rewrite (notin_alphabet_splitLeaf_id _ _ _ Hq).
- by rewrite (notin_alphabet_splitLeafF_id _ _ _ Hs).
by rewrite IH.
Qed.

Lemma splitLeafF_insortTree_in_alphabetF (t : tree A) ts wa a wb b :
  a \in alphabetF ts -> consistentF ts -> a \notin alphabet t -> freqF ts a = wa + wb ->
  splitLeafF (insortTree t ts) wa a wb b =
    insortTree t (splitLeafF ts wa a wb b).
Proof.
move=>+ + Ht; elim: ts=>//= u s IH; rewrite !inE=>Ha; case/and3P=>Hi Hu Hs Hf.
rewrite cachedWeight_splitLeaf; case: ifP=>/= _.
- by rewrite (notin_alphabet_splitLeaf_id _ _ _ Ht).
case/boolP: (a \in alphabet u) Ha=>Ha /=; last first.
- by move=>Has; rewrite IH //; rewrite notin_alphabet_freq_0 in Hf.
move/alpha_notF: Hi=>/(_ _ Ha) Has _.
by rewrite !notin_alphabet_splitLeafF_id // alphabetF_insortTree !inE negb_or Ht Has.
Qed.

(* sortedness *)

Equations sortedByWeight (ts : forest A) : bool :=
sortedByWeight [::] => true;
sortedByWeight (t1::ts) with ts := {
  | [::] => true;
  | t2 :: _ =>
    (weight t1 <= weight t2) && (sortedByWeight ts)
}.

Lemma sortedByWeight_cons2 t1 t2 ts :
  sortedByWeight (t1::t2::ts) = (weight t1 <= weight t2) && (sortedByWeight (t2::ts)).
Proof. by simp sortedByWeight. Qed.

Lemma sortedByWeight_cons t ts :
  sortedByWeight (t::ts) -> sortedByWeight ts.
Proof. by case: ts=>//=t2 s; rewrite sortedByWeight_cons2; case/andP. Qed.

Lemma sortedByWeight_cons_weight t ts :
  sortedByWeight (t::ts) -> all (fun u => weight t <= weight u) ts.
Proof.
elim: ts t=>//=t2 ts IH t1; rewrite sortedByWeight_cons2.
case/andP=>H12; rewrite H12 /= => /IH /sub_all; apply=>z Hz.
by apply/leq_trans/Hz.
Qed.

Lemma sortedByWeight_insortTree t ts :
  height t = 0 -> sortedByWeight ts -> heightF ts = 0 ->
  sortedByWeight (insortTree t ts).
Proof.
move=>Ht; funelim (sortedByWeight ts)=>//=.
- move=>_; rewrite maxn0=>/eqP/heightE [w2][x2]->/=.
  case: leqP; simp sortedByWeight=>/=; rewrite andbT height_0_cachedWeight //.
  by move/ltnW.
case/andP=>Hw Hs /eqP; rewrite !maxn_eq0 .
case/and3P=>/eqP H1 /eqP H2 Hl; rewrite !height_0_cachedWeight //.
case: leqP.
- by rewrite !sortedByWeight_cons2 Hs Hw =>->.
move=>H10; case: leqP; rewrite !sortedByWeight_cons2.
- by move/ltnW: H10; rewrite Hs =>->->.
move=>H20; rewrite Hw /=.
have Hm: maxn (height t2) (heightF l) = 0.
- by apply/eqP; rewrite maxn_eq0 Hl andbT; apply/eqP.
(move: (H _ _ Ht erefl Hs Hm)=>/=) || (move: (H t (t2 :: l) Ht erefl erefl Hs Hm)=>/=).
by rewrite !height_0_cachedWeight // leqNgt H20 /=.
Qed.


(* minima *)

Definition minima (t : tree A) (a b : A) : bool :=
  [&& a \in alphabet t,
      b \in alphabet t,
      a != b &
      all (fun c => (c != a) && (c != b) ==>
                    (freq t a <= freq t c) && (freq t b <= freq t c))
          (enum t)].

End OtherFunctions.

Section KeyLemmasAndTheorems.
Context {A : eqType}.

Theorem alphabet_huffman (t0 : tree A) ts :
  ~~ nilp ts -> alphabet (huffman t0 ts) =i alphabetF ts.
Proof.
funelim (huffman t0 ts)=>//; simp huffman=>/= _.
- by move=>x; rewrite !inE orbF.
move=>x; rewrite !inE H; last by apply: insortTree_notnil.
by rewrite alphabetF_insortTree inE /= !inE -orbA.
Qed.

Theorem consistent_huffman (t0 : tree A) ts :
  ~~ nilp ts -> consistentF ts -> consistent (huffman t0 ts).
Proof.
funelim (huffman t0 ts)=>//; simp huffman=>/= _.
- by rewrite andbT.
case/and5P=>Hif H1 Hi2 H2 Hs; apply: H; first by apply: insortTree_notnil.
rewrite consistentF_insortTree /= -!andbA H1 H2 Hs /= andbT.
move: Hif; rewrite alpha_intersectsF_cons negb_or; case/andP=>-> Hi1; rewrite andbT.
by rewrite alpha_intersectsF_uniteTrees negb_or Hi1 Hi2.
Qed.

Theorem freq_huffman (t0 : tree A) ts a :
  ~~ nilp ts -> freq (huffman t0 ts) a = freqF ts a.
Proof.
funelim (huffman t0 ts)=>//; simp huffman=>/= _.
- by rewrite addn0.
rewrite H; last by apply: insortTree_notnil.
by rewrite freqF_insortTree /= addnA.
Qed.

(* 13.4 *)
Lemma cost_swapFourSyms_le (t : tree A) a b c d :
  consistent t -> minima t a b -> c \in alphabet t -> d \in alphabet t ->
  depth t c = height t -> depth t d = height t -> c != d ->
  cost (swapFourSyms t a b c d) <= cost t.
Proof.
rewrite /minima=>Hct /and4P [Hat Hbt Hab Hf] Htc Htd Ec Ed Hcd.
case/boolP: ((a != d) && (b != c)).
- case/andP=>Had Hbc; rewrite /swapFourSyms (negbTE Had) (negbTE Hbc).
  case/boolP: (a == c)=>Hac; case/boolP: (b == d)=>Hbd.
  - rewrite (eqP Hac) (eqP Hbd).
    have Hd': d \in alphabet (swapSyms t c c) by rewrite alphabet_swapSyms.
    apply: (leq_trans (n:=cost (swapSyms t c c))); apply: cost_swapSyms_le=>//.
    by apply: consistent_swapSyms.
  - rewrite (eqP Hac).
    apply: (leq_trans (n:=cost (swapSyms t c c))); apply: cost_swapSyms_le=>//.
    - by apply: consistent_swapSyms.
    - by rewrite alphabet_swapSyms.
    - by rewrite alphabet_swapSyms.
    - rewrite !freq_swapSyms //.
      move/allP: Hf=>/(_ d); rewrite -alphabet_enum Htd => /(_ erefl).
      by rewrite eq_sym Had eq_sym Hbd /=; case/andP.
    rewrite !depth_swapSyms //; try by rewrite eq_sym.
    by rewrite Ed; apply: depth_le_height.
  - rewrite (eqP Hbd).
    apply: (leq_trans (n:=cost (swapSyms t a c))); apply: cost_swapSyms_le=>//.
    - by apply: consistent_swapSyms.
    - by rewrite alphabet_swapSyms.
    - by rewrite alphabet_swapSyms.
    - move/allP: Hf=>/(_ c); rewrite -alphabet_enum Htc => /(_ erefl).
      by rewrite eq_sym Hac eq_sym Hbc /=; case/andP.
    by rewrite Ec; apply: depth_le_height.
  apply: (leq_trans (n:=cost (swapSyms t a c))); apply: cost_swapSyms_le=>//.
  - by apply: consistent_swapSyms.
  - by rewrite alphabet_swapSyms.
  - by rewrite alphabet_swapSyms.
  - rewrite !freq_swapSyms //.
    move/allP: Hf=>/(_ d); rewrite -alphabet_enum Htd => /(_ erefl).
    by rewrite eq_sym Had eq_sym Hbd /=; case/andP.
  - rewrite !depth_swapSyms //; try by rewrite eq_sym.
    by rewrite Ed; apply: depth_le_height.
  - move/allP: Hf=>/(_ c); rewrite -alphabet_enum Htc => /(_ erefl).
    by rewrite eq_sym Hac eq_sym Hbc /=; case/andP.
  by rewrite Ec; apply: depth_le_height.
rewrite /swapFourSyms negb_and; case/orP=>/negbNE/eqP H.
- rewrite H in Hab Hf *; rewrite eq_refl.
  case/boolP: (c == b)=>[/eqP->|Hcb]; first by rewrite swapSyms_id.
  apply: cost_swapSyms_le=>//.
  - move/allP: Hf=>/(_ c); rewrite -alphabet_enum Htc => /(_ erefl).
    by rewrite Hcd Hcb /=; case/andP.
  by rewrite Ec; apply: depth_le_height.
rewrite H in Hf *; rewrite eq_refl.
case/boolP: (a == d)=>[_|Had]; first by rewrite swapSyms_id.
apply: cost_swapSyms_le=>//.
- move/allP: Hf=>/(_ d); rewrite -alphabet_enum Htd => /(_ erefl).
  by rewrite eq_sym Had eq_sym Hcd /=; case/andP.
by rewrite Ed; apply: depth_le_height.
Qed.

(* 13.5 *)
Lemma optimum_splitLeaf (t : tree A) a b wa wb :
  consistent t -> optimum t ->
  a \in alphabet t -> b \notin alphabet t ->
  freq t a = wa + wb ->
  all (fun c => (wa <= freq t c) && (wb <= freq t c)) (enum t) ->
  optimum (splitLeaf t wa a wb b).
Proof.
move=>Ht Ho Ha Hb Hf H u Hcu.
set s := splitLeaf t wa a wb b; move=>Hau Hfu.
case: (posnP (height s))=>[|Hs]; first by case/eqP/heightE=>w[x]->.
have Hhu : 0 < height u.
- by apply: (height_gt0_alphabet_eq Hs)=>//; rewrite /s; apply: consistent_splitLeaf.
have Haau: a \in alphabet u by rewrite -Hau /s alphabet_splitLeaf Ha !inE Ha orbT.
have Hbau: b \in alphabet u by rewrite -Hau /s alphabet_splitLeaf Ha !inE eq_refl.
have Hab: a != b by apply/eqP=>E; rewrite -E Ha in Hb.
case: (exists_at_height Hcu)=>c Hcau Hdc.
set d := sibling u c.
have Edc : d != c by rewrite /d; apply: depth_height_sibling_ne.
have Haad : d \in alphabet u by apply: sibling_ne_in_alphabet.
set w := swapFourSyms u a b c d.
have Hcw : consistent w by apply: consistent_swapFourSyms.
have Haw : alphabet w =i alphabet u by apply: alphabet_swapFourSyms.
have Hfw : freq w =1 freq u by apply: freq_swapFourSyms.
have Hsw : sibling w a = b by apply: sibling_swapFourSyms.
set v := mergeSibling w a.
have Hav : alphabet v =i alphabet t.
- move=>z; rewrite alphabet_mergeSibling //; last by rewrite Haw.
  rewrite !inE Haw Hsw; case: eqP=>[->|_] //=.
  case: eqP=>[->|/eqP Hzb] /=; first by rewrite (negbTE Hb).
  by rewrite -Hau alphabet_splitLeaf Ha !inE (negbTE Hzb).
have Hfv : freq v =1 freq t.
- move=>z; rewrite freq_mergeSibling //.
  - rewrite Hsw !Hfw -!Hfu !freq_splitLeaf // !eq_refl Ha (eq_sym b a) (negbTE Hab).
    case: eqP=>[->|Hza]; first by rewrite Hf.
    by case: eqP=>// ->; rewrite notin_alphabet_freq_0.
  - by rewrite Haw -Hau alphabet_splitLeaf Ha !inE Ha orbT.
  by rewrite Hsw eq_sym.
rewrite cost_splitLeaf //; apply: (leq_trans (n := cost w)).
- have <- : cost v + wa + wb = cost w.
  - have [->->]: wa = freq w a /\ wb = freq w b.
    - by rewrite !Hfw -!Hfu !freq_splitLeaf // Ha !eq_refl eq_sym (negbTE Hab).
    by rewrite -Hsw cost_mergeSibling // Hsw eq_sym.
  by rewrite -!addnA leq_add2r; apply: Ho=>//; apply: consistent_mergeSibling.
have Hm : minima u a b.
- rewrite /minima Haau Hbau Hab /=; apply/allP=>z.
  rewrite -alphabet_enum -Hau alphabet_splitLeaf Ha !inE.
  case/orP; first by move=>-> /=; rewrite andbF.
  rewrite alphabet_enum; move/allP: H=>/[apply]; case/andP=>Hwaz Hwbz.
  apply/implyP; case/andP=>Hza Hzb; rewrite -!Hfu !freq_splitLeaf // Ha.
  by rewrite !eq_refl (negbTE Hza) (negbTE Hzb) eq_sym (negbTE Hab) Hwaz Hwbz.
by apply: cost_swapFourSyms_le=>//; [rewrite depth_sibling | rewrite eq_sym].
Qed.

(* 13.6 *)
Lemma splitLeaf_huffman_commute (t0 : tree A) ts wa a wb b :
 consistentF ts -> ~~ nilp ts -> a \in alphabetF ts -> freqF ts a = wa + wb ->
 splitLeaf (huffman t0 ts) wa a wb b = huffman t0 (splitLeafF ts wa a wb b).
Proof.
funelim (huffman t0 ts); simp huffman=>//=; simp huffman.
rewrite alpha_intersectsF_cons negb_or -andbA; case/and6P=>Hi12 Hi1s Hc1 Hi2s Hc2 Hcs _.
rewrite !inE=>Ha Hf; rewrite H.
- rewrite /uniteTrees /= !cachedWeight_splitLeaf.
  case/or3P: Ha=>Ha.
  - move/alpha_notF: Hi1s=>/(_ _ Ha)=>Has.
    rewrite splitLeafF_insortTree_in_alphabet //=.
    - by rewrite notin_alphabet_splitLeafF_id.
    - by rewrite !inE Ha.
    - by rewrite Hi12 Hc1 Hc2.
    by move: Hf; rewrite notin_alphabet_freqF_0 // addn0.
  - move/alpha_notF: Hi2s=>/(_ _ Ha)=>Has.
    rewrite splitLeafF_insortTree_in_alphabet //=.
    - by rewrite notin_alphabet_splitLeafF_id.
    - by rewrite !inE Ha orbT.
    - by rewrite Hi12 Hc1 Hc2.
    by move: Hf; rewrite notin_alphabet_freqF_0 // addn0.
  move/alpha_notFC: Hi1s=>/(_ _ Ha)=>Ha1.
  move/alpha_notFC: Hi2s=>/(_ _ Ha)=>Ha2.
  rewrite splitLeafF_insortTree_in_alphabetF //=.
  - by rewrite !notin_alphabet_splitLeaf_id.
  - by rewrite !inE negb_or Ha1 Ha2.
  by move: Hf; rewrite !notin_alphabet_freq_0.
- by rewrite consistentF_insortTree /= alpha_intersectsF_uniteTrees negb_or
       Hi1s Hi2s Hi12 Hc1 Hc2 Hcs.
- by apply: insortTree_notnil.
- by rewrite alphabetF_insortTree /uniteTrees /= !inE -orbA.
by rewrite freqF_insortTree /uniteTrees /= -addnA.
Qed.

(* 13.7 *)
Theorem optimum_huffman (t0 : tree A) ts :
  consistentF ts -> heightF ts = 0 -> sortedByWeight ts -> ~~ nilp ts ->
  optimum (huffman t0 ts).
Proof.
elim/(@size_ind (tree A)): ts=>[xs|n IH xs Hs].
- by move/size0nil=>->.
case: xs Hs=>//= t1; case=>[_|t2 ts] /=.
- move=>_; simp sortedByWeight huffman.
  by rewrite maxn0=>/eqP/heightE [w][x] ->.
rewrite ltnS alpha_intersectsF_cons negb_or -andbA =>Hs.
case/and6P=>Hi12 Hi1s _ Hi2s _ Hcs; simp huffman.
move/eqP; rewrite !maxn_eq0; case/and3P=>Hh1 Hh2 Hhs.
move/heightE: Hh1=>[wa][a] Ea; move/heightE: Hh2=>[wb][b] Eb.
rewrite {t1}Ea {t2}Eb /uniteTrees /alpha_intersectsF /alpha_intersects /= ?orbF in Hi12 Hi1s Hi2s *.
move/[dup]=>/sortedByWeight_cons_weight /=; case/andP=>_ Haw1.
move/sortedByWeight_cons/[dup]=>/sortedByWeight_cons_weight /= Haw2.
move/sortedByWeight_cons=>Hsw _.
have Haas: a \notin alphabetF ts.
- move: Hi1s; rewrite alphabet_enumF.
  by move/hasPn=>H; apply/negP=>/H; rewrite inE eq_refl.
have {Hi2s}Hbas: b \notin alphabetF ts.
- move: Hi2s; rewrite alphabet_enumF.
  by move/hasPn=>H; apply/negP=>/H; rewrite inE eq_refl.
have {Hi1s}Hci : consistentF (insortTree (Leaf (wa + wb) a) ts).
- by rewrite consistentF_insortTree /= Hcs andbT.
have Hni : ~~ nilp (insortTree (Leaf (wa + wb) a) ts).
- by apply: insortTree_notnil.
have -> : huffman t0 (insortTree (Node (wa + wb) (Leaf wa a) (Leaf wb b)) ts) =
          splitLeaf (huffman t0 (insortTree (Leaf (wa + wb) a) ts)) wa a wb b.
- rewrite splitLeaf_huffman_commute //.
  - by rewrite splitLeafF_insortTree_in_alphabet /= ?eq_refl // inE eq_refl.
  - by rewrite alphabetF_insortTree !inE eq_refl.
  by rewrite freqF_insortTree /= eq_refl notin_alphabet_freqF_0 // addn0.
apply: optimum_splitLeaf; first by apply: consistent_huffman.
- apply: IH=>//; first by rewrite size_insortTree.
  - by rewrite heightF_insortTree; apply/eqP; rewrite maxn_eq0.
  by apply: sortedByWeight_insortTree=>//; apply/eqP.
- by rewrite alphabet_huffman=>//; rewrite alphabetF_insortTree !inE eq_refl.
- by rewrite alphabet_huffman=>//; rewrite alphabetF_insortTree !inE negb_or Hi12.
- by rewrite freq_huffman // freqF_insortTree /= eq_refl notin_alphabet_freqF_0 // addn0.
apply/allP=>z; rewrite -alphabet_enum alphabet_huffman // alphabetF_insortTree !inE
                 freq_huffman // freqF_insortTree /=; case/orP=>[/eqP->|Hz].
- by rewrite eq_refl notin_alphabet_freqF_0 // addn0 leq_addr leq_addl.
move: (heightF_0_Leaf_freqF Hcs (eqP Hhs) Hz)=>Hl.
case: eqP=>[Ez|_]; first by rewrite -Ez Hz in Haas.
by rewrite add0n; move/allP: Haw1=>/(_ _ Hl); move/allP: Haw2=>/(_ _ Hl) /=->->.
Qed.

End KeyLemmasAndTheorems.
