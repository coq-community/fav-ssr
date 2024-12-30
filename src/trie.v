From Equations Require Import Equations.
From mathcomp Require Import all_ssreflect.
From favssr Require Import prelude bintree adt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AbstractTriesViaFunctions.

Context {A : eqType}.

Inductive trieF A := NdF of bool & (A -> option (trieF A)).

Definition emptyTF : trieF A := NdF false (fun=>None).

Fixpoint isinTF (t : trieF A) (xs : seq A) : bool :=
  if xs is x::s then
    let: NdF _ m := t in
      match m x with
      | None => false
      | Some t => isinTF t s
      end
    else let: NdF b _ := t in b.

Fixpoint insertTF (xs : seq A) (t : trieF A) : trieF A :=
  if xs is x::s then
    let: NdF b m := t in
    let t' := match m x with
              | None => emptyTF
              | Some q => q
              end in
    NdF b [eta m with x |-> Some (insertTF s t')]
  else let: NdF _ m := t in NdF true m.

Fixpoint deleteTF (xs : seq A) (t : trieF A) : trieF A :=
  if xs is x::s then
    let: NdF b m := t in
    NdF b (match m x with
           | None => m
           | Some q => [eta m with x |-> Some (deleteTF s q)]
           end)
  else let: NdF _ m := t in NdF false m.

(* Functional Correctness *)

Definition set_ofF (t : trieF A) : pred (seq A) :=
  isinTF t.

Definition invarF (t : trieF A) : bool := true.

Lemma invar_emptyF : invarF emptyTF.
Proof. by []. Qed.

Lemma set_of_emptyF : set_ofF emptyTF =i pred0.
Proof. by case. Qed.

Lemma invar_insertF xs t : invarF t -> invarF (insertTF xs t).
Proof. by []. Qed.

Lemma set_of_insertF xs t : invarF t ->
  set_ofF (insertTF xs t) =i [predU1 xs & set_ofF t].
Proof.
rewrite /set_ofF=>_; elim: xs t=>/= [|x s IH];
case=>b o zs /=; rewrite -!topredE /= -!topredE /=.
- by case: zs.
case: zs=>[|z s'] //.
set t' := match o x with | Some t => t | None => emptyTF end.
case: ifP.
- move/eqP=>{z}->; move: (IH t' s'); rewrite -!topredE /= -!topredE /= => ->.
  have ->: (x :: s' == x :: s) = (s' == s).
  - case: eqP; first by case=>->; rewrite eq_refl.
    by move/eqP=>H; symmetry; apply/negbTE; move: H; apply: contra=>/eqP->.
  rewrite /t'; case E: (o x)=>[t''|] //=.
  by case: s'.
move/negbT=>H; suff: z :: s' != x :: s by move/negbTE=>->.
by move: H; apply: contra; case/eqP=>->.
Qed.

Lemma invar_deleteF xs t : invarF t -> invarF (deleteTF xs t).
Proof. by []. Qed.

Lemma set_of_deleteF xs t : invarF t ->
  set_ofF (deleteTF xs t) =i [predD1 set_ofF t & xs].
Proof.
rewrite /set_ofF=>_; elim: xs t=>/= [|x s IH];
case=>b o zs /=; rewrite -!topredE /= -!topredE /=.
- by case: zs.
case: zs=>// z s'; case E: (o x)=>[t|] /=.
- case: ifP.
  - move/eqP=>{z}->.
    move: (IH t s'); rewrite -!topredE /= -!topredE /= => ->.
    rewrite E; suff: (x :: s' == x :: s) = (s' == s) by move=>->.
    case: eqP; first by case=>->; rewrite eq_refl.
    by move/eqP=>H; symmetry; apply/negbTE; move: H; apply: contra=>/eqP->.
  move/negbT=>H'; suff: z :: s' != x :: s by move=>->.
  by move: H'; apply: contra; case/eqP=>->.
by case: eqP=>//=; case=>{z}->{s'}->; rewrite E.
Qed.

Lemma set_of_isinF t : invarF t -> isinTF t =i set_ofF t.
Proof. by []. Qed.

(* trieF A implements a Set (seq A) *)
Definition SetTrieF :=
  @ASetM.make _ (trieF A)
    emptyTF insertTF deleteTF isinTF
    set_ofF invarF
    invar_emptyF set_of_emptyF
    invar_insertF set_of_insertF
    invar_deleteF set_of_deleteF
    set_of_isinF.

End AbstractTriesViaFunctions.

Section BinaryTries.

Definition trie := tree bool.

Definition sel2 {A} (b : bool) (a1 a2 : A) : A :=
  if b then a2 else a1.

Definition mod2 {A} (f : A -> A) (b : bool) (a1 a2 : A) : A * A :=
  if b then (a1, f a2) else (f a1, a2).

Fixpoint isin (t : trie) (ks : seq bool) : bool :=
  if t is Node l b r then
    match ks with
    | [::] => b
    | k::s => isin (sel2 k l r) s
    end
  else false.

Fixpoint insert (ks : seq bool) (t : trie) : trie :=
  if ks is k::s then
    if t is Node l b r
      then
        let: (a1, a2) := mod2 (insert s) k l r in
        Node a1 b a2
      else
        let: (a1, a2) := mod2 (insert s) k leaf leaf in
        Node a1 false a2
    else if t is Node l _ r then Node l true r else Node leaf true leaf.

Definition node (b : bool) (l r : trie) : trie :=
  if [&& ~~ b, ~~ is_node l & ~~ is_node r] then leaf else Node l b r.

Fixpoint delete (ks : seq bool) (t : trie) {struct t}: trie :=
  if t is Node l b r then
    if ks is k :: s then
        let: (a1, a2) := mod2 (delete s) k l r in
        node b a1 a2
      else node false l r
  else leaf.

(* Functional Correctness s*)

Definition set_of (t : trie) : pred (seq bool) :=
  isin t.

Definition invar (t : trie) : bool := true.

Lemma invar_empty : invar leaf.
Proof. by []. Qed.

Lemma set_of_empty : set_of leaf =i pred0.
Proof. by case. Qed.

Lemma invar_insert xs t : invar t -> invar (insert xs t).
Proof. by []. Qed.

Lemma set_of_insert xs t : invar t ->
  set_of (insert xs t) =i [predU1 xs & set_of t].
Proof.
rewrite /set_of=>_ ys; elim: xs t ys=>/= [|x s IH] t ys; rewrite !inE.
- case: t=>/=[|l b r]; rewrite -!topredE /=; case: ys=>//.
  by case.
case: t=>/=[|l b r]; rewrite -!topredE /= /mod2.
- rewrite orbF; case: x=>/=; case: ys=>//y s'; rewrite /sel2; case: y=>//;
  by move: (IH leaf s'); rewrite inE -topredE /= =>->.
case: x=>/=; case: ys=>//=y s'; rewrite /sel2; case: y=>//=.
- by move: (IH r s'); rewrite inE -topredE /= =>->.
by move: (IH l s'); rewrite inE -topredE /= =>->.
Qed.

Lemma invar_delete xs t : invar t -> invar (delete xs t).
Proof. by []. Qed.

Lemma set_of_delete xs t : invar t ->
  set_of (delete xs t) =i [predD1 set_of t & xs].
Proof.
rewrite /set_of=>_ ys; elim: xs t ys=>/= [|x s IH] t ys; rewrite !inE.
- case: t=>/=[|l b r]; rewrite -!topredE /=; first by rewrite andbF.
  rewrite /node /=; case: ys=>/=[|y s']; case: ifP=>//= /andP [/not_node_leaf -> /not_node_leaf ->].
  by case: y.
case: t=>/=[|l b r]; rewrite -!topredE /= /mod2; first by rewrite andbF.
case: ys=>[|y s']; case: x=>/=.
- by rewrite /node; case: b=>//=; case: ifP.
- by rewrite /node; case: b=>//=; case: ifP.
- rewrite /node; case: b=>/=.
  - by case: y=>//=; move: (IH r s'); rewrite inE -topredE /= =>->.
  case: ifP=>/= [/andP [/not_node_leaf Hl /not_node_leaf Hd]|]; case: y=>//=.
  - by move: (IH r s'); rewrite inE Hd=><-.
  - by rewrite Hl.
  by move=>_; move: (IH r s'); rewrite inE -topredE /= =>->.
rewrite /node; case: b=>/=.
- by case: y=>//=; move: (IH l s'); rewrite inE -topredE /= =>->.
case: ifP=>/= [/andP [/not_node_leaf Hd /not_node_leaf Hr]|]; case: y=>//=.
- by rewrite Hr.
- by move: (IH l s'); rewrite inE Hd=><-.
by move=>_; move: (IH l s'); rewrite inE -topredE /= =>->.
Qed.

Lemma set_of_isin t : invar t -> isin t =i set_of t.
Proof. by []. Qed.

(* trie implements a Set (seq bool) *)
Definition SetTrie :=
  @ASetM.make _ trie
    leaf insert delete isin
    set_of invar
    invar_empty set_of_empty
    invar_insert set_of_insert
    invar_delete set_of_delete
    set_of_isin.

End BinaryTries.

Section BinaryPatriciaTries.

Definition trieP := tree (seq bool * bool).

Fixpoint isinP (t : trieP) (ks : seq bool) : bool :=
  if t is Node l (ps,b) r then
    let n := size ps in
    if ps == take n ks then
      if drop n ks is k::s then
           isinP (sel2 k l r) s
         else b
    else false
  else false.

Equations split {T : eqType} (xs ys : seq T) : seq T * seq T * seq T :=
split [::]    ys      => ([::],[::],ys);
split xs      [::]    => ([::],xs,[::]);
split (x::xs) (y::ys) => if x != y then ([::],x::xs,y::ys)
                            else let: (ps,xs',ys') := split xs ys in
                                 (x::ps,xs',ys').

Fixpoint insertP (ks : seq bool) (t : trieP) : trieP :=
  if t is Node l (ps,b) r then
    match split ks ps with
    | (_ , [::]  , [::]  ) => Node l (ps,true) r
    | (qs, [::]  , p::ps') => let t := Node l (ps',b) r in
                              if p then Node leaf (qs, true) t
                                   else Node t    (qs, true) leaf
    | (_ , k::ks', [::]  ) => let: (l',r') := mod2 (insertP ks') k l r in
                              Node l' (ps,b) r'
    | (qs, k::ks', _::ps') => let tp := Node l (ps',b) r in
                              let tk := Node leaf (ks',true) leaf in
                              if k then Node tp (qs,false) tk
                                   else Node tk (qs,false) tp
    end
  else Node leaf (ks, true) leaf.

Definition nodeP (ps : seq bool) (b : bool) (l r : trieP) : trieP :=
  if [&& ~~ b, ~~ is_node l & ~~ is_node r] then leaf else Node l (ps,b) r.

Fixpoint deleteP (ks : seq bool) (t : trieP) : trieP :=
  if t is Node l (ps,b) r then
    match split ks ps with
    | (qs, _     , p::ps') => Node l (ps,b) r
    | (qs, k::ks', [::]  ) => let: (l',r') := mod2 (deleteP ks') k l r in
                              nodeP ps b l' r'
    | (qs, [::]  , [::]  ) => nodeP ps false l r
    end
  else leaf.

(* Functional Correctness *)

Fixpoint prefix_trie (ks : seq bool) (t : trie) : trie :=
  if ks is k::s then
    let t' := prefix_trie s t in
    if k then Node leaf false t' else Node t' false leaf
  else t.

Fixpoint abs_trieP (t : trieP) : trie :=
  if t is Node l (ps,b) r then
    prefix_trie ps (Node (abs_trieP l) b (abs_trieP r))
  else leaf.

Lemma isin_prefix_trie ps t ks :
  isin (prefix_trie ps t) ks = ((ps == take (size ps) ks) && isin t (drop (size ps) ks)).
Proof.
elim: ps ks=>/=[|p ps IH] ks; first by rewrite take0 drop0.
by case: p=>/=; case: ks=>//= k s; case: k=>//=; rewrite IH.
Qed.

Lemma isinP_abs t ks :
  isinP t ks = isin (abs_trieP t) ks.
Proof.
elim: t ks=>//= l IHl [ps b] r IHr ks.
rewrite isin_prefix_trie /=; case: ifP=>//= E.
case: (drop (size ps) ks)=>// h t; case: h=>/=.
- apply: IHr.
apply: IHl.
Qed.

Lemma prefix_trie_leafs ks :
  prefix_trie ks (Node leaf true leaf) = insert ks leaf.
Proof. by elim: ks=>//=k s ->; case: k. Qed.

Lemma insert_prefix_trie_same ps l b r :
  insert ps (prefix_trie ps (Node l b r)) = prefix_trie ps (Node l true r).
Proof. by elim: ps=>//=p s IH; case: p=>/=; rewrite IH. Qed.

Lemma insert_append ks ks' t :
  insert (ks ++ ks') (prefix_trie ks t) = prefix_trie ks (insert ks' t).
Proof. by elim: ks=>//=k s IH; case: k=>/=; rewrite IH. Qed.

Lemma prefix_trie_append ps qs t :
  prefix_trie (ps ++ qs) t = prefix_trie ps (prefix_trie qs t).
Proof. by elim: ps=>//=p s IH; case: p; rewrite IH. Qed.

Lemma split_if {T : eqType} ks ps qs ks' ps' (x0 : T) :
  split ks ps = (qs, ks', ps') ->
  [&& ks == qs ++ ks', ps == qs ++ ps' & ((~~ nilp ks' && ~~ nilp ps' ==> (head x0 ks' != head x0 ps')))].
Proof.
funelim (split ks ps); simp split.
- by case=><-<-<-/=; rewrite eq_refl.
- by case=><-<-<- /=; rewrite eq_refl.
case: eqP=>/=.
- move=>->; case H': (split xs ys)=>[[zs xs'] ys'][<-<-<-] /=.
  by case/and3P: (H _ _ _ x0 H')=>/eqP->/eqP->->; rewrite !eq_refl.
by move/eqP=>H'; case=><-<-<-/=; rewrite !eq_refl.
Qed.

Lemma insertP_abs ks t :
  abs_trieP (insertP ks t) = insert ks (abs_trieP t).
Proof.
elim: t ks=>[|l IHl [ps b] r IHr] ks /=; first by exact: prefix_trie_leafs.
case H: (split ks ps)=>[[qs ks'] ps'].
case/and3P: (split_if false H)=>{H}.
case: ks'=>[|k ks'] /=; case: ps'=>[|p ps'] /=.
- by rewrite cats0 =>/eqP->/eqP->_; rewrite insert_prefix_trie_same.
- rewrite cats0=>/eqP->/eqP->_; rewrite prefix_trie_append /=; case: p=>/=;
  by rewrite insert_prefix_trie_same.
- rewrite cats0=>/eqP->/eqP->_. rewrite insert_append /=; case: k=>/=.
  - by rewrite IHr.
  by rewrite IHl.
move=>/eqP->/eqP->; rewrite prefix_trie_append insert_append /=; case: k; case: p=>//= _;
by rewrite prefix_trie_leafs.
Qed.

Lemma prefix_trie_leaf xs t :
  ~~ is_node (prefix_trie xs t) = (nilp xs && ~~ is_node t).
Proof. by case: xs=>//=x s; case: x. Qed.

Lemma abs_trieP_leaf t : ~~ is_node (abs_trieP t) = ~~ is_node t.
Proof. by case: t=>//=l [ps b] r; rewrite prefix_trie_leaf andbF. Qed.

Lemma delete_prefix_trie xs l b r :
  delete xs (prefix_trie xs (Node l b r)) =
    if ~~ is_node l && ~~ is_node r then leaf else prefix_trie xs (Node l false r).
Proof.
elim: xs=>//= x s IH; case: x=>/=; rewrite /node /= IH;
by case E: (~~ is_node l && ~~ is_node r)=>//=; rewrite prefix_trie_leaf /= andbF /=.
Qed.

Lemma delete_append_prefix_trie xs ys t :
  delete (xs ++ ys) (prefix_trie xs t) =
    if ~~ is_node (delete ys t) then leaf else prefix_trie xs (delete ys t).
Proof.
elim: xs=>/=[|x s IH]; first by case: (delete ys t).
case: x=>/=; rewrite /node /= IH;
by case E: (~~ is_node (delete ys t))=>//=; rewrite prefix_trie_leaf E andbF.
Qed.

Lemma deleteP_abs ks t :
  delete ks (abs_trieP t) = abs_trieP (deleteP ks t).
Proof.
elim: t ks=>[|l IHl [ps b] r IHr] ks //=.
case H: (split ks ps)=>[[qs ks'] ps'].
case/and3P: (split_if false H)=>{H}.
case: ks'=>[|k ks'] /=; case: ps'=>[|p ps'] /=.
- rewrite cats0 =>/eqP->/eqP->_.
  by rewrite delete_prefix_trie !abs_trieP_leaf /nodeP /=; case: ifP.
- rewrite cats0=>/eqP->/eqP->_; rewrite prefix_trie_append /=.
  by case: p; rewrite delete_prefix_trie /= ?andbT prefix_trie_leaf /= andbF.
- rewrite cats0 =>/eqP->/eqP->_.
  rewrite delete_append_prefix_trie /=; case: k=>/=; case: b=>/=; rewrite /node /nodeP /=.
  - by rewrite IHr.
  - by rewrite IHr !abs_trieP_leaf; case: (~~ is_node l && ~~ is_node (deleteP ks' r)).
  - by rewrite IHl.
  by rewrite IHl !abs_trieP_leaf; case: (~~ is_node (deleteP ks' l) && ~~ is_node r).
move=>/eqP->/eqP->; rewrite prefix_trie_append delete_append_prefix_trie /=; case: p; case: k=>//= _;
by rewrite /node /= prefix_trie_leaf /= andbF.
Qed.

(* Corollaries *)

Definition set_ofP (t : trieP) : pred (seq bool) :=
  set_of (abs_trieP t).

Definition invarP (t : trieP) : bool := true.

Lemma invar_emptyP : invarP leaf.
Proof. by []. Qed.

Lemma set_of_emptyP : set_ofP leaf =i pred0.
Proof. by []. Qed.

Lemma invar_insertP xs t : invarP t -> invarP (insertP xs t).
Proof. by []. Qed.

Corollary set_of_insertP xs t : invarP t ->
  set_ofP (insertP xs t) =i [predU1 xs & set_ofP t].
Proof. by rewrite /set_ofP=>H ys; rewrite insertP_abs set_of_insert. Qed.

Lemma invar_deleteP xs t : invarP t -> invarP (deleteP xs t).
Proof. by []. Qed.

Corollary set_of_deleteP xs t : invarP t ->
  set_ofP (deleteP xs t) =i [predD1 set_ofP t & xs].
Proof. by rewrite /set_ofP=>H ys; rewrite -deleteP_abs set_of_delete. Qed.

Corollary set_of_isinP t : invarP t -> isinP t =i set_ofP t.
Proof. by rewrite /set_ofP => _ z; rewrite -set_of_isin // -topredE /= isinP_abs. Qed.

(* trieP implements a Set (seq bool) *)
Definition SetTrieP :=
  @ASetM.make _ trieP
    leaf insertP deleteP isinP
    set_ofP invarP
    invar_emptyP set_of_emptyP
    invar_insertP set_of_insertP
    invar_deleteP set_of_deleteP
    set_of_isinP.

End BinaryPatriciaTries.

Section Exercises.

(* Exercise 12.1 *)

(* N for non-accepting, A for accepting *)
Inductive trie2 := Lf | NdN of trie2 & trie2 | NdA of trie2 & trie2.

Fixpoint isin2 (t : trie2) (ks : seq bool) : bool := false. (* FIXME *)

Fixpoint insert2 (ks : seq bool) (t : trie2) : trie2 := t. (* FIXME *)

Fixpoint delete2 (ks : seq bool) (t : trie2) {struct t}: trie2 := t. (* FIXME *)

(* Functional Correctness s*)

Definition set_of2 (t : trie2) : pred (seq bool) :=
  isin2 t.

Definition invar2 (t : trie2) : bool := true.

Lemma invar_empty2 : invar2 Lf.
Proof. Admitted.

Lemma set_of_empty2 : set_of2 Lf =i pred0.
Proof. Admitted.

Lemma invar_insert2 xs t : invar2 t -> invar2 (insert2 xs t).
Proof. Admitted.

Lemma set_of_insert2 xs t : invar2 t ->
  set_of2 (insert2 xs t) =i [predU1 xs & set_of2 t].
Proof.
Admitted.

Lemma invar_delete2 xs t : invar2 t -> invar2 (delete2 xs t).
Proof. Admitted.

Lemma set_of_delete2 xs t : invar2 t ->
  set_of2 (delete2 xs t) =i [predD1 set_of2 t & xs].
Proof.
Admitted.

Lemma set_of_isin2 t : invar2 t -> isin2 t =i set_of2 t.
Proof. Admitted.

(* trie2 implements a Set (seq bool) *)
Definition SetTrie2 :=
  @ASetM.make _ trie2
    Lf insert2 delete2 isin2
    set_of2 invar2
    invar_empty2 set_of_empty2
    invar_insert2 set_of_insert2
    invar_delete2 set_of_delete2
    set_of_isin2.

(* Exercise 12.2 *)

Fixpoint invar_shrunk (t : trie) : bool := true. (* FIXME *)

Lemma invar_shrunk_insert xs t : invar_shrunk t -> invar_shrunk (insert xs t).
Proof.
Admitted.

Lemma invar_shrunk_delete xs t : invar_shrunk t -> invar_shrunk (delete xs t).
Proof.
Admitted.

End Exercises.
