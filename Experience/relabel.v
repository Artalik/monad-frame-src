Require Import Gensym.

Import adequacy_gensym.

(* =tree= *)
Inductive Tree (X : Type) :=
| Leaf : X -> Tree X
| Node : Tree X -> Tree X -> Tree X.
(* =end= *)

Arguments Leaf {_}.
Arguments Node {X}.

(* =label= *)
Fixpoint label {X} (t : Tree X) : mon Fresh (Tree ident) :=
  match t with
  | Leaf _ =>
    let! v := gensym in
    ret! (Leaf v)
  | Node l r =>
    let! l' := label l in
    let! r' := label r in
    ret! (Node l' r')
  end.
(* =end= *)

Definition relabel {X} (t : Tree X): Tree ident := snd (run (label t) initial_state).

Fixpoint flatten {X} (t: Tree X) : list X :=
  match t with
  | Leaf v => cons v nil
  | Node l r => flatten l ++ flatten r
  end.

Fixpoint sameShape {X Y} (t1 : Tree X) (t2 : Tree Y) : Prop :=
  match t1,t2 with
  | Leaf _, Leaf _ => True
  | Node l r, Node l_res r_res  => sameShape l l_res /\ sameShape r r_res
  | _, _ => False
  end.

Definition labelPost {X} (t: Tree X) (t_res : Tree ident) : iProp :=
  ([∗ list] x ∈ (flatten t_res), IsFresh x) ∗ ⌜sameShape t t_res⌝.

Lemma label_spec : forall X (t : Tree X),
    ⊢ {{ emp }} label t {{ t'; labelPost t t' }}.
Proof.
  induction t.
  - iBind. eapply gensym_spec. iRet. rewrite /labelPost. simpl; auto.
  - simpl label. iBind. eapply IHt1. iBind. Frame. eapply IHt2. iRet.
    rewrite /labelPost. iIntros "[[HA %] [HB %]]". iSplitL; auto.
    simpl. iApply big_sepL_app. iFrame.
Qed.

Lemma sep_list_fold : forall a l, ⊢ (IsFresh a -∗ ([∗ list] x ∈ l, IsFresh x) -∗ ⌜a ∉ l⌝ : iProp).
Proof.
  induction l; iIntros "* HA HB".
  - iPureIntro. intro. inversion H.
  - iDestruct "HB" as "[HA' HB]".
    iDestruct (singleton_neq with "HA HA'") as "%".
    iDestruct (IHl with "HA HB") as "%". iPureIntro.
    intro. inversion H1; subst; auto.
Qed.

Lemma fold_nodup : forall l,
    ⊢ (([∗ list] x ∈ l, IsFresh x) : iProp) -∗ ⌜NoDup l⌝.
Proof.
  induction l; simpl; iIntros; norm_all; auto.
  - iPureIntro. apply NoDup_nil_2.
  - iDestruct (IHl with "HC") as "%". iDestruct (sep_list_fold with "HB HC") as "%".
    iPureIntro. constructor; auto.
Qed.

Lemma finish_him : forall X (t : Tree X) t' h,
    labelPost t t' () h -> NoDup (flatten t') /\ sameShape t t'.
Proof.
  intros. apply soundness3 in H. apply (soundness1 h).
  iIntros "HA". iDestruct (H with "HA") as "[HA HB]".
  iDestruct (fold_nodup with "HA") as "HA". iSplit; auto.
Qed.

Lemma relabel_spec : forall X (t : Tree X) t',
    relabel t = t' -> NoDup (flatten t') /\ sameShape t t'.
Proof.
  intros. unfold relabel in H. destruct (run (label t) initial_state) eqn:?.
  destruct H. simpl.
  destruct (use_adequacy _ _ _ _ _ emp_trivial (label_spec _ _) Heqp).
  eapply finish_him. eapply H.
Qed.
