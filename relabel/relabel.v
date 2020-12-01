Require Import MoSel.

Import adequacy_gensym_SLMin.

Inductive Tree (X : Type) :=
| Leaf : X -> Tree X
| Node : Tree X -> Tree X -> Tree X.

Arguments Leaf {_}.
Arguments Node {X}.


Fixpoint label {X} (t : Tree X) : mon Fresh (Tree ident) :=
  match t with
  | Leaf _ =>
    let! v := gensym in
    ret (Leaf v)
  | Node l r =>
    let! l' := label l in
    let! r' := label r in
    ret (Node l' r')
  end.

Definition relabel {X} (t : Tree X): Tree ident := snd (run (label t) initial_state).

Fixpoint labelPost {X} (t: Tree X) (t_res : Tree ident) : iProp :=
  match t,t_res with
  | Leaf _, Leaf v => IsFresh v
  | Node l r, Node l_res r_res => labelPost l l_res ∗ labelPost r r_res
  | _, _ => False
  end.

Lemma label_spec : forall X (tree : Tree X),
    ⊢ {{ emp }} label tree {{ tree'; labelPost tree tree' }}.
Proof.
  induction tree.
  - iBind. eapply gensym_spec. iRet.
  - iBind. eapply IHtree1. iBind. Frame. eapply IHtree2. iRet. iIntros "[$ $]".
Qed.

Fixpoint flatten {X} (t: Tree X) : list X :=
  match t with
  | Leaf v => cons v nil
  | Node l r => flatten l ++ flatten r
  end.

Definition sameShape {X Y} (t1 : Tree X) (t2 : Tree Y) : Prop :=
  match t1,t2 with
  | Leaf _, Leaf _ => True
  | Node _ _, Node _ _  => True
  | _, _ => False
  end.

Lemma labelpost_fold : forall X (tree : Tree X) tree0,
    ⊢ labelPost tree tree0 -∗ [∗ list] x ∈ (flatten tree0), IsFresh x.
Proof.
  induction tree, tree0; simpl; iIntros; norm_all; auto; try contradiction.
  iDestruct (IHtree1 with "HB") as "Ht1". iDestruct (IHtree2 with "HC") as "Ht2".
  iApply big_sepL_app. iFrame.
Qed.

Lemma sep_list_fold : forall a l, ⊢ (IsFresh a -∗ ([∗ list] x ∈ l, IsFresh x) -∗ ⌜a ∉ l⌝ : iProp).
Proof.
  induction l; iIntros "* HA HB".
  - iPureIntro. intro. inversion H.
  - iDestruct "HB" as "[HA' HB]".
    destruct (eq_dec a a0).
    + iExFalso. subst. iApply (singleton_false with "HA HA'").
    + iDestruct (IHl with "HA HB") as "%". iPureIntro.
      intro. inversion H0; subst; auto.
Qed.

Lemma fold_nodup : forall l,
    ⊢ (([∗ list] x ∈ l, IsFresh x) : iProp) -∗ ⌜NoDup l⌝.
Proof.
  induction l; simpl; iIntros; norm_all; auto.
  - iPureIntro. apply NoDup_nil_2.
  - iDestruct (IHl with "HC") as "%". iDestruct (sep_list_fold with "HB HC") as "%".
    iPureIntro. constructor; auto.
Qed.

Lemma labelpost_nodup : forall X (t : Tree X) t0,
    ⊢ labelPost t t0 -∗ ⌜NoDup (flatten t0)⌝.
Proof.
  iIntros; norm_all. iDestruct (labelpost_fold with "HB") as "HB".
  iDestruct (fold_nodup with "HB") as "$".
Qed.

Lemma finish_him : forall X (tree : Tree X) tree0 h,
    labelPost tree tree0 () h -> NoDup (flatten tree0) /\ sameShape tree tree0.
Proof.
  intros. apply soundness3 in H. apply (soundness1 h).
  iIntros "HA". iDestruct (H with "HA") as "HA". iDestruct (labelpost_nodup with "HA") as "%".
  iSplit; auto. destruct tree,tree0; auto.
Qed.

Lemma relabel_spec : forall X (tree : Tree X) tree0,
    relabel tree = tree0 -> NoDup (flatten tree0) /\ sameShape tree tree0.
Proof.
  intros. unfold relabel in H. destruct (run (label tree) initial_state) eqn:?. destruct H. simpl.
  eapply (finish_him _ _ _ _ (adequacy_triple_init _ _ _ _ _ emp_trivial (label_spec _ tree) Heqp)).
Qed.
