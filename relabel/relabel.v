Require Import MoSel.

Import adequacy_gensym_SLList.

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

Lemma label_spec : forall X (t : Tree X),
    ⊢ {{ emp }} label t {{ t'; labelPost t t' }}.
Proof.
  induction t.
  - iBind. eapply gensym_spec. iRet.
  - iBind. eapply IHt1. iBind. Frame. eapply IHt2. iRet. iIntros "[$ $]".
Qed.

Fixpoint flatten {X} (t: Tree X) : list X :=
  match t with
  | Leaf v => cons v nil
  | Node l r => flatten l ++ flatten r
  end.

Fixpoint sameShape {X Y} (t1 : Tree X) (t2 : Tree Y) : Prop :=
  match t1,t2 with
  | Leaf _, Leaf _ => True
  | Node l1 r1, Node l2 r2  => sameShape l1 l2 /\ sameShape r1 r2
  | _, _ => False
  end.

Lemma finish_him2 X : forall (t : Tree X) t' h,
    labelPost t t' () h -> NoDup h (* /\ sameShape t t' *).
Proof.
induction t; intros t' h; destruct t'; simpl.
- unfold hsingle=> ->. constructor. intro. inversion H. constructor.
- MonPred.unseal; contradiction.
- MonPred.unseal; contradiction.
- MonPred.unseal => [-H].
  repeat red in H.
  destruct H as [h1 [h2 [P [Q [disj Heq]]]]].
  specialize (IHt1 t'1 h1 P).
  specialize (IHt2 t'2 h2 Q).
  apply list_eq_comm in Heq.
  eapply prop_eq; eauto. clear Heq.
  apply NoDup_app; repeat split; auto.
  intros * H1 H2.
  unfold list_disjoint in disj.
  apply elem_of_list_In in H1.
  apply elem_of_list_In in H2.
  eapply disj; eauto.
Qed.

Lemma finish_him2b X : forall (t : Tree X) t' h,
    labelPost t t' () h -> NoDup (flatten t') /\ sameShape t t'.
Proof.
induction t; intros t' h; destruct t'; simpl.
- unfold hsingle=> _. split; auto.
  apply NoDup_singleton.
- MonPred.unseal; contradiction.
- MonPred.unseal; contradiction.
- MonPred.unseal => [-H].
  repeat red in H.
  destruct H as [h1 [h2 [P [Q [disj Heq]]]]].
  destruct (IHt1 t'1 h1 P) as [H11 H12].
  destruct (IHt2 t'2 h2 Q) as [H21 H22].
  apply list_eq_comm in Heq.
  eapply prop_eq; eauto. clear Heq.
  repeat split; auto.
  apply NoDup_app; repeat split; auto.
  intros * H1 H2.
  unfold list_disjoint in disj.
  apply elem_of_list_In in H1.
  apply elem_of_list_In in H2.
  eapply disj; eauto.
Abort. (* NOT PROVABLE AS-IS! *)

Lemma finish_him3 X : forall t' (t : Tree X) h,
    labelPost t t' () h -> flatten t' = h.
Proof.
induction t'; intros t h; destruct t; simpl.
- unfold hsingle=> ->. done.
- MonPred.unseal; contradiction.
- MonPred.unseal; contradiction.
- MonPred.unseal => [-H].
  repeat red in H.
  destruct H as [h1 [h2 [P [Q [disj Heq]]]]].
  rewrite (IHt'1 t1 h1 P).
  rewrite (IHt'2 t2 h2 Q).
  apply list_eq_comm in Heq.
  eapply prop_eq; eauto.
Qed.

Lemma finish_him4 X : forall (t : Tree X) t' h,
    labelPost t t' () h -> h = flatten t' /\ NoDup h /\ sameShape t t'.
Proof.
induction t; intros t' h; destruct t'; simpl.
- unfold hsingle=> ->. repeat split; auto.
  apply NoDup_singleton.
- MonPred.unseal; contradiction.
- MonPred.unseal; contradiction.
- MonPred.unseal => [-H].
  repeat red in H.
  destruct H as [h1 [h2 [P [Q [disj Heq]]]]].
  eapply list_eq_comm in Heq.
  pattern h.
  eapply prop_eq; eauto.
  destruct (IHt1 t'1 h1 P) as [-> [H12 H13]].
  destruct (IHt2 t'2 h2 Q) as [-> [H22 H23]].
  repeat split; auto.
  apply NoDup_app; repeat split; auto.
  intros * H1 H2.
  unfold list_disjoint in disj.
  apply elem_of_list_In in H1.
  apply elem_of_list_In in H2.
  eapply disj; eauto.
Qed.

Lemma finish_him4w X : forall (t : Tree X) t' h,
    labelPost t t' () h -> NoDup (flatten t') /\ sameShape t t'.
Proof.
intros.
apply finish_him4 in H as [-> ?]. auto.
Qed.

Lemma relabel_spec : forall X (t : Tree X) t',
    relabel t = t' -> NoDup (flatten t') /\ sameShape t t'.
Proof.
  intros. 
  unfold relabel in H. destruct (run (label t) initial_state) eqn:?. 
  destruct H. simpl.
  eapply finish_him4w. (* XXX: this suggests that [adequacy_triple_init] is too specific *)
  eapply adequacy_triple_init; eauto.
  by apply emp_trivial.
  by apply label_spec.
Qed.
