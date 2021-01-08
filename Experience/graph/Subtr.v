From stdpp Require Import fin_sets.

Fixpoint subtr {A} (eq : forall (v v': A), {v = v'}+{v <> v'}) (l1 : list A) (l2 : list A) : list A :=
  match l2 with
  | [] => l1
  | h :: t => remove eq h (subtr eq l1 t)
  end.

Lemma subtrV_nil X eq (l : list X) : subtr eq l [] = l.
Proof. reflexivity. Qed.

Lemma In_subtr_weak : forall X eq (l1 l2 : list X) v,
    In v (subtr eq l1 l2) -> In v l1.
Proof.
  induction l2; simpl; auto.
  intros. apply IHl2.
  destruct (eq v a).
  - subst. apply remove_In in H. contradiction.
  - apply (in_remove _ _ _ _ H).
Qed.

Lemma In_subtr1 : forall X eq (l1 l2 : list X) v,
    not (In v l2) -> In v l1 -> In v (subtr eq l1 l2).
Proof.
  induction l2; simpl; auto.
  intros.
  assert (a <> v). intro. apply H. left; auto.
  apply in_in_remove; auto.
Qed.

Lemma In_subtr2 : forall X eq (l1 l2 : list X) v,
    In v (subtr eq l1 l2) -> not (In v l2) /\ In v l1.
Proof.
  induction l2; simpl; auto.
  intros.
  assert (a <> v). intro. subst. apply (remove_In _ _ _ H).
  apply in_remove in H as [P0 P1]. apply IHl2 in P0 as [P0 P2].
  split; auto. intro. destruct H; auto.
Qed.

Lemma In_subtr : forall X eq (l1 l2 : list X) v,
    not (In v l2) /\ In v l1 <-> In v (subtr eq l1 l2).
Proof.
  split.
  - intros [P0 P1]. apply In_subtr1; auto.
  - apply In_subtr2.
Qed.

Lemma subtr_remove : forall X eq (l1 l2 : list X) a,
    subtr eq (remove eq a l1) l2 = remove eq a (subtr eq l1 l2).
Proof.
  induction l2; simpl; auto.
  intros. rewrite IHl2. rewrite remove_remove_comm. reflexivity.
Qed.

Lemma subtr_app : forall X eq (l1 l2 l3 : list X),
    subtr eq (subtr eq l1 l2) l3 = subtr eq l1 (l2 ++ l3).
Proof.
  induction l2; simpl; auto.
  intros. rewrite <- IHl2. apply subtr_remove.
Qed.

Lemma In_subtr_app : forall X eq (l1 l2 l3 : list X) v,
    not (In v l3) -> In v (subtr eq l1 l2) -> In v (subtr eq l1 (l2 ++ l3)).
Proof.
  induction l2; intros.
  - apply In_subtr; auto.
  - rewrite <- subtr_app. apply In_subtr; auto.
Qed.

Lemma NoDup_remove : forall X eq (l : list X) a, NoDup l -> NoDup (remove eq a l).
Proof.
  induction l; simpl; auto.
  intros. inversion_clear H.
  destruct (eq a0 a).
  - subst. apply IHl; auto.
  - constructor.
    2 : apply (IHl _ H1).
    intro. rewrite elem_of_list_In in H. apply in_remove in H as [P0 P1].
    apply H0. apply elem_of_list_In; auto.
Qed.

Lemma NoDup_subtr : forall X eq (l1 l2 : list X), NoDup l1 -> NoDup (subtr eq l1 l2).
Proof.
  induction l2; auto.
  intros. simpl. apply IHl2 in H. apply NoDup_remove; auto.
Qed.
