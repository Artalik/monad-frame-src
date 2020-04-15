Require Import MoSel.
Export Maps.PTree.

Import weakestpre_gensym.

Notation "a ! b" := (get b a) (at level 1).

Definition hlocally {A} (le : t A) (f : t A -> iProp) : hprop :=
  fun h => forall le', (forall id v, h !! id = Some v -> le ! id = le' ! id) -> f le' () h.

Definition locally {A} (le : t A) (f : t A -> iProp) : iProp := MonPred (fun _ => hlocally le f) _.
  

(** Useful invariance properties. *)
Ltac inv H := inversion H; clear H; subst.

Ltac unfold_locally :=
  unfold locally; unfold hlocally; MonPred.unseal; split; MonPred.unseal; intros i h H;
  destruct i; inversion H as (H0&H1); clear H; inv H1;
  clear H0; intros j H; destruct j; clear H;
  exists emp, heap_empty, heap_empty; repeat split; auto with heap_scope; [intros h H0; inversion_star h H;
  inversion H1 as (H4&H5); inv H5; clear H4; clear H1; clear H0;
  rewrite heap_union_empty_l | rewrite heap_union_empty_r; auto].

Lemma locally_indep {A} : forall (P : iProp) (le : t A), ⊢P -∗ locally le (fun _ => P).
Proof.
  unfold_locally. intros. apply H2.
Qed.

Lemma locally_simpl {A} : forall P (le : t A), ⊢(∀ le', P le') -∗ locally le (fun le' => P le').
Proof.
  unfold_locally. intros. apply H2.
Qed.

Lemma locally_delete {A} : forall P (le : t A), ⊢ locally le (fun le' => P le') -∗ P le.
Proof.
  unfold_locally. apply H2. eauto. 
Qed.

Lemma locally_sep {A} : forall P R (le : t A),
    ⊢locally le (fun le' => P le') -∗ locally le (fun le' => R le') -∗
            locally le (fun le' => P le' ∗ R le').
Proof.
  unfold_locally. intros j H. destruct j. exists (hheap_ctx h1), h1, heap_empty.
  repeat split; auto with heap_scope.
  repeat red. intros. inversion_star h P. clear H0. red in P1. subst.
  exists h1, h0. repeat split; auto with heap_scope. apply H2.
  intros. eapply H1.
  eapply lookup_union_Some; eauto with heap_scope.
  eapply P2. intros. eapply H1. eapply lookup_union_Some; eauto with heap_scope.
  rewrite heap_union_empty_r; auto. 
Qed.

Lemma locally_and {A} : forall P R (le : t A),
    ⊢locally le (fun le' => P le') ∧ locally le (fun le' => R le') -∗
            locally le (fun le' => P le' ∧ R le').
Proof.
  unfold locally; unfold hlocally; MonPred.unseal; split; MonPred.unseal; intros i h H;
  destruct i; inversion H as (H0&H1); clear H; inv H1;
  clear H0; intros j H; destruct j; clear H.
  exists emp, heap_empty, heap_empty; repeat split; auto.
  3 : rewrite heap_union_empty_l; auto.
  all :inversion_star h P; clear H;
    destruct P2; inv P1; inv H3; clear H2; clear P3; rewrite heap_union_empty_l;
      rewrite heap_union_empty_l in H0. apply (H _ H0). apply (H1 _ H0).
Qed.

Lemma locally_and_out {A} : forall P R (le : t A),
    ⊢locally le (fun le' => P le' ∧ R le') -∗
     locally le (fun le' => P le') ∧ locally le (fun le' => R le').
Proof.
  unfold locally; unfold hlocally; MonPred.unseal; split; MonPred.unseal; intros i h H;
  destruct i; inversion H as (H0&H1); clear H; inv H1;
  clear H0; intros j H; destruct j; clear H.
  exists emp, heap_empty, heap_empty; repeat split; auto.
  3 : rewrite heap_union_empty_l; auto.
  all : inversion_star h P; clear H;
    intros; inv P1; inv H1; clear H0; clear P3; rewrite heap_union_empty_l;
      rewrite heap_union_empty_l in H; eapply P2 in H; destruct H; auto.
Qed.


Lemma locally_indep_frame {A} : forall P R (Q : iProp) (le : t A),
    ⊢locally le (fun le' => P le' -∗ R le') -∗ locally le (fun le' => P le' ∗ Q -∗ R le' ∗ Q).
Proof.
  unfold_locally. intros. repeat red. repeat red in H2.
  intros. destruct a. eapply H2 in H; eauto. clear H0.
  destruct H. inversion_star h P. clear H. destruct P2.
  inv H0. clear P3. red in H. rewrite heap_union_empty_r.
  exists x. exists h,heap_empty. repeat split; auto with heap_scope. intros h0 P3. inversion_star h P.
  clear P3. inversion_star h P. clear P4. eexists. exists h4.
  repeat split; auto. eapply H. exists h1, h3. repeat split; auto.
  - subst. eapply heap_disjoint_union_r_l; eauto.
  - subst. apply map_disjoint_union_l. split; auto.
    apply map_disjoint_union_r in P5 as (_&P10). auto.
  - subst. apply heap_union_assoc.
  - apply map_disjoint_empty_r.
  - rewrite heap_union_empty_r; auto.
Qed.

Lemma locally_modout {A} : forall P (le : t A),
    ⊢<absorb> (locally le (fun le' => P le')) -∗ locally le (fun le' => <absorb> P le').
Proof.
  unfold_locally. clear H3. red in H2. inversion_star h P. clear H2.
  exists h, h0. repeat split; auto. subst. apply P2. intros. eapply H.
  eapply lookup_union_Some; eauto.
Qed.


Lemma locally_sep_indep_r {A} : forall P Q (le : t A),
    ⊢locally le (fun le' => P le') ∗ Q -∗ locally le (fun le' => P le' ∗ Q).
Proof.
  iIntros "* [HA HB]". iApply (locally_sep with "HA"). iApply locally_indep. iFrame.
Qed.

Lemma locally_sep_indep_l {A} : forall P Q (le : t A),
    ⊢locally le (fun le' => P le') ∗ Q -∗ locally le (fun le' => Q ∗ P le').
Proof.
  iIntros "* [HA HB]". iApply (locally_sep with "[HB] HA"). iApply locally_indep. iFrame.
Qed.

Lemma locally_forall {A B} : forall P (le : t A),
    ⊢(∀ l, locally le (fun le' => P l le')) -∗ locally le (fun le' => ∀ (l:B), P l le').
Proof.
  unfold_locally. red. intros. red in H2. apply H2. apply H.
Qed.

Lemma locally_doublon {A} : forall P (le : t A),
    ⊢locally le (fun le' => P le') -∗ locally le (fun le' => locally le' (fun le'' => P le'')).
Proof.
  unfold_locally. intros. apply H2. intros.
  pose H1. apply H in e.
  etransitivity; eauto.
Qed.

Lemma locally_exists {A B} : forall P (le : t A), ∀ t,
      ⊢locally le (fun le' => P t le') -∗ locally le (fun le' => ∃ (t : B), P t le').
Proof.
  unfold_locally. intros. apply H2 in H. exists t0. apply H.
Qed.

Lemma locally_exists_sep {A B} : forall P Q (le : t A), ∀ t,
      ⊢locally le (fun le' => Q t le') -∗ locally le (fun le' => P t le') -∗
              locally le (fun le' => ∃ (t : B), Q t le' ∗ P t le').
Proof.
  iIntros "* HA HB". iApply locally_exists. iApply (locally_sep with "HA HB").
Qed.

Lemma locally_apply {A} : forall (P Q : t A -> iProp) (le : t A),
    ⊢locally le (λ le', P le') -∗ (∀ le, P le -∗ Q le) -∗ locally le (λ le', Q le').
Proof.
  unfold_locally. clear H3. intros j H. destruct j. clear H.
  repeat red. exists (hheap_ctx h1), h1, heap_empty. repeat split; auto with heap_scope.
  red. intros. inversion_star h P. clear H. red in P1. subst.
  edestruct P2. instantiate (1 := tt). repeat red. exists heap_empty, h0.
  repeat split; auto with heap_scope.
  apply map_disjoint_empty_l. rewrite heap_union_empty_l; auto. inversion_star h P.
  clear H. destruct P4. inv H1. clear P5.
  rewrite heap_union_empty_r. rewrite heap_union_empty_r in P3. rewrite heap_union_empty_r in H0.
  apply H. exists h, h1. repeat split; auto. apply H2. intros. erewrite <- H0; auto.
  eapply lookup_union_Some; eauto. apply heap_union_comm; auto. apply map_disjoint_empty_r.
  rewrite heap_union_empty_r; auto.
Qed.


Lemma locally_consequence {A} : forall (P Q : t A -> iProp) (le : t A),
    ⊢(∀ le, P le -∗ Q le) -∗ locally le (λ le', P le') -∗ locally le (λ le', Q le').
Proof.
  iIntros "* HA HB". iApply (locally_apply with "HB HA").
Qed.

    
Lemma locally_delete_2 {A} : forall P Q R (le : t A),
      ⊢locally le (fun le' => R le') -∗
      locally le (fun le' => P le') -∗
      (∀ le, R le -∗ P le -∗ Q le) -∗
      locally le (fun le' => Q le').
Proof.
  iIntros "* HA HB HC". iDestruct (locally_sep with "HA HB") as "HA".
  iApply (locally_apply with "HA [HC]"). iIntros "* [HA HB]".
  iApply ("HC" with "HA HB").
Qed.

Lemma locally_delete_3 {A} : forall P Q R S (le : t A),
      ⊢locally le (fun le' => R le') -∗
      locally le (fun le' => P le') -∗
      locally le (fun le' => S le') -∗
      (∀ le, R le -∗ P le -∗ S le -∗ Q le) -∗
      locally le (fun le' => Q le').
Proof.
  iIntros "* HA HB HC HD". iDestruct (locally_sep with "HB HC") as "HB".
  iApply (locally_delete_2 with "HA HB"). iIntros "* HA [HB HC]". iApply ("HD" with "HA HB HC").
Qed.
  
  

Lemma locally_conseq {A} : forall P Q Q' (le : t A),
    ⊢locally le (fun le' => P le' -∗ Q le') -∗
    locally le (fun le' => Q le' -∗ Q' le') -∗
    locally le (fun le' => P le' -∗ Q' le').
Proof.
  iIntros "* HA HB". iApply (locally_delete_2 with "HA HB"). iIntros "* HA HB HC".
  iApply "HB". iApply "HA". iFrame.
Qed.

Lemma locally_frame_l {A} : forall P Q (le : t A),
    ⊢ P -∗ locally le (fun le' => Q le') -∗ locally le (fun le' => P ∗ Q le').
Proof.
  iIntros. iApply locally_sep_indep_l. iFrame.
Qed.

Lemma locally_frame_r {A} : forall P Q (le : t A),
    ⊢ P -∗ locally le (fun le' => Q le') -∗ locally le (fun le' => Q le' ∗ P).
Proof.
  iIntros. iApply locally_sep_indep_r. iFrame.
Qed.

Lemma locally_set {A} : forall Q (le : t A) t v,
    ⊢\s t -∗ locally le (fun le' => Q le') -∗ locally (set t v le) (fun le' => Q le') ∗ \s t.
Proof.
  unfold_locally.
  destruct H2. red in H. clear H3. repeat red. intros. destruct a. clear H0.
  exists (hheap_ctx h1), h1, heap_empty. repeat split; auto with heap_scope. red. intros. subst.
  inversion_star h P. clear H0. red in P0. exists h0, h. subst. repeat split; auto.
  intros le' H. eapply P1. intros. erewrite <- H. assert (id <> t0). intro. subst.
  eapply map_disjoint_spec.
  eapply P2. eapply lookup_singleton_Some. split; eauto. eauto.
  rewrite gso; eauto. eauto.
  exists x. reflexivity. apply heap_union_comm; auto. apply map_disjoint_empty_r.
  rewrite heap_union_empty_r; auto.
Qed.

Lemma locally_out {A} : forall P Q (le : t A),
    ⊢locally le (fun le' => P le' -∗ Q le') -∗ P le -∗ Q le.
Proof.
  iIntros "* HA HB". iDestruct (locally_delete with "HA HB") as "HA". iApply "HA".
Qed.

Lemma locally_conseq_pure {A} : forall (P Q : t A -> Prop) (le : t A),
    (forall le, P le -> Q le) -> ⊢locally le (λ le', ⌜ P le' ⌝) -∗ locally le (λ le', ⌜ Q le' ⌝).
Proof.
  intros. iApply locally_consequence. eauto.
Qed.

Lemma locally_destruct {A} : forall Q (le : t A) t,
    ⊢locally le (fun le' => \s t ∗ Q le') -∗ locally le (fun le' => (\s t -∗ \s t ∗ Q le') ∗ \s t).
Proof.
  unfold_locally. clear H3. repeat red. intros.
  eapply H2 in H. inversion_star h P. clear H. destruct P0. red in H.
  exists h0, h. subst. repeat split; auto. repeat red. intros. clear H. destruct a.
  exists (hheap_ctx h0), h0, heap_empty. repeat split; auto with heap_scope. intros h H.
  inversion_star h P. clear H. red in P0. destruct P3. red in H. exists h2, h1.
  subst. repeat split; auto. exists x0. reflexivity. apply heap_union_comm; auto.
  apply map_disjoint_empty_r. rewrite heap_union_empty_r; auto.
  exists x. reflexivity. apply heap_union_comm; auto.
Qed.
