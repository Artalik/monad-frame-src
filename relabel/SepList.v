Require Import FunctionalExtensionality.

From iris Require Export bi.bi proofmode.tactics proofmode.monpred.

Axiom prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.
Definition pred_incl {A} (P Q : A -> Prop) := forall x, P x -> Q x.

Definition pred_impl {A} (P Q : A -> Prop) := fun x => P x -> Q x.

Notation "P ==> Q" := (pred_incl P Q).

Section hprop.

  Definition list_disjoint {X} (l1 l2 : list X) := forall x y : X, In x l1 -> In y l2 -> x <> y.
  Definition eq_list {X} (l1 l2 : list X) := forall x, In x l1 <-> In x l2.
  Notation "l1 ≡ l2" := (eq_list l1 l2).
  Notation "l1 ∪ l2" := (l1 ++ l2).
  Notation "l1 ##ₘ l2" := (list_disjoint l1 l2).
  Notation "∅" := ([]).

  Lemma list_eq_comm : forall X (l1 l2 : list X), l1 ≡ l2 -> l2 ≡ l1.
  Proof. split; intros; apply H; auto. Qed.

  Lemma list_disjoint_comm : forall X (l1 l2 : list X), l1 ##ₘ l2 -> l2 ##ₘ l1.
  Proof. intros X l1 l2 P0 x y P1 P2 eq. eapply P0; eauto. Qed.

  Lemma list_eq_union_comm : forall X (l1 l2 l3 : list X), l1 ≡ l2 ∪ l3 -> l1 ≡ l3 ∪ l2.
  Proof.
    split; intros. apply H in H0. eapply in_app_or in H0 as [H0|H0]; apply in_or_app; auto.
    apply H. eapply in_app_or in H0 as [H0|H0]; apply in_or_app; auto.
  Qed.

  Lemma list_eq_disjoint : forall X (l1 l2 l3 : list X), l1 ≡ l2 -> l2 ##ₘ l3 -> l1 ##ₘ l3.
  Proof.
    intros X l1 l2 l3 P0 P1 x y P2 P3 eq. eapply P1; eauto. apply P0; auto.
  Qed.

  Lemma list_disjoint_empty_l : forall X (l : list X), ∅ ##ₘ l.
  Proof. intros X l x y P0 P1. inversion P0. Qed.

  Lemma list_disjoint_empty_r : forall X (l : list X), l ##ₘ ∅.
  Proof. intros X l x y P0 P1. inversion P1. Qed.

  Lemma list_disjoint_union_l : forall X (l1 l2 l3 : list X), l1 ##ₘ l3 -> l2 ##ₘ l3 -> l1 ∪ l2 ##ₘ l3.
  Proof.
    intros X l1 l2 l3 P0 P1 x y P2 P3 eq.
    eapply in_app_or in P2 as [P2|P2]. eapply P0; eauto. eapply P1; eauto.
  Qed.

  Lemma list_disjoint_union_r : forall X (l1 l2 l3 : list X), l1 ##ₘ l3 -> l1 ##ₘ l2 -> l1 ##ₘ l3 ∪ l2.
  Proof.
    intros X l1 l2 l3 P0 P1 x y P2 P3 eq.
    eapply in_app_or in P3 as [P3|P3]. eapply P0; eauto. eapply P1; eauto.
  Qed.

  Lemma list_disjoint_union_l_l : forall X (l1 l2 l3 : list X) , l1 ∪ l2 ##ₘ l3 -> l1 ##ₘ l3.
  Proof.
    intros. intros x y P0 P1. apply H; auto. apply in_or_app. left; auto.
  Qed.

  Lemma list_disjoint_union_l_r : forall X (l1 l2 l3 :list X) , l1 ∪ l2 ##ₘ l3 -> l2 ##ₘ l3.
  Proof.
    intros. intros x y P0 P1. apply H; auto. apply in_or_app. right; auto.
  Qed.

  Lemma list_disjoint_union_r_r : forall X (l1 l2 l3 :list X) , l1 ##ₘ l2 ∪ l3 -> l1 ##ₘ l3.
  Proof.
    intros. intros x y P0 P1. apply H; auto. apply in_or_app. right; auto.
  Qed.

  Lemma list_disjoint_union_r_l : forall X (l1 l2 l3 :list X) , l1 ##ₘ l2 ∪ l3 -> l1 ##ₘ l2.
  Proof.
    intros. intros x y P0 P1. apply H; auto. apply in_or_app. left; auto.
  Qed.

  Lemma in_empty_l : forall X (l: list X) x, In x l <-> In x (∅ ∪ l).
  Proof.
    split; intros. apply in_app_iff. right; auto.
    apply in_app_iff in H as [H|H]; auto. inversion H.
  Qed.


  Hint Resolve list_eq_comm list_disjoint_union_l_l list_disjoint_union_l_r
       list_disjoint_union_r_l list_disjoint_union_r_r list_disjoint_comm
       list_eq_union_comm list_eq_disjoint list_disjoint_union_r
       list_disjoint_union_l list_disjoint_empty_r list_disjoint_empty_l
       in_empty_l : list_scope.

  (* Operators *)
  Context {X : Type}.
  Definition hprop := list X -> Prop.

  Definition hand (H1 H2:hprop):hprop :=
    fun h => H1 h /\ H2 h.

  Definition hor (H1 H2:hprop) : hprop := fun h => H1 h \/ H2 h.

  Definition hempty : hprop :=
    fun h => h = ∅.

  Definition hsingle loc : hprop :=
    fun h =>  h = [loc].

  Definition hheap_ctx (ctx : list X) : hprop := fun h => h = ctx.

  Definition hstar (H1 H2 : hprop) : hprop :=
    fun h => exists h1 h2, H1 h1
                   /\ H2 h2
                   /\ (h1 ##ₘ h2)
                   /\ h ≡ h1 ∪ h2.

  Definition hexists {A} (J : A -> hprop) : hprop :=
    fun h => exists x, J x h.

  Definition hpure (P:Prop) : hprop :=
    fun h => P /\ hempty h.

  Definition htop : hprop :=
    fun h => True.

  Definition hforall {A} (f : A -> hprop) : hprop := fun h => forall a, f a h.


  Definition hwand (H1 H2 : hprop) : hprop :=
    hexists (fun (H:hprop) => (hstar H (hpure ((hstar H H1) ==> H2)))).

  Definition qwand A (Q1 Q2:A->hprop) :=
    hforall (fun x => hwand (Q1 x) (Q2 x)).

  Definition hpure_abs (P : Prop) : hprop := fun h => P.

  Lemma hempty_intro : hempty ∅.
  Proof using. reflexivity. Qed.

  Local Notation "'heap_empty'" := (∅).

  Local Notation "h1 \u h2" := (h1 ∪ h2) (at level 37, right associativity).

  Local Notation "'Hexists' x1 , H" := (hexists (fun x1 => H))
                                         (at level 39, x1 ident, H at level 50).
  Local Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
                                            (at level 39, x1 ident, x2 ident, H at level 50).
  Local Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
                                               (at level 39, x1 ident, x2 ident, x3 ident, H at level 50).

  Local Notation "'\[]'" := (hempty)
                              (at level 0).

  Local Notation "\[ P ]" := (hpure P)
                               (at level 0, P at level 99, format "\[ P ]").

  Local Notation "H1 '\*' H2" := (hstar H1 H2)
                                   (at level 41, right associativity).

  Local Notation "\Top" := htop.


  Declare Scope heap_scope.

  Ltac inversion_star h P :=
    match goal with
    | H : (_ \* _) _ |- _ =>
      let W := fresh h in
      let w := fresh P in
      inversion H as (W&w);
      let W := fresh h in
      destruct w as (W&w);
      do 3 (let w0 := fresh P in
            destruct w as (w0&w))
    end.
  Ltac extens := apply functional_extensionality; intro; apply prop_extensionality.

  Section Properties.

    Lemma hstar_comm : forall H1 H2,
      H1 \* H2 = H2 \* H1.
    Proof using.
      intros H1 H2. extens.
      split; intros P; inversion_star h P; exists h0; exists h; do 3 (split; eauto with list_scope).
    Qed.

    Lemma hstar_assoc : forall H1 H2 H3,
        (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
    Proof using.
      intros H1 H2 H3. extens. split.
      { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U).
        exists h1; exists (h2 ∪ h3). repeat split; eauto with list_scope.
        { exists h2; exists h3; repeat split; eauto with list_scope. }
        { intros. apply U in H. apply in_app_or in H as [H|H]. apply U' in H.
          apply in_app_or in H as [H|H]. apply in_or_app. left; auto.
          apply in_or_app. right. apply in_or_app. left; auto.
          apply in_or_app. right; auto. apply in_or_app. right; auto. }
        { intros. apply in_app_or in H as [H|H]. apply U.
          apply in_or_app. left. apply U'. apply in_or_app. left; auto.
          apply in_app_or in H as [H|H]. apply U. apply in_or_app. left; auto.
          apply U'. apply in_or_app. right; auto.
          apply U. apply in_or_app. right; auto. } }
      { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U).
        exists (h1 ∪ h2); exists h3. repeat split; eauto with list_scope.
        { exists h1; exists h2; repeat split; eauto with list_scope.
          intros y z P0 P1 eq. eapply D; eauto. apply U'. apply in_or_app. left; auto. }
        { eapply list_disjoint_union_l; auto.
          intros y z P0 P1 eq. eapply D; eauto. apply U'. apply in_or_app. right; auto. }
        { intros. apply U in H. apply in_app_or in H as [H|H]. apply in_or_app.
          left. apply in_or_app. left; auto. apply U' in H. apply in_app_or in H as [H|H].
          apply in_or_app. left. apply in_or_app. right; auto.
          apply in_or_app. right; auto. }
        { intros. apply in_app_or in H as [H|H]. apply U.
          apply in_or_app. apply in_app_or in H as [H|H]. left; auto.
          right. apply U'. apply in_or_app. left; auto.
          apply U. apply in_or_app. right. apply U'. apply in_or_app. right; auto. } }
    Qed.
    Axiom prop_eq : forall (l1 l2 : list X) (P : hprop), l1 ≡ l2 -> P l1 -> P l2.
  End Properties.

  Definition hpersistent (H:hprop) : hprop := fun h => H ∅.

  Definition hlater (H : hprop) := H.

  Set Warnings "-redundant-canonical-projection -convert_concl_no_check".
  Canonical Structure hpropO := leibnizO hprop.

  Program Canonical Structure hpropList : bi :=
    Bi hprop _ _ pred_incl hempty hpure_abs hand hor
       pred_impl (@hforall) (@hexists) hstar hwand hpersistent hlater _ _ _ _.
  Next Obligation.
    repeat split; try(solve_proper); eauto with list_scope.
    - intros H h P. assumption.
    - rewrite /Transitive. intros. intros h P. eauto.
    - rewrite leibniz_equiv_iff. intros (P0&P1). extens. split; intro; auto.
    - intros n P0 P1 equiv. extens. unfold hpure_abs. auto.
    - intros A n P0 P1 equiv. unfold hforall. eapply functional_extensionality in equiv.
      subst. auto.
    - intros A n P0 P1 equiv. unfold hexists. eapply functional_extensionality in equiv.
      subst. auto.
    - intros. intros l0 P0. red in P0. apply H; repeat red; auto.
    - intros. intros l P0. destruct P0. auto.
    - intros. intros l P0. destruct P0. auto.
    - intros. intros l P0. left; auto.
    - intros. intros l P0. right; auto.
    - rewrite /hor. intros P Q h P0 P1 h0 P2. destruct P2; auto.
    - intros Q R W H l P0 P1. apply H. split; auto.
    - intros Q R W H l P0. destruct P0. apply H in H0. apply H0 in H1. assumption.
    - intros x W a H h P h0. apply H. apply P.
    - intros h Q a H H0. apply H0.
    - intros x W H P Q. exists H. apply Q.
    - intros x W Q P h P0. destruct P0. eapply P. apply H.
    - intros P P' Q Q' A B C D. inversion_star h P. exists h; exists h0. repeat split; eauto; intro.
      apply P0; auto. apply P0. auto.
    - intros x W A. exists heap_empty; exists W. repeat split; auto with list_scope.
    - intros P h Q. inversion_star H H. inversion H3. subst. eapply prop_eq; eauto.
      split; intros. apply H1. apply in_or_app. right; auto. apply H1 in H.
      apply in_app_or in H as [H|H]. inversion H. apply H.
    - intros P Q h R. inversion_star H H. exists H2; exists H0. repeat split; eauto with list_scope; intro.
      apply H1 in H. apply in_app_iff. apply in_app_iff in H as [H|H]; auto.
      apply H1. apply in_app_iff. apply in_app_iff in H as [H|H]; auto.
    - intros P Q R h P0. rewrite <- hstar_assoc. apply P0.
    - intros P Q R P0 h P1. exists P. exists h; exists heap_empty. repeat split; auto with list_scope; intros.
      apply in_app_iff. left; auto.
      apply in_app_iff in H as [H|H]; auto. inversion H.
    - intros P Q R W h P0. inversion_star h P. clear P0. apply W in P2. destruct P2.
      inversion_star h H. clear H. inversion H2. inversion H4. subst. clear H4.
      apply H. exists h2; exists h1. repeat split; auto; subst; intros. intros y z P0 P5 eq.
      eapply P4; eauto. apply H0. apply in_or_app. left. auto.
      + apply P1 in H4. apply in_app_iff in H4 as [H4|H4]. apply H0 in H4.
        apply in_app_or in H4 as [H4|H4]. apply in_app_iff. left; auto. inversion H4.
        apply in_app_iff. right; auto.
      + apply P1. apply in_app_or in H4 as [H4|H4]. apply in_app_iff. left; auto.
        apply H0. apply in_app_iff. left; auto. apply in_app_iff. right; auto.
    - rewrite /hpersistent. intros P Q H h P0. apply H. apply P0.
    - rewrite /hpersistent. rewrite /hforall. intros A B C D E. apply D.
    - rewrite /hpersistent. intros P Q h P0. inversion_star h P. apply P2.
    - intros P Q x W. destruct W. exists heap_empty; exists x. repeat split; auto with list_scope.
  Qed.
  Next Obligation.
    repeat split; try(solve_proper); eauto.
    - intros A Φ h a. rewrite /hlater. unfold hforall in *. unfold hlater in a. apply a.
    - intros A Φ h a. rewrite /hor. unfold hlater in *. destruct a. right. exists x. apply H.
    - intros Hp h P. unfold hlater in *. right. intro. apply P.
  Qed.

  Instance inhabited_unit : Inhabited unit.
  Proof.
    split. apply ().
  Qed.

  Instance PreOrder_unit : PreOrder (fun (t1 t2 : unit) => t1 = t2).
  Proof.
    split; repeat red; intros; trivial. destruct x,y,z. reflexivity.
  Qed.

  Program Canonical Structure biInd := BiIndex unit inhabited_unit _ PreOrder_unit.

  Definition single (l : X) : @monPred biInd hpropList := MonPred (fun _ => hsingle l) _.

  Definition heap_ctx (h : list X) : monPred biInd hpropList := MonPred (fun _ => hheap_ctx h) _.

  Ltac inv H := inversion H; clear H; subst.

  Local Open Scope bi_scope.
  Local Notation "'IsFresh' l" :=
    (single l) (at level 20) : bi_scope.

  Lemma singleton_neq : forall t t', ⊢ IsFresh t -∗ IsFresh t' -∗ ⌜t ≠ t'⌝.
  Proof.
    MonPred.unseal. split. MonPred.unseal. repeat red. intros.
    exists emp, heap_empty, heap_empty. repeat split; auto with list_scope. clear H0. destruct a.
    repeat red. intros l P0. inv H. destruct i. inversion_star h P. clear P0.
    inv P1. clear P3. intros. destruct a. clear H. red in P2. subst.
    exists (hheap_ctx l), l, ∅. repeat split; eauto with list_scope.
    intros h H eq. inversion_star h P. clear H. red in P1. repeat red in P2. subst.
    eapply P3. eapply P. apply in_or_app. right. apply (in_eq t'); eauto.
    apply (in_eq t'); eauto. reflexivity. intros. apply in_or_app. left; auto.
    intros. apply in_app_or in H as [H|H]; auto. inv H.
    intros. inv H. apply in_app_iff. left; auto.
    intros. inv H. apply in_app_iff in H1 as [H1|H1]; auto.
  Qed.

  Definition pure_empty (P : Prop) : monPred biInd hpropList := <affine> ⌜P⌝.

  Local Notation "\⌜ P ⌝" := (pure_empty P)
                               (at level 0, P at level 99, format "\⌜ P ⌝").

  Global Instance affine_pure (P : Prop) : Affine (pure_empty P).
  Proof.
    red. iIntros "HA". trivial.
  Qed.

  Lemma emp_trivial : ⊢ (emp : monPred biInd hpropList). Proof. simpl. auto. Qed.

  Lemma pure_empty_destruct : forall P Q, ⊢ \⌜ P /\ Q ⌝ -∗ \⌜ P ⌝ ∗ \⌜ Q ⌝ .
  Proof. iIntros (P Q H). destruct H. iSplit; iPureIntro; auto. Qed.


  Global Instance affine_heap_empty : Affine (heap_ctx ∅).
  Proof.
    split. intro. MonPred.unseal. repeat red. intros. apply H.
  Qed.

  Lemma init_heap : ⊢ heap_ctx ∅.
  Proof.
    split. MonPred.unseal. repeat red. intros. apply H.
  Qed.

  Lemma instance_heap : forall (P : monPred biInd hpropList) (Q : Prop), (forall tmps, P () tmps -> Q) -> (P ⊢ ⌜Q⌝).
  Proof.
    MonPred.unseal. intros. split. repeat red. intros.
    eapply H. destruct i. eapply H0.
  Qed.

  Lemma soundness1 h (Φ : Prop) : (heap_ctx h ⊢ (⌜ Φ ⌝) : monPred biInd hpropList) -> Φ.
  Proof.
    MonPred.unseal=> -[H]. repeat red in H.
    pose (e := H () h). eapply e. reflexivity.
  Qed.

  Lemma soundness2 (Φ : monPred biInd hpropList) h : (⊢heap_ctx h -∗ Φ) -> Φ () h.
  Proof.
    MonPred.unseal=> -[H]. repeat red in H.
    pose (e := H () ∅).
    simpl in *. edestruct e.
    - rewrite monPred_at_emp. split; auto; apply hempty_intro.
    - repeat red. repeat split; auto.
    - inversion_star h P. inversion P1. apply H1. exists heap_empty; exists h.
      inv H2. repeat split; eauto with list_scope.
      eapply prop_eq. 2 : apply P0. split; intro. apply P. apply in_app_iff. left; auto.
      apply P in H2. apply in_app_iff in H2 as [H2|H2]; auto. inv H2.
  Qed.

  Lemma soundness3 (Φ : monPred biInd hpropList) h : Φ () h -> (⊢heap_ctx h -∗ Φ).
  Proof.
    MonPred.unseal. split. MonPred.unseal. intros. repeat red. intros.
    exists emp. exists x; exists heap_empty. repeat split; auto with list_scope.
    inv H0. destruct i,a. clear H1. intros h0 P0. inversion_star h P. clear P0.
    inv P1. red in P2. subst. eapply prop_eq; eauto. split; intro. apply P.
    apply in_app_iff. right; auto. apply P in H0. apply in_app_iff in H0 as [H0|H0].
    inv H0. auto. intro. apply in_app_iff. left; auto.
    intro. apply in_app_iff in H2 as [H2|H2]. auto. inv H2.
  Qed.

  Lemma heap_ctx_split (h h' : list X) : h ##ₘ h' -> (⊢heap_ctx (h \u h') -∗ heap_ctx h ∗ heap_ctx h').
  Proof.
    MonPred.unseal. split. MonPred.unseal. repeat red. intros. destruct a. destruct i. clear H1.
    inv H0. exists emp, ∅, ∅. repeat split; eauto with list_scope. intros l P0.
    inversion_star h P. clear P0. inv P1. red in P2. subst.
    exists h; exists h'. repeat split; eauto with list_scope.
    + intro. apply P in H0. apply in_empty_l; auto.
    + intro. apply P. apply in_empty_l; auto.
  Qed.

End hprop.

Notation "'heap_empty'" := (∅).

Notation "'\[]'" := (hempty) (at level 0).

Notation "\[ P ]" := (hpure P) (at level 0, P at level 99, format "\[ P ]").

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

Notation "\Top" := htop.

Declare Scope heap_scope.

Ltac inversion_star h P :=
  match goal with
  | H : (_ \* _) _ |- _ =>
    let W := fresh h in
    let w := fresh P in
    inversion H as (W&w);
    let W := fresh h in
    destruct w as (W&w);
    do 3 (let w0 := fresh P in
          destruct w as (w0&w))
  end.

Open Scope bi_scope.

Definition IsFresh {type} l : monPred biInd (@hpropList type) := single l.

Notation "\⌜ P ⌝" := (pure_empty P)
                       (at level 0, P at level 99, format "\⌜ P ⌝").
