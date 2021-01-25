Require Import FunctionalExtensionality.

From iris Require Export bi.bi proofmode.tactics proofmode.monpred.

Axiom prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.
Definition pred_incl {A} (P Q : A -> Prop) := forall x, P x -> Q x.

Definition pred_impl {A} (P Q : A -> Prop) := fun x => P x -> Q x.

Notation "P ==> Q" := (pred_incl P Q).

Section hprop.

  (* Operators *)
  Definition hprop := Prop.

  Definition hand (H1 H2:hprop):hprop := H1 /\ H2.

  Definition hor (H1 H2:hprop) : hprop := H1 \/ H2.

  Definition hempty : hprop := True.

  Definition hsingle : hprop := True.

  Definition hstar := hand.

  Definition hexists {A} (J : A -> hprop) : hprop :=
    exists x, J x.

  Definition hpure (P:Prop) : hprop := P.

  Definition htop : hprop := True.

  Definition hforall {A} (f : A -> hprop) : hprop := forall a, f a.

  Definition hwand (H1 H2 : hprop) : hprop := H1 -> H2.

  Definition hpure_abs (P : Prop) : hprop := P.

  Lemma hempty_intro : hempty.
  Proof. reflexivity. Qed.

  Local Notation "'heap_empty'" := (∅).

  Local Notation "h1 \u h2" := (h1 ∪ h2) (at level 37, right associativity).

  Local Notation "'Hexists' x1 , H" := (hexists (fun x1 => H))
                                         (at level 39, x1 name, H at level 50).
  Local Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
                                            (at level 39, x1 name, x2 name, H at level 50).
  Local Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
                                               (at level 39, x1 name, x2 name, x3 name, H at level 50).

  Local Notation "'\[]'" := (hempty)
                              (at level 0).

  Local Notation "\[ P ]" := (hpure P)
                               (at level 0, P at level 99, format "\[ P ]").

  Local Notation "H1 '\*' H2" := (hstar H1 H2)
                                   (at level 41, right associativity).

  Local Notation "\Top" := htop.


  Declare Scope heap_scope.

  Ltac extens := apply prop_extensionality.

  Section Properties.

    Lemma hstar_comm : forall H1 H2,
      H1 \* H2 = H2 \* H1.
    Proof using.
      intros H1 H2. extens.
      split; intro; destruct H; split; auto.
    Qed.

    Lemma hstar_assoc : forall H1 H2 H3,
        (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
    Proof.
      intros H1 H2 H3. extens. split.
      intros [[P0 P1] P2]. repeat split; auto.
      intros [P0 [P1 P2]]. repeat split; auto.
    Qed.

  End Properties.

  Definition hpersistent (H:hprop) : hprop := H.

  Definition hlater (H : hprop) := H.

  Set Warnings "-redundant-canonical-projection -convert_concl_no_check".
  Canonical Structure hpropO := leibnizO hprop.

  Program Canonical Structure hpropProp : bi :=
    Bi hprop _ _ impl hempty hpure_abs hand hor
       impl (@hforall) (@hexists) hstar hwand hpersistent hlater _ _ _ _.
  Next Obligation.
    repeat split; unfold impl; intros; eauto.
    - rewrite H in H0. auto.
    - rewrite H. auto.
    - rewrite leibniz_equiv_iff. destruct H. extens. split; intro; auto.
    - intros P0 P1 equiv. extens. unfold hpure_abs. auto.
    - intros A P0 P1 equiv y P2. unfold hand. rewrite P1. rewrite P2. reflexivity.
    - intros A P0 P1 equiv y P2. rewrite P1. rewrite P2. reflexivity.
    - intros l0 P0 P1. repeat red. intros. rewrite H. rewrite P1. reflexivity.
    - intros l P0 P1. repeat red in P1. repeat red. unfold hforall. extens.
      split; intros. rewrite <- P1. auto. rewrite P1. auto.
    - intros l P0 P1. repeat red in P1. repeat red. unfold hexists. extens.
      split; intros [x P]; exists x. rewrite <- P1. auto. rewrite P1. auto.
    - intros l P0 P1 P2 y P3. rewrite P1. rewrite P3. auto.
    - intros l P0 P1 P2 y P3. rewrite P1. rewrite P3. auto.
    - intros l P0 P1. rewrite P1. auto.
    - apply H; auto. red. trivial.
    - destruct H. auto.
    - destruct H. auto.
    - left. auto.
    - right. auto.
    - destruct H1; tauto.
    - apply H. split; auto.
    - destruct H0. tauto.
    - unfold hforall. intro. auto.
    - exists a. auto.
    - destruct H0. eapply H. eauto.
    - unfold impl in *. unfold hstar in *. destruct H1. tauto.
    - destruct H1. unfold impl in *. tauto.
    - destruct H. auto.
    -  destruct H. auto.
    - destruct H. auto.
    - do 2 destruct H. auto.
    - do 2 destruct H. auto.
    - do 2 destruct H. auto.
    - intro. unfold hstar in H. unfold hand in H. tauto.
    - destruct H0. apply H; tauto.
    - unfold hpersistent in *. tauto.
    - unfold hpersistent in *. destruct H. tauto.
    - destruct H. apply H.
    - destruct H. auto.
  Qed.
  Next Obligation.
    repeat split; try(solve_proper); eauto.
    - intros A Φ. rewrite /hlater. auto.
    - intros A Φ h a. apply h.
    - intros Hp h P. right. destruct P. exists x; auto.
    - destruct H. auto.
    - destruct H. auto.
    - destruct H. auto.
    - destruct H. auto.
    - intros P0 P1. right. intro. auto.
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

  Lemma emp_trivial : ⊢ (emp : monPred biInd hpropProp). Proof. simpl. auto. Qed.

  Lemma soundness1 (Φ : Prop) : (⊢ ⌜ Φ ⌝ : monPred biInd hpropProp) -> Φ.
  Proof.
    MonPred.unseal=> -[H]. repeat red in H. eapply (H tt).
    MonPred.unseal. repeat red. trivial.
  Qed.

  Lemma soundness2 (Φ : monPred biInd hpropProp) : (⊢ Φ) -> Φ ().
  Proof.
    intros. apply H. MonPred.unseal. repeat red. trivial.
  Qed.

  Lemma soundness3 (Φ : monPred biInd hpropProp) : Φ () -> (⊢Φ).
  Proof.
    split. MonPred.unseal. intros i P0. destruct i. auto.
  Qed.

End hprop.
