From iris.proofmode Require Export base intro_patterns spec_patterns
     sel_patterns coq_tactics reduction
     coq_tactics ltac_tactics.
Require Import FunctionalExtensionality.
From iris Require Export bi.bi proofmode.tactics proofmode.monpred proofmode.reduction.
From stdpp Require Export pmap.

Axiom prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.
Global Set Warnings "-convert_concl_no_check".

Definition pred_incl {A} (P Q : A -> Prop) :=
  forall x, P x -> Q x.

Definition pred_impl {A} (P Q : A -> Prop) :=
  fun x => P x -> Q x.

Notation "P ==> Q" := (pred_incl P Q).

Module SepBasicCore.
  Export monpred.
  Section hprop.
    Context {type : Type}.
    Definition heap : Type := Pmap type.

    (* Properties on heap *)
    Instance heap_union_empty_l : LeftId (=@{heap}) ∅ (∪) := _.
    Instance heap_union_empty_r : RightId (=@{heap}) ∅ (∪) := _.
    Instance heap_union_assoc : base.Assoc (=@{heap}) (∪).
    Proof.
      intros m1 m2 m3. unfold base.union, map_union, union_with, map_union_with.
      apply (merge_assoc _). intros i.
      unfold heap in m1. unfold heap in m2. unfold heap in m3.
        by destruct (m1 !! i), (m2 !! i), (m3 !! i).
    Qed.

    Definition heap_union_comm (h1 h2 : heap) := map_union_comm h1 h2.

    Lemma heap_disjoint_union_l_l : forall (h1 h2 h3 :heap) , h1 ∪ h2 ##ₘ h3 -> h1 ##ₘ h3.
    Proof.
      intros. apply map_disjoint_union_l in H as (P0&P1). assumption.
    Qed.

    Lemma heap_disjoint_union_l_r : forall (h1 h2 h3 :heap) , h1 ∪ h2 ##ₘ h3 -> h2 ##ₘ h3.
    Proof.
      intros. apply map_disjoint_union_l in H as (P0&P1). assumption.
    Qed.

    Lemma heap_disjoint_union_r_r : forall (h1 h2 h3 :heap) , h1 ##ₘ h2 ∪ h3 -> h1 ##ₘ h3.
    Proof.
      intros. apply map_disjoint_union_r in H as (P0&P1). assumption.
    Qed.

    Lemma heap_disjoint_union_r_l : forall (h1 h2 h3 :heap) , h1 ##ₘ h2 ∪ h3 -> h1 ##ₘ h2.
    Proof.
      intros. apply map_disjoint_union_r in H as (P0&P1). assumption.
    Qed.

    (* Operators *)

    Definition hprop := heap -> Prop.

    Definition hand (H1 H2:hprop):hprop :=
      fun h => H1 h /\ H2 h.

    Definition hor (H1 H2:hprop) : hprop := fun h => H1 h \/ H2 h.

    Definition hempty : hprop :=
      fun h => h = ∅.

    Definition hsingle loc t : hprop :=
      fun h =>  h = {[loc := t]}.

    Definition hheap_ctx (ctx : heap) : hprop := fun h => h = ctx.

    Definition hstar (H1 H2 : hprop) : hprop :=
      fun h => exists h1 h2, H1 h1
                     /\ H2 h2
                     /\ (h1 ##ₘ h2)
                     /\ h = h1 ∪ h2.

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

    Definition hpure_abs (φ : Prop) : hprop := hstar (hpure φ) htop.


    Lemma hempty_intro : hempty ∅.
    Proof using. reflexivity. Qed.

    Lemma hempty_inv : forall h, hempty h -> h = ∅.
    Proof using. auto. Qed.

    Local Notation "'heap_empty'" := (∅ : heap).

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

    Hint Resolve heap_union_empty_l heap_union_empty_r hempty_intro map_disjoint_empty_l map_disjoint_empty_r heap_union_assoc heap_disjoint_union_r_l heap_disjoint_union_l_l heap_disjoint_union_r_r heap_disjoint_union_l_r : heap_scope.

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

      Lemma hstar_intro : forall (H1 H2 :hprop) h1 h2,
        H1 h1 ->
        H2 h2 ->
        h1 ##ₘ h2 ->
        (H1 \* H2) (h1 ∪ h2).
      Proof using. intros. exists h1; exists h2. auto. Qed.

      Lemma hstar_hempty_l : forall H,
          hempty \* H = H.
      Proof using.
        intros. extens.
        split; intro.
        - inversion_star h P. inversion P0; subst. rewrite heap_union_empty_l. assumption.
        - exists heap_empty; exists x. repeat split; auto with heap_scope. apply map_disjoint_empty_l.
      Qed.

      Lemma hstar_comm : forall H1 H2,
          H1 \* H2 = H2 \* H1.
      Proof using.
        intros H1 H2. extens.
        split; intro P; inversion_star h P; exists h0; exists h; repeat split; auto;
          rewrite heap_union_comm; auto.
      Qed.

      Lemma hstar_assoc : forall H1 H2 H3,
          (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
      Proof using.
        intros H1 H2 H3. extens. split.
        { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
          exists h1; exists (h2 ∪ h3). repeat split; auto.
          { exists h2; exists h3; eauto with heap_scope. }
          { apply map_disjoint_union_l in D as (P0&P1).
            apply map_disjoint_union_r. split; auto. }
          { by rewrite heap_union_assoc. }}
        { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
          exists (h1 ∪ h2); exists h3. repeat split; auto.
          { exists h1; exists h2; eauto with heap_scope. }
          { rewrite map_disjoint_union_l. split; auto.
            apply map_disjoint_union_r in D as (P0&P1).
            assumption. }
            by rewrite <- heap_union_assoc. }
      Qed.

      Lemma hstar_hexists : forall A (J:A->hprop) H,
          (hexists J) \* H = hexists (fun x => (J x) \* H).
      Proof using.
        intros. extens. split; intro M.
        { destruct M as (h1&h2&(h3&M1)&M2&D&U). exists h3; exists h1; exists h2; eauto. }
        { destruct M as (h3&(h1&h2&M1&M2&D&U)). exists h1; exists h2. split; eauto. by exists h3. }
      Qed.

      Lemma himpl_frame_l : forall H2 H1 H1',
          H1 ==> H1' ->
          (H1 \* H2) ==> (H1' \* H2).
      Proof using. intros. intros h P. inversion_star h P. exists h0; exists h1. split; eauto. Qed.

    End Properties.

    Definition hpersistent (H:hprop) : hprop := fun h => H heap_empty.

    Set Warnings "-redundant-canonical-projection".
    Canonical Structure hpropO := leibnizO hprop.

    Definition hprop_emp := hpure True.

    Program Canonical Structure hpropI : bi :=
      Bi hprop _ _ pred_incl hprop_emp hpure_abs hand hor
         pred_impl (@hforall) (@hexists) hstar hwand hpersistent _ _.
    Next Obligation.
      apply discrete_ofe_mixin, _.
    Qed.
    Next Obligation.
      repeat split; try(solve_proper); eauto.
      - intros H h P. assumption.
      - rewrite /Transitive. intros. intros h P. eauto.
      - rewrite leibniz_equiv_iff. intros (P0&P1). extens. split; intro; auto.
      - intros X Y Z. rewrite /hpure_abs. repeat red. intro. extens.
        split; intro; inversion_star h P; exists h; exists h0; repeat split; auto; inversion P0; inversion H2;
          auto with heap_scope; apply H; assumption.
      - intros X Y Z. rewrite /hforall. repeat red. intros. extens. split; intros; repeat red in H;
                                                                      apply functional_extensionality in H; subst; auto.
      - intros X Y Z. rewrite /hexists. repeat red. intros. extens.
        split; intro; repeat red in H; apply functional_extensionality in H; subst; auto.
      - rewrite /hpure_abs. intros φ P. exists heap_empty. exists x. repeat split; auto with heap_scope.
        apply map_disjoint_empty_l.
      - unfold hpure_abs in *. intros x W P h P0. inversion_star h P. inversion P2. apply P; auto.
        exists h0; exists h1. repeat split; auto.
      - rewrite /hforall /hpure_abs. intros h W h0 P. exists heap_empty; exists h0.
        repeat split; auto with heap_scope.
        + intro a. pose (P a). inversion_star h P. inversion P1. apply H.
        + apply map_disjoint_empty_l.
      - rewrite /hand. intros P Q h (P0&P1). apply P0.
      - rewrite /hand. intros P Q h (P0&P1). apply P1.
      - rewrite /hor. intros P Q h P0. auto.
      - rewrite /hor. intros P Q h P0. auto.
      - rewrite /hor. intros P Q h P0 P1 h0 P2. destruct P2; auto.
      - intros x W X H h P x0. apply H. split; auto.
      - intros x W X H h P. destruct P. apply H in H0. apply H0 in H1. assumption.
      - intros x W a H h P h0. apply H. apply P.
      - intros h Q a H H0. apply H0.
      - intros x W H P Q. exists H. apply Q.
      - intros x W Q P h P0. destruct P0. eapply P. apply H.
      - intros P P' Q Q' A B C D. inversion_star h P. exists h; exists h0. repeat split; auto.
      - intros x W A. exists heap_empty; exists W. repeat split; auto with heap_scope.
        apply map_disjoint_empty_l.
      - intros P h Q. inversion_star H H. inversion H3; inversion H6; subst.
        rewrite heap_union_empty_l. apply H4.
      - intros P Q h R. inversion_star H H. exists H2; exists H0. repeat split; auto. subst.
        apply heap_union_comm. apply H5.
      - intros P Q R h P0. rewrite <- hstar_assoc. apply P0.
      - intros P Q R P0 h P1. exists P. exists h; exists heap_empty. repeat split; auto with heap_scope.
        apply map_disjoint_empty_r.
      - intros P Q R W h P0. inversion_star h P. apply W in P2. destruct P2. inversion_star h H.
        inversion H2. apply H4. exists h2; exists h1. repeat split; auto; subst.
        + apply heap_disjoint_union_l_l in P4. apply P4.
        + inversion H5. subst. rewrite heap_union_empty_r. reflexivity.
      - rewrite /hpersistent. intros P Q H h P0. apply H. apply P0.
      - rewrite /hpersistent. rewrite /hforall. intros A B C D E. apply D.
      - rewrite /hpersistent. intros P Q h P0. inversion_star h P. apply P2.
      - intros P Q x W. destruct W. exists heap_empty; exists x. repeat split; auto with heap_scope.
        apply map_disjoint_empty_l.
    Qed.


    Lemma hpure_pure φ : \[φ] = bi_affinely ⌜φ⌝.
    Proof.
      extens. split.
      - intro. destruct H. split. split; auto. exists heap_empty; exists x. repeat split; auto with heap_scope.
        apply map_disjoint_empty_l.
      - intros [? Hφ]. destruct Hφ as (h1&h2&P0&P1&P2&P3). destruct P0. repeat split; auto.
        inversion H. apply H3.
    Qed.

    Lemma htop_True : \Top = True%I.
    Proof.
      extens. split.
      - exists heap_empty; exists x. repeat split; auto with heap_scope. apply map_disjoint_empty_l.
      - red; trivial.
    Qed.

    Opaque hpure_abs.

    (** * Specific Proofmode instances about hpure and htop. *)

    Global Instance htop_absorbing : Absorbing \Top.
    Proof. intros ??. red; trivial. Qed.
    Global Instance htop_persistent : Persistent \Top.
    Proof. intros ??. repeat red. trivial. Qed.

    Global Instance htop_into_pure : IntoPure \Top True.
    Proof.
      unfold IntoPure. intros h H. exists ∅, h. repeat split; auto with heap_scope.
      apply map_disjoint_empty_l.
    Qed.
    Global Instance htop_from_pure a : FromPure a \Top True.
    Proof. intros ??. red; trivial. Qed.

    Global Instance hpure_affine φ : Affine \[φ].
    Proof. rewrite hpure_pure. apply _. Qed.
    Global Instance hpure_persistent φ : Persistent \[φ].
    Proof. rewrite hpure_pure. apply _. Qed.

    Global Instance hpure_into_pure φ : IntoPure \[φ] φ.
    Proof. rewrite hpure_pure /IntoPure. intros h H. destruct H. auto. Qed.
    Global Instance hpure_from_pure φ : FromPure true \[φ] φ.
    Proof. by rewrite hpure_pure /FromPure /= /bi_affinely stdpp.base.comm. Qed.

    Global Instance from_and_hpure φ ψ : FromAnd \[φ ∧ ψ] \[φ] \[ψ].
    Proof.
      rewrite /FromAnd. intros h H. destruct H. inversion H. inversion H0. repeat eexists; auto.
    Qed.
    Global Instance from_sep_hpure φ ψ : FromSep \[φ ∧ ψ] \[φ] \[ψ].
    Proof.
      rewrite /FromSep. intros h H. red in H. inversion_star h P.
      inversion P0. inversion P1. inversion H1. inversion H3. subst. rewrite heap_union_empty_l.
      repeat eexists; auto.
    Qed.



    Global Instance into_and_hpure (p : bool) φ ψ : IntoAnd p \[φ ∧ ψ] \[φ] \[ψ].
    Proof. rewrite /IntoAnd. f_equiv. auto. Qed.
    Global Instance into_sep_hpure φ ψ : IntoSep \[φ ∧ ψ] \[φ] \[ψ].
    Proof. rewrite /IntoSep. auto. Qed.
    Global Instance from_or_hpure φ ψ : FromOr \[φ ∨ ψ] \[φ] \[ψ].
    Proof. rewrite /FromOr. auto. Qed.
    Global Instance into_or_hpure φ ψ : IntoOr \[φ ∨ ψ] \[φ] \[ψ].
    Proof. rewrite /IntoOr. auto. Qed.
    Global Instance from_exist_hpure {A} (φ : A → Prop) :
      FromExist \[∃ x : A, φ x] (λ a : A, \[φ a]).
    Proof. rewrite /FromExist. auto. Qed.
    Global Instance into_exist_hpure {A} (φ : A → Prop) :
      IntoExist \[∃ x : A, φ x] (λ a : A, \[φ a]).
    Proof. rewrite /IntoExist. auto. Qed.
    Global Instance from_forall_hpure {A : Type} `{Inhabited A} (φ : A → Prop) :
      FromForall \[∀ a : A, φ a] (λ a : A, \[φ a]).
    Proof. rewrite /FromForall. auto. Qed.
    Global Instance frame_here_hpure p (φ : Prop) Q :
      FromPure true Q φ → Frame p \[φ] Q emp.
    Proof.
      rewrite /FromPure /Frame=><- /=. destruct p=>/=; iIntros "[% _] !%"; auto.
    Qed.

    (** Instance affine *)

    Global Instance from_affinely_affine P : Affine P → @FromAffinely hpropI P P.
    Proof. intros. rewrite /FromAffinely. iIntros "HA". iApply "HA". Qed.
    Global Instance from_affinely_default P : @FromAffinely hpropI (<affine> P) P | 100.
    Proof. by rewrite /FromAffinely. Qed.
    Global Instance from_affinely_intuitionistically P : @FromAffinely hpropI (□ P) (<pers> P) | 100.
    Proof. by rewrite /FromAffinely. Qed.

    (** Instance Sep *)

    Global Instance from_sep_sep P1 P2 : @FromSep hpropI (P1 ∗ P2) P1 P2 | 100.
    Proof. by rewrite /FromSep. Qed.

    Global Instance into_sep_sep P Q : @IntoSep hpropI (P ∗ Q) P Q.
    Proof. by rewrite /IntoSep. Qed.

    (** Instance Wand *)

    Global Instance from_wand_wand P1 P2 : @FromWand hpropI (P1 -∗ P2) P1 P2.
    Proof. by rewrite /FromWand. Qed.


    Instance inhabited_unit : Inhabited unit.
    Proof.
      split. apply ().
    Qed.

    Instance PreOrder_unit : PreOrder (fun (t1 t2 : unit) => t1 = t2).
    Proof.
      split; repeat red; intros; trivial. destruct x,y,z. reflexivity.
    Qed.

    Program Canonical Structure biInd := BiIndex unit inhabited_unit _ PreOrder_unit.

    Definition single (l : positive) (t : type) : monPred biInd hpropI := MonPred (fun _ => hsingle l t) _.

    Definition heap_ctx (h : heap) : monPred biInd hpropI := MonPred (fun _ => hheap_ctx h) _.

    Ltac inv H := inversion H; clear H; subst.

    Local Open Scope bi_scope.
    Local Notation "l ↦ t" :=
      (single l t) (at level 20) : bi_scope.

    Local Notation "\s l" :=
      (∃ t, l ↦ t) (at level 10) : bi_scope.

    Lemma singleton_false : forall t, ⊢ \s t -∗ \s t -∗ False.
    Proof.
      MonPred.unseal. split. MonPred.unseal. repeat red. intros. destruct i. destruct a. clear H0.
      inv H. inv H1. clear H0. exists emp, heap_empty, heap_empty. repeat split; auto with heap_scope.
      intros h H j C. clear C. clear j. inversion_star h P. clear H. inv P0. inv H0. clear H. clear P2.
      destruct P1. red in H. rewrite heap_union_empty_l. exists (hheap_ctx h1), h1, heap_empty.
      repeat split; eauto with heap_scope. subst. intros h H. inversion_star h P. destruct P1.
      red in H0. red in P0. subst. clear H. erewrite map_disjoint_spec in P2.
      edestruct P2; eapply lookup_singleton_Some; eauto.
      apply map_disjoint_empty_r.
    Qed.


    Definition pure_empty (P : Prop) : monPred biInd hpropI := <affine> ⌜P⌝.

    Local Notation "\⌜ P ⌝" := (pure_empty P)
                                 (at level 0, P at level 99, format "\⌜ P ⌝").

    Global Instance affine_pure (P : Prop) : Affine (pure_empty P).
    Proof.
      red. iIntros "HA". trivial.
    Qed.

    Lemma pureIntro {X} P : ∀ (a b : X), P a ⊢ pure_empty (a = b) -∗ P b.
    Proof.
      iIntros (a b) "HA %". rewrite a0. iApply "HA".
    Qed.


    Lemma pure_empty_destruct : forall P Q, ⊢ \⌜ P /\ Q ⌝ -∗ \⌜ P ⌝ ∗ \⌜ Q ⌝ .
    Proof. iIntros. destruct a. iSplit; iPureIntro; auto. Qed.


    Global Instance affine_heap_empty : Affine (heap_ctx ∅).
    Proof.
      split. intro. MonPred.unseal. repeat red. intros. split; auto.
    Qed.

    Lemma init_heap : ⊢ heap_ctx ∅.
    Proof.
      split. MonPred.unseal. repeat red. intros. inversion H. inversion H1. reflexivity.
    Qed.

    Lemma instance_heap : forall (P : monPred biInd hpropI) (Q : Prop), (forall tmps, P () tmps -> Q) -> (P ⊢ ⌜Q⌝).
    Proof.
      MonPred.unseal. intros. split. repeat red. intros.
      exists ∅, x. repeat split; auto. destruct i. eapply H. eauto.
      apply map_disjoint_empty_l. rewrite heap_union_empty_l. reflexivity.
    Qed.

    Lemma soundness1 h (Φ : Prop) : (heap_ctx h ⊢ (⌜ Φ ⌝) : monPred biInd hpropI) -> Φ.
    Proof.
      MonPred.unseal=> -[H]. repeat red in H.
      pose (e := H () h).
      edestruct e as (h1&h2&P0&P1&P2&P3).
      - reflexivity.
      - inversion P0. apply H0.
    Qed.

    Lemma soundness2 (Φ : monPred biInd hpropI) h : (⊢heap_ctx h -∗ Φ) -> Φ () h.
    Proof.
      MonPred.unseal=> -[H]. repeat red in H.
      pose (e := H () ∅).
      simpl in *. edestruct e.
      - rewrite monPred_at_emp. split; auto; apply hempty_intro.
      - repeat red. exists ∅. exists ∅. repeat split; auto. rewrite heap_union_empty_l. auto.
      - inversion_star h P.
        inversion P1.
        apply H1.
        exists heap_empty; exists h.
        inversion H2; subst. rewrite heap_union_empty_r in P; subst.
        repeat split; auto. apply map_disjoint_empty_l. rewrite heap_union_empty_l. auto.
    Qed.

    Lemma soundness3 (Φ : monPred biInd hpropI) h : Φ () h -> (⊢heap_ctx h -∗ Φ).
    Proof.
      MonPred.unseal. unfold monPred_wand_def. unfold monPred_upclosed. simpl. split.
      intros. simpl. repeat red. intros. exists emp. exists x; exists heap_empty.
      repeat split; auto with heap_scope. rewrite monPred_at_emp in H0. apply H0.
      intros h0 P0. inversion_star h P. simpl in *. rewrite <- P2 in *. inversion P1. inversion H3.
      subst. rewrite heap_union_empty_l. rewrite <- P2. destruct a. apply H.
      apply map_disjoint_empty_r.
    Qed.

    Lemma heap_ctx_split (h h' : heap) : h ##ₘ h' -> (⊢heap_ctx (h \u h') -∗ heap_ctx h ∗ heap_ctx h').
    Proof.
      intro.
      MonPred.unseal. repeat red.
      unfold monPred_wand_def.
      unfold monPred_sep_def.
      unfold monPred_upclosed. split. simpl.
      intro. intro P. intro. repeat red. exists hempty. rewrite monPred_at_emp in H0.
      inversion H0; subst.
      exists heap_empty; exists heap_empty. repeat split; auto.
      + repeat intro. inversion_star h P. inversion P1. subst.
        exists h; exists h'. repeat split; auto. inversion P2; subst.
        rewrite heap_union_empty_l. reflexivity.
      + inversion H3. rewrite heap_union_empty_l. reflexivity.
    Qed.

    Lemma heap_ctx_split_sing (h : heap) l t : h ##ₘ ({[l := t]}) ->
                                                (⊢heap_ctx (<[l := t]>h) -∗ heap_ctx h ∗ l ↦ t).
    Proof.
      iIntros (?) "HA". rewrite insert_union_singleton_r; auto. iApply heap_ctx_split; auto.
      rewrite <- map_disjoint_singleton_r. eauto.
    Qed.

  End hprop.

  Notation "'heap_empty'" := (∅ : heap).

  Notation "h1 \u h2" := (h1 ∪ h2) (at level 37, right associativity).

  Notation "'Hexists' x1 , H" := (hexists (fun x1 => H))
                                   (at level 39, x1 ident, H at level 50).
  Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
                                      (at level 39, x1 ident, x2 ident, H at level 50).
  Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
                                         (at level 39, x1 ident, x2 ident, x3 ident, H at level 50).

  Notation "'\[]'" := (hempty) (at level 0).

  Notation "\[ P ]" := (hpure P) (at level 0, P at level 99, format "\[ P ]").

  Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

  Notation "\Top" := htop.

  Declare Scope heap_scope.

  Hint Resolve heap_union_empty_l heap_union_empty_r hempty_intro map_disjoint_empty_l map_disjoint_empty_r heap_union_assoc heap_disjoint_union_r_l heap_disjoint_union_l_l heap_disjoint_union_r_r heap_disjoint_union_l_r : heap_scope.

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

  Notation "l ↦ t" :=
    (single l t) (at level 20) : bi_scope.

  Notation "'IsFresh' l" :=
    (∃ t, l ↦ t) (at level 10) : bi_scope.

  Notation "\⌜ P ⌝" := (pure_empty P)
                         (at level 0, P at level 99, format "\⌜ P ⌝").

  Local Ltac Fresh :=
    let x := iFresh in
    match x with
    | IAnon ?x =>
      let x := eval compute in (ascii_of_pos (x + 64)) in
          let x := eval compute in (append "H" (string_of_list_ascii [x])) in
              let env := iGetCtx in
              let P := reduction.pm_eval (envs_lookup x env) in
              match P with
              | None => x
              | Some _ => Fresh
              end
    | _ => fail "iFresh returns " x " sometimes."
    end.

  (*h should be in the environment *)
  Local Ltac norm h :=
    let env := iGetCtx in
    let P := reduction.pm_eval (envs_lookup h env) in
    match P with
    | None => fail "assert false"
    | Some (false, ?P) =>
      match P with
      | bi_exist ?Q => let x := fresh "x" in (iDestruct h as (x) h; norm h)
      | bi_sep ?Q ?W =>
        let x := Fresh in
        let y := Fresh in
        eapply tac_and_destruct with h _ x y _ _ _;
        [ pm_reflexivity | pm_reduce; iSolveTC | pm_reduce; norm x; norm y]
      | pure_empty (and ?P ?Q) =>
        let x := Fresh in
        iPoseProof (pure_empty_destruct with h) as x; norm x
      | pure_empty _ => iPure h as ?
      | bi_pure (and ?P ?Q) =>
        let x := Fresh in
        eapply tac_and_destruct with h _ h x _ _ _;
        [pm_reflexivity
        |pm_reduce; iSolveTC
        |pm_reduce; norm h; norm x]
      | bi_pure _ => iPure h as ?
      | bi_wand _ _ => iDestruct (h with "[]") as h; [progress auto | norm h]
      | bi_absorbingly _ =>
        let name := Fresh in
        let name_mod := eval compute in (append ">" name) in
            iPoseProof h as name; iDestruct name as name_mod; norm name
      | _ =>
        match h with
        | IAnon _ =>
          let x := Fresh in
          iPoseProof h as x
        | _ => idtac
        end
      end
    | Some (true,?P) => idtac
    end.

  (* (List.fold norm) in Ltac *)
  Local Ltac norm_list l :=
    match l with
    | [] => idtac
    | ?h :: ?t => norm h ; norm_list t
    end.

  (* List.fold norm list_ident idtac *)
  Ltac norm_all :=
    iStartProof;
    let env := iGetCtx in
    let list_ident := eval compute in (rev (envs_dom env)) in
        norm_list list_ident; auto.

  Tactic Notation "iNorm" := norm_all.

  (* Context {type : Type}. *)
  (* Lemma test : forall P Q (R T: monPred biInd (@hpropI type)), *)
  (*     ⊢  <absorb> (T ∗ R) -∗ (∃ (x: nat), (True -∗ T)) -∗ ⌜ P /\ Q ⌝ -∗ ((⌜ P ⌝ -∗ R) ∗ True) -∗ <absorb> R. *)
  (* Proof. iIntros. destruct a. iNorm. Qed. *)


End SepBasicCore.

Require Import Ctypes.

Module gensym.
  Import Errors.
  Export SepBasicCore.
  
  Definition ident := positive.
  
  Record state := mk_state { state_heap : @heap type;
                                 next : ident
                               }.   

  Definition wf_state s := forall p, (∃ v, state_heap s !! p = Some v) -> Pos.lt p (next s).
 
  Definition initial_state : state := mk_state ∅ 1%positive.

  Lemma wf_init : wf_state initial_state.
  Proof.
    unfold wf_state. intros. destruct H. rewrite lookup_empty in H. inversion H.
  Qed.
  
  Inductive mon (X : Type) : Type :=
  | ret : X -> mon X
  | Err : Errors.errmsg -> mon X
  | Gensym : type -> (ident -> mon X) -> mon X.

  Arguments Err [X].
  Arguments Gensym [X].
  Arguments ret {_} x.
  

  Fixpoint bind {X Y} (m : mon X) (f : X -> mon Y) : mon Y :=
    match m with
    | ret x => f x
    | Err e => Err e
    | Gensym t g => Gensym t (fun x => bind (g x) f)
    end.

  Notation "'let!' x ':=' e1 'in' e2" := (bind e1 (fun x => e2))
                                           (x ident, at level 90).

  Notation "'ret!' v" := (ret v)
                           (v ident, at level 90).

  Definition error {X} (e : Errors.errmsg) : mon X := Err e.
  Definition gensym (t : type) : mon ident := Gensym t ret.

  Lemma lid : forall X Y (a : X) (f : X -> mon Y), bind (ret a) f = f a.
  Proof. auto. Qed.

  Lemma rid : forall X (m : mon X), bind m ret = m.
  Proof.
    fix m 2.
    destruct m0.
    * reflexivity.
    * reflexivity.
    * simpl. do 2 f_equal. apply functional_extensionality. intro. apply m.
  Qed.

  Lemma ass_bind : forall X Y Z (m : mon X) f (g : Y -> mon Z),
      bind (bind m f) g = bind m (fun x => bind (f x) g).
  Proof.
    fix m 4.
    destruct m0; intros.
    * reflexivity.
    * reflexivity.
    * simpl. do 2 f_equal. apply functional_extensionality. intro. apply m.
  Qed.

  Definition fresh (ty : type) (s: state) : ident * state :=
    let h := state_heap s in
    let n := next s in
    (n, mk_state (<[n:=ty]>h) (Pos.succ n)).

  Fixpoint run {X} (m : mon X) : state -> res (state * X) :=
    match m with
    | ret v => fun s => OK (s, v)
    | Err e => fun s => Error e
    | Gensym t f =>
      fun s =>
        let (i,s') := fresh t s in
        run (f i) s'
    end.
  
  Lemma run_stay_fresh : forall {X} (m : mon X) s s' v,
      wf_state s ->
      run m s = OK (s',v) ->
      (state_heap s') !! (next s') = None.
  Proof.
    induction m; intros.
    - inversion H0. subst. destruct (state_heap s' !! next s') eqn:?.
      assert (Pos.lt (next s') (next s')). apply H; eauto. lia. reflexivity.
    - inversion H0.
    - simpl in H1. eapply H. 2 : eauto. unfold wf_state in *. simpl in *. intros.
      destruct H2. destruct (Pos.eq_dec p (next s)). lia.
      rewrite lookup_insert_ne in H2; auto.
      assert (Pos.lt p (next s)). apply H0; eauto. lia.
  Qed.

  Lemma fresh_is_fresh : forall (s : state), wf_state s -> (state_heap s) !! (next s) = None.
  Proof.
    unfold wf_state. 
    intros. destruct ((state_heap s) !! (next s)) eqn:?; auto.
    assert (Pos.lt (next s) (next s)). apply H. eauto. lia.
  Qed.

End gensym.


Module weakestpre_gensym.
  Export gensym.
  Export proofmode.monpred.
  Export SepBasicCore.
  Import reduction.

  Definition iProp := monPred biInd (@hpropI type).
  
  Fixpoint wp {X} (e1 : mon X) (Q : X -> iProp) : iProp :=
    match e1 with
    | ret v => Q v
    | Err e => True
    | Gensym _ f =>
      ∀ l, IsFresh l -∗ wp (f l) Q
    end.

  Notation "'{{' P } } e {{ v ; Q } }" := (P -∗ wp e (fun v => Q))
                                            (at level 20,
                                             format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").

(** triple rules *)
  (** Generic rules *)
Lemma wp_bind {X Y} (e : mon X) (f :  X → mon Y) (Q : Y -> iProp)  (Q' : X -> iProp) :
  wp e Q' ⊢ (∀ v,  Q' v -∗ wp (f v) Q ) -∗ wp (bind e f) Q %I.
Proof.
  iIntros "HA HB". revert e. fix e 1.
  destruct e0.
  - iApply "HB". iApply "HA".
  - simpl. auto.
  - simpl. iIntros (l) "HC".
      iDestruct ("HA" with "HC") as "HA".
      iPoseProof "HB" as "HB". apply e.
Qed.

Lemma wp_consequence : forall {X} (P Q : X -> iProp) (f : mon X),
    ⊢ wp f P -∗
      (∀ x, P x -∗ Q x) -∗
      wp f Q.
Proof.
  induction f; simpl; intros; auto.
  - iIntros "HA HB". iApply ("HB" with "HA").
  - iIntros "HA * HB * HC". iApply (H with "[HA HC] HB"). iApply ("HA" with "HC").
Qed.

  
Lemma ret_spec {X} (v : X) H (Q : X -> iProp) :
  (H ⊢ Q v) -> ⊢{{ H }} ret v {{ v'; Q v' }}.
Proof. simpl; iIntros. iApply H0; auto. Qed.

Lemma bind_spec {X Y} (e : mon X) (f : X -> mon Y) Q Q' H :
   (⊢{{ H }} e {{ v; Q' v }}) ->
    (∀ v, ⊢{{ Q' v }} (f v) {{ v'; Q v' }}) ->
    ⊢ {{ H }} (bind e f) {{ v; Q v}}.
Proof.
  intros. iIntros "HA".
  iApply (wp_bind e f _ Q' with "[HA]").
  - iApply (H0 with "[HA]"); auto.
  - iIntros (v) "HC". iApply (H1 with "[HC]"); auto.  
Qed.

Lemma consequence {X} H H' (Q : X -> iProp) (Q' : X -> iProp) (e : mon X) :
  (⊢{{ H' }} e {{ v; Q' v }}) ->
  (forall v, Q' v ⊢ Q v) ->
  (H ⊢ H') ->
  ⊢{{ H }} e {{ v; Q v }}.
Proof.
  intros. iIntros "HA". iDestruct (H2 with "HA") as "HA".
  iDestruct (H0 with "HA") as "HA". iApply (wp_consequence with "HA"). iIntros "*". iApply H1.
Qed.


Lemma frame_bind : forall (P : iProp), ⊢ P -∗ emp ∗ P.
Proof. iIntros "* $". Qed.

Lemma frame {X} H R Q (e : mon X) :
  (⊢{{ H }} e {{ v; Q v }}) ->
  ⊢{{ H ∗ R }} e {{ v; Q v ∗ R }}.
Proof.
  intro P. iIntros "[HA HC]". iApply (wp_consequence with "[HA]").
  iApply P; auto. iIntros; iFrame.   
Qed.

Lemma intro_true_r {X} H Q (e : mon X) :
  (⊢{{ emp ∗ H }} e {{ v; Q v }}) ->
  ⊢{{ H }} e {{ v; Q v }}.
Proof.
  intro P. iIntros "HA". iApply (P with "[HA]").
  iFrame.
Qed.

Lemma exists_spec {X Y} v' H (Q : X -> Y -> iProp) (e : mon X) :
  (⊢{{ H }} e {{ v; Q v v' }}) ->
  ⊢{{ H }} e {{ v; ∃ t, Q v t }}.
Proof.
  intros. iIntros "HA". iApply consequence; eauto. 
Qed.

Ltac Frame := eapply intro_true_r; eapply frame.

(** Effects rules *)
Lemma gensym_spec t :
  ⊢{{ emp }} gensym t {{ l; IsFresh l }}.
Proof. simpl; auto. Qed.

Lemma error_spec {X} (Q : X -> iProp) e :
  ⊢{{ emp }} error e {{ v; Q v }}.
Proof. simpl. auto. Qed.

End weakestpre_gensym.

Module adequacy.
  (* Import fresh. *)
  Export gensym.
  Export weakestpre_gensym.
  
  Lemma adequacy {X} : forall (e : mon X) (Q : X -> iProp) (s s' : state) v ,
      wf_state s ->
      (heap_ctx (state_heap s) ⊢ wp e Q) ->
      run e s = Errors.OK (s', v) ->
      (Q v) () (state_heap s').
  Proof.
    fix e 1.
    destruct e0; intros.
    - inversion H1; subst. apply soundness2. iApply H0.
    - inversion H1.
    - simpl in *. eapply e.
      3 : apply H1.
      + unfold wf_state in *. simpl. intros. destruct H2.
        destruct (Pos.eq_dec p (next s)). lia. rewrite lookup_insert_ne in H2; auto.
        assert (Pos.lt p (next s)). apply H. eauto. lia.
      + iIntros "HA". simpl. apply fresh_is_fresh in H.
        apply (map_disjoint_singleton_r _ _ t) in H.
        iDestruct (heap_ctx_split_sing _ _ _ H with "HA") as "[HA HB]".
        iApply (H0 with "HA [HB]"); auto.
  Qed.

  Lemma adequacy_init {X} : forall (e : mon X) (Q : X -> iProp) (s' : state) v ,
      (⊢ wp e Q) ->
      run e initial_state = Errors.OK (s', v) ->
      (Q v) () (state_heap s').
  Proof. intros. eapply adequacy; eauto. apply wf_init. auto. Qed.
  
  Lemma adequacy_triple {X} : forall (e : mon X) (Q : X -> iProp) s v s' H,
      wf_state s ->
      (heap_ctx (state_heap s) ⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e s = Errors.OK (s', v) ->
      (Q v) () (state_heap s').
  Proof.
    intros. eapply adequacy; eauto. iIntros "HA". iDestruct (H1 with "HA") as "HA".
    iApply (H2 with "HA"); auto.
  Qed.

  Lemma adequacy_triple_init {X} : forall (e : mon X) (Q : X -> iProp) v s' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e initial_state = Errors.OK (s', v) ->
      (Q v) () (state_heap s').
  Proof.
    intros. eapply adequacy_init; eauto. iApply H1; eauto.
  Qed.

  Lemma adequacy_wp_pure {X} : forall (e : mon X) (Q : X -> Prop) s v s',
      wf_state s ->
      (heap_ctx (state_heap s) ⊢ wp e (fun v =>  ⌜Q v⌝)) ->
      run e s = Errors.OK (s', v) ->
      Q v.
  Proof.
    fix e 1. destruct e0; intros.
    - apply (soundness1 (state_heap s)). inversion H1. subst. simpl in H0. apply H0.
    - inversion H1.
    - simpl in *. eapply e.
      3 : apply H1.
      + unfold wf_state in *. simpl. intros. destruct H2.
        destruct (Pos.eq_dec p (next s)). lia. rewrite lookup_insert_ne in H2; auto.
        assert (Pos.lt p (next s)). apply H. eauto. lia.
      + simpl. iIntros "HA". apply fresh_is_fresh in H.
        apply (map_disjoint_singleton_r _ _ t) in H.
        iDestruct (heap_ctx_split_sing _ _ _ H with "HA") as "[HA HB]".
        iApply (H0 with "HA [HB]"); auto.
  Qed.

  Lemma adequacy_pure {X} : forall (e : mon X) (Q : X -> Prop) s v s' H,
      wf_state s ->
      (heap_ctx (state_heap s) ⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e s = Errors.OK (s', v) ->
      Q v.
  Proof.
    intros. eapply adequacy_wp_pure; eauto. iIntros "HA". iDestruct (H1 with "HA") as "HA".
    iDestruct (H2 with "HA") as "$". 
  Qed.

  Lemma adequacy_pure_init {X} : forall (e : mon X) (Q : X -> Prop) v s' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e initial_state = Errors.OK (s', v) ->
      Q v.
  Proof.
    intros. eapply adequacy_pure; eauto. apply wf_init.
    iIntros "_". iApply H1; auto. 
  Qed.

End adequacy.

  
