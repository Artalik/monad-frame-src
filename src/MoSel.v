From iris.proofmode Require Export coq_tactics ltac_tactics.
Require Import FunctionalExtensionality.
From iris Require Export bi proofmode.tactics proofmode.monpred.
From stdpp Require Export pmap.
Require Import Ctypes.
Axiom prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.

Definition pred_incl {A} (P Q : A -> Prop) :=
  forall x, P x -> Q x.

Definition pred_impl {A} (P Q : A -> Prop) :=
  fun x => P x -> Q x.

Notation "P ==> Q" := (pred_incl P Q).

Module SepBasicCore.

  Definition heap : Type := Pmap type.

  Definition hprop := heap -> Prop.

  Notation "'heap_empty'" := (∅ : heap) : heap_scope.

  Notation "h1 \u h2" := (h1 ∪ h2)
                           (at level 37, right associativity) : heap_scope.

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

  Open Scope heap_scope.

  (* Operators *)

  Definition hand (H1 H2:hprop):hprop :=
    fun h => H1 h /\ H2 h.

  Definition hor (H1 H2:hprop) : hprop := fun h => H1 h \/ H2 h.

  Definition hempty : hprop :=
    fun h => h = heap_empty.

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

  Notation "'Hexists' x1 , H" := (hexists (fun x1 => H))
                                   (at level 39, x1 ident, H at level 50) : heap_scope.
  Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
                                      (at level 39, x1 ident, x2 ident, H at level 50) : heap_scope.
  Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
                                         (at level 39, x1 ident, x2 ident, x3 ident, H at level 50) : heap_scope.


  Notation "'\[]'" := (hempty)
                        (at level 0) : heap_scope.

  Notation "\[ P ]" := (hpure P)
                         (at level 0, P at level 99, format "\[ P ]") : heap_scope.

  Notation "H1 '\*' H2" := (hstar H1 H2)
                             (at level 41, right associativity) : heap_scope.

  Notation "\Top" := (htop) : heap_scope.
  Open Scope heap_scope.

  Definition hwand (H1 H2 : hprop) : hprop :=
    hexists (fun (H:hprop) => H \* (hpure (H \* H1 ==> H2))).

  Definition qwand A (Q1 Q2:A->hprop) :=
    hforall (fun x => hwand (Q1 x) (Q2 x)).

  Definition hpure_abs (φ : Prop) : hprop := \[φ] \* \Top.

  Lemma hempty_intro :
    \[] heap_empty.
  Proof using. reflexivity. Qed.

  Lemma hempty_inv : forall h,
      \[] h ->
      h = heap_empty.
  Proof using. auto. Qed.


  Hint Resolve heap_union_empty_l heap_union_empty_r hempty_intro map_disjoint_empty_l map_disjoint_empty_r heap_union_assoc heap_disjoint_union_r_l heap_disjoint_union_l_l heap_disjoint_union_r_r heap_disjoint_union_l_r.

  Ltac inversion_star H h P :=
    match goal with
    | H : (_ \* _) _ |- _ =>
      let W := fresh h in
      let w := fresh P in
      inversion H as (W&w);
      let W := fresh h in
      destruct w as (W&w);
      do 3 (let w0 := fresh P in
            destruct w as (w0&w))
    (* | H : (_ ∗ _) _ |- _ => *)
    (*   let W := fresh h in *)
    (*   let w := fresh P in *)
    (*   inversion H as (W&w); *)
    (*   let W := fresh h in *)
    (*   destruct w as (W&w); *)
    (*   do 3 (let w0 := fresh P in *)
    (*         destruct w as (w0&w)) *)
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
      - inversion_star H h P. inversion P0; subst. rewrite heap_union_empty_l. assumption.
      - exists heap_empty; exists x. repeat split; auto. apply map_disjoint_empty_l.
    Qed.

    Lemma hstar_comm : forall H1 H2,
        H1 \* H2 = H2 \* H1.
    Proof using.
      intros H1 H2. extens.
      split; intro P; inversion_star H h P; exists h0; exists h; repeat split; auto;
        rewrite heap_union_comm; auto.
    Qed.

    Lemma hstar_assoc : forall H1 H2 H3,
        (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
    Proof using.
      intros H1 H2 H3. extens. split.
      { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
        exists h1; exists (h2 ∪ h3). repeat split; auto. { exists h2; exists h3; eauto. }
                                               { apply map_disjoint_union_l in D as (P0&P1).
                                                 apply map_disjoint_union_r. split; auto. }
                                               { by rewrite heap_union_assoc. }
      }
      { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
        exists (h1 ∪ h2); exists h3. repeat split; auto. { exists h1; exists h2; eauto. }
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
    Proof using. intros. intros h P. inversion_star H h P. exists h0; exists h1. split; eauto. Qed.

  End Properties.

  Definition hpersistent (H:hprop) : hprop := fun h => H heap_empty.


End SepBasicCore.

Export SepBasicCore.

Module ProofModeInstantiate.

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
      split; intro; inversion_star H h P; exists h; exists h0; repeat split; auto; inversion P0; inversion H2;
        auto; apply H; assumption.
    - intros X Y Z. rewrite /hforall. repeat red. intros. extens. split; intros; repeat red in H;
      apply functional_extensionality in H; subst; auto.
    - intros X Y Z. rewrite /hexists. repeat red. intros. extens. 
      split; intro; repeat red in H; apply functional_extensionality in H; subst; auto.
    - rewrite /hpure_abs. intros φ P. exists heap_empty. exists x. repeat split; auto.
      apply map_disjoint_empty_l.
    - unfold hpure_abs in *. intros x W P h P0. inversion_star W h P. inversion P2. apply P; auto.
      exists h0; exists h1. repeat split; auto.
    - rewrite /hforall /hpure_abs. intros h W h0 P. exists heap_empty; exists h0.
      repeat split; auto.
      + intro a. pose (P a). inversion_star h0 h P. inversion P1. apply H.
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
    - intros P P' Q Q' A B C D. inversion_star HHH h P. exists h; exists h0. repeat split; auto.
    - intros x W A. exists heap_empty; exists W. repeat split; auto. apply map_disjoint_empty_l.
    - intros P h Q. inversion_star H H H. inversion H3; inversion H6; subst.
      rewrite heap_union_empty_l. apply H4.
    - intros P Q h R. inversion_star H H H. exists H2; exists H0. repeat split; auto. subst.
      apply heap_union_comm. apply H5.
    - intros P Q R h P0. rewrite <- hstar_assoc. apply P0.
    - intros P Q R P0 h P1. exists P. exists h; exists heap_empty. repeat split; auto. apply map_disjoint_empty_r.
    - intros P Q R W h P0. inversion_star h h P. apply W in P2. destruct P2. inversion_star H h H.
      inversion H2. apply H4. exists h2; exists h1. repeat split; auto; subst.
      + apply heap_disjoint_union_l_l in P4. apply P4.
      + inversion H5. subst. rewrite heap_union_empty_r. reflexivity.
    - rewrite /hpersistent. intros P Q H h P0. apply H. apply P0.
    - rewrite /hpersistent. rewrite /hforall. intros A B C D E. apply D.
    - rewrite /hpersistent. intros P Q h P0. inversion_star P0 h P. apply P2.
    - intros P Q x W. destruct W. exists heap_empty; exists x. repeat split; auto. apply map_disjoint_empty_l.
  Qed.


  Lemma hpure_pure φ : \[φ] = bi_affinely ⌜φ⌝.
  Proof.
    extens. split.
    - intro. destruct H. split. split; auto. exists heap_empty; exists x. repeat split; auto.
      apply map_disjoint_empty_l.
    - intros [? Hφ]. destruct Hφ as (h1&h2&P0&P1&P2&P3). destruct P0. repeat split; auto.
      inversion H. apply H3.      
  Qed.

  Open Scope bi_scope.

  Lemma htop_True : \Top = True%I.
  Proof.
    extens. split.
    - exists heap_empty; exists x. repeat split; auto. apply map_disjoint_empty_l.
    - red; trivial.
  Qed.

  Opaque hpure_abs.

End ProofModeInstantiate.

Module ProofMode.

  Export ProofModeInstantiate.


  (* We need to repeat all these hints appearing in proofmode/tactics.v,
   so that they state something about CFML connectives. [Hint Extern]
   patterns are not matched modulo canonical structure unification. *)

  Hint Extern 0 (_ ==> _) => iStartProof.
  Hint Extern 0 (envs_entails _ (hpure _)) => iPureIntro.
  Hint Extern 0 (envs_entails _ (hempty)) => iEmpIntro.
  Hint Extern 0 (envs_entails _ (hforall _)) => iIntros (?).
  Hint Extern 0 (envs_entails _ (hwand _ _)) => iIntros "?".

  Hint Extern 1 (envs_entails _ (hand _ _)) => iSplit.
  Hint Extern 1 (envs_entails _ (hstar _ _)) => iSplit.
  Hint Extern 1 (envs_entails _ (hexists _)) => iExists _.
  Hint Extern 1 (envs_entails _ (hor _ _)) => iLeft.
  Hint Extern 1 (envs_entails _ (hor _ _)) => iRight.

  Hint Extern 2 (envs_entails _ (hstar _ _)) => progress iFrame : iFrame.

  (* Specific instances for CFML. *)

  Hint Extern 3 (envs_entails _ ?P) => is_evar P; iAccu.
  Hint Extern 3 (envs_entails _ (?P _)) => is_evar P; iAccu.

  Hint Extern 0 (envs_entails _ (\[_] \* _)) => iSplitR.
  Hint Extern 0 (envs_entails _ (\[_] ∗ _)) => iSplitR.
  Hint Extern 0 (envs_entails _ (_ \* \[_])) => iSplitL.
  Hint Extern 0 (envs_entails _ (_ ∗ \[_])) => iSplitL.

  Hint Extern 0 (envs_entails _ (emp \* _)) => iSplitR.
  Hint Extern 0 (envs_entails _ (emp ∗ _)) => iSplitR.
  Hint Extern 0 (envs_entails _ (_ \* emp)) => iSplitL.
  Hint Extern 0 (envs_entails _ (_ ∗ emp)) => iSplitL.

  (** * Specific Proofmode instances about hpure and htop. *)

  Global Instance htop_absorbing : Absorbing \Top.
  Proof. intros ??. red; trivial. Qed.
  Global Instance htop_persistent : Persistent \Top.
  Proof. intros ??. repeat red. trivial. Qed.

  Global Instance htop_into_pure : IntoPure \Top True.
  Proof. unfold IntoPure. auto. Qed.
  Global Instance htop_from_pure a : FromPure a \Top True.
  Proof. intros ??. red; trivial. Qed.

  Global Instance hpure_affine φ : Affine \[φ].
  Proof. rewrite hpure_pure. apply _. Qed.
  Global Instance hpure_persistent φ : Persistent \[φ].
  Proof. rewrite hpure_pure. apply _. Qed.

  Global Instance hpure_into_pure φ : IntoPure \[φ] φ.
  Proof. rewrite hpure_pure /IntoPure. by iDestruct 1 as "%". Qed.
  Global Instance hpure_from_pure φ : FromPure true \[φ] φ.
  Proof. by rewrite hpure_pure /FromPure /= /bi_affinely stdpp.base.comm. Qed.

  Global Instance from_and_hpure φ ψ : FromAnd \[φ ∧ ψ] \[φ] \[ψ].
  Proof. rewrite /FromAnd. auto. Qed.
  Global Instance from_sep_hpure φ ψ : FromSep \[φ ∧ ψ] \[φ] \[ψ].
  Proof. rewrite /FromSep. auto. Qed.
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

  (** Instance bi_emp_valid *)

  Global Instance as_emp_valid_emp_valid0 P : @AsEmpValid0 hpropI (emp ⊢ P) P | 0.
  Proof. by rewrite /AsEmpValid0 /AsEmpValid. Qed.

  Global Instance as_emp_valid_emp_valid0_bis (P : hprop) :
    @AsEmpValid0 hpropI (bi_emp_valid P) P | 0.
  Proof. by rewrite /AsEmpValid0 /AsEmpValid. Qed.

  Global Instance as_emp_valid_entails0 P Q : @AsEmpValid0 hpropI (P ⊢ Q) (P -∗ Q).
  Proof. split. apply bi.entails_wand. apply bi.wand_entails. Qed.

  Global Instance as_emp_valid_entails P Q : @AsEmpValid hpropI (P ⊢ Q) (P -∗ Q).
  Proof. split. apply bi.entails_wand. apply bi.wand_entails. Qed.

  Global Instance as_emp_valid_forall {A : Type} (φ : A → Prop) (P : A → hprop) :
    (∀ x, AsEmpValid (φ x) (P x)) → AsEmpValid (∀ x, φ x) (∀ x, P x).
  Proof.
    rewrite /AsEmpValid=>H1. split=>H2.
    - apply bi.forall_intro=>?. apply H1, H2.
    - intros x. apply H1. revert H2. by rewrite (bi.forall_elim x).
  Qed.

  Global Instance as_emp_valid_emp_valid (P : hprop) :
    @AsEmpValid hpropI (emp ⊢ P) P | 0.
  Proof.
    rewrite /AsEmpValid. split.
    - intro. eapply H.
    - intro. intro. intro. inversion H0. apply H. apply H0. 
  Qed.

  Global Instance as_emp_valid_emp_valid_bis (P : hprop) :
    @AsEmpValid hpropI (bi_emp_valid P) P | 0.
  Proof.
      by rewrite /AsEmpValid.
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

End ProofMode.

Module biInd.
  Import ProofMode.
  Import monpred.

  Instance inhabited_nat : Inhabited nat.
  Proof.
    split. apply 0%nat.
  Qed.

  Definition lt (n0 n1 : nat) := n0 <= n1.

  Instance PreOrder_nat : PreOrder lt.
  Proof.
    split; repeat red; intros.
    - left.
    - inversion H; inversion H0; subst.
      + left.
      + right. apply H2.
      + right. apply H1.
      + right. omega.
  Qed.

  Program Canonical Structure biInd := BiIndex nat inhabited_nat _ PreOrder_nat.

End biInd.



Module gensym.

  Definition ident := positive.

  Definition state := heap.

  Definition max := Pos.max.
  Definition upper := fun r i => max (i+1) r.
  Definition fresh (s:list ident) : ident := foldl upper 1%positive s.

  Lemma max_comm : forall n m, max n m = max m n.
  Proof.
    intros. unfold max. rewrite Pos.max_comm. reflexivity.
  Qed.

  Lemma foldl_upper : forall l a0 a1, foldl upper (max a0 a1) l = max a1 (foldl upper a0 l).
  Proof.
    induction l; simpl; intros.
    - by rewrite max_comm.
    - repeat rewrite IHl. unfold max. rewrite Pos.max_assoc. rewrite (Pos.max_comm a0). reflexivity.
  Qed.

  Lemma upper_spec: forall l a, Pos.le a (foldl upper a l).
  Proof.
    unfold upper.
    induction l; simpl.
    - reflexivity.
    - intro. rewrite foldl_upper. apply Pos.le_max_l.
  Qed.

  Lemma test3 : forall l a, fresh (a :: l) = max (a + 1) (fresh l).
  Proof.
    induction l; intros.
    - reflexivity.
    - unfold fresh. unfold upper. simpl. unfold max.
      unfold fresh in IHl. unfold upper in IHl. simpl in IHl. unfold max in IHl.
      rewrite IHl. rewrite Pos.max_1_r. rewrite foldl_upper.
      unfold upper. unfold max.
      f_equal. rewrite <- (Pos.max_1_r (a+1)%positive). rewrite IHl.
      rewrite Pos.max_1_r. reflexivity.
  Qed.

  Lemma test4 : forall l v, v ∈ l -> Pos.lt v (fresh l).
  Proof.
    intros. unfold fresh.
    apply elem_of_list_split in H as (l1&l2&H0).
    rewrite H0. rewrite foldl_app. pose test3. unfold fresh in e. simpl in *. unfold upper.
    rewrite foldl_upper.
    destruct (Pos.max_spec (foldl (λ r i : positive, max (i + 1) r) 1%positive l1)
                           (foldl upper (v + 1)%positive l2)); destruct H.
    - unfold max. rewrite H1. pose (upper_spec l2 (v+1)).
      eapply Pos.lt_le_trans; eauto.
      setoid_rewrite Pos2Nat.inj_lt. rewrite <- Pplus_one_succ_r.
      rewrite Pos2Nat.inj_succ. omega.
    - unfold max. rewrite H1. pose (upper_spec l2 (v+1)). eapply Pos.lt_le_trans; eauto.
      eapply Pos.lt_le_trans; eauto.
      setoid_rewrite Pos2Nat.inj_lt. rewrite <- Pplus_one_succ_r.
      rewrite Pos2Nat.inj_succ. omega.
  Qed.

  Lemma fresh_is_fresh : forall l, (fresh l) ∉ l.
  Proof.
    induction l.
    - intro. inversion H.
    - intro. inversion H ; subst.
      + unfold fresh in H2. unfold upper in H2. unfold max in H2.
        simpl in H2. rewrite Pos.max_1_r in H2.
        pose (upper_spec l (a+1)%positive). unfold upper in l0. unfold max in l0.
        rewrite <- H2 in l0 at 1.
        rewrite Pos.add_1_r in l0. apply Pos.le_succ_l in l0.
        apply Pos.lt_irrefl in l0. apply l0.
      + rewrite  test3 in H2. destruct (Pos.max_spec (a+1) (fresh l)); destruct H0.
        * unfold max in H2. rewrite H1 in H2.
          contradiction IHl.
        * unfold max in H2. rewrite H1 in H2. apply test4 in H.
          setoid_rewrite Pos2Nat.inj_lt in H. setoid_rewrite Pos2Nat.inj_le in H0.
          omega.
  Qed.

  Definition fresh_ident (s:state) :=
    fresh (map_to_list s).*1.

  Lemma fresh_ident_spec : forall (s : state), s !! (fresh_ident s) = None.
  Proof.
    intros. unfold fresh_ident. pose (fresh_is_fresh (map_to_list s).*1).
    apply not_elem_of_list_to_map in n.
    rewrite (list_to_map_to_list s) in n.
    apply n.
  Qed.

  Inductive sig (X : Type) : Type :=
  | Err : Errors.errmsg -> sig X
  | Gensym : type -> (ident -> X) -> sig X.

  Arguments Err [X].
  Arguments Gensym [X].

  Inductive mon (X : Type) : Type :=
  | ret : X -> mon X
  | op : sig (mon X) -> mon X.

  Arguments ret {_} x.
  Arguments op {_} s.

  Fixpoint bind {X Y} (m : mon X) (f : X -> mon Y) : mon Y :=
    match m with
    | ret x => f x
    | op (Err e) => op (Err e)
    | op (Gensym t g) => op (Gensym t (fun x => bind (g x) f))
    end.

  Notation "'let!' x ':=' e1 'in' e2" := (bind e1 (fun x => e2))
                                           (x ident, at level 90).

  Definition error {X} (e : Errors.errmsg) : mon X := op (Err e).
  Definition gensym (t : type) : mon ident := op (Gensym t ret).

  Lemma lid : forall X Y (a : X) (f : X -> mon Y), bind (ret a) f = f a.
  Proof. auto. Qed.

  Lemma rid : forall X (m : mon X), bind m ret = m.
  Proof.
    fix m 2.
    destruct m0.
    * reflexivity.
    * destruct s.
      ** reflexivity.
      ** simpl. do 2 f_equal. apply functional_extensionality. intro. apply m.
  Qed.

  Lemma ass_bind : forall X Y Z (m : mon X) f (g : Y -> mon Z),
      bind (bind m f) g = bind m (fun x => bind (f x) g).
  Proof.
    fix m 4.
    destruct m0; intros.
    * reflexivity.
    * destruct s.
      ** reflexivity.
      ** simpl. do 2 f_equal. apply functional_extensionality. intro. apply m.
  Qed.

  Inductive err (X: Type) : Type :=
  | Erro : Errors.errmsg -> err X
  | Res : X -> err X.
  
  Arguments Erro [X].
  Arguments Res [X].
  Local Open Scope positive_scope.

  Fixpoint run {X} (m : mon X) : state -> err (state * X) :=
    match m with
    | ret v => fun s => Res (s, v)
    | op (Err e) => fun s => Erro e
    | op (Gensym t f) =>
      fun s =>
        let l := fresh_ident s in
        run (f l) (<[l:=t]>s)
    end.

End gensym.


Module weakestpre_gensym.
  Export gensym.
  Export ProofMode.
  Export proofmode.monpred.
  Import biInd.

  Definition iProp := monPred biInd hpropI.

  Definition single (l : positive) (t : type) : iProp := MonPred (fun _ => hsingle l t) _.

  Definition heap_ctx (h : heap) : iProp := MonPred (fun _ => hheap_ctx h) _.


  Global Instance affine_heap_empty : Affine (heap_ctx ∅).
  Proof.
    split. intro. MonPred.unseal. repeat red. intros. split; auto.
  Qed.

  Lemma init_heap : bi_emp_valid (heap_ctx ∅).
  Proof.
    split. MonPred.unseal. repeat red. intros. inversion H. inversion H1.
    reflexivity.
  Qed.
    
  Definition pure_empty (P : Prop) : iProp := <affine> ⌜P⌝.

  Global Instance affine_pure (P : Prop) : Affine (pure_empty P).
  Proof.
    red.
    iIntros "HA". trivial.
  Qed.

  Lemma pureIntro {X} (P0 : X -> iProp) : ∀ a b, P0 a -∗ pure_empty (a = b) -∗ P0 b.
  Proof.
    iIntros (a b) "HA %". rewrite a0. iApply "HA".
  Qed.

  Notation "\⌜ P ⌝" := (pure_empty P)
                         (at level 0, P at level 99, format "\⌜ P ⌝") : heap_scope.
  
  Notation "l ↦ t" :=
    (single l t) (at level 20) : bi_scope.

  Fixpoint mwp {X} (e1 : mon X) (Q : X -> iProp) : iProp :=
    match e1 with
    | ret v => Q v
    | op (Err e) => True
    | op (Gensym t f) =>
      ∀ l, l ↦ t -∗ mwp (f l) Q
    end%I.


  Notation "'WP' e |{ Φ } |" := (mwp e Φ)
                                  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

  Notation "'WP' e |{ v , Q } |" := (mwp e (λ v, Q))
                                      (at level 20, e, Q at level 200,
                                       format "'[' 'WP'  e  '[ ' |{  v ,  Q  } | ']' ']'") : bi_scope.

  Notation "'{{' P } } e {{ x .. y , 'RET' pat ; Q } }" :=
    (∀ Φ,
        P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e |{ Φ }|)%I
                                                             (at level 20, x closed binder, y closed binder,
                                                              format "'[hv' {{  P  } }  '/  ' e  '/'  {{  x  ..  y ,  RET  pat ;  Q  } } ']'") : bi_scope.
  
  (** wp rules *)
  (** Generic rules *)
  Lemma wp_value' {X} (Φ : X -> iProp) (v : X) : Φ v ⊢ WP ret v |{ Φ }|%I.
  Proof. auto. Qed.
  Lemma wp_value_inv' {X} Φ (v : X) : WP ret v |{ Φ }| -∗ Φ v%I.
  Proof. auto. Qed.

  Lemma wp_mono {X} e (Φ Ψ : X -> iProp) :
    WP e |{ Φ }| -∗ (∀ (v : X), Φ v -∗ Ψ v) -∗ WP e |{ Ψ }|%I.
  Proof.
    iIntros "HA HB". revert e. fix e 1.
    destruct e0.
    { iApply "HB". iApply "HA". }
    { destruct s.
      { simpl. trivial. }
      { simpl. iIntros (l) "HC".
        iDestruct ("HA" with "HC") as "HA".
        iPoseProof "HB" as "HB". apply e. }}
  Qed.

  Lemma wp_bind {X Y} (e : mon X) (f :  X → mon Y) (Φ : Y -> iProp)  (Φ' : X -> iProp) :
    WP e |{ Φ' }| -∗ (∀ v,  Φ' v -∗ WP (f v) |{ Φ }|) -∗ WP bind e f |{ Φ }|%I.
  Proof.
    iIntros "HA HB". revert e. fix e 1.
    destruct e0.
    { iApply "HB". iApply "HA". }
    { destruct s.
      { simpl. auto. }
      { simpl. iIntros (l) "HC".
        iDestruct ("HA" with "HC") as "HA".
        iPoseProof "HB" as "HB". apply e. }}
  Qed.
  
  (** Monad rules *)
  Lemma wp_gensym (t : type) : emp -∗ WP gensym t |{ l, l ↦ t }|.
  Proof.
    simpl. iIntros. iFrame.
  Qed.
  
  Lemma wp_frame_l {X} (e : mon X) Φ (R : iProp) : R ∗ WP e |{ Φ }| ⊢ WP e |{ v, R ∗ Φ v }|.
  Proof. iIntros "[HA HB]". iApply (wp_mono with "HB"). auto with iFrame. Qed.
  Lemma wp_frame_r {X} (e : mon X) Φ R : WP e |{ Φ }| ∗ R ⊢ WP e |{ v, Φ v ∗ R }|.
  Proof. iIntros "[H ?]". iApply (wp_mono with "H"); auto with iFrame. Qed.


  (** triple rules *)
  (** Generic rules *)

  Lemma ret_spec_complete {X} (v : X) H (Q : X -> iProp) :
    (H -∗ Q v)
      -∗
      {{ H }} ret v {{ v', RET v'; Q v' }}.
  Proof.
    iIntros "HA" (?) "HB HC". iDestruct ("HA" with "HB") as "HA". iApply "HC". iApply "HA".
  Qed.

  Lemma ret_spec {X} (v : X) :
    {{ emp }} ret v {{ v', RET v'; ⌜ v' = v ⌝  }}.
  Proof. iIntros (?) "HA HB". iApply "HB". auto. Qed.

  Lemma ret_spec_pure {X} (v : X) :
    {{ emp }} ret v {{ v', RET v'; \⌜ v' = v ⌝  }}.
  Proof.
    iIntros (?) "HA HB". iApply "HB". auto.
  Qed.

  Lemma ret_spec_bis {X} (v : X) (Q : X -> iProp) :
    Q v
      -∗
      {{ emp }} ret v {{ v', RET v'; Q v' }}.
  Proof.
    iIntros "HA" (?) "HB HC". iApply "HC". iApply "HA".
  Qed.
  
  Lemma bind_spec {X Y} (e : mon X) (f : X -> mon Y) Φ' Φ'' H :
    {{ H }} e {{ v, RET v; Φ'' v }} ->
    (∀ v, {{ Φ'' v }} (f v) {{ v', RET v'; Φ' v' }}) ->
    {{ H }} (bind e f) {{ v, RET v; Φ' v}}.
  Proof.
    intros. iIntros (?) "HA HB".
    iApply (wp_bind e f _ Φ'' with "[HA]").
    - iApply (H0 with "[HA]"); auto.
    - iIntros (v) "HC". iApply (H1 with "[HC]"); auto.
  Qed.

  Lemma frame_r {X} H R Φ' (e : mon X) :
    {{ H }} e {{ v, RET v; Φ' v }} ->
    {{ H ∗ R }} e {{ v, RET v; Φ' v ∗ R }}.
  Proof.
    intro P. iIntros (?) "[HA HC] HB".
    iApply (P with "[HA]"); auto.
    iIntros (v) "HA". iApply "HB". iFrame.
  Qed.

  Lemma frame_l {X} H R Φ' (e : mon X) :
    {{ H }} e {{ v, RET v; Φ' v }} ->
    {{ R ∗ H }} e {{ v, RET v; R ∗ Φ' v }}.
  Proof.
    intro P. iIntros (?) "HA HB". iDestruct "HA" as "[HA HC]".
    iApply (P with "[HC]"); auto.
    iIntros (v) "HC". iApply "HB". iFrame.
  Qed.

  Lemma exists_spec {X Y} v' H (Q : X -> Y -> iProp) (e : mon X) :
    {{ H }} e {{ v, RET v; Q v v' }} ->
    {{ H }} e {{ v, RET v; ∃ t, Q v t }}.
  Proof.
    iIntros (? ?) "HA HB".
    iApply (H0 with "HA").
    iIntros (?) "HA". iApply "HB". iExists v'. iApply "HA".
  Qed.

  Lemma intro_true_l {X} H Φ' (e : mon X) :
    {{ H ∗ emp }} e {{ v, RET v; Φ' v }} ->
    {{ H }} e {{ v, RET v; Φ' v }}.
  Proof.
    intro P. iIntros (?) "HA HB". iApply (P with "[HA]").
    iFrame.
    iIntros (v) "HA". iApply "HB". iFrame. 
  Qed.

  Lemma intro_true_r {X} H Φ' (e : mon X) :
    {{ emp ∗ H }} e {{ v, RET v; Φ' v }} ->
    {{ H }} e {{ v, RET v; Φ' v }}.
  Proof.
    intro P. iIntros (?) "HA HB". iApply (P with "[HA]").
    iFrame.
    iIntros (v) "HA". iApply "HB". iFrame. 
  Qed.


  Lemma wand_post {X} H R Φ' (v : X):
    {{ H ∗ R }} ret v {{ v, RET v; Φ' v }} ->
    {{ H }} ret v {{ v, RET v; R -∗ Φ' v }}.
  Proof.
    iIntros (? ?) "HH HB". iApply "HB". iIntros "HR". iApply (H0 with "[HH HR]"). iFrame.
    iIntros. iFrame.
  Qed.

  
  Lemma assoc_pre {X} H R Q Φ' (e : mon X):
    {{ H ∗ R ∗ Q }} e {{ v, RET v; Φ' v }} <->
    {{ (H ∗ R) ∗ Q}} e {{ v, RET v; Φ' v }}.
  Proof.
    split; iIntros (? ?) "[HA HC] HB"; iApply (H0 with "[HA HC]"); iFrame. iApply "HC".
  Qed.

  Lemma assoc_post {X} H R Q P (e : mon X) :
    {{ P }} e {{ v, RET v; H v ∗ R v ∗ Q v }} <->
    {{ P }} e {{ v, RET v; (H v ∗ R v) ∗ Q v}}.
  Proof.
    split; iIntros (? ?) "HA HB"; iApply (H0 with "HA"); iIntros (?) "[HA HC]"; iApply "HB"; iFrame.
    iApply "HC".
  Qed.
  
  Lemma comm_pre {X} H R Φ' (e : mon X):
    {{ H ∗ R }} e {{ v, RET v; Φ' v }} <->
    {{ R ∗ H }} e {{ v, RET v; Φ' v }}.
  Proof.
    split; iIntros (? ?) "[HA HC] HB"; iApply (H0 with "[HA HC]"); iFrame.
  Qed.
  
  Lemma comm_post {X} P H R (e : mon X):
    {{ P }} e {{ v, RET v; H v ∗ R v }} <->
    {{ P }} e {{ v, RET v; R v ∗ H v }}.
  Proof.
    split; iIntros (? ?) "HA HB"; iApply (H0 with "HA"); iIntros (?) "[HA HC]"; iApply "HB"; iFrame.
  Qed.

  
  Ltac frameL := apply intro_true_l; apply frame_l.
  Ltac frameR := apply intro_true_r; apply frame_r.

  
  
  (** Monad rules *)
  Lemma gensym_spec t :
    {{ emp }} gensym t {{ l, RET l; l ↦ t }}.
  Proof.
    iIntros (Φ) "HA HB". simpl.
    iIntros (σ) "HC". iApply "HB". iApply "HC".
  Qed.
  
  Lemma error_spec {X} (Q : X -> iProp) e :
    {{ emp }} error e {{ v, RET v; Q v }}.
  Proof.
    simpl. auto.
  Qed.

  
  Ltac tac :=
    match goal with
    | |- bi_emp_valid ({{ _ }} bind _ (fun _ => _) {{ _, RET _; _ }}) =>
      eapply bind_spec; [> tac | intro; tac]
    | |- bi_emp_valid ({{ _ }} ret _ {{ _, RET _; ∃ _, _ }}) => eapply exists_spec; tac
    | |- bi_emp_valid ({{ emp }} error _ {{ _, RET _; _ }}) => apply error_spec
    | |- bi_emp_valid ({{ emp }} gensym _ {{ _, RET _; _ }}) => apply gensym_spec
    | |- bi_emp_valid ({{ ?H }} gensym _ {{ _, RET _; _ }}) => frameR; apply gensym_spec 
    | |- bi_emp_valid ({{ _ }} ret _ {{ _, RET _; _ -∗ _ }}) => apply wand_post; tac
    | H :  bi_emp_valid ({{ ?Pre }} ?e {{ _, RET _; _ }})
      |-  bi_emp_valid ({{ ?Pre }} ?e {{ _, RET _; _ }}) => apply H
    | H :  (forall x, bi_emp_valid ({{ ?Pre }} ?e x {{ _, RET _; _ }}))
      |-  bi_emp_valid ({{ ?Pre }} ?e _ {{ _, RET _; _ }}) => apply H
    | H :  (forall x y, bi_emp_valid ({{ ?Pre }} ?e x y {{ _, RET _; _ }}))
      |-  bi_emp_valid ({{ ?Pre }} ?e _ _ {{ _, RET _; _ }}) => apply H
    | H :  (forall x y, bi_emp_valid ({{ ?Pre }} ?e x ?r {{ _, RET _; _ }}))
      |-  bi_emp_valid ({{ ?Pre }} ?e _ ?r {{ _, RET _; _ }}) => apply H
    | H :  (forall x y z, bi_emp_valid ({{ ?Pre }} ?e x y z {{ _, RET _; _ }}))
      |-  bi_emp_valid ({{ ?Pre }} ?e _ _ _ {{ _, RET _; _ }}) => apply H
    | H :  bi_emp_valid ({{ emp }} ?e {{ _, RET _; _ }}) |-
      bi_emp_valid ({{ ?Pre }} ?e {{ _, RET _; _ }}) => frameR; apply H
    | |- bi_emp_valid ({{ emp }} ret ?v {{ v', RET v'; ⌜ v' = ?v ⌝ }}) => apply ret_spec
    | |- bi_emp_valid ({{ emp }} ret ?v {{ v', RET v'; \⌜ v' = ?v ⌝ }}) => apply ret_spec_pure
    | _ => idtac
    end.

  
End weakestpre_gensym.

Module adequacy.
  Export gensym.
  Export weakestpre_gensym.
  Lemma soundness1 (Φ : Prop) h : (heap_ctx h ⊢ (⌜ Φ ⌝) : iProp) -> Φ.
  Proof.
    MonPred.unseal=> -[H]. repeat red in H.
    pose (H 0%nat h).
    edestruct e as (h1&h2&P0&P1&P2&P3).
    - reflexivity.
    - inversion P0. apply H0.
  Qed.
  Lemma soundness_pure (Φ : Prop) : bi_emp_valid ((⌜ Φ ⌝) : iProp) -> Φ.
  Proof.
    MonPred.unseal=> -[H]. repeat red in H.
    pose (H 0%nat heap_empty).
    edestruct e as (h1&h2&P0&P1&P2&P3).
    - rewrite monPred_at_emp. split; auto; apply hempty_intro.
    - inversion P0. apply H0.
  Qed.
  
  Lemma soundness2 (Φ : iProp) i h : (heap_ctx h -∗ Φ) -> Φ i h.
  Proof.
    MonPred.unseal=> -[H]. repeat red in H.
    pose (H i heap_empty).
    simpl in *. edestruct e.
    - rewrite monPred_at_emp. split; auto; apply hempty_intro.
    - repeat red. exists heap_empty; exists heap_empty. repeat split; auto.
    - inversion_star H0 h P.
      inversion P1.
      apply H1.
      exists heap_empty; exists h.
      inversion H2; subst. rewrite heap_union_empty_r in P; subst.
      repeat split; auto. apply map_disjoint_empty_l.
  Qed.
  
  Lemma soundness3 (Φ : iProp) h : (forall i, Φ i h) -> heap_ctx h -∗ Φ.
  Proof.
    MonPred.unseal. unfold monPred_wand_def. unfold monPred_upclosed. simpl. split.
    intros. simpl. repeat red. intros. exists emp. exists x; exists heap_empty.
    repeat split; auto. rewrite monPred_at_emp in H0. apply H0.
    intros h0 P0. inversion_star H h P. simpl in *. rewrite <- P2 in *. inversion P1. inversion H3.
    subst. rewrite heap_union_empty_l. rewrite <- P2. apply H.
    apply map_disjoint_empty_r.
  Qed.
  
  Lemma heap_ctx_split h l t : h ##ₘ ({[l := t]}) -> heap_ctx (<[l := t]>h) -∗ heap_ctx h ∗ l ↦ t.
  Proof.
    intro.
    MonPred.unseal. repeat red.
    unfold monPred_wand_def.
    unfold monPred_sep_def.
    unfold monPred_upclosed. split. simpl.
    intro. intro P. intro. intros. repeat red. exists hempty. rewrite monPred_at_emp in H0.
    inversion H0; subst.
    exists heap_empty; exists heap_empty. repeat split; auto.
    + repeat intro. inversion_star H1 h P. inversion P1. subst.
      exists h; exists ({[l := t]} : heap). repeat split; auto. inversion P2; subst.
      rewrite heap_union_empty_l. rewrite insert_union_singleton_r. reflexivity.
      apply (map_disjoint_singleton_r) in H. apply H.
    + inversion H3. rewrite heap_union_empty_l. reflexivity.
  Qed.

  Lemma adequacy {X} : forall (e : mon X) (Φ : X -> iProp) h v h' i,
      (heap_ctx h ⊢ WP e |{ Φ }|) ->
      run e h = Res (h', v) ->
      (Φ v) i h'.
  Proof.
    fix e 1. destruct e0; simpl; intros.
    - inversion H0; subst. apply soundness2. iApply H.
    - destruct s.
      + inversion H0.
      + eapply e.
        2 : apply H0.
        iIntros "HA".
        pose (fresh_ident_spec h).
        apply (map_disjoint_singleton_r h (fresh_ident h) t) in e0.
        iDestruct ((heap_ctx_split _ _ _ e0) with "HA") as "[HA HB]".
        iApply (H with "HA HB").
  Qed.

  Lemma adequacy_triple {X} : forall (e : mon X) (Φ : X -> iProp) h v h' i H,
      (heap_ctx h ⊢ {{ H }} e {{ v, RET v; Φ v }} ∗ H) ->
      run e h = Res (h', v) ->
      (Φ v) i h'.
  Proof.
    fix e 1. destruct e0; simpl; intros.
    - apply soundness2.
      inversion H1; subst.
      iIntros "HA".
      iDestruct (H0 with "HA") as "HA".
      iDestruct "HA" as "[HA HB]".
      iApply ("HA" with "HB"). iIntros. iFrame.
    - destruct s.
      + inversion H1.
      + eapply e.
        2 : apply H1.
        iIntros "HA". pose (fresh_ident_spec h).
        apply (map_disjoint_singleton_r h (fresh_ident h) t) in e0.
        iDestruct ((heap_ctx_split _ _ _ e0) with "HA") as "[HA HB]".
        iDestruct (H0 with "HA") as "[HA HC]".
        iSplitR "HC".
        iIntros (?) "HC HD". iApply ("HA" with "HC [HD]"); eauto. iApply "HC".
  Qed.

End adequacy.
       
