Require Import Program.Wf Lia Omega.
From stdpp Require Import fin_sets.

Fixpoint subtr {A} (eq : forall (v v': A), {v = v'}+{v <> v'}) (l1 : list A) (l2 : list A) : list A :=
  match l2 with
  | [] => l1
  | h :: t => remove eq h (subtr eq l1 t)
  end.

Module REACHABILITY.
  Section definitions.
  Variable (State : Type) (trans : State -> State -> Prop).

  Inductive reachable: State -> State -> Prop :=
  | reachable_refl s: reachable s s
  | reachable_next a b c: reachable a b -> trans b c -> reachable a c.

  Lemma reachable_trans a b: reachable a b -> forall c, reachable b c -> reachable a c.
  Proof.
    induction 2; auto.
    apply reachable_next with b; auto.
  Qed.

  End definitions.
End REACHABILITY.

(* Hint Constructors REACHABILITY.reachable. *)

Record DiGraph : Type :=
  Build
    { Vertex:Set;
      Vertex_eq_dec: forall (v v': Vertex), {v = v'}+{v <> v'};
      vertices : list Vertex;
      vertices_exhaustive : forall v, In v vertices;
      edges : Vertex -> list Vertex;
      edges_NoDup : forall v, NoDup (edges v)
    }.

Arguments edges {d}.

Section contents.
  Import REACHABILITY.
  Variable (G: DiGraph).

  Definition Edge (v w : Vertex G): Prop := In w (edges v).
  Definition ved := Vertex_eq_dec G.
  Definition subtrV := subtr ved.
  Definition SubsetV := list (Vertex G).
  Definition emptyV : SubsetV := [].
  Definition addV v vs : SubsetV := v :: vs.

  Variable start: SubsetV.
  Hypothesis NoDup_start : NoDup start.

  Let reachable v: Prop := exists s,
      In s start /\ reachable _ Edge s v.

  Lemma reachable_start : forall v, In v start -> reachable v.
  Proof. intros. exists v. split; auto. constructor. Qed.

  Lemma reachable_next : forall v, reachable v -> forall w, Edge v w -> reachable w.
  Proof.
    intros. destruct H as [x [P0 P1]]. exists x. split; auto.
    econstructor; eauto.
  Qed.

  Definition Sound (ss : SubsetV) : Prop := forall v, In v ss -> reachable v.

  Lemma Sound_empty : Sound emptyV. intros v P. destruct P. Qed.

  Definition Complete (ss : SubsetV) : Prop := forall v, reachable v -> In v ss.

  Definition closed_under {A} (P : A -> A -> Prop) (l : list A) :=
    forall v w, In v l -> P v w -> In w l.

  Definition GComplete (vs ws rs : SubsetV): Prop :=
    closed_under Edge rs /\ incl ws rs /\ incl vs rs.

  Lemma gcomplete_complete vs: GComplete [] start vs -> Complete vs.
  Proof. intros[P0 [P1 P2]] v [s [P3 P4]]. induction P4; eauto. Qed.

  Definition Specification rs : Prop := Sound rs /\ Complete rs.

  Let neighbours := flat_map (@edges G).
  Definition Invariant vs ws : Prop := incl (neighbours vs) (ws ++ vs).

  Definition rstep vs w ws := (subtrV (edges w) ((addV w vs) ++ ws)) ++ ws.

  Definition Disjoint (l1 l2 : SubsetV) := l1 ## l2.

  Definition Termination (vs ws : SubsetV) :=
    NoDup ws /\ Disjoint ws vs.

  Inductive mon X :=
  | ret : X -> mon X
  | Reach (vs : SubsetV) : {ws | Termination vs ws} -> (SubsetV -> mon X) -> mon X.

  Arguments ret {X}.
  Arguments Reach {X}.

  Definition reach (visited : SubsetV) (waiting : {ws | Termination visited ws}) : mon SubsetV :=
    Reach visited waiting ret.

  Fixpoint bind {X Y} (m : mon X) (f : X -> mon Y) : mon Y :=
    match m with
    | ret v => f v
    | Reach vs ws c => Reach vs ws (fun x => bind (c x) f)
    end.

  Notation "let! n := A 'in' B" := (bind A (fun n => B))(at level 20).

  Program Fixpoint wp {X} (m : mon X) (Q : X -> Prop) : Prop :=
    match m with
    | ret x => Q x
    | Reach vs ws c =>
      Sound vs /\ Sound ws /\ Invariant vs ws /\ (forall rs, Sound rs /\ GComplete vs ws rs -> wp (c rs) Q)
    end.

  Notation "'{{' P } } e '{{' Q } }" := (P -> wp e Q)
                                            (at level 20,
                                             format "'[hv' {{  P  } }  '/  ' e  '/'  {{  Q  } } ']'").

  Lemma wp_bind : forall {X Y} Q (f : mon X) (g : X -> mon Y),
      wp f (fun x => wp (g x) Q) -> wp (let! v := f in g v) Q.
  Proof.
    induction f; intros.
    - apply H.
    - simpl in *. destruct H0 as [P0 [P1 [P2 P3]]]. repeat split; auto.
  Qed.

  Lemma wp_consequence : forall {X} (P Q : X -> Prop) (f : mon X),
      wp f P ->
      (forall x, P x -> Q x) ->
      wp f Q.
  Proof.
    induction f; simpl; intros.
    - apply (H0 x H).
    - destruct H0 as [P0 [P1 [P2 P3]]]. repeat split; auto.
  Qed.

  Lemma wp_ret : forall {X} (P : X -> Prop) (v : X),
      P v -> wp (ret v) P.
  Proof.
    intros. exact H.
  Qed.

  Program Lemma wp_reach : forall vs (ws : {ws : SubsetV | Termination vs ws}),
      Sound vs -> Sound ws -> Invariant vs ws -> wp (reach vs ws) (fun rs => Sound rs /\ GComplete vs ws rs).
  Proof. simpl. intros. do 3 (split; auto). Qed.

Lemma rule_value : forall {X} (Q : X -> Prop) (v : X),
      {{ Q v }} ret v {{ Q }}.
Proof. auto. Qed.

Lemma rule_composition {X Y} (P : Prop)(Q : X -> Prop)(R : Y -> Prop) f g:

    {{ P }} f {{ Q }} ->
    (forall v, {{ Q v }} g v  {{ R }}) ->
    (*-------------------------------*)
    {{ P }} let! x := f in g x {{ R }}.
Proof.
  revert P Q R g.
  induction f; intros.
  - apply H in H1. apply wp_bind. apply wp_ret. apply H0. apply H1.
  - simpl in *. apply H0 in H2 as [P0 [P1 [P2 P3]]]. repeat split; auto.
    intro rs. eapply H. apply P3. apply H1.
Qed.


Program Lemma rule_reach vs (ws : {ws : SubsetV | Termination vs ws}):

    (*-------------------------------------------------------*)
  {{ Sound vs /\ Sound ws /\ Invariant vs ws }} reach vs ws {{ fun rs => Sound rs /\ GComplete vs ws rs }}.
Proof.
  intros. destruct H as [P0 [P1 P2]]. apply wp_reach; auto.
Qed.

Lemma rule_consequence {X} (P P' : Prop) (Q Q' : X -> Prop) m:

    {{ P' }} m {{ Q' }} ->
    (P -> P') ->
    (forall x, Q' x -> Q x) ->
    (*-----------------------*)
    {{ P }} m {{ Q }}.
Proof.
  revert P P' Q Q'.
  induction m.
  - simpl; intros. apply (H1 _ (H (H0 H2))).
  - simpl. intros P P' Q Q' P0 P2 P3 P4.
    apply P2 in P4. apply P0 in P4 as [P5 [P6 [P7 P8]]].
    repeat split; auto. intro rs. eapply H; eauto.
Qed.

Lemma rule_ret : forall X (v : X) H (Q : X -> Prop),
    (H -> Q v) -> {{ H }} ret v {{ Q }}.
Proof. auto. Qed.

Lemma in_subtr : forall (l1 l2 : SubsetV) v, In v (subtr (Vertex_eq_dec G) l1 l2) -> In v l1.
Proof.
  induction l2; simpl; auto.
  intros. apply IHl2.
  destruct (ved v a).
  - subst. apply remove_In in H. contradiction.
  - apply (in_remove _ _ _ _ H).
Qed.

Lemma subtrV_nil l : subtrV l [] = l.
Proof. reflexivity. Qed.

Lemma In_subtrV : forall l1 l2 v, not (In v l2) -> In v l1 -> In v (subtrV l1 l2).
Proof.
  unfold subtrV.
  induction l2; simpl; auto.
  intros.
  assert (a <> v). intro. apply H. left; auto.
  apply in_in_remove; auto.
Qed.

Lemma In_subtrV' : forall l1 l2 v, In v (subtrV l1 l2) -> not (In v l2) /\ In v l1.
Proof.
  unfold subtrV.
  induction l2; simpl; auto.
  intros.
  assert (a <> v). intro. subst. apply (remove_In _ _ _ H).
  apply in_remove in H as [P0 P1]. apply IHl2 in P0 as [P0 P2].
  split; auto. intro. destruct H; auto.
Qed.

Lemma In_subtrV_bis : forall l1 l2 v, not (In v l2) /\ In v l1 <-> In v (subtrV l1 l2).
Proof.
  split.
  - intros [P0 P1]. apply In_subtrV; auto.
  - apply In_subtrV'.
Qed.

Lemma subtrV3_aux : forall l3 l1 l2 a,
    subtr ved (remove ved a (subtr ved l1 l2)) l3 = remove ved a (subtr ved (subtr ved l1 l2) l3).
Proof.
  induction l3; simpl; auto.
  intros. rewrite IHl3. rewrite remove_remove_comm. reflexivity.
Qed.

Lemma subtrV3 : forall l1 l2 l3, subtrV (subtrV l1 l2) l3 = subtrV l1 (l2 ++ l3).
Proof.
  unfold subtrV. induction l2; simpl; auto.
  intros. rewrite <- IHl2. apply subtrV3_aux.
Qed.

Lemma In_subtrV3_spec : forall l1 l2 l3 v,
    not (In v l3) -> In v (subtrV l1 l2) -> In v (subtrV l1 (l2 ++ l3)).
Proof.
  induction l2; simpl; intros.
  - apply In_subtrV; auto.
  - rewrite app_comm_cons. rewrite <- subtrV3.
    apply In_subtrV; auto.
Qed.

Lemma NoDup_subtrV_aux : forall l a, NoDup l -> NoDup (remove ved a l).
Proof.
  induction l; simpl; auto.
  intros. inversion_clear H.
  destruct (ved a0 a).
  - subst. apply IHl; auto.
  - constructor.
    2 : apply (IHl _ H1).
    intro. rewrite elem_of_list_In in H. apply in_remove in H as [P0 P1].
    apply H0. apply elem_of_list_In; auto.
Qed.

Lemma NoDup_subtrV : forall l1 l2, NoDup l1 -> NoDup (subtrV l1 l2).
Proof.
  unfold subtrV. induction l2; auto.
  intros. simpl. apply IHl2 in H. apply NoDup_subtrV_aux; auto.
Qed.

Lemma Termination_preserved : forall vs w ws,
    Termination vs (w :: ws) ->
    Termination (addV w vs) (rstep vs w ws).
Proof.
  unfold Termination. unfold Disjoint. intros. destruct H. split.
  - inversion_clear H. apply NoDup_app. repeat split; auto.
    + apply NoDup_subtrV. apply edges_NoDup.
    + intros. intro. rewrite elem_of_list_In in H.
      apply In_subtrV_bis in H as [P0 P1].
      apply P0. apply in_or_app. right. apply elem_of_list_In; auto.
  - inversion_clear H. intros v P0 P1.
    unfold rstep in P0. unfold subtrV in P0. rewrite elem_of_list_In in P0.
     rewrite elem_of_list_In in P1. apply in_app_or in P0. destruct P0.
    + apply In_subtrV_bis in H as [P0 P2]. apply P0. apply in_or_app. left; auto.
    + inversion P1.
      * subst. apply H1. apply elem_of_list_In. apply H.
      * apply H0 with v.
        apply elem_of_list_In. apply in_cons. auto.
        apply elem_of_list_In. auto.
Qed.

Program Definition reachables_workers (visited : SubsetV)
        (waiting : {ws : SubsetV | Termination visited ws}) : mon SubsetV :=
  match waiting with
  | [] => ret visited
  | w :: ws => reach (addV w visited) (rstep visited w ws)
  end.
Next Obligation.
  intros. simpl. destruct waiting. simpl in *.
  apply Termination_preserved. rewrite Heq_waiting. apply t.
Qed.

Lemma rstep_Invariant_lemma vs w ws :
  incl (subtrV (edges w) (addV w vs)) (rstep vs w ws).
Proof.
  intros v P0. unfold rstep. simpl in *.
  apply in_or_app.
  destruct (In_dec (Vertex_eq_dec G) v ws).
  right; auto.
  left. rewrite app_comm_cons. apply In_subtrV3_spec; auto.
Qed.

Program Lemma reachable_workers_spec : forall visited (waiting : {ws : SubsetV | Termination visited ws}),
    {{ Sound visited /\ Sound waiting /\ Invariant visited waiting }}
      reachables_workers visited waiting
      {{ fun rs => Sound rs /\ GComplete visited waiting rs }}.
Proof.
  unfold reachables_workers. intros visited waiting. destruct waiting. simpl in *.
  destruct x.
  - apply rule_ret. intros [Svs [Snil Inv]].
    split; auto. unfold GComplete. repeat split; auto.
    + unfold closed_under. intros. apply Inv.
      apply in_flat_map. exists v. split; auto.
    + intros a P0. inversion P0.
    + intros a P; auto.
  - eapply rule_consequence.
    apply rule_reach.
    + intros [P0 [P1 P2]]. repeat split; auto.
      * intros v0 P3. apply in_inv in P3.
        destruct P3. subst. apply P1. apply in_eq.
        apply P0. apply H.
      * intros v0 P3. unfold rstep in P3. apply in_app_or in P3. destruct P3.
        -- apply reachable_next with v.
           apply P1. apply in_eq. eapply in_subtr; eauto.
        -- apply P1. apply in_cons. apply H.
      * unfold Invariant in *.
        unfold neighbours in *. simpl. apply incl_app.
        -- intros v0 P3.
           destruct (In_dec (Vertex_eq_dec G) v0 (addV v visited)).
           apply in_or_app; auto.
           apply in_or_app. left.
           apply rstep_Invariant_lemma. apply In_subtrV; auto.
        -- apply incl_tran with (addV v x ++ visited); auto.
           apply incl_app. apply incl_cons. apply in_or_app. right. apply in_eq.
           apply incl_appl. unfold rstep. apply incl_appr. apply incl_refl.
           apply incl_appr. unfold addV. intros v0 P3. apply in_cons; auto.
    + simpl. intros v0 [P0 [P1 [P2 P3]]]. split; auto.
      repeat split; auto. apply incl_cons. apply P3. apply in_eq.
      apply incl_tran with (rstep visited v x); auto.
      apply incl_appr. apply incl_refl.
      intros v1 P4. apply P3. apply in_cons; auto.
Qed.


Definition measureV {X} (m : mon X): nat :=
  match m with
  | ret x => 0
  | Reach vs ws c => S (length (subtrV (vertices G) vs))
  end.

Lemma measureV_decrease ws w vs :
    Disjoint (w :: ws) vs -> length (subtrV (vertices G) (w :: vs)) < length (subtrV (vertices G) vs).
Proof.
  intros. apply remove_length_lt. apply In_subtrV.
  intro. eapply H. econstructor. apply elem_of_list_In; auto.
  apply vertices_exhaustive.
Qed.

Program Fixpoint runReach (m : mon SubsetV) {measure (measureV m)}: SubsetV :=
  match m with
  | ret x => x
  | Reach vs ws c => runReach (reachables_workers vs ws)
  end.
Next Obligation.
  intros. subst. simpl. unfold reachables_workers. destruct ws.
  simpl. destruct x.
  - simpl. lia.
  - simpl. destruct t. rewrite <- Nat.succ_lt_mono.
    eapply measureV_decrease; eauto.
Defined.
Next Obligation.
  simpl. apply measure_wf. apply lt_wf.
Defined.

Program Fixpoint run {X} (m : mon X): X :=
  match m with
  | ret x => x
  | Reach vs ws c =>
    let rs := runReach (reachables_workers vs ws) in
    run (c rs)
  end.

Program Definition reachables : SubsetV := run (reachables_workers emptyV start).
Next Obligation.
  simpl. split; auto. intros v P0 P1. inversion P1.
Defined.

End contents.

Program Definition graph : DiGraph := Build bool bool_dec [true;false] _ (fun b => if b then [true;false] else []) _.
Next Obligation.
  intros. destruct v. apply in_eq. apply in_cons. apply in_eq.
Defined.
Next Obligation.
  intros. simpl. destruct v. constructor. intro. inversion_clear H. inversion H0.
  apply NoDup_singleton. apply NoDup_nil. trivial.
Defined.

Program Definition test : {ws : list bool| Termination graph [] ws} := [true].
Next Obligation.
  simpl. split; auto. apply NoDup_singleton. intros v P0 P1. inversion P1.
Defined.

Definition print := reachables graph [true] (NoDup_singleton true) .

Compute print.
