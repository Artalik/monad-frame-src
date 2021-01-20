Require Import FM.

(* Gensym avec la monade libre *)
Module Error.
  Export FreeMonad.

  Inductive Error (X : Type) : Type :=
  | Raise : Error X.

  Definition raise {X} : mon Error X := syntax_effect (Raise X).

End Error.

Module Error_run.
  Export Error.

  Definition run {X} (m : mon Error X) : option X :=
    match m with
    | ret v => Some v
    | op (Raise _) f => None
    end.

End Error_run.

(* Raisonnement pour error avec la SL sur liste minimaliste *)
Module weakestpre_error.
  Export SepList.
  Export weakestpre.
  Export Error_run.

  (* unit est le type des elements de la liste*)
  Definition iProp := @iPropGen (@hpropList unit) biInd.

  (* retourne (pre,post) *)
  Definition op_spec X (m : Error X) : iProp * (X -> iProp) :=
    match m with
    | Gensym => (emp, fun _ => False)
    end.

  Definition wp {X} (m : mon Error X) (Q : X -> iProp) : iProp :=
    @wp_gen _ _ _ op_spec _ m Q.

  Notation "'{{' P } } e {{ v ; Q } }" := (@triple _ _ _ op_spec _ P e (fun v => Q))
      (at level 20, format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").
  (** triple rules *)

  Lemma raise_spec {X} :
  ⊢{{ emp }} (raise : mon Error X) {{ v ; False }}.
  Proof. unfold triple. simpl. auto. Qed.

End weakestpre_error.

(* Adequacy pour gensym avec la SL minimaliste *)
Module adequacy_error.
  Export weakestpre_error.

  Lemma adequacy {X} : forall (e : mon Error X) (Q : X -> iProp) v l,
      (heap_ctx l ⊢ wp e Q ) ->
      run e = Some v ->
      (Q v) () l.
  Proof.
    fix e 1.
    destruct e0; intros.
    - inversion H0; subst. apply soundness2. iApply H.
    - simpl in *. destruct e0. inversion H0.
  Qed.

  Lemma adequacy_init {X} : forall (e : mon Error X) (Q : X -> iProp) v,
      (⊢ wp e Q) ->
      run e  = Some v ->
      (Q v) () nil.
  Proof. intros. eapply adequacy; eauto. Qed.

  Lemma adequacy_triple {X} : forall (e : mon Error X) (Q : X -> iProp) v H l,
      (heap_ctx l ⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e = Some v ->
      (Q v) () l.
  Proof.
    intros. eapply adequacy; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iApply (H1 with "HA").
  Qed.

  Lemma adequacy_triple_init {X} : forall (e : mon Error X) (Q : X -> iProp) v H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e = Some v ->
      (Q v) () nil.
  Proof.
    intros. eapply adequacy_init; eauto. iApply H1; eauto.
  Qed.

  Lemma use_adequacy {X} : forall (e : mon Error X) (Q : X -> iProp) v H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e = Some v ->
      ∃ s, (Q v) () s.
  Proof.
    intros. exists nil. apply (adequacy_triple_init _ _ _ _ H0 H1 H2).
  Qed.

  Lemma adequacy_wp_pure {X} : forall (e : mon Error X) (Q : X -> Prop) v l,
      (heap_ctx l ⊢ wp e (fun v =>  ⌜Q v⌝)) ->
      run e = Some v ->
      Q v.
  Proof.
    intros. apply (soundness1 l). iApply soundness3.
    eapply (adequacy _ _ _ _ H H0).
  Qed.

  Lemma adequacy_pure {X} : forall (e : mon Error X) (Q : X -> Prop) v H l,
      (heap_ctx l ⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e = Some v ->
      Q v.
  Proof.
    intros. eapply adequacy_wp_pure; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iApply (H1 with "HA").
  Qed.

  Lemma adequacy_pure_init {X} : forall (e : mon Error X) (Q : X -> Prop) v H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e = Some v ->
      Q v.
  Proof.
    intros. eapply adequacy_pure; eauto.
    iIntros "_". iApply H1; auto.
  Qed.

End adequacy_error.
