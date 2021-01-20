Require Import FM.

(* Gensym avec la monade libre *)
Module gensym.
  Export FreeMonad.

  Inductive Fresh {ident} : Type -> Type :=
  | Gensym : Fresh ident.

  Definition gensym {ident} : mon Fresh ident := syntax_effect Gensym.

End gensym.

Module gensym_run.
  Export gensym.

  Definition ident := nat.

  Definition Fresh := @Fresh ident.

  Definition initial_state := 0.

  Fixpoint run {X} (m : mon Fresh X) : ident -> ident * X :=
    match m with
    | ret v => fun n => (n, v)
    | op Gensym f =>
      fun n => run (f n) (S n)
    end.

End gensym_run.


(* Raisonnement pour gensym avec la SL sur liste minimaliste *)
Module weakestpre_gensym.
  Export SepList.
  Export weakestpre.
  Export gensym_run.

  Definition iProp := @iPropGen (@hpropList ident) biInd.

  Definition op_spec X (m : Fresh X) : iProp * (X -> iProp) :=
    match m with
    | Gensym => (emp, IsFresh)
    end.

  Definition wp {X} (m : mon Fresh X) (Q : X -> iProp) : iProp :=
    @wp_gen _ _ _ op_spec _ m Q.

  Notation "'{{' P } } e {{ v ; Q } }" := (@triple _ _ _ op_spec _ P e (fun v => Q))
      (at level 20, format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").
  (** triple rules *)

  Lemma gensym_spec :
  ⊢{{ emp }} gensym {{ l; IsFresh l }}.
  Proof. unfold triple. simpl. auto. Qed.

End weakestpre_gensym.


(* Adequacy pour gensym avec la SL minimaliste *)
Module adequacy_gensym.
  Export weakestpre_gensym.

  Definition inject n := seq 0 n.

  Lemma inject_last : forall n, inject (S n) = inject n ++ [n].
  Proof. intros. unfold inject. rewrite seq_S. reflexivity. Qed.

  Lemma next_disjoint : forall n, list_disjoint (inject n) [n].
  Proof.
    intros n x y P0 P1 eq. subst. inversion P1. subst. apply in_seq in P0.
    destruct P0. lia. inversion H.
  Qed.

  Lemma adequacy {X} : forall (e : mon Fresh X) (Q : X -> iProp) n n' v,
      (heap_ctx (inject n) ⊢ wp e Q ) ->
      run e n = (n', v) ->
      (Q v) () (inject n').
  Proof.
    fix e 1.
    destruct e0; intros.
    - inversion H0; subst. apply soundness2. iApply H.
    - simpl in *. destruct f. eapply e.
      2 : apply H0.
      + iIntros "HA". rewrite inject_last.
        iDestruct (heap_ctx_split with "HA") as "[HA HB]". apply next_disjoint.
        iDestruct (H with "HA") as "[_ HA]".
        iApply ("HA" with "HB").
  Qed.

  Lemma adequacy_init {X} : forall (e : mon Fresh X) (Q : X -> iProp) (s' : nat) v ,
      (⊢ wp e Q) ->
      run e initial_state = (s', v) ->
      (Q v) () (inject s').
  Proof. intros. eapply adequacy; eauto. iIntros "_". auto. Qed.

  Lemma adequacy_triple {X} : forall (e : mon Fresh X) (Q : X -> iProp) n v n' H,
      (heap_ctx (inject n) ⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e n = (n', v) ->
      (Q v) () (inject n').
  Proof.
    intros. eapply adequacy; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iApply (H1 with "HA").
  Qed.

  Lemma adequacy_triple_init {X} : forall (e : mon Fresh X) (Q : X -> iProp) v n' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e initial_state = (n', v) ->
      (Q v) () (inject n').
  Proof.
    intros. eapply adequacy_init; eauto. iApply H1; eauto.
  Qed.

  Lemma use_adequacy {X} : forall (e : mon Fresh X) (Q : X -> iProp) v n' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e initial_state = (n', v) ->
      ∃ s, (Q v) () s.
  Proof.
    intros. exists (inject n'). apply (adequacy_triple_init _ _ _ _ _ H0 H1 H2).
  Qed.

  Lemma adequacy_wp_pure {X} : forall (e : mon Fresh X) (Q : X -> Prop) n v n',
      (heap_ctx (inject n) ⊢ wp e (fun v =>  ⌜Q v⌝)) ->
      run e n = (n', v) ->
      Q v.
  Proof.
    intros. apply (soundness1 (inject n')). iApply soundness3.
    eapply (adequacy _ _ _ _ _ H H0).
  Qed.

  Lemma adequacy_pure {X} : forall (e : mon Fresh X) (Q : X -> Prop) n v n' H,
      (heap_ctx (inject n) ⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e n = (n', v) ->
      Q v.
  Proof.
    intros. eapply adequacy_wp_pure; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iApply (H1 with "HA").
  Qed.

  Lemma adequacy_pure_init {X} : forall (e : mon Fresh X) (Q : X -> Prop) v s' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e initial_state = (s', v) ->
      Q v.
  Proof.
    intros. eapply adequacy_pure; eauto.
    iIntros "_". iApply H1; auto.
  Qed.

End adequacy_gensym.
