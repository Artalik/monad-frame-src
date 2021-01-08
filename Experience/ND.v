Require Import FM.

Module NDG.
  Export FreeMonad.

  Section op.
    Context {T : Type}.
    Context {ident : Type}.

    Inductive NDG : Type -> Type :=
    | Gensym : NDG ident
    | Fail : NDG T
    | Pick : NDG T.

    Definition fail : mon NDG T := syntax_effect Fail.
    Definition pick : mon NDG T := syntax_effect Pick.
    Definition gensym : mon NDG ident := syntax_effect Gensym.

  End op.

End NDG.

Module NDG_run.
  Export NDG.

  Definition initial_state : nat := 0.

  Definition NDG := @NDG bool nat.

  Fixpoint run {X} (m : mon NDG X) : nat -> nat * list X :=
    match m with
    | ret v => fun n => (n,[v])
    | op Fail f => fun n => (n,[])
    | op Pick f =>
      fun n =>
        let (m, l) := run (f true) n in
        let (m', r) := run (f false) n in
        (m `max` m', l ++ r)
    | op Gensym f =>
      fun n => run (f n) (S n)
    end.

End NDG_run.

(* Raisonnement pour gensym avec la SL sur liste minimaliste *)
Module weakestpre_NDG.
  Export SepList.
  Export weakestpre.
  Export NDG_run.

  Definition iProp := @iPropGen (@hpropList nat) biInd.

  Definition op_spec X (m : NDG X) : iProp * (X -> iProp) :=
    match m with
    | Fail
    | Pick => (emp, (fun _ => emp))
    | Gensym => (emp, IsFresh)
    end.

  Definition wp {X} (m : mon NDG X) (Q : X -> iProp) : iProp :=
    @wp_gen _ _ _ op_spec _ m Q.

  Notation "'{{' P } } e {{ v ; Q } }" := (@triple _ _ _ op_spec _ P e (fun v => Q))
      (at level 20, format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").
  (** triple rules *)

  Lemma pick_spec :
  ⊢{{ emp }} pick {{ _; emp }}.
  Proof. unfold triple. simpl. auto. Qed.

  Lemma gensym_spec :
  ⊢{{ emp }} gensym {{ v; IsFresh v }}.
  Proof. unfold triple. simpl. auto. Qed.

  Lemma fail_spec :
  ⊢{{ emp }} fail {{ _; emp }}.
  Proof. unfold triple. simpl. auto. Qed.

End weakestpre_NDG.


(* Adequacy pour NDG avec booléen en ND *)
Module adequacy_NDG.
  Export weakestpre_NDG.

  Definition inject n := seq 0 n.

  Lemma inject_last : forall n, inject (S n) = inject n ++ [n].
  Proof. apply seq_S_end_app. Qed.

  Lemma next_disjoint : forall n, list_disjoint (inject n) [n].
  Proof.
    intros n x y P0 P1 eq. subst. inversion P1. subst. apply in_seq in P0.
    destruct P0. lia. inversion H.
  Qed.

  Lemma absorb_out : forall X l (Q : X -> iProp),
      ⊢ <absorb> ([∧ list] v ∈ l, <absorb> Q v) -∗ [∧ list] v ∈ l, <absorb> Q v.
  Proof.
    induction l; simpl; iIntros "*"; auto. iIntros "HA".
    iSplit. iDestruct "HA" as ">[$ _]".
    iApply IHl. iDestruct "HA" as ">[_ HA]". iApply "HA".
  Qed.

  Lemma inject_lt : forall n2 n1, n1 < n2 -> ⊢ heap_ctx (inject n2) -∗ <absorb> heap_ctx (inject n1).
  Proof.
    induction n2; simpl; intros.
    - inversion H.
    - rewrite inject_last. iIntros "HA".
      iDestruct (heap_ctx_split with "HA") as "[HA HB]". apply next_disjoint.
      destruct (Nat.eq_dec n1 n2).
      + subst. iApply "HA".
      + iApply (IHn2 with "HA"). lia.
  Qed.

  Lemma demonic_adequacy {X} : forall (e : mon NDG X) (Q : X -> iProp) n n' l',
      (heap_ctx (inject n) ⊢ wp e Q) ->
      run e n = (n',l') ->
      ([∧ list] v ∈ l' , <absorb> Q v) () (inject n').
  Proof.
    induction e; intros.
    - inversion H0; subst. apply soundness2. simpl in *. iIntros "HA". iSplit; auto.
      iApply (H with "HA").
    - destruct e.
      + simpl in *. eapply H.
        2 : apply H1.
        iIntros "HA". rewrite inject_last.
        iDestruct (heap_ctx_split with "HA") as "[HA HB]". apply next_disjoint.
        iDestruct (H0 with "HA") as "[_ HA]".
        iApply ("HA" with "HB").
      + inversion H1. subst. clear H1. simpl. apply soundness2. auto.
      + simpl in *. destruct (run (m true) n) eqn:?. destruct (run (m false) n) eqn:?.
        inversion H1. subst. clear H1.
        assert (([∧ list] v ∈ l, <absorb> Q v) () (inject n0)).
        eapply H. 2 : apply Heqp.
        iIntros "HA". iDestruct (H0 with "HA") as "[_ HA]". iApply "HA"; auto.
        assert (([∧ list] v ∈ l0, <absorb> Q v) () (inject n1)).
        eapply H. 2 : apply Heqp0.
        iIntros "HA". iDestruct (H0 with "HA") as "[_ HA]". iApply "HA"; auto.
        apply soundness2. iIntros "HA". iApply big_andL_app.
        destruct (Nat.max_spec n0 n1) as [[P0 P1]|[P0 P1]]; rewrite P1; iSplit.
        * iApply absorb_out. iDestruct (inject_lt with "HA") as ">HA"; eauto.
          iModIntro. apply soundness3 in H1. iApply (H1 with "HA").
        * apply soundness3 in H2. iApply (H2 with "HA").
        * apply soundness3 in H1. iApply (H1 with "HA").
        * destruct (Nat.eq_dec n1 n0).
          -- subst. apply soundness3 in H2. iApply (H2 with "HA").
          -- iApply absorb_out. iDestruct (inject_lt with "HA") as ">HA".
             instantiate (1 := n1). lia.
             iModIntro. apply soundness3 in H2. iApply (H2 with "HA").
  Qed.

  Lemma demonic_adequacy_init {X} : forall (e : mon NDG X) (Q : X -> iProp) (n' : nat) l,
      (⊢ wp e Q) ->
      run e initial_state = (n', l) ->
      ([∧ list] v ∈ l , <absorb> Q v) () (inject n').
  Proof. intros. eapply demonic_adequacy; eauto. iIntros "_". auto. Qed.

  Lemma demonic_adequacy_triple {X} : forall (e : mon NDG X) (Q : X -> iProp) n l n' H,
      (heap_ctx (inject n) ⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e n = (n', l) ->
      ([∧ list] v ∈ l , <absorb> Q v) () (inject n').
  Proof.
    intros. eapply demonic_adequacy; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iApply (H1 with "HA").
  Qed.

  Lemma demonic_adequacy_triple_init {X} : forall (e : mon NDG X) (Q : X -> iProp) l n' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e initial_state = (n', l) ->
      ([∧ list] v ∈ l , <absorb> Q v) () (inject n').
  Proof.
    intros. eapply demonic_adequacy_init; eauto. iApply H1; eauto.
  Qed.

  Lemma demonic_adequacy_wp_pure {X} : forall (e : mon NDG X) (Q : X -> Prop) n l n',
      (heap_ctx (inject n) ⊢ wp e (fun v =>  ⌜Q v⌝)) ->
      run e n = (n', l) ->
      (forall x, x ∈ l -> Q x).
  Proof.
    intros. apply (soundness1 (inject n')). iApply soundness3.
    epose (demonic_adequacy _ _ _ _ _ H H0).
    apply soundness2. apply soundness3 in m. iIntros "HA". iDestruct (m with "HA") as "HA".
    iDestruct (big_andL_elem_of with "HA") as ">$"; eauto.
  Qed.

  Lemma demonic_adequacy_pure {X} : forall (e : mon NDG X) (Q : X -> Prop) n l n' H,
      (heap_ctx (inject n) ⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e n = (n', l) ->
      (forall x, x ∈ l -> Q x).
  Proof.
    intros. eapply demonic_adequacy_wp_pure; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iApply (H1 with "HA").
  Qed.

  Lemma demonic_adequacy_pure_init {X} : forall (e : mon NDG X) (Q : X -> Prop) l s' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e initial_state = (s', l) ->
      (forall x, x ∈ l -> Q x).
  Proof.
    intros. eapply demonic_adequacy_pure; eauto.
    iIntros "_". iApply H1; auto.
  Qed.

End adequacy_NDG.
