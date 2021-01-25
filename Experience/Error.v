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

Require Import SepProp.

(* Raisonnement pour error avec la SL sur liste minimaliste *)
Module weakestpre_error.
  Export SepProp.
  Export weakestpre.
  Export Error_run.

  (* unit est le type des elements de la liste*)
  Definition iProp := @iPropGen hpropProp biInd.

  (* retourne (pre,post) *)
  Definition op_spec X (m : Error X) : iProp * (X -> iProp) :=
    match m with
    | Gensym => (bi_emp, (fun _ => False)%I)
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

  Lemma adequacy {X} : forall (e : mon Error X) (Q : X -> iProp) v,
      (⊢ wp e Q ) ->
      run e = Some v ->
      (Q v) ().
  Proof.
    fix e 1.
    destruct e0; intros.
    - inversion H0; subst. apply soundness2. iApply H.
    - simpl in *. destruct e0. inversion H0.
  Qed.

  Lemma adequacy_triple {X} : forall (e : mon Error X) (Q : X -> iProp) v H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e = Some v ->
      (Q v) ().
  Proof.
    intros. eapply adequacy; eauto. iApply H1. iApply H0.
  Qed.

End adequacy_error.
