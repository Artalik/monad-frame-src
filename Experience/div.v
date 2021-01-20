Require Import Error.

Import adequacy_error.

Definition div42 (m : nat) : mon Error nat :=
  match m with
  | 0 => raise
  | S n => ret (42 / m)
  end.

Lemma div42_spec m :
  ⊢ {{ emp }} div42 m {{ v; ⌜v = 42 / m ⌝ }}.
Proof.
  unfold div42. destruct m.
  - iApply consequence. apply raise_spec.
    all : eauto.
  - apply ret_spec. eauto.
Qed.
