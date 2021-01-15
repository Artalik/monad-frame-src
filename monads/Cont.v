(* https://github.com/coq-community/coq-ext-lib/blob/159c36111a95e5e587020c9f10b2e2ecd9fa3914/theories/Structures/MonadCont.v *)
Require Import Monads.Monad.
Require Import Monads.State.
Require Import Monads.Error.

Set Implicit Arguments.
Set Strict Implicit.

Class MonadCont (m : Type -> Type) : Type :=
{ callCC : forall a b, ((a -> m b) -> m a) -> m a }.

Arguments callCC {m Cm} {_ _} _ : rename.

(* https://github.com/coq-community/coq-ext-lib/blob/159c36111a95e5e587020c9f10b2e2ecd9fa3914/theories/Data/Monads/ContMonad.v *)


Section ContType.
  Variable Ans : Type.

  Record cont (t : Type) : Type := mkCont
  { runCont : (t -> Ans) -> Ans }.


  Global Instance Monad_cont : Monad cont :=
  { ret := fun _ x => mkCont (fun k => k x)
  ; bind := fun u c1 v c2 =>
    mkCont (fun c =>
     runCont v (fun a => runCont (c2 a) c))
  }.

  Global Instance Cont_cont : MonadCont cont :=
  { callCC := fun _ _ f => mkCont (fun c => runCont (f (fun x => mkCont (fun _ => c x))) c)
  }.

End ContType.

Section ContState.
  Variable S : Type.

  (* Effect-handler interpretation of State *)
  Global Instance State_cont : MonadState S (cont (S -> S)).
  split.
  - apply mkCont.
    intros k s.
    apply (k s s).
  - intros s.
    apply mkCont.
    intros k _.
    apply (k tt s).
  Defined.

  (* Weakest-pre interpretation of State *)
  Global Instance State_wp : MonadState S (cont (S -> Prop)).
  split.
  - apply mkCont. 
    intros k s.
    apply (k s s).
  - intros s. 
    apply mkCont. 
    intros k _.
    apply (k tt s).
  Defined.

  (* Under-specification of State as 'anything goes' *)
  Global Instance State_any : MonadState S (cont Prop).
  split.
  - apply mkCont. 
    intros k.
    refine (exists s, _).
    apply k. eauto.
  - intros s. 
    apply mkCont. 
    intros k.
    apply (k tt).
  Defined.

End ContState.

Section ContError.
  Variable E : Type.

  Definition contFalse := cont Prop.
  Definition contTrue := cont Prop.

  (* `raise` as an `assert False` *)
  Global Instance MonadError_wp1 : MonadError E contFalse :=
    { raise := fun _ e => mkCont (fun k => False) }.

  (* Partial correctness *)
  Global Instance MonadError_wp2 : MonadError E contTrue :=
  { raise := fun _ e => mkCont (fun k => True)
  }.

End ContError.
