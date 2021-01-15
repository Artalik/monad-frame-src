Require Import Monads.Monad.

Class MonadError (E : Type) (m : Type -> Type) : Type :=
{ raise : forall {T}, E -> m T
(* ; catch : forall {T}, m T -> (E -> m T) -> m T *)
}.

Arguments raise {E m mE} {_} _ : rename.
(* Arguments catch {E m mE} {_} _ _ : rename. *)

Section ErrorType.
  Variable E : Type.
  Variable m : Type -> Type.
  Variable M : Monad m.

  Record errorT (t : Type) : Type := mkErrorT
  { runErrorT : m (t + E)%type }.


  Global Instance Monad_errorT : Monad errorT :=
  { ret := fun _ x => mkErrorT _ (@ret _ M _ (inl x))
  ; bind := fun _ _ c1 c2 =>
    mkErrorT _ (@bind _ M _ _ (runErrorT _ c1) (fun vs =>
                                                match vs with
| inl v => runErrorT _ (c2 v)
| inr e => ret (inr e)
                                                end
))  }.

  Global Instance MonadError_errorT : MonadError E errorT :=
  { raise := fun _ e => mkErrorT _ (@ret _ M _  (inr e))
  }.

End ErrorType.
