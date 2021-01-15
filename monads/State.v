(* https://github.com/coq-community/coq-ext-lib/blob/159c36111a95e5e587020c9f10b2e2ecd9fa3914/theories/Structures/MonadState.v *)

Require Import Monads.Monad.

Set Implicit Arguments.
Set Strict Implicit.

Class MonadState (T : Type) (m : Type -> Type) : Type :=
{ get : m T
; put : T -> m unit
}.

Arguments get {_ m MS} : rename.
Arguments put {_ m MS} _ : rename.


(* https://github.com/coq-community/coq-ext-lib/blob/159c36111a95e5e587020c9f10b2e2ecd9fa3914/theories/Data/Monads/StateMonad.v *)

Section StateType.
  Variable S : Type.
  Variable m : Type -> Type.
  Variable M : Monad m.

  Record stateT (t : Type) : Type := mkStateT
  { runStateT : S -> m (t * S)%type }.

  Global Instance Monad_stateT : Monad stateT :=
  { ret := fun _ x => mkStateT (fun s => @ret _ M _ (x,s))
  ; bind := fun _ _ c1 c2 =>
    mkStateT (fun s =>
      @bind _ M _ _ (runStateT c1 s) (fun vs =>
        let (v,s) := vs in
        runStateT (c2 v) s))
  }.

  Global Instance MonadState_stateT : MonadState S stateT :=
  { get := mkStateT (fun x => ret (x,x))
  ; put := fun v => mkStateT (fun _ => ret (tt, v))
  }.

End StateType.
