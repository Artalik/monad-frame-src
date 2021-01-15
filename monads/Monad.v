(* https://github.com/coq-community/coq-ext-lib/blob/master/theories/Structures/Monad.v *)

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
  { ret : forall {t : Type@{d}}, t -> m t
  ; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
  }.
Module MonadBaseNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope.

  Notation "e1 ;; e2" := (@bind _ _ _ _ e1%monad (fun _ => e2%monad))%monad
    (at level 61, right associativity) : monad_scope.

End MonadBaseNotation.

Module MonadLetNotation.

  Export MonadBaseNotation.

  Notation "'let*' x ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : monad_scope.

End MonadLetNotation.

(* https://github.com/coq-community/coq-ext-lib/blob/159c36111a95e5e587020c9f10b2e2ecd9fa3914/theories/Data/Monads/IdentityMonad.v *)

Section Ident.
  Inductive ident A := mkIdent { unIdent : A }.

  Global Instance Monad_ident : Monad ident :=
  { ret  := fun _ v => mkIdent v
  ; bind := fun _ _ c f => f (unIdent c)
  }.

End Ident.

Arguments mkIdent {A} (_).
Arguments unIdent {A} (_).
