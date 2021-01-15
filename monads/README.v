Require Import Monads.Monad.
Require Import Monads.State.
Require Import Monads.Cont.
Require Import Monads.Error.
Require Import Nat.

Section Example.
Context `{m: Type -> Type}.
Context `{Monad m}.
Context `{MonadState nat m}.

Definition adder : m unit :=
  bind get (fun n =>
  bind (put (n + n)) (fun _ =>
  ret tt)).

End Example.

(* Direct semantics *)
Definition adder1 : stateT nat ident unit
  := adder.

(* Dijkstra state *)
Definition adder2 : stateT nat (cont Prop) unit
               (* = nat -> (nat * unit -> Prop) -> Prop *)
  := adder.

Definition Post2 := False.

Variable n0 : nat.
Variable post : unit * nat -> Prop.
Check (runCont (runStateT adder2 n0) post).

(* Same as above ? *)

Definition adder3 : cont (nat -> Prop) unit
  (* = (unit -> nat -> Prop) -> nat -> Prop *)
  := adder.

Check ((runCont adder3) (fun tt n => post (tt, n))).


Definition adder4 : cont Prop unit
  (* = (unit -> Prop) -> Prop *)
  := adder.

Variable post4 : unit -> Prop.

Check ((runCont adder4) post4).

(* **************************************************************** *)

Section Example2.
Context `{m: Type -> Type}.
Context `{Monad m}.
Context `{MonadError unit m}.



Definition divider (n: nat) : m nat :=
  if eqb n 0 then raise tt
  else ret (42 / n).

End Example2.

(* Direct semantics *)
Definition divider1 n : errorT unit ident nat
                     (* = unit + nat *)
  := divider n.

(* Exception visible *)
Definition divider2 n : errorT unit (cont Prop) nat
                     (* = (nat + unit -> Prop) -> Prop *)
  := divider n.

Variable P2 : nat + unit -> Prop.
Variable n : nat.
Check (runCont (runErrorT _ _ _ (divider2 n)) P2).

(* Exception invisible: raise = assert False *)
Definition divider3 n : contFalse nat
                     (* = (nat -> Prop) -> Prop *)
  := divider n.

Variable P3 : nat -> Prop.
Check (runCont (divider3 n) P3).


(* Exception invisible: raise = assert True (partial correctness) *)
Definition divider4 n : contTrue nat
                     (* = (nat -> Prop) -> Prop *)
  := divider n.

Check (runCont (divider4 n) P3).
(* Eval lazy in runCont (divider4 n) P3. *)

(* https://cakeml.org/vstte18.pdf *)
(* liveness ITP'18 https://cakeml.org/publications.html *)
(* https://cakeml.org/ijcar18.pdf *)
