Require Import Coqlib Integers Floats Errors Globalenvs.
Require Import AST Linking Values Memory Csyntax Clight.

Inductive set_destination : Type :=
  | SDbase (tycast ty: type) (tmp: AST.ident)
  | SDcons (tycast ty: type) (tmp: AST.ident) (sd: set_destination).

Inductive destination : Type :=
  | For_val
  | For_effects
  | For_set (sd: set_destination).


Fixpoint do_set (sd: set_destination) (a: expr) : list statement :=
  match sd with
  | SDbase tycast ty tmp => Sset tmp (Ecast a tycast) :: nil
  | SDcons tycast ty tmp sd' => Sset tmp (Ecast a tycast) :: do_set sd' (Etempvar tmp ty)
  end.

Definition finish (dst: destination) (sl: list statement) (a: expr) :=
  match dst with
  | For_val => (sl, a)
  | For_effects => (sl, a)
  | For_set sd => (sl ++ do_set sd a, a)
  end.

Definition sd_temp (sd: set_destination) :=
  match sd with SDbase _ _ tmp => tmp | SDcons _ _ tmp _ => tmp end.
Definition sd_seqbool_val (tmp: AST.ident) (ty: type) :=
  SDbase type_bool ty tmp.
Definition sd_seqbool_set (ty: type) (sd: set_destination) :=
  let tmp :=  sd_temp sd in SDcons type_bool ty tmp sd.

 
Fixpoint eval_simpl_expr (a: expr) : option val :=
  match a with
  | Econst_int n _ => Some(Vint n)
  | Econst_float n _ => Some(Vfloat n)
  | Econst_single n _ => Some(Vsingle n)
  | Econst_long n _ => Some(Vlong n)
  | Ecast b ty =>
      match eval_simpl_expr b with
      | None => None
      | Some v => sem_cast v (typeof b) ty Mem.empty
      end
  | _ => None
  end.

Function makeif (a: expr) (s1 s2: statement) : statement :=
  match eval_simpl_expr a with
  | Some v =>
      match bool_val v (typeof a) Mem.empty with
      | Some b => if b then s1 else s2
      | None   => Sifthenelse a s1 s2
      end
  | None => Sifthenelse a s1 s2
  end.

Fixpoint makeseq_rec (s: statement) (l: list statement) : statement :=
  match l with
  | nil => s
  | s' :: l' => makeseq_rec (Ssequence s s') l'
  end.

Definition makeseq (l: list statement) : statement := makeseq_rec Sskip l.

Definition dummy_expr := Econst_int Int.zero type_int32s.


Definition final (dst: destination) (a: expr) : list statement :=
  match dst with
  | For_val => nil
  | For_effects => nil
  | For_set sd => do_set sd a
  end.
