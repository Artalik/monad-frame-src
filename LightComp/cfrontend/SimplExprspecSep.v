Require Import Coqlib Integers Floats Errors Globalenvs.
Require Import AST Linking Values Memory Csyntax Clight Divers MoSel Locally.

Notation "a ! b" := (Maps.PTree.get b a) (at level 1).

Import gensym.
Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Fixpoint transl_expr (dst: destination) (a: Csyntax.expr) : mon (list statement * expr) :=
  match a with
  | Csyntax.Evar x ty =>
      ret (finish dst nil (Evar x ty))
  | Csyntax.Eval (Vint n) ty =>
      ret (finish dst nil (Econst_int n ty))
  | Csyntax.Eval (Vfloat n) ty =>
      ret (finish dst nil (Econst_float n ty))
  | Csyntax.Eval (Vsingle n) ty =>
      ret (finish dst nil (Econst_single n ty))
  | Csyntax.Eval (Vlong n) ty =>
      ret (finish dst nil (Econst_long n ty))
  | Csyntax.Eval _ ty =>
      error (msg "SimplExpr.transl_expr: Eval")
  | Csyntax.Eseqand r1 r2 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      match dst with
      | For_set sd =>
          do (sl2, a2) <- transl_expr (For_set (sd_seqbool_set ty sd)) r2;
          ret (sl1 ++
               makeif a1 (makeseq sl2) (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil,
               dummy_expr)
      | _ =>
        error (msg "SimplExpr.transl_expr: Econd")
      end
  | Csyntax.Econdition r1 r2 r3 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      match dst with
      | For_val =>
          do t <- gensym ty;
          do (sl2, a2) <- transl_expr (For_set (SDbase ty ty t)) r2;
          do (sl3, a3) <- transl_expr (For_set (SDbase ty ty t)) r3;
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               Etempvar t ty)
      | _ =>
        error (msg "SimplExpr.transl_expr: Econd")
      end
  | Csyntax.Eparen r1 tycast ty =>
      error (msg "SimplExpr.transl_expr: paren")
  end.

Import adequacy.

Fixpoint tr_expr (le : temp_env) (dst : destination) (e : Csyntax.expr)
           (sl : list statement ) (a : expr) : iProp :=
    <absorb>
    match e with
    | Csyntax.Evar id ty =>
      \⌜ sl = final dst (Evar id ty) /\  a = Evar id ty ⌝
    | Csyntax.Eval v ty =>
      match dst with
      | For_effects => ⌜sl = nil⌝
      | For_val =>
        locally le (fun le' => ⌜eval_expr le' a v⌝) ∗ ⌜ typeof a = ty /\ sl = nil ⌝
      | For_set sd => ∃ a,
  locally le (fun le' => ⌜eval_expr le' a v⌝) ∗ ⌜ typeof a = ty /\ sl = do_set sd a ⌝
end
 
| Csyntax.Eseqand e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sl2 a2 sl3 a3 t,
    \s t ∗
     tr_expr le For_val e1 sl2 a2 ∗
     tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl3 a3 ∗
     \⌜ sl = sl2 ++ makeif a2 (makeseq sl3) (Sset t (Econst_int Int.zero ty)) :: nil /\
               a = Etempvar t ty ⌝
| For_effects =>
  ∃ sl2 a2 sl3 a3, tr_expr le For_val e1 sl2 a2 ∗
  tr_expr le For_effects e2 sl3 a3  ∗
  \⌜  sl = sl2 ++ makeif a2 (makeseq sl3) Sskip :: nil ⌝
| For_set sd =>
  ∃ sl2 a2 sl3 a3,
    tr_expr le For_val e1 sl2 a2
    ∗ tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl3 a3
    ∗ ⌜ sl = sl2 ++ makeif a2 (makeseq sl3) (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil ⌝
  end

| Csyntax.Econdition e1 e2 e3 ty =>
  match dst with
  | For_val =>
    ∃ sl2 a2 sl3 a3 sl4 a4 t,
    \s t ∗
     tr_expr le For_val e1 sl2 a2 ∗
     tr_expr le (For_set (SDbase ty ty t)) e2 sl3 a3 ∗
     tr_expr le (For_set (SDbase ty ty t)) e3 sl4 a4 ∗
     \⌜ sl = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil /\ a = Etempvar t ty⌝
| For_effects =>
  ∃ sl2 a2 sl3 a3 sl4 a4,
    tr_expr le For_val e1 sl2 a2  ∗
    tr_expr le For_effects e2 sl3 a3 ∗
    tr_expr le For_effects e3 sl4 a4 ∗
    \⌜ sl = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil ⌝
| For_set sd =>
  ∃ sl2 a2 sl3 a3 sl4 a4 t,
    \s t ∗
     tr_expr le For_val e1 sl2 a2  ∗
     tr_expr le (For_set (SDcons ty ty t sd)) e2 sl3 a3 ∗
     tr_expr le (For_set (SDcons ty ty t sd)) e3 sl4 a4 ∗
     ⌜ sl = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil ⌝
  end




| Csyntax.Eparen e1 tycast ty =>
  match dst with
  | For_val =>
    ∃ a2 t, \s t ∗
     tr_expr le (For_set (SDbase tycast ty t)) e1 sl a2 ∗
     ⌜ a = Etempvar t ty ⌝
| For_effects =>
  ∃ a2, tr_expr le For_effects e1 sl a2
| For_set sd =>
  ∃ a2 t,tr_expr le (For_set (SDcons tycast ty t sd)) e1 sl a2
  end
end.
  
Lemma transl_meets_spec :
  forall r dst, ⊢ {{ emp }} transl_expr dst r {{ res, RET res; ∀ le, tr_expr le dst r res.1 res.2 }}.
Admitted.
