Require Import Coqlib Integers Floats Errors Globalenvs.
Require Import AST Linking Values Memory Csyntax Clight Divers.

Notation "a ! b" := (Maps.PTree.get b a) (at level 1).

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Parameter first_unused_ident: unit -> ident.

Definition initial_generator (x: unit) : generator :=
  mkgenerator (first_unused_ident x) nil.

Definition gensym (ty: type): mon ident :=
  fun (g: generator) =>
    Res (gen_next g)
        (mkgenerator (Pos.succ (gen_next g)) ((gen_next g, ty) :: gen_trail g))
        (Ple_succ (gen_next g)).

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

Inductive tr_expr: temp_env -> destination -> Csyntax.expr -> list statement -> expr -> list ident -> Prop :=
  | tr_var: forall le dst id ty tmp,
      tr_expr le dst (Csyntax.Evar id ty)
              (final dst (Evar id ty)) (Evar id ty) tmp
  | tr_val_effect: forall le v ty any tmp,
      tr_expr le For_effects (Csyntax.Eval v ty) nil any tmp
  | tr_val_value: forall le v ty a tmp,
      typeof a = ty ->
      (forall le',
         (forall id, In id tmp -> le'!id = le!id) ->
         eval_expr le' a v) ->
      tr_expr le For_val (Csyntax.Eval v ty)
                           nil a tmp
  | tr_val_set: forall le sd v ty a any tmp,
      typeof a = ty ->
      (forall le',
         (forall id, In id tmp -> le'!id = le!id) ->
         eval_expr le' a v) ->
      tr_expr le (For_set sd) (Csyntax.Eval v ty)
                   (do_set sd a) any tmp
  | tr_seqand_set: forall le sd e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In (sd_temp sd) tmp ->
      tr_expr le (For_set sd) (Csyntax.Eseqand e1 e2 ty)
                    (sl1 ++ makeif a1 (makeseq sl2)
                                      (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil)
                    any tmp
  | tr_condition_val: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (SDbase ty ty t)) e2 sl2 a2 tmp2 ->
      tr_expr le (For_set (SDbase ty ty t)) e3 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 ->
      list_disjoint tmp1 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp ->  incl tmp3 tmp -> In t tmp ->
      tr_expr le For_val (Csyntax.Econdition e1 e2 e3 ty)
                      (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                      (Etempvar t ty) tmp
  | tr_paren_val: forall le e1 tycast ty sl1 a1 t tmp,
      tr_expr le (For_set (SDbase tycast ty t)) e1 sl1 a1 tmp ->
      In t tmp ->
      tr_expr le For_val (Csyntax.Eparen e1 tycast ty)
                       sl1
                       (Etempvar t ty) tmp
  | tr_paren_set: forall le t sd e1 tycast ty sl1 a1 tmp any,
      tr_expr le (For_set (SDcons tycast ty t sd)) e1 sl1 a1 tmp ->
      In t tmp ->
      tr_expr le (For_set sd) (Csyntax.Eparen e1 tycast ty) sl1 any tmp.

Definition add_dest (dst: destination) (tmps: list ident) :=
  match dst with
  | For_set sd => sd_temp sd :: tmps
  | _ => tmps
  end.

Definition within (id: ident) (g1 g2: generator) : Prop :=
  Ple (gen_next g1) id /\ Plt id (gen_next g2).

Definition contained (l: list ident) (g1 g2: generator) : Prop :=
  forall id, In id l -> within id g1 g2.

Definition dest_below (dst: destination) (g: generator) : Prop :=
  match dst with
  | For_set sd => Plt (sd_temp sd) g.(gen_next)
  | _ => True
  end.

Lemma transl_meets_spec:
   (forall r dst g sl a g' I,
    transl_expr dst r g = Res (sl, a) g' I ->
    dest_below dst g ->
    exists tmps, (forall le, tr_expr le dst r sl a (add_dest dst tmps)) /\ contained tmps g g').
Admitted.
