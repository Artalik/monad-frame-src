(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Relational specification of expression simplification. *)

Require Import Coqlib (* Maps  *)Errors Integers Floats.
Require Import AST Linking Memory.
Require Import Ctypes Cop Csyntax Clight SimplExpr.
Require Import MoSel.
Import Maps.PTree.
Export weakestpre_gensym.

Section SPEC.

  Local Open Scope gensym_monad_scope.
  Notation "a ! b" := (get b a) (at level 1).
  (** * Relational specification of the translation. *)

  (** ** Translation of expressions *)

  (** This specification covers:
- all cases of [transl_lvalue] and [transl_rvalue];
- two additional cases for [Csyntax.Eparen], so that reductions of [Csyntax.Econdition]
  expressions are properly tracked;
- three additional cases allowing [Csyntax.Eval v] C expressions to match
  any Clight expression [a] that evaluates to [v] in any environment
  matching the given temporary environment [le].
   *)

  Ltac tac2 :=
    match goal with
    | |- bi_emp_valid ({{ _ }} bind2 _ (fun _ _ => _) {{ _, RET _; _ }}) =>
      eapply bind_spec; intros; tac2
    | _ => tac
    end.
  
  Notation "\s l" := (∃ t, l ↦ t) (at level 10).
  Definition final (dst: destination) (a: expr) : list statement :=
    match dst with
    | For_val => nil
    | For_effects => nil
    | For_set sd => do_set sd a
    end.

  Definition dest_below (dst: destination) : iProp :=
    match dst with
    | For_set sd => \s (sd_temp sd)
    | _ => \⌜True⌝
    end.

  (** Iris version *)
  Definition tr_rvalof (ty : type) (e1 : expr) (lse : list statement * expr) : iProp :=
    if type_is_volatile ty
    then
      (∃ t, \⌜ lse = (make_set t e1 :: nil ,Etempvar t ty)⌝ ∗ t ↦ ty )%I
    else
      \⌜lse = (nil,e1)⌝%I.

  Fixpoint tr_expr (le : temp_env) (dst : destination) (e : Csyntax.expr)
           (sla : list statement * expr) : iProp :=
    match e with
    | Csyntax.Evar id ty =>
      dest_below dst ∗
                 \⌜ sla = (final dst (Evar id ty),Evar id ty) ⌝
    | Csyntax.Ederef e1 ty =>
      ∃ sla2, tr_expr le For_val e1 sla2 ∗
                      dest_below dst ∗
                      \⌜sla = (sla2.1 ++ final dst (Ederef' sla2.2 ty),Ederef' sla2.2 ty)⌝
| Csyntax.Efield e1 f ty =>
  ∃ sla2, tr_expr le For_val e1 (sla2) ∗
                  dest_below dst ∗
                  \⌜ sla = (sla2.1 ++ final dst (Efield sla2.2 f ty),Efield sla2.2 f ty) ⌝

| Csyntax.Eval v ty =>
  match dst with
  | For_effects => \⌜sla.1 = nil⌝
  | For_val =>
    \⌜ (forall tge e le' m, eval_expr tge e le' m sla.2 v) /\ typeof sla.2 = ty /\ sla.1 = nil ⌝
  | For_set sd =>
    ⌜ (forall tge e le' m, eval_expr tge e le' m sla.2 v) /\ typeof sla.2 = ty /\ sla.1 = do_set sd sla.2 ⌝
  end
| Csyntax.Esizeof ty' ty =>
  dest_below dst ∗
             \⌜ sla = (final dst (Esizeof ty' ty), Esizeof ty' ty)⌝
| Csyntax.Ealignof ty' ty =>
  dest_below dst ∗
             \⌜ sla = (final dst (Ealignof ty' ty), Ealignof ty' ty) ⌝
| Csyntax.Evalof e1 ty =>
  ∃ sla2 sl3, tr_expr le For_val e1 sla2  ∗
                      tr_rvalof (Csyntax.typeof e1) sla2.2 (sl3,sla.2)  ∗
                      dest_below dst ∗
                      \⌜ sla.1 = (sla2.1 ++ sl3 ++ final dst sla.2) ⌝
| Csyntax.Eaddrof e1 ty =>
  ∃ sla2, tr_expr le For_val e1 sla2  ∗
                  dest_below dst ∗
                  \⌜ sla = (sla2.1 ++ final dst (Eaddrof' sla2.2 ty), Eaddrof' sla2.2 ty) ⌝
| Csyntax.Eunop ope e1 ty =>
  ∃ sla2, tr_expr le For_val e1 sla2  ∗
                  dest_below dst ∗
                  \⌜ sla = (sla2.1 ++ final dst (Eunop ope sla2.2 ty), Eunop ope sla2.2 ty) ⌝
| Csyntax.Ebinop ope e1 e2 ty =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
                       tr_expr le For_val e2 sla3  ∗
                       dest_below dst ∗
                       \⌜ sla = (sla2.1 ++ sla3.1 ++ final dst (Ebinop ope sla2.2 sla3.2 ty), Ebinop ope sla2.2 sla3.2 ty) ⌝
| Csyntax.Ecast e1 ty =>
  ∃ sla2, tr_expr le For_val e1 sla2  ∗
                  dest_below dst ∗
                  \⌜ sla = (sla2.1 ++ final dst (Ecast sla2.2 ty), Ecast sla2.2 ty ) ⌝
| Csyntax.Eseqand e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 t, tr_expr le For_val e1 sla2  ∗
                           (t ↦ ty -∗ tr_expr le (For_set (sd_seqbool_val t ty)) e2 sla3)  ∗
                           t ↦ ty ∗
                           \⌜ sla = (sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (Sset t (Econst_int Int.zero ty)) :: nil, Etempvar t ty ) ⌝
| For_effects =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
                       tr_expr le For_effects e2 sla3  ∗
                       \⌜  sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) Sskip :: nil ⌝
| For_set sd =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
                       (\s (sd_temp sd) -∗ tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sla3)  ∗
                       \s (sd_temp sd)  ∗
                       ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil ⌝
  end
| Csyntax.Eseqor e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 t, tr_expr le For_val e1 sla2  ∗
                           (t ↦ ty -∗ tr_expr le (For_set (sd_seqbool_val t ty)) e2 sla3)  ∗
                           t ↦ ty  ∗
                           \⌜ sla = (sla2.1 ++ makeif sla2.2 (Sset t (Econst_int Int.one ty)) (makeseq sla3.1) :: nil, Etempvar t ty) ⌝
| For_effects =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
                       tr_expr le For_effects e2 sla3  ∗
                       \⌜ sla.1 = sla2.1 ++ makeif sla2.2 Sskip (makeseq sla3.1) :: nil ⌝
| For_set sd =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
                       (\s (sd_temp sd) -∗ tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sla3)  ∗
                       \s (sd_temp sd)  ∗
                       ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq (do_set sd (Econst_int Int.one ty))) (makeseq sla3.1) :: nil ⌝
  end

| Csyntax.Econdition e1 e2 e3 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 sla4 t, tr_expr le For_val e1 sla2  ∗
                                (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1,
          ce sera encore provable avec tr_expr_incl *)
                                (t ↦ ty -∗ tr_expr le (For_set (SDbase ty ty t)) e2 sla3) ∗
                                (t ↦ ty -∗ tr_expr le (For_set (SDbase ty ty t)) e3 sla4) ∗
                                t ↦ ty ∗
                                \⌜ sla = (sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil,Etempvar t ty)⌝
| For_effects =>
  ∃ sla2 sla3 sla4, tr_expr le For_val e1 sla2  ∗
                            (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1,
          ce sera encore provable avec tr_expr_incl *)
                            tr_expr le For_effects e2 sla3 ∗
                            tr_expr le For_effects e3 sla4 ∗
                            \⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil ⌝
| For_set sd =>
  ∃ sla2 sla3 sla4 t, tr_expr le For_val e1 sla2  ∗
                              (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1,
          ce sera encore provable avec tr_expr_incl *)
                              (t ↦ ty -∗ tr_expr le (For_set (SDcons ty ty t sd)) e2 sla3) ∗
                              (t ↦ ty -∗ tr_expr le (For_set (SDcons ty ty t sd)) e3 sla4) ∗
                              t ↦ ty ∗
                              ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil ⌝
  end
| Csyntax.Eassign e1 e2 ty =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
                       tr_expr le For_val e2 sla3  ∗
                       ((⌜ sla.1 = sla2.1 ++ sla3.1 ++ make_assign sla2.2 sla3.2 :: nil /\  dst = For_effects ⌝ -∗ False) ∗
                                                                                                                          ((∃ t, \s t ∗ ⌜ sla.1 = sla2.1 ++ sla3.1 ++ Sset t (Ecast sla3.2 (Csyntax.typeof e1)) :: make_assign sla2.2 (Etempvar t (Csyntax.typeof e1)) :: final dst (Etempvar t (Csyntax.typeof e1)) ⌝) -∗ False) -∗ False)
| Csyntax.Eassignop ope e1 e2 tyres ty =>
  ∃ sla2 sla3 sla4, tr_expr le For_val e1 sla2  ∗
                            tr_expr le For_val e2 sla3  ∗
                            tr_rvalof (Csyntax.typeof e1) sla2.2 sla4  ∗
                            ((⌜ dst = For_effects /\
                              sla.1 = sla2.1 ++ sla3.1 ++ sla4.1 ++ make_assign sla2.2 (Ebinop ope sla4.2 sla3.2 tyres) :: nil ⌝ -∗ False) ∗ ((∃ t, \s t ∗ ⌜ sla = (sla2.1 ++ sla3.1 ++ sla4.1 ++ Sset t (Ecast (Ebinop ope sla4.2 sla3.2 tyres) (Csyntax.typeof e1)) :: make_assign sla2.2 (Etempvar t (Csyntax.typeof e1)) :: final dst (Etempvar t (Csyntax.typeof e1)), (Etempvar t (Csyntax.typeof e1))) ⌝) -∗ False) -∗ False)
| Csyntax.Epostincr id e1 ty =>
  (((∃ sla2 sla3,
        tr_expr le For_val e1 sla2  ∗
                tr_rvalof (Csyntax.typeof e1) sla2.2 sla3  ∗
                ⌜ sla.1 = sla2.1 ++ sla3.1 ++
                                 make_assign sla2.2 (transl_incrdecr id sla3.2 (Csyntax.typeof e1)) :: nil ⌝) -∗ False) ∗
                                                                                                                        ((∃ sla2 t,
                                                                                                                             tr_expr le For_val e1 sla2  ∗
                                                                                                                                     \s t  ∗
                                                                                                                                     ⌜ sla = (sla2.1 ++ make_set t sla2.2 ::
                                                                                                                                                     make_assign sla2.2 (transl_incrdecr id (Etempvar t (Csyntax.typeof e1)) (Csyntax.typeof e1)) ::
                                                                                                                                                     final dst (Etempvar t (Csyntax.typeof e1)),Etempvar t (Csyntax.typeof e1))⌝) -∗ False) -∗ False)

| Csyntax.Ecomma e1 e2 ty =>
  ∃ sla2 sl3,
    tr_expr le For_effects e1 sla2  ∗
            (dest_below dst -∗ tr_expr le dst e2 (sl3,sla.2))  ∗
            dest_below dst ∗
            \⌜ sla.1 = sla2.1 ++ sl3 ⌝

| Csyntax.Ecall e1 el2 ty =>
  match dst with
  | For_effects =>
    ∃ sla2 slal3,
    tr_expr le For_val e1 sla2  ∗
            tr_exprlist le el2 slal3  ∗
            \⌜  sla.1 = sla2.1 ++ slal3.1 ++ Scall None sla2.2 slal3.2 :: nil ⌝
| _ =>
  ∃ sla2 slal3 t,
    tr_expr le For_val e1 sla2  ∗
            tr_exprlist le el2 slal3  ∗
            \s t  ∗
            dest_below dst ∗
            \⌜ sla = (sla2.1 ++ slal3.1 ++ Scall (Some t) sla2.2 slal3.2 :: final dst (Etempvar t ty), Etempvar t ty)⌝
  end

| Csyntax.Ebuiltin ef tyargs el ty =>
  match dst with
  | For_effects =>
    ∃ slal2,
    tr_exprlist le el (slal2)  ∗
                \⌜ sla.1 = slal2.1 ++ Sbuiltin None ef tyargs slal2.2 :: nil ⌝
| _ =>
  ∃ slal2 t,
    tr_exprlist le el slal2  ∗
                \s t  ∗
                dest_below dst ∗
                \⌜ sla = (slal2.1 ++ Sbuiltin (Some t) ef tyargs slal2.2 :: final dst (Etempvar t ty), Etempvar t ty)⌝
  end

| Csyntax.Eparen e1 tycast ty =>
  match dst with
  | For_val =>
    ∃ a2 t,
    tr_expr le (For_set (SDbase tycast ty t)) e1 (sla.1,a2)  ∗
            \s t  ∗
            \⌜ sla.2 = Etempvar t ty ⌝
| For_effects =>
  ∃ a2, tr_expr le For_effects e1 (sla.1,a2)
| For_set sd =>
  ∃ a2 t,
    tr_expr le (For_set (SDcons tycast ty t sd)) e1 (sla.1,a2)  ∗ \s t
  end

| _ => False
  end
  with tr_exprlist (le : temp_env) (e : Csyntax.exprlist) (sla : list statement * list expr) : iProp :=
         match e with
         | Csyntax.Enil => \⌜ sla = (nil,nil)⌝
         | Csyntax.Econs e1 el2 =>
           ∃ sla2 slal3,
    tr_expr le For_val e1 sla2  ∗
            tr_exprlist le el2 slal3  ∗
            \⌜ sla = (sla2.1 ++ slal3.1, sla2.2 :: slal3.2) ⌝
  end.

  Lemma transl_valof_meets_spec ty a :
    {{ emp }} transl_valof ty a {{ r, RET r; tr_rvalof ty a r }}.
  Proof.
    unfold transl_valof. unfold tr_rvalof.
    destruct (type_is_volatile ty); tac.
    frameR. iApply ret_spec_bis.
    iPureIntro; reflexivity.
  Qed.



  (** ** Top-level translation *)

  (** The "top-level" translation is equivalent to [tr_expr] above
  for source terms.  It brings additional flexibility in the matching
  between Csyntax values and Cminor expressions: in the case of
  [tr_expr], the Cminor expression must not depend on memory,
  while in the case of [tr_top] it can depend on the current memory
  state. *)

  Scheme expr_ind2 := Induction for Csyntax.expr Sort Prop
    with exprlist_ind2 := Induction for Csyntax.exprlist Sort Prop.
  Combined Scheme tr_expr_exprlist from expr_ind2, exprlist_ind2.

  
  Lemma transl_meets_spec :
    (forall r dst le,
        {{ emp }} transl_expr dst r {{ res, RET res; dest_below dst -∗ tr_expr le dst r res}})
    /\
    (forall rl le,
        {{ emp }} transl_exprlist rl {{ res, RET res; tr_exprlist le rl res }}).
  Proof.
    pose transl_valof_meets_spec.
    apply tr_expr_exprlist; intros; rewrite /transl_expr; rewrite /transl_exprlist;
      fold transl_exprlist; fold transl_expr; tac2; rewrite /tr_expr; fold tr_expr; tac2.
    - destruct v; tac2; iApply ret_spec_complete; destruct dst; iIntros; eauto;
        try (iSplit); eauto; iIntros; iPureIntro; eauto; intros; constructor; intros;
          try constructor; try reflexivity.
    - iApply ret_spec_complete. iIntros "[HA HB]"; iFrame.
      destruct dst; iIntros; iPureIntro; reflexivity.
    - iApply ret_spec_complete. 
      iIntros "[HA HB]". iFrame.
      iSplitL "HA". iApply "HA". trivial. iPureIntro.
      destruct dst; simpl; eauto; rewrite app_nil_r; reflexivity.
    - frameR; apply b.
    - iApply ret_spec_complete.
      iIntros "[[HA HB] HC]". iFrame. iSplitL "HB". iApply "HB". trivial.
      destruct dst; iSimpl; iSplitL "HA"; try(rewrite <- surjective_pairing; iApply "HA");
        iPureIntro; try(rewrite app_nil_r; reflexivity); rewrite app_assoc; reflexivity.
    - iApply ret_spec_complete.
      iIntros "[HA HB]". iFrame. iSplitL "HA". iApply "HA". trivial. iFrame.
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - iApply ret_spec_complete.
      iIntros "[HA HB]". iFrame. iSplitL "HA". iApply "HA". trivial.
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - iApply ret_spec_complete.
      iIntros "[HA HB]". iSplitL "HA". iApply "HA". trivial. iFrame.
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - frameR. apply H0.
    - iApply ret_spec_complete.
      iIntros "[[HA HC] HB]". iSplitL "HC". iApply "HC". trivial.
      iSplitL "HA". iApply "HA". trivial. iFrame.
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r; reflexivity).
      rewrite app_assoc. reflexivity.
    - iApply ret_spec_complete.
      iIntros "[HA HB]". iSplitL "HA". iApply "HA". trivial. iFrame.
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - destruct dst; repeat tac2.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[[HA [HC HD]] HB]".
        iSplitL "HD". iApply "HD". trivial. iFrame.
        iSplitL "HA". iIntros "HB". iApply "HA".  iExists ty. iApply "HB".
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[[HA HC] HB]".
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iApply "HA".  trivial.
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + iApply ret_spec_complete. iIntros "[[HA HC] HB]". iFrame.
        iSplitL "HC". iApply "HC". trivial.
        iPureIntro. reflexivity.
    - destruct dst; repeat tac2.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[[HA [HC HD]] HB]".
        iSplitL "HD". iApply "HD". trivial. iFrame.
        iSplitL "HA". iIntros "HB". iApply "HA".  iExists ty. iApply "HB".
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[[HA HC] HB]".
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iApply "HA".  trivial.
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + iApply ret_spec_complete. iIntros "[[HA HC] HB]". iFrame.
        iSplitL "HC". iApply "HC". trivial.
        iPureIntro. reflexivity.
    - destruct dst; repeat tac2.
      + frameR. apply H0.
      + frameR. apply H1.
      + iApply ret_spec_complete.
        iIntros "[[HA [HC [HE HD]]] HB]".
        iSplitL "HD". iApply "HD". trivial. iFrame.
        iSplitL "HC". iIntros. iApply "HC". iExists ty. iFrame.
        iSplitL "HA". iIntros "HB". iApply "HA".  iExists ty. iApply "HB".
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + frameR. apply H1.
      + iApply ret_spec_complete.
        iIntros "[[HA [HC HD]] HB]".
        iSplitL "HD". iApply "HD". trivial.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iApply "HA". trivial.
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + frameR. apply H1.
      + iApply ret_spec_complete. iIntros "[[HA [HD [HE HC]]] HB]". iFrame.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HD". iIntros "HA". iApply "HD". iExists ty. iFrame.
        iSplitL "HA". iIntros "HB". iApply "HA". iExists ty. iFrame.
        iPureIntro. reflexivity.
    - iApply ret_spec_complete. iIntros "[HA HB]". iFrame. iPureIntro. destruct dst; reflexivity.
    - iApply ret_spec_complete. iIntros "[HA HB]". iFrame. iPureIntro. destruct dst; reflexivity.
    - frameR. eapply H0.
    - destruct dst; tac2.
      + iApply ret_spec_complete.
        iIntros "[[HA [HD HC]] HB]".
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HD". iApply "HD". trivial.
        iIntros "[HLeft HRight]". iApply "HRight".
        iExists v1. 
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA". 
        iPureIntro. reflexivity.
      + iApply ret_spec_complete.
        iIntros "[[HA HC] HB]".
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iApply "HA". trivial.
        iIntros "[HLeft HRight]". iApply "HLeft".
        iPureIntro. split; reflexivity.
      + iApply ret_spec_complete.
        iIntros "[[HA [HD HC]] HB]".
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HD". iApply "HD". trivial.
        iIntros "[HLeft HRight]". iApply "HRight".
        iExists v1.
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA". 
        iPureIntro. simpl. admit.
    - frameR. apply H0.
    - frameR. apply transl_valof_meets_spec.
    - destruct dst; tac2.
      + iApply ret_spec_complete.
        iIntros "[[HA [HD [HE HC]]] HB]".
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HE". iApply "HE". trivial.
        iSplitL "HD". iApply "HD".
        iIntros "[HLeft HRight]". iApply "HRight".
        iExists v2.
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA". 
        iPureIntro. reflexivity.
      + iApply ret_spec_complete.
        iIntros "[[HA [HD HC]] HB]".
         iSplitL "HC". iApply "HC". trivial.
         iSplitL "HD". iApply "HD". trivial.
         iFrame.
         iIntros "[HLeft HRight]". iApply "HLeft".
         iPureIntro. split; reflexivity.
      + iApply ret_spec_complete.
        iIntros "[[HA [HD [HE HC]]] HB]".
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HE". iApply "HE". trivial.
        iSplitL "HD". iApply "HD".
        iIntros "[HLeft HRight]". iApply "HRight".
        iExists v2.
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA". 
        iPureIntro. simpl. admit.
    - destruct dst; tac2.
      + iApply ret_spec_complete.
        iIntros "[[HA HC] HB] [HLeft HRight]".
        iApply "HRight".
        iExists v. iExists v0.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA".
        iPureIntro. reflexivity.
      + frameR. apply b.
      + iApply ret_spec_complete.
        iIntros "[[HA HC] HB] [HLeft HRight]".
        iApply "HLeft". iExists v. iExists v0.
        iSplitL "HC". iApply "HC". trivial.
        iFrame.
        iPureIntro. reflexivity.
      + iApply ret_spec_complete.
        iIntros "[[HA HC] HB] [HLeft HRight]".
        iApply "HRight".
        iExists v. iExists v0.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA".
        iPureIntro. simpl. admit.
    - frameR. apply H0.
    - iApply ret_spec_complete. 
      iIntros "[[HA HC] HB]".
      iSplitL "HC". iApply "HC". trivial.
      iSplitL "HA". iIntros "HC". iSimpl. rewrite <- surjective_pairing.
      iApply "HA". iApply "HC".
      iFrame. iPureIntro. reflexivity.
    - frameL. apply H0.
    - destruct dst; tac2; fold tr_exprlist; fold tr_expr.
      + iApply ret_spec_complete. 
        iIntros "[[HA [HD HC]] HB]".
        iSplitL "HD". iApply "HD". trivial.
        iFrame.
        iSplitL "HA". iExists ty. iApply "HA". 
        iPureIntro. reflexivity.
      + iApply ret_spec_complete. 
        iIntros "[[HA HD] HB]".
        iSplitL "HA". iApply "HA". trivial.
        iFrame.
        iPureIntro. reflexivity.
      + iApply ret_spec_complete. 
        iIntros "[[HA [HD HC]] HB]".
        iSplitL "HD". iApply "HD". trivial.
        iFrame "HC".
        iSplitL "HA". iExists ty. iApply "HA".
        iFrame.
        iPureIntro. simpl. admit. 
    - apply H.
    - fold tr_exprlist. destruct dst; tac2.
      + iApply ret_spec_complete. 
        iIntros "[[HA HC] HB]".
        iFrame.
        iSplitL "HA". iExists ty. iApply "HA".
        iPureIntro. reflexivity.
      + iApply ret_spec_complete.
        iIntros "[HA HB]".
        iFrame.
        iPureIntro. reflexivity.
      + iApply ret_spec_complete. 
        iIntros "[[HA HC] HB]".
        iFrame "HC".
        iSplitL "HA". iExists ty. iApply "HA".
        iFrame.
        iPureIntro. simpl. admit. 
    - apply ret_spec_pure.
    - frameR. apply H0.
    - rewrite /tr_exprlist; fold tr_exprlist; fold tr_expr; tac2.
      iApply ret_spec_complete. 
      iIntros "[HA HB]".
      iFrame.
      iSplitL "HB". iApply "HB". trivial.
      iPureIntro. reflexivity.          
  Admitted.

  Section TR_TOP.

    Variable ge: genv.
    Variable e: Clight.env.
    Variable le: temp_env.
    Variable m: mem.

    Definition tr_top_base dst r sla := tr_expr le dst r sla.

    Definition tr_top_val_val (dst : destination) expr (sla : list statement * Clight.expr)  : iProp :=
      match sla with
      | (nil,a) => ∃ v ty, ⌜ typeof a = ty /\ eval_expr ge e le m a v /\ dst = For_val
                  /\ expr = Csyntax.Eval v ty⌝
      | _ => False
    end.

    Definition tr_top dst expr sla := ((tr_top_base dst expr sla -∗ False)
                                         ∗ (tr_top_val_val dst expr sla -∗ False)) -∗ False.
  
  End TR_TOP.

  (** ** Translation of statements *)

  Definition tr_expression (r : Csyntax.expr) (s : statement) (a: expr) : iProp :=
    ∃ sl, \⌜ s = makeseq sl ⌝ ∗ ∃ le, tr_expr le For_val r (sl,a).

  Definition tr_expr_stmt (r : Csyntax.expr) (s : statement) : iProp :=
    ∃ sla, \⌜ s = makeseq sla.1 ⌝ ∗ ∃ le, tr_expr le For_effects r sla.

  
  Definition tr_if (r : Csyntax.expr) (s0 : statement) (s1: statement) (s2 : statement) : iProp :=
    ∃ sla, \⌜ s2 = makeseq (sla.1 ++ makeif sla.2 s0 s1 :: nil) ⌝ ∗ ∃ le, tr_expr le For_val r sla.
  
  Fixpoint tr_stmt (r : Csyntax.statement) (s : statement) :=
    match r with
    | Csyntax.Sskip =>
      \⌜ s = Sskip ⌝
    | Csyntax.Sdo r =>
      tr_expr_stmt r s                   
    | Csyntax.Ssequence s1 s2 =>
      ∃ ts1 ts2,
      tr_stmt s1 ts1 ∗ tr_stmt s2 ts2 ∗ \⌜ s = Ssequence ts1 ts2⌝        
    | Csyntax.Sifthenelse r1 s1 s2 =>
      match s with
      | Ssequence s' Sskip =>
        ∃ a, \⌜ s1 = Csyntax.Sskip /\ s2 = Csyntax.Sskip⌝ ∗ tr_expression r1 s' a
      | Ssequence s' (Sifthenelse a ts1 ts2) =>
        ∃ a, tr_expression r1 s' a ∗ tr_stmt s1 ts1 ∗ tr_stmt s2 ts2
      | _ => False
      end        
    | Csyntax.Swhile r1 s1 =>
      match s with
      | Sloop (Ssequence s' ts1) Sskip =>
        tr_if r1 Sskip Sbreak s' ∗
        tr_stmt s1 ts1
      | _ => False
      end              
    | Csyntax.Sdowhile r s1 =>
      match s with
      | Sloop ts1 s' =>
        tr_if r Sskip Sbreak s' ∗
              tr_stmt s1 ts1
      | _ => False
      end
    | Csyntax.Sfor s1 r s3 s4 =>
      match s with
      | Sloop (Ssequence s' ts4) ts3 =>
        tr_if r Sskip Sbreak s' ∗
        tr_stmt s3 ts3 ∗
        tr_stmt s4 ts4 ∗
        \⌜ s1 = Csyntax.Sskip⌝
      | Ssequence ts1 (Sloop (Ssequence s' ts4) ts3) =>
        tr_if r Sskip Sbreak s' ∗
        tr_stmt s1 ts1 ∗
        tr_stmt s3 ts3 ∗
        tr_stmt s4 ts4 ∗
        \⌜ s1 = Csyntax.Sskip -> False⌝
      | _ => False
      end        
    | Csyntax.Sbreak =>
      \⌜ s = Sbreak⌝       
    | Csyntax.Scontinue =>
      \⌜ s = Scontinue⌝       
    | Csyntax.Sreturn None =>
      \⌜ s = Sreturn None⌝       
    | Csyntax.Sreturn (Some r) =>
      match s with
      | Ssequence s' (Sreturn (Some a)) =>
        tr_expression r s' a
      | _ => False
      end
    | Csyntax.Sswitch r ls =>
      match s with
      | Ssequence s' (Sswitch a tls) =>
        tr_expression r s' a ∗
        tr_lblstmts ls tls
      | _ => False
      end
    | Csyntax.Slabel lbl s' =>
      ∃ ts, tr_stmt s' ts ∗ \⌜ s = Slabel lbl ts⌝
    | Csyntax.Sgoto lbl =>
      \⌜ s = Sgoto lbl⌝
    end
  with tr_lblstmts (r : Csyntax.labeled_statements) (ls : labeled_statements) : iProp :=
         match r with
         | Csyntax.LSnil => \⌜ ls = LSnil⌝
         | Csyntax.LScons c s ls' =>
           ∃ ts tls,
            tr_stmt s ts ∗
            tr_lblstmts ls' tls ∗
            \⌜ls = LScons c ts tls⌝
         end.

  Lemma transl_expression_meets_spec: forall r,
      {{ emp }} transl_expression r {{ res, RET res; tr_expression r res.1 res.2 }}.
  Proof.
    intro. unfold transl_expression. epose transl_meets_spec. destruct a. unfold tr_expression; tac2.
    - apply (H r For_val Maps.PTree.Leaf).
    - iApply ret_spec_complete.
      iIntros "HA". iSplitR.
      + iPureIntro. reflexivity.
      + iExists Maps.PTree.Leaf. iSimpl. rewrite <- surjective_pairing.
        iApply "HA". trivial.
  Qed.

  Lemma transl_expr_stmt_meets_spec: forall r,
      {{ emp }} transl_expr_stmt r {{ res, RET res; tr_expr_stmt r res }}.
  Proof.
    intro. unfold transl_expr_stmt. epose transl_meets_spec. destruct a; unfold tr_expr_stmt; tac2.
    - apply (H _ _ Maps.PTree.Leaf).
    - iApply ret_spec_complete.
      iIntros "HA". iSplitR; eauto. iExists Maps.PTree.Leaf. iApply "HA". trivial.
  Qed.

  Lemma transl_if_meets_spec: forall r s1 s2,
      {{ emp }} transl_if r s1 s2 {{ res, RET res; tr_if r s1 s2 res }}.
  Proof.
    intros. epose transl_meets_spec. destruct a; unfold transl_if; unfold tr_if; tac2.
    - apply (H _ _ Maps.PTree.Leaf).
    - iApply ret_spec_complete.
      iIntros "HA". iSplitR.
      + iPureIntro. reflexivity.
      + iExists Maps.PTree.Leaf. iApply "HA". trivial.
  Qed.
  
  Lemma transl_stmt_meets_spec : forall s,
      {{ emp }} transl_stmt s {{ res, RET res; tr_stmt s res }}
  with transl_lblstmt_meets_spec:
         forall s,
           {{ emp }} transl_lblstmt s {{ res, RET res; tr_lblstmts s res }}. 
  Proof.
    pose transl_expression_meets_spec. pose transl_if_meets_spec. pose transl_expr_stmt_meets_spec.
    clear transl_stmt_meets_spec.
    intro. induction s; rewrite /transl_stmt; fold transl_stmt; rewrite /tr_stmt; fold tr_stmt; tac2.
    - apply comm_pre. apply frame_l. frameL. apply ret_spec_pure.
    - tac2. frameR. apply transl_expression_meets_spec.
      destruct (is_Sskip s1); destruct (is_Sskip s2) eqn:?.
      + rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
        iIntros "[HA HB]". iExists v1.2. iSplitR.
        ** iPureIntro; subst. split; reflexivity.
        ** rewrite e0 e1. simpl. iApply "HA".
      + rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
        iIntros "[HA [HC HB]]". iExists v1.2. iFrame.
      + rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
        iIntros "[HA [HC HB]]". iExists v1.2. iFrame.
      + rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
        iIntros "[HA [HC HB]]". iExists v1.2. iFrame.
    - iApply ret_spec_complete.
      iIntros "[HA HB]". iFrame.
    - iApply ret_spec_complete.
      iIntros "[HA HB]". iFrame.
    - frameR. apply transl_if_meets_spec.
    - destruct (is_Sskip).
      + iApply ret_spec_complete.
        iIntros "[HA [HC [HD HB]]]". iFrame.
        rewrite e0.
        iPureIntro. reflexivity.
      + iApply ret_spec_complete.
        iIntros "[HA [HC [HD HB]]]". iFrame.
        iPureIntro. apply n.
    - destruct o; tac2. iApply ret_spec_complete. eauto.
    - fold transl_lblstmt. frameR. apply transl_lblstmt_meets_spec.
    -  fold tr_lblstmts. iApply ret_spec_complete. iIntros "[HA HB]". iFrame.
    - frameL. apply ret_spec_pure.
    - induction s; rewrite /transl_lblstmt; fold transl_lblstmt; fold transl_stmt;
        rewrite /tr_lblstmts; fold tr_lblstmts; fold tr_stmt; tac2.
      apply comm_pre. apply frame_l. frameL. apply ret_spec_pure.
  Qed.
      
  (** Relational presentation for the transformation of functions, fundefs, and variables. *)

  Inductive tr_function: Csyntax.function -> Clight.function -> Prop :=
  | tr_function_intro: forall f tf i h,
      tr_stmt f.(Csyntax.fn_body) tf.(fn_body) i h ->
      fn_return tf = Csyntax.fn_return f ->
      fn_callconv tf = Csyntax.fn_callconv f ->
      fn_params tf = Csyntax.fn_params f ->
      fn_vars tf = Csyntax.fn_vars f ->
      tr_function f tf.
  

  Inductive tr_fundef: Csyntax.fundef -> Clight.fundef -> Prop :=
  | tr_internal: forall f tf,
      tr_function f tf ->
      tr_fundef (Internal f) (Internal tf)
  | tr_external: forall ef targs tres cconv,
      tr_fundef (External ef targs tres cconv) (External ef targs tres cconv).
  
  Import adequacy.
  Lemma transl_function_spec:
    forall f tf,
      transl_function f = OK tf ->
      tr_function f tf.
  Proof.
    unfold transl_function; intros.
    destruct (run (transl_stmt (Csyntax.fn_body f)) ∅) eqn:?. rewrite Heqe in H. inversion H.
    destruct p.
    apply (tr_function_intro _ _ 0%nat s); inv H; rewrite Heqe in H1; inversion H1; auto.
      apply (adequacy_triple (transl_stmt (Csyntax.fn_body f)) _ ∅ s0 s 0%nat emp).
      2 : apply Heqe.
      iIntros "HA". iSplitL. iApply (transl_stmt_meets_spec (Csyntax.fn_body f)). trivial.
  Qed.

  Lemma transl_fundef_spec:
    forall fd tfd,
      transl_fundef fd = OK tfd ->
      tr_fundef fd tfd.
  Proof.
    unfold transl_fundef; intros.
    destruct fd; Errors.monadInv H.
    + constructor. eapply transl_function_spec; eauto.
    + constructor.
  Qed.

End SPEC.
