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
Import weakestpre_gensym.
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
    | _ => True
    end.

  (** Iris version *)
  Definition tr_rvalof (ty : type) (e1 : expr) (lse : list statement * expr) : iProp :=
    if type_is_volatile ty
    then
      (∃ t, ⌜ lse = (make_set t e1 :: nil ,Etempvar t ty)⌝ ∗ t ↦ ty )%I
    else
      ⌜lse = (nil,e1)⌝%I.

  Fixpoint tr_expr (le : temp_env) (dst : destination) (e : Csyntax.expr)
           (sla : list statement * expr) : iProp :=
    match e with
    | Csyntax.Evar id ty => ⌜ sla = (final dst (Evar id ty),Evar id ty) ⌝
    | Csyntax.Ederef e1 ty =>
      ∃ sla2, tr_expr le For_val e1 sla2 ∗
                      ⌜sla = (sla2.1 ++ final dst (Ederef' sla2.2 ty),Ederef' sla2.2 ty)⌝
| Csyntax.Efield e1 f ty =>
  ∃ sla2, tr_expr le For_val e1 (sla2) ∗
                  ⌜ sla = (sla2.1 ++ final dst (Efield sla2.2 f ty),Efield sla2.2 f ty) ⌝

| Csyntax.Eval v ty =>
  match dst with
  | For_effects => ⌜sla.1 = nil⌝
  | For_val =>
    (∀ tge e le' m,  (∀ id, \s id -∗ ⌜ le'!id = le!id ⌝) -∗ ⌜ eval_expr tge e le' m sla.2 v ⌝)  ∗
                                                                                                ⌜ typeof sla.2 = ty ⌝ ∗ ⌜ sla.1 = nil ⌝
  | For_set sd =>
    (∀ tge e le' m, (∀ id, \s id -∗ ⌜ le'!id = le!id ⌝) -∗ ⌜ eval_expr tge e le' m sla.2 v ⌝)  ∗
                                                                                               ⌜ typeof sla.2 = ty /\ sla.1 = do_set sd sla.2 ⌝
  end
| Csyntax.Esizeof ty' ty => ⌜ sla = (final dst (Esizeof ty' ty), Esizeof ty' ty)⌝
| Csyntax.Ealignof ty' ty => ⌜ sla = (final dst (Ealignof ty' ty), Ealignof ty' ty) ⌝
| Csyntax.Evalof e1 ty =>
  ∃ sla2 sl3, tr_expr le For_val e1 sla2  ∗
                      tr_rvalof (Csyntax.typeof e1) sla2.2 (sl3,sla.2)  ∗
                      ⌜ sla.1 = (sla2.1 ++ sl3 ++ final dst sla.2) ⌝
| Csyntax.Eaddrof e1 ty =>
  ∃ sla2, tr_expr le For_val e1 sla2  ∗
                  ⌜ sla = (sla2.1 ++ final dst (Eaddrof' sla2.2 ty), Eaddrof' sla2.2 ty) ⌝
| Csyntax.Eunop ope e1 ty =>
  ∃ sla2, tr_expr le For_val e1 sla2  ∗
                  ⌜ sla = (sla2.1 ++ final dst (Eunop ope sla2.2 ty), Eunop ope sla2.2 ty) ⌝
| Csyntax.Ebinop ope e1 e2 ty =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
                       tr_expr le For_val e2 sla3  ∗
                       ⌜ sla = (sla2.1 ++ sla3.1 ++ final dst (Ebinop ope sla2.2 sla3.2 ty), Ebinop ope sla2.2 sla3.2 ty) ⌝
| Csyntax.Ecast e1 ty =>
  ∃ sla2, tr_expr le For_val e1 sla2  ∗
                  ⌜ sla = (sla2.1 ++ final dst (Ecast sla2.2 ty), Ecast sla2.2 ty ) ⌝
| Csyntax.Eseqand e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 t, tr_expr le For_val e1 sla2  ∗
                           (t ↦ ty -∗ tr_expr le (For_set (sd_seqbool_val t ty)) e2 sla3)  ∗
                           t ↦ ty ∗
                           ⌜ sla = (sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (Sset t (Econst_int Int.zero ty)) :: nil, Etempvar t ty ) ⌝
| For_effects =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
                       tr_expr le For_effects e2 sla3  ∗
                       ⌜  sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) Sskip :: nil ⌝
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
                           ⌜ sla = (sla2.1 ++ makeif sla2.2 (Sset t (Econst_int Int.one ty)) (makeseq sla3.1) :: nil, Etempvar t ty) ⌝
| For_effects =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
                       tr_expr le For_effects e2 sla3  ∗
                       ⌜ sla.1 = sla2.1 ++ makeif sla2.2 Sskip (makeseq sla3.1) :: nil ⌝
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
                                ⌜ sla = (sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil,Etempvar t ty)⌝
| For_effects =>
  ∃ sla2 sla3 sla4, tr_expr le For_val e1 sla2  ∗
                            (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1,
          ce sera encore provable avec tr_expr_incl *)
                            tr_expr le For_effects e2 sla3 ∗
                            tr_expr le For_effects e3 sla4 ∗
                            ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil ⌝
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
            ⌜ sla.1 = sla2.1 ++ sl3 ⌝

| Csyntax.Ecall e1 el2 ty =>
  match dst with
  | For_effects =>
    ∃ sla2 slal3,
    tr_expr le For_val e1 sla2  ∗
            tr_exprlist le el2 slal3  ∗
            ⌜  sla.1 = sla2.1 ++ slal3.1 ++ Scall None sla2.2 slal3.2 :: nil ⌝
| _ =>
  ∃ sla2 slal3 t,
    tr_expr le For_val e1 sla2  ∗
            tr_exprlist le el2 slal3  ∗
            \s t  ∗
            ⌜ sla = (sla2.1 ++ slal3.1 ++ Scall (Some t) sla2.2 slal3.2 :: final dst (Etempvar t ty), Etempvar t ty)⌝
  end

| Csyntax.Ebuiltin ef tyargs el ty =>
  match dst with
  | For_effects =>
    ∃ slal2,
    tr_exprlist le el (slal2)  ∗
                ⌜ sla.1 = slal2.1 ++ Sbuiltin None ef tyargs slal2.2 :: nil ⌝
| _ =>
  ∃ slal2 t,
    tr_exprlist le el slal2  ∗
                \s t  ∗
                ⌜ sla = (slal2.1 ++ Sbuiltin (Some t) ef tyargs slal2.2 :: final dst (Etempvar t ty), Etempvar t ty)⌝
  end

| Csyntax.Eparen e1 tycast ty =>
  match dst with
  | For_val =>
    ∃ a2 t,
    tr_expr le (For_set (SDbase tycast ty t)) e1 (sla.1,a2)  ∗
            \s t  ∗
            ⌜ sla.2 = Etempvar t ty ⌝
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
         | Csyntax.Enil => ⌜ sla = (nil,nil)⌝
         | Csyntax.Econs e1 el2 =>
           ∃ sla2 slal3,
    tr_expr le For_val e1 sla2  ∗
            tr_exprlist le el2 slal3  ∗
            ⌜ sla = (sla2.1 ++ slal3.1, sla2.2 :: slal3.2) ⌝
  end.

  Lemma transl_valof_meets_spec ty a :
    {{ emp }} transl_valof ty a {{ r, RET r; tr_rvalof ty a r }}.
  Proof.
    unfold transl_valof. unfold tr_rvalof.
    destruct (type_is_volatile ty).
    eapply bind_spec.
    + eapply gensym_spec.
    + intro. eapply exists_spec. frameR.
      eapply ret_spec.
    + iApply ret_spec.
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
  Combined Scheme expr_exprlist_ind from expr_ind2, exprlist_ind2.

  
  Lemma transl_meets_spec :
    (forall r dst le,
    {{ emp }} transl_expr dst r {{ res, RET res; dest_below dst -∗ tr_expr le dst r res}})
    /\
    (forall rl le,
    {{ emp }} transl_exprlist rl {{ res, RET res; tr_exprlist le rl res }}).
  Proof.
    apply expr_exprlist_ind; intros; rewrite /transl_expr; fold transl_expr.
    - destruct v; try(apply error_spec); iApply ret_spec_bis;
        destruct dst; iIntros; eauto; iSplit; eauto; iIntros; iPureIntro; constructor.
    - iApply ret_spec_bis. destruct dst; iIntros; iPureIntro; reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. rewrite /tr_expr. fold tr_expr. apply wand_post. eapply exists_spec.
        iApply ret_spec_complete.
        iIntros "[HA HB]".
        iSplitL. iApply "HA". trivial. iPureIntro.
        destruct dst; simpl; eauto; rewrite app_nil_r; reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. rewrite /tr_expr. fold tr_expr. eapply bind_spec.
        * frameL. apply transl_valof_meets_spec.
        * intro. apply wand_post. eapply (exists_spec v). eapply (exists_spec v0.1). iApply ret_spec_complete.
          iIntros "[[HA HB] HC]". iSplitL "HA". iApply "HA". trivial.
          destruct dst; iSimpl; iSplitL "HB"; try(rewrite <- surjective_pairing; iApply "HB");
            iPureIntro; try(rewrite app_nil_r; reflexivity); rewrite app_assoc; reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
        eapply (exists_spec v). iApply ret_spec_complete.
        iIntros "[HA HB]". iSplitL "HA". iApply "HA". trivial.
        iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
        eapply (exists_spec v). iApply ret_spec_complete.
        iIntros "[HA HB]". iSplitL "HA". iApply "HA". trivial.
        iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
        eapply (exists_spec v). iApply ret_spec_complete.
        iIntros "[HA HB]". iSplitL "HA". iApply "HA". trivial.
        iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. rewrite /tr_expr. fold tr_expr. eapply bind_spec.
        * frameL. apply H0.
        * intro. apply wand_post. eapply (exists_spec v). eapply (exists_spec v0).
          iApply ret_spec_complete.
          iIntros "[[HA HC] HB]". iSplitL "HA". iApply "HA". trivial.
          iSplitL "HC". iApply "HC". trivial.
          iPureIntro. destruct dst; simpl; try (rewrite app_nil_r; reflexivity).
          rewrite app_assoc. reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
        eapply (exists_spec v). iApply ret_spec_complete.
        iIntros "[HA HB]". iSplitL "HA". iApply "HA". trivial.
        iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. destruct dst.
        * eapply bind_spec.
          -- frameL. apply gensym_spec.
          -- intro. eapply bind_spec.
             ++ frameL. apply H0.
             ++ intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
                eapply (exists_spec v). eapply (exists_spec v1).
                eapply (exists_spec v0).
                iApply ret_spec_complete.
                iIntros "[[[HA HD] HC] HB]".
                iSplitL "HA". iApply "HA". trivial.
                iSplitL "HC". iIntros "HA". iApply "HC". iSimpl. iExists ty. iApply "HA".
                iFrame "HD".
                iPureIntro. reflexivity.
        * eapply bind_spec.
          -- frameL. iApply H0.
          -- intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
             eapply (exists_spec v). eapply (exists_spec v0).
             iApply ret_spec_complete.
             iIntros "[[HA HC] HB]".
             iSplitL "HA". iApply "HA". trivial.
             iSplitL "HC". iApply "HC". trivial.
             iPureIntro. reflexivity.
        * eapply bind_spec.
          -- frameL. iApply H0.
          -- intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
             eapply (exists_spec v). eapply (exists_spec v0).
             iApply ret_spec_complete.
             iIntros "[[HA HC] HB]".
             iSplitL "HA". iApply "HA". trivial.
             iSplitL "HC". iApply "HC".
             iSplitL "HB". iApply "HB".
             iPureIntro. reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. destruct dst.
        * eapply bind_spec.
          -- frameL. apply gensym_spec.
          -- intro. eapply bind_spec.
             ++ frameL. apply H0.
             ++ intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
                eapply (exists_spec v). eapply (exists_spec v1).
                eapply (exists_spec v0).
                iApply ret_spec_complete.
                iIntros "[[[HA HD] HC] HB]".
                iSplitL "HA". iApply "HA". trivial.
                iSplitL "HC". iIntros "HA". iApply "HC". iSimpl. iExists ty. iApply "HA".
                iFrame "HD".
                iPureIntro. reflexivity.
        * eapply bind_spec.
          -- frameL. iApply H0.
          -- intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
             eapply (exists_spec v). eapply (exists_spec v0).
             iApply ret_spec_complete.
             iIntros "[[HA HC] HB]".
             iSplitL "HA". iApply "HA". trivial.
             iSplitL "HC". iApply "HC". trivial.
             iPureIntro. reflexivity.
        * eapply bind_spec.
          -- frameL. iApply H0.
          -- intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
             eapply (exists_spec v). eapply (exists_spec v0).
             iApply ret_spec_complete.
             iIntros "[[HA HC] HB]".
             iSplitL "HA". iApply "HA". trivial.
             iSplitL "HC". iApply "HC".
             iSplitL "HB". iApply "HB".
             iPureIntro. reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. destruct dst.
        * eapply bind_spec.
          -- frameL. apply gensym_spec.
          -- intro. eapply bind_spec.
             ++ frameL. apply H0.
             ++ intro. eapply bind_spec.
                ** frameL. eapply H1.
                ** intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
                   eapply (exists_spec v). eapply (exists_spec v1).
                   eapply (exists_spec v2).
                   eapply (exists_spec v0).
                   iApply ret_spec_complete.
                   iIntros "[[[[HA HE] HD] HC] HB]".
                   iSplitL "HA". iApply "HA". trivial.
                   iSplitL "HD". iIntros "HA". iApply "HD". iSimpl. iExists ty. iApply "HA".
                   iSplitL "HC". iIntros "HA". iApply "HC". iExists ty. iApply "HA".
                   iFrame. iPureIntro. reflexivity.
        * eapply bind_spec.
          -- frameL. iApply H0.
          -- intro. eapply bind_spec.
             ++ frameL. eapply H1.
             ++ intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
             eapply (exists_spec v). eapply (exists_spec v0).
             eapply (exists_spec v1).
             iApply ret_spec_complete.
             iIntros "[[[HA HD] HC] HB]".
             iSplitL "HA". iApply "HA". trivial.
             iSplitL "HD". iApply "HD". trivial. 
             iSplitL "HC". iApply "HC". trivial.
             iPureIntro. reflexivity.
        * eapply bind_spec.
          -- frameL. eapply gensym_spec.
          -- intro. eapply bind_spec.
             ++ frameL. eapply H0.
             ++ intro. eapply bind_spec.
                ** frameL. eapply H1.
                ** intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
                   eapply (exists_spec v). eapply (exists_spec v1).
                   eapply (exists_spec v2). eapply (exists_spec v0).
                   iApply ret_spec_complete.
                   iIntros "[[[[HA HE] HD] HC] HB]".
                   iSplitL "HA". iApply "HA". trivial.
                   iSplitL "HD". iIntros "HA". iApply "HD". iExists ty. iApply "HA".
                   iSplitL "HC". iIntros "HA". iApply "HC". iExists ty. iApply "HA".
                   iFrame. iPureIntro. reflexivity.
    - iApply ret_spec_bis. iIntros. destruct dst; iSimpl; iPureIntro; reflexivity.
    - iApply ret_spec_bis. iIntros. destruct dst; iSimpl; iPureIntro; reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro. destruct dst.
        * eapply bind_spec.
          -- frameL. eapply H0.
          -- intro. eapply bind_spec.
             ++ frameL. apply gensym_spec.
             ++ intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
                   eapply (exists_spec v). eapply (exists_spec v0).
                   iApply ret_spec_complete.
                   iIntros "[[[HA HD] HC] HB]".
                   iSplitL "HA". iApply "HA". trivial.
                   iSplitL "HD". iApply "HD". trivial.
                   iIntros "[HLeft HRight]". iApply "HRight".
                   iExists v1.
                   iSplitL "HC". iExists (Csyntax.typeof l). iApply "HC". 
                   iPureIntro. reflexivity.
        * eapply bind_spec.
          -- frameL. apply H0.
          -- intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
             eapply (exists_spec v). eapply (exists_spec v0).
             iApply ret_spec_complete.
             iIntros "[[HA HC] HB]".
             iSplitL "HA". iApply "HA". trivial. 
             iSplitL "HC". iApply "HC". trivial.
             iIntros "[HLeft HRight]". iApply "HLeft".
             iPureIntro. split; reflexivity.
        * eapply bind_spec.
          -- frameL. apply H0.
          -- intro. eapply bind_spec.
             ++ frameL. apply gensym_spec.
             ++ intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
                eapply (exists_spec v). eapply (exists_spec v0).
                iApply ret_spec_complete.
                iIntros "[[[HA HD] HC] HB]".
                iSplitL "HA". iApply "HA". trivial.
                iSplitL "HD". iApply "HD". trivial.
                iIntros "[HLeft HRight]". iApply "HRight".
                iExists v1.
                iSplitL "HC". iExists (Csyntax.typeof l). iApply "HC". 
                iPureIntro. simpl. admit.
    - eapply bind_spec.
      + apply H.
      + intro. eapply bind_spec.
        * frameL. apply H0.
        * intro. eapply bind_spec.
          -- frameL. apply transl_valof_meets_spec.
          -- intro. destruct dst.
             ++ eapply bind_spec.
                ** frameL. eapply gensym_spec.
                ** intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
                   eapply (exists_spec v). eapply (exists_spec v0).
                   eapply (exists_spec v1).
                   iApply ret_spec_complete.
                   iIntros "[[[[HA HE] HD] HC] HB]".
                   iSplitL "HA". iApply "HA". trivial.
                   iSplitL "HE". iApply "HE". trivial.
                   iFrame.
                   iIntros "[HLeft HRight]". iApply "HRight".
                   iExists v2.
                   iSplitL "HC". iExists (Csyntax.typeof l). iApply "HC". 
                   iPureIntro. reflexivity.
             ++ rewrite /tr_expr. fold tr_expr. apply wand_post.
                eapply (exists_spec v). eapply (exists_spec v0).
                eapply (exists_spec v1).
                iApply ret_spec_complete.
                iIntros "[[[HA HD] HC] HB]".
                iSplitL "HA". iApply "HA". trivial.
                iSplitL "HD". iApply "HD". trivial.
                iFrame.
                iIntros "[HLeft HRight]". iApply "HLeft".
                iPureIntro. split; reflexivity.
             ++ eapply bind_spec.
                ** frameL. eapply gensym_spec.
                ** intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
                   eapply (exists_spec v). eapply (exists_spec v0).
                   eapply (exists_spec v1).
                   iApply ret_spec_complete.
                   iIntros "[[[[HA HE] HD] HC] HB]".
                   iSplitL "HA". iApply "HA". trivial.
                   iSplitL "HE". iApply "HE". trivial.
                   iFrame.
                   iIntros "[HLeft HRight]". iApply "HRight".
                   iExists v2.
                   iSplitL "HC". iExists (Csyntax.typeof l). iApply "HC". 
                   iPureIntro. simpl. admit.
    - eapply bind_spec.
      + apply H.
      + intro. destruct dst.
        * eapply bind_spec.
          -- frameL. apply gensym_spec.
          -- intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
             iApply ret_spec_complete.
             iIntros "[[HA HC] HB] [HLeft HRight]".
             iApply "HRight".
             iExists v. iExists v0.
             iSplitL "HA". iApply "HA". trivial.
             iSplitL "HC". iExists (Csyntax.typeof l). iApply "HC".
             iPureIntro. reflexivity.
        * eapply bind_spec.
          -- frameL. eapply transl_valof_meets_spec.
          -- intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
             iApply ret_spec_complete.
             iIntros "[[HA HC] HB] [HLeft HRight]".
             iApply "HLeft". iExists v. iExists v0.
             iSplitL "HA". iApply "HA". trivial.
             iFrame.
             iPureIntro. reflexivity.
        * eapply bind_spec.
          -- frameL. apply gensym_spec.
          -- intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
             iApply ret_spec_complete.
             iIntros "[[HA HC] HB] [HLeft HRight]".
             iApply "HRight".
             iExists v. iExists v0.
             iSplitL "HA". iApply "HA". trivial.
             iSplitL "HC". iExists (Csyntax.typeof l). iApply "HC".
             iPureIntro. simpl. admit.
    - eapply bind_spec.
      + apply H.
      + intro. eapply bind_spec.
        * frameL. apply H0.
        * intro. rewrite /tr_expr. fold tr_expr. apply wand_post.
          eapply (exists_spec v). eapply (exists_spec v0.1).
          iApply ret_spec_complete. 
          iIntros "[[HA HC] HB]".
          iSplitL "HA". iApply "HA". trivial.
          iSplitL "HC". iIntros "HA". iSimpl. rewrite <- surjective_pairing.
          iApply "HC". iApply "HA".
          iFrame. iPureIntro. reflexivity.
    - fold transl_exprlist. eapply bind_spec.
      + apply H.
      + intro. eapply bind_spec.
        * frameL. apply H0.
        * intro. destruct dst.
          -- eapply bind_spec.
             ++ frameL. apply gensym_spec.
             ++ intro. rewrite /tr_expr. fold tr_expr. fold tr_exprlist. apply wand_post.
                eapply (exists_spec v). eapply (exists_spec v0). apply (exists_spec v1).
                iApply ret_spec_complete. 
                iIntros "[[[HA HD] HC] HB]".
                iSplitL "HA". iApply "HA". trivial.
                iFrame.
                iSplitL "HC". iExists ty. iApply "HC". 
                iPureIntro. reflexivity.
          -- rewrite /tr_expr. fold tr_expr. fold tr_exprlist. apply wand_post.
             eapply (exists_spec v). eapply (exists_spec v0).
             iApply ret_spec_complete. 
             iIntros "[[HA HC] HB]".
             iSplitL "HA". iApply "HA". trivial.
             iFrame.
             iPureIntro. reflexivity.
          -- eapply bind_spec.
             ++ frameL. apply gensym_spec.
             ++ intro. rewrite /tr_expr. fold tr_expr. fold tr_exprlist. apply wand_post.
                eapply (exists_spec v). eapply (exists_spec v0). apply (exists_spec v1).
                iApply ret_spec_complete. 
                iIntros "[[[HA HD] HC] HB]".
                iSplitL "HA". iApply "HA". trivial.
                iFrame.
                iSplitL "HC". iExists ty. iApply "HC". 
                iPureIntro. simpl. admit.
    - fold transl_exprlist. eapply bind_spec.
      + apply H.
      + intro. destruct dst.
        * eapply bind_spec.
          -- frameL. apply gensym_spec.
          -- intro. rewrite /tr_expr. fold tr_expr. fold tr_exprlist. apply wand_post.
             eapply (exists_spec v). eapply (exists_spec v0). 
             iApply ret_spec_complete. 
             iIntros "[[HA HC] HB]".
             iFrame.
             iSplitL "HC". iExists ty. iApply "HC".
             iPureIntro. reflexivity.
        * rewrite /tr_expr. fold tr_expr. fold tr_exprlist. apply wand_post.
          eapply (exists_spec v).
          iApply ret_spec_complete.
          iIntros "[HA HB]".
          iFrame.
          iPureIntro. reflexivity.
        *  eapply bind_spec.
          -- frameL. apply gensym_spec.
          -- intro. rewrite /tr_expr. fold tr_expr. fold tr_exprlist. apply wand_post.
             eapply (exists_spec v). eapply (exists_spec v0). 
             iApply ret_spec_complete. 
             iIntros "[[HA HC] HB]".
             iFrame.
             iSplitL "HC". iExists ty. iApply "HC".
             iPureIntro. simpl. admit.
    - apply error_spec.
    - apply error_spec.
    - apply ret_spec.
    - rewrite /transl_exprlist. fold transl_exprlist. fold transl_expr. eapply bind_spec.
      + apply H.
      + intro. eapply bind_spec.
        * frameL. apply H0.
        * intro. rewrite /tr_exprlist. fold tr_expr. fold tr_exprlist.
          eapply (exists_spec v). eapply (exists_spec v0).
          iApply ret_spec_complete. 
          iIntros "[HA HB]".
          iFrame.
          iSplitL "HA". iApply "HA". trivial.
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

  (* Lemma transl_expr_meets_spec: forall r dst, *)
  (*     {{ emp }} *)
  (*       transl_expr dst r *)
  (*       {{ res, RET res; dest_below dst -∗ (∃ ge e le m, tr_top ge e le m dst r res) }}. *)
  (* Proof. *)
  (*   intros. epose transl_meets_spec. destruct a. *)
  (*   iIntros (?) "HA HB". iApply H. trivial. iIntros (?) "HC". *)
  (*   iApply "HB". iIntros.  iApply "HC". *)


  (** ** Translation of statements *)

  Definition tr_expression (r : Csyntax.expr) (s : statement) (a: expr) : iProp :=
    ∃ sl, ⌜ s = makeseq sl ⌝ ∗ ∃ le, tr_expr le For_val r (sl,a).

  Definition tr_expr_stmt (r : Csyntax.expr) (s : statement) : iProp :=
    ∃ sla, ⌜ s = makeseq sla.1 ⌝ ∗ ∃ le, tr_expr le For_effects r sla.

  Print transl_if.
  Definition tr_if (r : Csyntax.expr) (s0 : statement) (s1: statement) (s2 : statement) : iProp :=
    ∃ sla, ⌜ s2 = makeseq (sla.1 ++ makeif sla.2 s0 s1 :: nil) ⌝ ∗ ∃ le, tr_expr le For_val r sla.
  
  Fixpoint tr_stmt (r : Csyntax.statement) (s : statement) :=
    match r with
    | Csyntax.Sskip =>
      ⌜ s = Sskip ⌝
    | Csyntax.Sdo r =>
      tr_expr_stmt r s                   
    | Csyntax.Ssequence s1 s2 =>
      ∃ ts1 ts2,
      tr_stmt s1 ts1 ∗ tr_stmt s2 ts2 ∗ ⌜ s = Ssequence ts1 ts2⌝        
    | Csyntax.Sifthenelse r1 s1 s2 =>
      match s with
      | Ssequence s' Sskip =>
        ∃ a, ⌜ s1 = Csyntax.Sskip /\ s2 = Csyntax.Sskip⌝ ∗ tr_expression r1 s' a
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
        ⌜ s1 = Csyntax.Sskip⌝
      | Ssequence ts1 (Sloop (Ssequence s' ts4) ts3) =>
        tr_if r Sskip Sbreak s' ∗
        tr_stmt s1 ts1 ∗
        tr_stmt s3 ts3 ∗
        tr_stmt s4 ts4 ∗
        ⌜ s1 = Csyntax.Sskip -> False⌝
      | _ => False
      end        
    | Csyntax.Sbreak =>
      ⌜ s = Sbreak⌝       
    | Csyntax.Scontinue =>
      ⌜ s = Scontinue⌝       
    | Csyntax.Sreturn None =>
      ⌜ s = Sreturn None⌝       
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
      ∃ ts, tr_stmt s' ts ∗ ⌜ s = Slabel lbl ts⌝
    | Csyntax.Sgoto lbl =>
      ⌜ s = Sgoto lbl⌝
    end
  with tr_lblstmts (r : Csyntax.labeled_statements) (ls : labeled_statements) : iProp :=
         match r with
         | Csyntax.LSnil => ⌜ ls = LSnil⌝
         | Csyntax.LScons c s ls' =>
           ∃ ts tls,
            tr_stmt s ts ∗
            tr_lblstmts ls' tls ∗
            ⌜ls = LScons c ts tls⌝
         end.

  Lemma transl_expression_meets_spec: forall r,
      {{ emp }} transl_expression r {{ res, RET res; tr_expression r res.1 res.2 }}.
  Proof.
    intro. unfold transl_expression. epose transl_meets_spec. destruct a.
    eapply bind_spec.
    - apply (H r For_val Leaf).
    - intro. rewrite /tr_expression. apply (exists_spec v.1).
      iApply ret_spec_complete.
      iIntros "HA". iSplitR.
      + iPureIntro. reflexivity.
      + iExists Leaf. iSimpl. rewrite <- surjective_pairing.
        iApply "HA". trivial.
  Qed.

  Lemma transl_expr_stmt_meets_spec: forall r,
      {{ emp }} transl_expr_stmt r {{ res, RET res; tr_expr_stmt r res }}.
  Proof.
    intro. unfold transl_expr_stmt. epose transl_meets_spec. destruct a.
    eapply bind_spec.
    - apply (H _ _ Leaf).
    - intro. apply (exists_spec v).
      iApply ret_spec_complete.
      iIntros "HA". iSplitR; eauto. iExists Leaf. iApply "HA". trivial.
  Qed.

  Lemma transl_if_meets_spec: forall r s1 s2,
      {{ emp }} transl_if r s1 s2 {{ res, RET res; tr_if r s1 s2 res }}.
  Proof.
    intros. eapply bind_spec. epose transl_meets_spec. destruct a.
    - apply (H _ _ Leaf).
    - intro. apply (exists_spec v).
      iApply ret_spec_complete.
      iIntros "HA". iSplitR.
      + iPureIntro. reflexivity.
      + iExists Leaf. iApply "HA". trivial.
  Qed.
  
  Lemma transl_stmt_meets_spec : forall s,
      {{ emp }} transl_stmt s {{ res, RET res; tr_stmt s res }}
  with transl_lblstmt_meets_spec:
         forall s,
           {{ emp }} transl_lblstmt s {{ res, RET res; tr_lblstmts s res }}. 
  Proof.
    clear transl_stmt_meets_spec.
    intro. induction s; rewrite /transl_stmt; fold transl_stmt.
    - apply ret_spec.
    - apply transl_expr_stmt_meets_spec.
    - eapply bind_spec.
      + apply IHs1.
      + intro. eapply bind_spec.
        * frameL. apply IHs2.
        * intro. rewrite /tr_stmt; fold tr_stmt. apply (exists_spec v). apply (exists_spec v0).
          apply frame_l. frameL. apply ret_spec.
    - eapply bind_spec.
      + apply IHs1.
      + intro. eapply bind_spec.
        * frameL. apply IHs2.
        * intro. eapply bind_spec.
          -- frameL. apply transl_expression_meets_spec.
          -- intro. destruct (is_Sskip s1); destruct (is_Sskip s2) eqn:?.
             ++ rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
                iIntros "[HA HB]". iExists v1.2. iSplitR.
                ** iPureIntro; subst. split; reflexivity.
                ** iApply "HB".
             ++ rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
                iIntros "[[HA HC] HB]". iExists v1.2. iFrame.
             ++ rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
                iIntros "[[HA HC] HB]". iExists v1.2. iFrame.
             ++ rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
                iIntros "[[HA HC] HB]". iExists v1.2. iFrame.
    - eapply bind_spec.
      + apply transl_if_meets_spec.
      + intro. eapply bind_spec.
        * frameL. apply IHs.
        * intro. rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
          iIntros "[HA HB]". iFrame.
    - eapply bind_spec.
      + apply transl_if_meets_spec.
      + intro. eapply bind_spec.
        * frameL. apply IHs.
        * intro. rewrite /tr_stmt; fold tr_stmt. iApply ret_spec_complete.
          iIntros. iFrame.
    - eapply bind_spec.
      + apply IHs1.
      + intro. eapply bind_spec.
        * frameL. apply transl_if_meets_spec.
        * intro. eapply bind_spec.
          -- frameL. apply IHs2.
          -- intro. eapply bind_spec.
             ++ frameL. apply IHs3.
             ++ intro. destruct (is_Sskip).
                ** rewrite /tr_stmt. fold tr_stmt. iApply ret_spec_complete.
                   iIntros "[[[HA HD] HC] HB]". iFrame.
                   iPureIntro. apply e0.
                ** rewrite /tr_stmt. fold tr_stmt. iApply ret_spec_complete.
                   iIntros "[[[HA HD] HC] HB]". iFrame.
                   iPureIntro. apply n.
    - apply ret_spec.
    - apply ret_spec.
    - destruct o.
      + eapply bind_spec.
        * apply transl_expression_meets_spec.
        * intro. rewrite /tr_stmt. fold tr_stmt. iApply ret_spec_complete. eauto.
      + apply ret_spec.
    - fold transl_lblstmt. eapply bind_spec.
      + apply transl_expression_meets_spec.
      + intro. eapply bind_spec.
        * frameL. apply transl_lblstmt_meets_spec.
        * intro. rewrite /tr_stmt. fold tr_lblstmts. iApply ret_spec_complete. iIntros. iFrame.
    - eapply bind_spec.
      + apply IHs.
      + intro. rewrite /tr_stmt. fold tr_stmt. apply (exists_spec v). frameL. apply ret_spec.
    - apply ret_spec.
    - induction s; rewrite /transl_lblstmt; fold transl_lblstmt; fold transl_stmt.
      + apply ret_spec.
      + eapply bind_spec.
        * apply transl_stmt_meets_spec.
        * intro. eapply bind_spec.
          -- frameL. apply IHs.
          -- intro. rewrite /tr_lblstmts. fold tr_lblstmts. fold tr_stmt.
             apply (exists_spec v). apply (exists_spec v0). apply frame_l. frameL. apply ret_spec.
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

  
  (* Lemma adequacy {X} : forall (e : mon X) (Φ : X -> iProp) h v h' i, *)
  (*     (heap_ctx h ⊢ WP e |{ Φ }|) -> *)
  (*     run e h = Res (h', v) -> *)
  (*     (Φ v) i h'. *)
  Import adequacy.
  Lemma transl_function_spec:
    forall f tf,
      transl_function f = OK tf ->
      tr_function f tf.
  Proof.
    unfold transl_function; intros.
    destruct (transl_stmt (Csyntax.fn_body f)) eqn:T; inv H.
    econstructor; eauto. simpl. eapply (adequacy (transl_stmt (Csyntax.fn_body f))). epose (adequacy (transl_stmt(Csyntax.fn_body f)) (tr_stmt (Csyntax.fn_body f))).
    eapply m.
    epose (transl_stmt_meets_spec (Csyntax.fn_body f)).
    
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
