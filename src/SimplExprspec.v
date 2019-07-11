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

Require Import Coqlib Errors Integers Floats.
From iris.proofmode Require Import tactics.
Require Import AST Linking Memory.
Require Import Ctypes Cop Csyntax Clight Monad SimplExpr.
From stdpp Require Import binders strings.
From iris.proofmode Require Import tactics notation.
From iris.base_logic.lib Require Import gen_heap.


Section SPEC.
  Import Maps.PTree.
  Import weakestpre_gensym.
  Import proofmode.
  Context `{!heapG Σ}.
  Local Open Scope gensym_monad_scope.
  Open Scope bi_scope.

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

  Definition final (dst: destination) (a: expr) : list statement :=
    match dst with
    | For_val => nil
    | For_effects => nil
    | For_set sd => do_set sd a
    end.

  (** Iris version *)
  Definition tr_rvalof (ty : type) (e1 : expr) (lse : list statement * expr) : iProp Σ :=
    if type_is_volatile ty
    then
      (∃ t, ⌜ lse = (make_set t e1 :: nil ,Etempvar t ty)⌝ ∗ t ↦ ty )%I
    else
      ⌜lse = (nil,e1)⌝%I.

  Definition dest_below (dst: destination) : iProp Σ :=
    match dst with
    | For_set sd => \s (sd_temp sd)
    | _ => True
    end.
  
  Fixpoint tr_expr (le : temp_env) (dst : destination) (e : Csyntax.expr) (sla : list statement * expr) : iProp Σ :=
    match e with
    | Csyntax.Evar id ty => ⌜ sla = (final dst (Evar id ty),Evar id ty) ⌝
                                                                       
    | Csyntax.Ederef e1 ty =>
      ∃ sla2,
    tr_expr le For_val e1 sla2 ∗
            ⌜ sla = (sla2.1 ++ final dst (Ederef' sla2.2 ty),Ederef' sla2.2 ty)⌝
                                                                               
| Csyntax.Efield e1 f ty =>
  ∃ sla2,
    tr_expr le For_val e1 (sla2) ∗
            ⌜ sla = (sla2.1 ++ final dst (Efield sla2.2 f ty),Efield sla2.2 f ty) ⌝
                                                                                  
| Csyntax.Eval v ty =>
  match dst with
  | For_effects => ⌜sla.1 = nil⌝
  | For_val =>
    (∀ tge e le' m,
        (∀ id, \s id -∗ ⌜ le'!id = le!id ⌝) -∗
                                            ⌜ eval_expr tge e le' m sla.2 v ⌝)  ∗
                                                                                ⌜ typeof sla.2 = ty ⌝ ∗ ⌜ sla.1 = nil ⌝ 
  | For_set sd =>
    (∀ tge e le' m,
        (∀ id, \s id -∗ ⌜ le'!id = le!id ⌝) -∗
                                            ⌜ eval_expr tge e le' m sla.2 v ⌝)  ∗
                                                                                ⌜ typeof sla.2 = ty /\ sla.1 = do_set sd sla.2 ⌝
  end

| Csyntax.Esizeof ty' ty =>
  ⌜ sla = (final dst (Esizeof ty' ty), Esizeof ty' ty)⌝

| Csyntax.Ealignof ty' ty =>
  ⌜ sla = (final dst (Ealignof ty' ty), Ealignof ty' ty) ⌝

| Csyntax.Evalof e1 ty =>
  ∃ sla2 sl3,
    tr_expr le For_val e1 sla2  ∗
            tr_rvalof (Csyntax.typeof e1) sla2.2 (sl3,sla.2)  ∗
            ⌜ sla.1 = (sla2.1 ++ sl3 ++ final dst sla.2) ⌝

| Csyntax.Eaddrof e1 ty =>
  ∃ sla2,
    tr_expr le For_val e1 sla2  ∗
            ⌜ sla = (sla2.1 ++ final dst (Eaddrof' sla2.2 ty), Eaddrof' sla2.2 ty) ⌝

| Csyntax.Eunop ope e1 ty =>
  ∃ sla2,
    tr_expr le For_val e1 sla2  ∗
            ⌜ sla = (sla2.1 ++ final dst (Eunop ope sla2.2 ty), Eunop ope sla2.2 ty) ⌝

| Csyntax.Ebinop ope e1 e2 ty =>
  ∃ sla2 sla3,
    tr_expr le For_val e1 sla2  ∗
            tr_expr le For_val e2 sla3  ∗
            ⌜ sla = (sla2.1 ++ sla3.1 ++ final dst (Ebinop ope sla2.2 sla3.2 ty), Ebinop ope sla2.2 sla3.2 ty) ⌝
                                                                                                               
| Csyntax.Ecast e1 ty =>
  ∃ sla2,
    tr_expr le For_val e1 sla2  ∗
            ⌜ sla = (sla2.1 ++ final dst (Ecast sla2.2 ty), Ecast sla2.2 ty ) ⌝
                                                                              
| Csyntax.Eseqand e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 t,
    tr_expr le For_val e1 sla2  ∗
            (t ↦ ty -∗ tr_expr le (For_set (sd_seqbool_val t ty)) e2 sla3)  ∗
            t ↦ ty ∗
            ⌜ sla = (sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (Sset t (Econst_int Int.zero ty)) :: nil, Etempvar t ty ) ⌝
                                                                                                                        
| For_effects =>
  ∃ sla2 sla3,
    tr_expr le For_val e1 sla2  ∗
            tr_expr le For_effects e2 sla3  ∗
            ⌜  sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) Sskip :: nil ⌝
                              
| For_set sd =>
  ∃ sla2 sla3,
    tr_expr le For_val e1 sla2  ∗
            (\s sd_temp sd -∗ tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sla3)  ∗
            \s (sd_temp sd)  ∗
            ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq (do_set sd (Econst_int Int.zero ty)))
                             :: nil ⌝
  end

| Csyntax.Eseqor e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 t,
    tr_expr le For_val e1 sla2  ∗
            (t ↦ ty -∗ tr_expr le (For_set (sd_seqbool_val t ty)) e2 sla3)  ∗
            t ↦ ty  ∗
            ⌜ sla = (sla2.1 ++ makeif sla2.2 (Sset t (Econst_int Int.one ty)) (makeseq sla3.1) :: nil, Etempvar t ty) ⌝

| For_effects =>
  ∃ sla2 sla3,
    tr_expr le For_val e1 sla2  ∗
            tr_expr le For_effects e2 sla3  ∗
            ⌜ sla.1 = sla2.1 ++ makeif sla2.2 Sskip (makeseq sla3.1) :: nil ⌝

| For_set sd =>
  ∃ sla2 sla3,
    tr_expr le For_val e1 sla2  ∗
            (\s (sd_temp sd) -∗ tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sla3)  ∗
            \s (sd_temp sd)  ∗
            ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq (do_set sd (Econst_int Int.one ty))) (makeseq sla3.1)
                             :: nil ⌝
  end

| Csyntax.Econdition e1 e2 e3 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 sla4 t,
    tr_expr le For_val e1 sla2  ∗
            (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1,
          ce sera encore provable avec tr_expr_incl *)
            (t ↦ ty -∗ tr_expr le (For_set (SDbase ty ty t)) e2 sla3) ∗
            (t ↦ ty -∗ tr_expr le (For_set (SDbase ty ty t)) e3 sla4) ∗
            t ↦ ty ∗
            ⌜ sla = (sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil,Etempvar t ty)⌝

| For_effects =>
  ∃ sla2 sla3 sla4,
    tr_expr le For_val e1 sla2  ∗
            (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1,
          ce sera encore provable avec tr_expr_incl *)
            tr_expr le For_effects e2 sla3 ∗
            tr_expr le For_effects e3 sla4 ∗
            ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil ⌝

| For_set sd =>
  ∃ sla2 sla3 sla4 t,
    tr_expr le For_val e1 sla2  ∗
            (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1,
          ce sera encore provable avec tr_expr_incl *)
            (t ↦ ty -∗ tr_expr le (For_set (SDcons ty ty t sd)) e2 sla3) ∗
            (t ↦ ty -∗ tr_expr le (For_set (SDcons ty ty t sd)) e3 sla4) ∗
            t ↦ ty ∗
            ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil ⌝
  end

| Csyntax.Eassign e1 e2 ty =>
  ∃ sla2 sla3,
    tr_expr le For_val e1 sla2  ∗
            tr_expr le For_val e2 sla3  ∗
            ((⌜ sla.1 = sla2.1 ++ sla3.1 ++ make_assign sla2.2 sla3.2 :: nil /\  dst = For_effects ⌝ -∗ False) ∗
                                                                                                          ((∃ t, \s t ∗
                                                                                                                  ⌜ sla.1 = sla2.1 ++ sla3.1 ++ Sset t (Ecast sla3.2 (Csyntax.typeof e1)) ::
                                                                                                                                   make_assign sla2.2 (Etempvar t (Csyntax.typeof e1)) ::
                                                                                                                                   final dst (Etempvar t (Csyntax.typeof e1)) ⌝) -∗ False) -∗ False)

| Csyntax.Eassignop ope e1 e2 tyres ty =>
  ∃ sla2 sla3 sla4,
    tr_expr le For_val e1 sla2  ∗
            tr_expr le For_val e2 sla3  ∗
            tr_rvalof (Csyntax.typeof e1) sla2.2 sla4  ∗
            ((⌜ dst = For_effects /\
              sla.1 = sla2.1 ++ sla3.1 ++ sla4.1 ++ make_assign sla2.2 (Ebinop ope sla4.2 sla3.2 tyres) :: nil ⌝ -∗ False) ∗
                                                                                                                       ((∃ t, \s t ∗
                                                                                                                               ⌜ sla = (sla2.1 ++ sla3.1 ++ sla4.1 ++
                                                                                                                                               Sset t (Ecast (Ebinop ope sla4.2 sla3.2 tyres) (Csyntax.typeof e1)) ::
                                                                                                                                               make_assign sla2.2 (Etempvar t (Csyntax.typeof e1)) ::
                                                                                                                                               final dst (Etempvar t (Csyntax.typeof e1)), (Etempvar t (Csyntax.typeof e1))) ⌝) -∗ False) -∗ False)


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
  with tr_exprlist (le : temp_env) (e : Csyntax.exprlist) (sla : list statement * list expr) : iProp Σ :=
         match e with
         | Csyntax.Enil => ⌜ sla = (nil,nil)⌝
         | Csyntax.Econs e1 el2 =>
           ∃ sla2 slal3,
    tr_expr le For_val e1 sla2  ∗
            tr_exprlist le el2 slal3  ∗
            ⌜ sla = (sla2.1 ++ slal3.1, sla2.2 :: slal3.2) ⌝
  end.

  
  Ltac init_proof S := iIntros; iModIntro; iIntros (Φ) S.
  
  Lemma transl_valof_meets_spec ty a :
  |{{ True }}| transl_valof ty a |{{ r, RET r; tr_rvalof ty a r }}|.
  Proof.
    unfold transl_valof. unfold tr_rvalof. 
    destruct (type_is_volatile ty).
      eapply bind_spec.
      + eapply gensym_spec.
      + intro.
        iApply (exists_frame_r
                           v
                           (fun x => x ↦ ty)
                           (fun x r => ⌜r = ([make_set x a], Etempvar x ty)⌝ )).
        iApply ret_spec.
      + iApply ret_spec.
  Qed.

  Lemma transl_exprlist_meets_spec :
    (forall r dst le,
    |{{ True }}| transl_expr dst r |{{ res, RET res;
    dest_below dst -∗ tr_expr le dst r res}}|)
    -> (forall rl le,
    |{{ True }}| transl_exprlist rl |{{ res, RET res; tr_exprlist le rl res }}|).
  Proof.
    induction rl; intro.
    - apply ret_spec.
    - eapply bind_spec.
      + apply H.
      + intro. simpl. apply (exist v). simpl.
        apply exists_out_l. apply impl_true_pre. tFrame_l.
        eapply bind_spec.
        * apply IHrl.
        * intro. apply exists_frame_l. apply ret_spec.
  Qed.

  Scheme expr_ind2 := Induction for Csyntax.expr Sort Prop
    with exprlist_ind2 := Induction for Csyntax.exprlist Sort Prop.
  Combined Scheme expr_exprlist_ind from expr_ind2, exprlist_ind2.

  
  Lemma transl_meets_spec :
    (forall r dst le,
    |{{ True }}| transl_expr dst r |{{ res, RET res;
                                    dest_below dst -∗ tr_expr le dst r res}}|)
    /\
    (forall rl le,
    |{{ True }}| transl_exprlist rl |{{ res, RET res; tr_exprlist le rl res }}|).
  Proof.
    apply expr_exprlist_ind; intros; unfold transl_expr.
    - destruct dst.
      + apply impl_true_post.
        destruct v; eauto; try (apply error_spec); apply ret_spec_bis;
          iSplit; eauto; iIntros; iPureIntro; constructor.
      + apply impl_true_post.
        destruct v; eauto; try (apply error_spec); apply ret_spec_bis; iPureIntro; reflexivity.
      + destruct v; try (apply error_spec); apply ret_spec_bis;
          iIntros; simpl; iSplit; iIntros; iPureIntro; auto; constructor.
    - unfold finish. destruct dst.
      + apply impl_true_post. apply ret_spec.
      + apply impl_true_post. apply ret_spec.
      + apply ret_spec_bis. iIntros. iPureIntro. auto.
    - eapply bind_spec.
      + apply H.
      + intro. apply impl_true_pre. destruct dst.
        1-2 : apply impl_true_post.
        * rewrite /tr_expr. fold tr_expr. apply exists_frame_l.
          unfold finish. unfold final. rewrite app_nil_r. apply ret_spec.
        * rewrite /tr_expr. fold tr_expr. apply exists_frame_l.
          unfold finish. unfold final. rewrite app_nil_r. apply ret_spec.
        * rewrite /tr_expr. fold tr_expr. apply impl_post. apply exists_frame_l.
          apply ret_spec.
    - eapply bind_spec.
      + apply H.
      + intro. apply impl_true_pre. eapply bind_spec.
        * tFrame_l. apply transl_valof_meets_spec.
        * intro. apply impl_post. apply (exist v). apply exists_out_l.
          apply frame_l. destruct dst; unfold finish; unfold final.
          -- apply (exist v0.1). apply ret_frame_l; simpl.
             ++ simpl_list. iPureIntro. reflexivity.
             ++ intuition.
          -- apply (exist v0.1). apply ret_frame_l; simpl.
             ++ simpl_list. iPureIntro. reflexivity.
             ++ intuition.
          -- apply (exist v0.1). apply ret_frame_l; simpl.
             ++ iPureIntro. rewrite app_assoc. reflexivity.
             ++ intuition.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. destruct dst.
        1-2 : apply impl_true_post; apply exists_frame_l; simpl_list; apply ret_spec.
        * apply impl_post. apply exists_frame_l. apply ret_spec.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. destruct dst.
        1-2 : apply impl_true_post; apply exists_frame_l; simpl_list; apply ret_spec.
        * apply impl_post. apply exists_frame_l. apply ret_spec.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. destruct dst.
        1-2 : apply impl_true_post; apply exists_frame_l; simpl_list; apply ret_spec.
        * apply impl_post. apply exists_frame_l. apply ret_spec.
    - eapply bind_spec.
      + apply H.
      + intro v. eapply bind_spec.
        * apply impl_true_pre. tFrame_l. apply H0.
        * intro v0. destruct dst.
          1-2 : apply impl_true_post.
          -- rewrite /tr_expr. fold tr_expr. apply (exist v). apply exists_out_l.
             apply frame_l. apply impl_true_pre. apply exists_frame_l. rewrite app_nil_r.
             apply ret_spec.
          -- rewrite /tr_expr. fold tr_expr. apply (exist v). apply exists_out_l.
             apply frame_l. apply impl_true_pre. apply exists_frame_l. rewrite app_nil_r.
             apply ret_spec.
          -- rewrite /tr_expr. fold tr_expr. apply impl_post.
             apply (exist v). apply exists_out_l. apply frame_l.
             apply impl_true_pre. apply exists_frame_l. apply ret_spec_bis. rewrite app_assoc.
             iPureIntro. reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. destruct dst.
        1-2 : apply impl_true_post; apply exists_frame_l; simpl_list; apply ret_spec.
        * apply impl_post. apply exists_frame_l. apply ret_spec.
    - eapply bind_spec.
      + apply H.
      + intro v. destruct dst.
        * apply impl_true_pre. eapply bind_spec.
          -- tFrame_l. apply gensym_spec.
          -- intro v0. eapply bind_spec.
             ++ apply frame_l. tFrame_l. apply H0.
             ++ intro v1. apply impl_true_post.
                rewrite /tr_expr. fold tr_expr. apply (exist v).
                apply (exist v1). apply (exist v0). apply frame_l.
                apply comm_post. apply star_assoc_post. apply frame_l.
                apply (consequence_post
                         (fun v2 =>
                        ⌜v2 = (v.1 ++ [makeif v.2 (makeseq v1.1) (Sset v0 (Econst_int Int.zero ty))],
                               Etempvar v0 ty)⌝
                              ∗ (dest_below (For_set (sd_seqbool_val v0 ty))
                              -∗ tr_expr le (For_set (sd_seqbool_val v0 ty)) r2
                              v1))).
                ** iIntros (v2) "HA".
                   iDestruct "HA" as "[HA HB]". iFrame.
                   iIntros "HA". iApply "HB". iExists ty. iApply "HA".
                ** apply comm_post. tFrame_l. apply ret_spec.
        * apply impl_true_pre. eapply bind_spec.
          -- tFrame_l. apply H0.
          -- intro v0. rewrite /tr_expr. fold tr_expr.
             apply impl_true_post. apply (exist v). apply (exist v0).
             apply frame_l. apply impl_true_pre. tFrame_l.
             apply ret_spec_bis. iPureIntro. reflexivity.
        * apply impl_true_pre. eapply bind_spec.
          -- tFrame_l. apply H0.
          -- intro v0. rewrite /tr_expr. fold tr_expr.
             apply (consequence_post
                      (fun v' =>
                          dest_below (For_set sd)
                                     -∗
                                     \s sd_temp sd ∗
                              tr_expr le For_val r1 v
                                      ∗ (\s sd_temp sd
                                          -∗ tr_expr le (For_set (sd_seqbool_set ty sd))
                                          r2 v0)
                                      ∗ ⌜v'.1 =
                              v.1 ++
                                     [makeif v.2
                                             (makeseq v0.1)
                                             (makeseq
                                                (do_set sd (Econst_int Int.zero ty)))]⌝)).
             ++ iIntros (v1) "HA HB". iExists v. iExists v0.
                iDestruct ("HA" with "HB") as "[HA [HB [HC HD]]]". iFrame.
             ++ apply impl_post_id. apply frame_l. tFrame_l. apply ret_spec_bis.
                simpl. iPureIntro. reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro v. destruct dst.
        * apply impl_true_pre. eapply bind_spec.
          -- tFrame_l. apply gensym_spec.
          -- intro v0. eapply bind_spec.
             ++ apply frame_l. tFrame_l. apply H0.
             ++ intro v1. apply impl_true_post.
                rewrite /tr_expr. fold tr_expr. apply (exist v).
                apply (exist v1). apply (exist v0). apply frame_l.
                apply comm_post. apply star_assoc_post. apply frame_l.
                apply (consequence_post
                         (fun v2 =>
                            (dest_below (For_set (sd_seqbool_val v0 ty))
                                                -∗ tr_expr le (For_set (sd_seqbool_val v0 ty)) r2
                                                     v1) ∗
                                                     ⌜v2 =
                            (v.1 ++
                                 [makeif v.2 (Sset v0 (Econst_int Int.one ty))
                                         (makeseq v1.1)], Etempvar v0 ty)⌝)).
                ** iIntros (v2) "HA".
                   iDestruct "HA" as "[HA HB]". iFrame. iIntros "HB".
                   iApply "HA". iExists ty. iApply "HB".
                ** tFrame_l. apply ret_spec.
        * apply impl_true_pre. eapply bind_spec.
          -- tFrame_l. apply H0.
          -- intro v0. rewrite /tr_expr. fold tr_expr.
             apply impl_true_post. apply (exist v). apply (exist v0).
             apply frame_l. apply impl_true_pre. tFrame_l.
             apply ret_spec_bis. iPureIntro. reflexivity.
        * apply impl_true_pre. eapply bind_spec.
          -- tFrame_l. apply H0.
          -- intro v0. rewrite /tr_expr. fold tr_expr.
             apply (consequence_post
                      (fun v' =>
                          dest_below (For_set sd)
                                     -∗
                                     \s sd_temp sd ∗
                              tr_expr le For_val r1 v
                                      ∗ (\s sd_temp sd
                                          -∗ tr_expr le (For_set (sd_seqbool_set ty sd))
                                          r2 v0)
                                      ∗ ⌜v'.1 =
                              v.1 ++
                                     [makeif v.2
                                             (makeseq
                                                (do_set sd (Econst_int Int.one ty)))
                                             (makeseq v0.1)]⌝)).
             ++ iIntros (v1) "HA HB". iExists v. iExists v0.
                iDestruct ("HA" with "HB") as "[HA [HB [HC HD]]]". iFrame.
             ++ apply impl_post_id. apply frame_l. tFrame_l. apply ret_spec_bis.
                simpl. iPureIntro. reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. destruct dst.
        * eapply bind_spec.
          -- tFrame_l. apply gensym_spec.
          -- intro v0. eapply bind_spec.
             ++ apply frame_l. tFrame_l. apply H0.
             ++ intro v1. eapply bind_spec.
                ** apply frame_l. apply frame_l. tFrame_l. apply H1.
                ** intro v2. apply impl_true_post. rewrite /tr_expr. fold tr_expr.
                   apply (exist v). apply (exist v1). apply (exist v2). apply (exist v0).
                   apply frame_l.
                   apply (consequence_post
                            (fun v3 =>
                               v0 ↦ ty ∗
                                  (dest_below (For_set (SDbase ty ty v0))
                                      -∗ tr_expr le (For_set (SDbase ty ty v0)) r2 v1)
                                  ∗ (dest_below (For_set (SDbase ty ty v0))
                                        -∗ tr_expr le (For_set (SDbase ty ty v0)) r3 v2)
                            ∗ ⌜v3 =
                          (v.1 ++
                               [makeif v.2 (makeseq v1.1) (makeseq v2.1)],
                           Etempvar v0 ty)⌝ )).
                   --- iIntros (v3) "HA".
                       iDestruct "HA" as "[HA [HB [HC HD]]]". iFrame.
                       iSplitL "HB"; iIntros "HA".
                       +++ iApply "HB". iExists ty. iApply "HA".
                       +++ iApply "HC". iExists ty. iApply "HA".
                   --- apply frame_l. apply frame_l. tFrame_l. apply ret_spec.
        * eapply bind_spec.
          -- tFrame_l. apply H0.
          -- intro v0. eapply bind_spec.
             ++ apply frame_l. apply impl_true_pre. tFrame_l. apply H1.
             ++ intro v1. apply impl_true_post. rewrite /tr_expr. fold tr_expr.
                apply (exist v). apply (exist v0). apply (exist v1). apply frame_l.
                apply frame_l. apply impl_true_pre. tFrame_l. apply ret_spec_bis.
                iPureIntro. reflexivity.
        * eapply bind_spec.
          -- tFrame_l. apply gensym_spec.
          -- intro v0. eapply bind_spec.
             ++ apply frame_l. tFrame_l. apply H0.
             ++ intro v1. eapply bind_spec.
                *** apply frame_l. apply frame_l. tFrame_l. apply H1.
                *** intro v2. rewrite /tr_expr. fold tr_expr. apply impl_post.
                    apply (exist v). apply (exist v1). apply (exist v2). apply (exist v0).
                    apply frame_l.
                    apply (consequence_post
                             (fun v' =>
                                v0 ↦ ty
                                   ∗ (dest_below (For_set (SDcons ty ty v0 sd))
                                                 -∗ tr_expr le (For_set (SDcons ty ty v0 sd)) r2 v1)
                                   ∗ (dest_below (For_set (SDcons ty ty v0 sd))
                                                 -∗
                                                 tr_expr le (For_set (SDcons ty ty v0 sd)) r3 v2)
                                      ∗ ⌜v'.1 =
                              v.1 ++
                                     [makeif v.2
                                             (makeseq v1.1)
                                             (makeseq v2.1)]⌝)).
                    ---- iIntros (v3) "HA".
                         iDestruct ("HA") as "[HA [HB [HC HD]]]". iFrame.
                         iSplitL "HB".
                         ++++ iIntros "HA". iApply "HB". iExists ty. iApply "HA".
                         ++++ iIntros "HA". iApply "HC". iExists ty. iApply "HA".
                    ---- apply frame_l. apply frame_l. tFrame_l. apply ret_spec_bis.
                         iPureIntro. reflexivity.
    - destruct dst.
      1-2 : apply impl_true_post; apply ret_spec.
      apply impl_post. apply ret_spec.
    - destruct dst.
      1-2 : apply impl_true_post; apply ret_spec.
      apply impl_post. apply ret_spec.
    - eapply bind_spec.
      + apply H.
      + intro v. eapply bind_spec.
        * apply impl_true_pre. tFrame_l. apply H0.
        * intro v0. destruct dst.
          -- eapply bind_spec.
             ++ apply frame_l. apply impl_true_pre. tFrame_l. apply gensym_spec.
             ++ intro v1. apply impl_true_post. rewrite /tr_expr. fold tr_expr.
                apply (exist v). apply (exist v0). apply frame_l. apply frame_l.
                apply tRight. apply (exist v1).
                eapply (consequence_pre (\s v1)).
                ** iIntros "HA". iExists (Csyntax.typeof l). iApply "HA".
                ** tFrame_l. apply ret_spec_bis. iPureIntro. reflexivity.
          -- apply impl_true_post. apply (exist v). apply (exist v0).
             apply frame_l. apply impl_true_pre. tFrame_l. apply tLeft.
             apply ret_spec_bis. iPureIntro. split; reflexivity.
          -- eapply bind_spec.
             ** apply frame_l. apply impl_true_pre. tFrame_l. apply gensym_spec.
             ** intro v1. apply impl_post. apply (exist v). apply (exist v0). apply frame_l.
                apply frame_l. apply tRight. apply (exist v1).
                eapply (consequence_pre (\s v1)).
                --- iIntros. iExists (Csyntax.typeof l). iFrame.
                --- tFrame_l. apply ret_spec_bis. iPureIntro. simpl_list. simpl. admit.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. eapply bind_spec.
        ** tFrame_l. apply H0.
        ** intro v0. destruct dst.
           --- eapply bind_spec.
               +++ apply frame_l. apply impl_true_pre. tFrame_l. apply transl_valof_meets_spec.
               +++ intro v1. eapply bind_spec.
                   *** apply frame_l. apply frame_l. tFrame_l. apply gensym_spec.
                   *** intro v2. apply impl_true_post. apply (exist v). apply (exist v0).
                       apply (exist v1). apply frame_l. apply frame_l. apply frame_l.
                       apply tRight. apply (exist v2). apply (consequence_pre (\s v2)).
                       ---- iIntros. iExists (Csyntax.typeof l). iFrame.
                       ---- tFrame_l. apply ret_spec.
           --- eapply bind_spec.
               +++ apply frame_l. apply impl_true_pre. tFrame_l. apply transl_valof_meets_spec.
               +++ intro v1. apply impl_true_post. apply (exist v). apply (exist v0).
                   apply (exist v1). apply frame_l. apply frame_l. tFrame_l. apply tLeft.
                   apply ret_spec_bis. iPureIntro. split; reflexivity.
           --- eapply bind_spec.
               +++ apply frame_l. apply impl_true_pre. tFrame_l. apply transl_valof_meets_spec.
               +++ intro v1. eapply bind_spec.
                   *** apply frame_l. apply frame_l. tFrame_l. apply gensym_spec.
                   *** intro v2. apply impl_post. apply (exist v). apply (exist v0).
                       apply (exist v1). apply frame_l. apply frame_l. apply frame_l.
                       apply tRight. apply (exist v2).
                       apply (consequence_pre (\s v2)).
                       ---- iIntros. iExists (Csyntax.typeof l). iFrame.
                       ---- tFrame_l. apply ret_spec_bis. iPureIntro. simpl. admit.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. destruct dst.
        * eapply bind_spec.
          -- tFrame_l. apply gensym_spec.
          -- intro v0. apply impl_true_post. rewrite /tr_expr. fold tr_expr. apply tRight.
             apply (exist v). apply (exist v0). apply frame_l.
             eapply (consequence_pre (\s v0)).
             ---- iIntros. iExists (Csyntax.typeof l). iFrame.
             ---- tFrame_l. apply ret_spec.
        * eapply bind_spec.
          -- tFrame_l. apply transl_valof_meets_spec.
          -- intro v0. apply impl_true_post. rewrite /tr_expr. fold tr_expr. apply tLeft.
             apply (exist v). apply (exist v0). apply frame_l. tFrame_l. apply ret_spec_bis.
             iPureIntro. reflexivity.
        * eapply bind_spec.
          -- tFrame_l. apply gensym_spec.
          -- intro v0. apply impl_post. rewrite /tr_expr. fold tr_expr.
             apply tRight. apply (exist v). apply (exist v0). apply frame_l.
             apply (consequence_pre (\s v0)).
             ++ iIntros. iExists (Csyntax.typeof l). iFrame.
             ++ tFrame_l. apply ret_spec_bis. iPureIntro. admit.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. eapply bind_spec.
        * tFrame_l. apply H0.
        * intro v0. rewrite /tr_expr. fold tr_expr.
          apply (consequence_post (fun v' =>
                                     dest_below dst -∗
                                                dest_below dst ∗
                                                tr_expr le For_effects r1 v ∗
                                                (dest_below dst
                                                            -∗ tr_expr le dst r2 (v0.1, v'.2)) ∗
                                                 ⌜v'.1 = v.1 ++ v0.1⌝)).
          -- iIntros (v1) "HA HB". iExists v. iExists v0.1.
             iDestruct ("HA" with "HB") as "[HA [HB [HC HD]]]".
             iFrame.
          -- apply impl_post_id. apply frame_l.
             apply (consequence_pre (dest_below dst -∗ tr_expr le dst r2 (v0.1,v0.2))).
             ++ iIntros "HA". intuition.
             ++ apply ret_frame_l; intuition. iPureIntro. reflexivity.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. eapply bind_spec.
        * tFrame_l.
        * intro v0. destruct dst.
          -- eapply bind_spec.
             ++ apply frame_l. tFrame_l. apply gensym_spec.
             ++ intro v1. apply impl_true_post. apply (exist v). apply (exist v0). apply (exist v1).
                apply frame_l. apply frame_l.
                apply (consequence_pre (\s v1)).
                ** iIntros. iExists ty. iFrame.
                ** tFrame_l. apply ret_spec.
          -- apply impl_true_post. apply (exist v). apply (exist v0). apply frame_l. tFrame_l.
             apply ret_spec_bis. iPureIntro. reflexivity.
          -- eapply bind_spec.
             ++ apply frame_l. tFrame_l. apply gensym_spec.
             ++ intro v1. apply impl_post. apply (exist v). apply (exist v0). apply (exist v1).
                apply frame_l. apply frame_l.
                apply (consequence_pre (\s v1)).
                ** iIntros. iExists ty. iFrame.
                ** tFrame_l. apply ret_spec_bis. iPureIntro. simpl. admit.
    - eapply bind_spec.
      + apply H.
      + intro v. destruct dst.
        * apply impl_true_post. eapply bind_spec.
          -- tFrame_l. apply gensym_spec.
          -- intro v0. apply (exist v). apply (exist v0). apply frame_l.
             apply (consequence_pre (\s v0)).
             ++ iIntros. iExists ty. iFrame.
             ++ tFrame_l. apply ret_spec.
        * apply impl_true_post. apply (exist v). tFrame_l. apply ret_spec_bis.
          iPureIntro. reflexivity.
        * eapply bind_spec.
          -- tFrame_l. apply gensym_spec.
          -- intro v0. apply impl_post. apply (exist v). apply (exist v0).
             apply frame_l. apply (consequence_pre (\s v0)).
             ++ iIntros. iExists ty. iFrame.
             ++ tFrame_l. apply ret_spec_bis. iPureIntro. admit.
    - apply error_spec.
    - apply error_spec.
    - apply ret_spec.
    - eapply bind_spec.
      + apply H.
      + intro v. apply impl_true_pre. eapply bind_spec.
        * tFrame_l.
        * intro v0. apply (exist v). apply (exist v0). apply frame_l.
          tFrame_l. apply ret_spec.
  Admitted.
  
  Definition tr_expression (r : Csyntax.expr) (s : statement) (a: expr) : iProp Σ :=
    ∃ sl, ⌜ s = makeseq sl ⌝ ∗ ∃ le, tr_expr le For_val r (sl,a).
                        
  Lemma transl_expression_meets_spec:
    forall r, |{{ True }}| transl_expression r |{{ res, RET res; tr_expression r (fst res) (snd res) }}|.
  Proof.
    pose (P := transl_meets_spec). destruct P as (P0&P1).
    intro. eapply bind_spec.
    - apply (P0 _ _ Leaf).
    - intro v. unfold tr_expression. apply impl_true_pre. apply (exist v.1).
      apply (consequence_pre (∃ le, tr_expr le For_val r v)).
      + iIntros. iExists Leaf. iFrame.
      + apply ret_frame_r.
        * iPureIntro. intuition.
        * intuition.
  Qed.

  Definition tr_expr_stmt (r : Csyntax.expr) (s : statement) : iProp Σ :=
    ∃ sla, ⌜ s = makeseq sla.1 ⌝ ∗ ∃ le, tr_expr le For_effects r sla.  

  Lemma transl_expr_stmt_meets_spec :
    forall r, |{{ True }}| transl_expr_stmt r |{{ res, RET res; tr_expr_stmt r res }}|.
  Proof.
    pose (P := transl_meets_spec). destruct P as (P0&P1).
    intro. eapply bind_spec.
    - apply (P0 _ _ Leaf).
    - intro v. apply impl_true_pre. apply (exist v).
      apply (consequence_pre (∃ le, tr_expr le For_effects r v)).
      + iIntros. iExists Leaf. iFrame.
      + apply ret_frame_r.
        * iPureIntro. reflexivity.
        * reflexivity. 
  Qed.

  Definition tr_if (r : Csyntax.expr) (s1 : statement) (s2 : statement) (s3 : statement) : iProp Σ :=
    ∃ sla, ⌜ s3 = makeseq (sla.1 ++ makeif sla.2 s1 s2 :: nil) ⌝ ∗ ∃ le, tr_expr le For_val r sla.

  Lemma transl_if_meets_spec :
    forall r s1 s2,
  |{{ True }}| transl_if r s1 s2 |{{ res, RET res; tr_if r s1 s2 res }}|.
  Proof.
    pose (P := transl_meets_spec). destruct P as (P0&P1).
    intros. eapply bind_spec.
    - apply (P0 _ _ Leaf).
    - intro v. apply impl_true_pre. apply (exist v).
      apply (consequence_pre (∃ le, tr_expr le For_val r v)).
      + iIntros. iExists Leaf. iFrame.
      + apply ret_frame_r.
        * iPureIntro. reflexivity.
        * reflexivity. 
  Qed.

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
  with tr_lblstmts (r : Csyntax.labeled_statements) (ls : labeled_statements) : iProp Σ :=
         match r with
         | Csyntax.LSnil => ⌜ ls = LSnil⌝
         | Csyntax.LScons c s ls' =>
           ∃ ts tls,
            tr_stmt s ts ∗
            tr_lblstmts ls' tls ∗
            ⌜ls = LScons c ts tls⌝
         end.

  Lemma transl_stmt_meets_spec : forall s,
      |{{ True }}| transl_stmt s |{{ res, RET res; tr_stmt s res }}|
  with transl_lblstmt_meets_spec:
         forall s,
      |{{ True }}| transl_lblstmt s |{{ res, RET res; tr_lblstmts s res }}|.
  Proof.
    clear transl_stmt_meets_spec.
    generalize transl_expression_meets_spec transl_expr_stmt_meets_spec transl_if_meets_spec; intros T1 T2 T3.
    Opaque transl_expression transl_expr_stmt.
    - induction s; unfold transl_stmt.
      + apply ret_spec.
      + apply T2.
      + eapply bind_spec.
        * apply IHs1.
        * intro v. eapply bind_spec.
          -- tFrame_l. 
          -- intro v0. apply (exist v). apply (exist v0). apply frame_l. tFrame_l. apply ret_spec.
      + eapply bind_spec.
        * apply IHs1.
        * intro v. eapply bind_spec.
          -- tFrame_l.
          -- intro v0. eapply bind_spec.
             ++ apply frame_l. tFrame_l. apply T1.
             ++ intro v1.
                destruct (is_Sskip s1 && is_Sskip s2) eqn:?.
                ** rewrite /tr_stmt. fold tr_stmt. apply ret_spec_complete.
                   iIntros "HA". iDestruct "HA" as "[HA [HB HC]]". iExists v1.2. iFrame.
                   iPureIntro. destruct (is_Sskip s1); destruct (is_Sskip s2) eqn:?. split; auto.
                   apply andb_true_iff in Heqb.
                   destruct Heqb. inversion H0.
                   apply andb_true_iff in Heqb.
                   destruct Heqb. inversion H.
                   apply andb_true_iff in Heqb.
                   destruct Heqb. inversion H0.
                ** rewrite /tr_stmt. fold tr_stmt. apply ret_spec_complete.
                   iIntros "HA". iDestruct "HA" as "[HA [HB HC]]". iExists v1.2. iFrame.
      + eapply bind_spec.
        * apply T3.
        * intro v. eapply bind_spec.
          -- tFrame_l.
          -- intro v0. rewrite /tr_stmt. fold tr_stmt. apply ret_spec_complete.
             iIntros. iFrame.
      + eapply bind_spec.
        * apply T3.
        * intro v. eapply bind_spec.
          -- tFrame_l.
          -- intro v0. rewrite /tr_stmt. fold tr_stmt. apply ret_spec_complete.
             iIntros. iFrame.
      + eapply bind_spec.
        * apply IHs1.
        * intro v. eapply bind_spec.
          -- tFrame_l.
          -- intro v0. eapply bind_spec.
             ++ apply frame_l. tFrame_l.
             ++ intro v1. eapply bind_spec.
                ** apply frame_l. apply frame_l. tFrame_l.
                ** intro v2. destruct (is_Sskip s1).
                   --- rewrite /tr_stmt. fold tr_stmt. apply ret_spec_complete.
                       iIntros "HA". iDestruct "HA" as "[HA [HB [HC HD]]]". iFrame. iPureIntro; auto.
                   --- rewrite /tr_stmt. fold tr_stmt. apply ret_spec_complete.
                       iIntros "HA". iDestruct "HA" as "[HA [HB [HC HD]]]". iFrame. iPureIntro; auto.
      + apply ret_spec.
      + apply ret_spec.
      + destruct o.
        * eapply bind_spec.
          -- apply T1.
          -- intro v. rewrite /tr_stmt. apply ret_spec_complete.
             iIntros. iFrame.
        * apply ret_spec.
      + eapply bind_spec.
        * apply T1.
        * intro v. eapply bind_spec.
          -- tFrame_l.
          -- intro v0. apply ret_spec_complete. iIntros. iFrame.
      + eapply bind_spec.
        * apply IHs.
        * intro v. rewrite /tr_stmt. fold tr_stmt. apply exists_frame_l. apply ret_spec.
      + apply ret_spec.
    - clear transl_lblstmt_meets_spec.
      induction s.
      * apply ret_spec.
      * eapply bind_spec.
        -- apply transl_stmt_meets_spec.
        -- intro v. eapply bind_spec.
           ++ tFrame_l.
           ++ intro v0. apply (exist v). apply (exist v0). apply frame_l. tFrame_l. apply ret_spec.
  Qed.


  Inductive tr_function: Csyntax.function -> Clight.function -> Prop :=
  | tr_function_intro: forall f tf,
      tr_stmt f.(Csyntax.fn_body) tf.(fn_body) ->
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

  Lemma transl_function_spec:
    forall f tf,
      transl_function f = OK tf ->
      tr_function f tf.
  Proof.
    unfold transl_function; intros.
    destruct (run (transl_stmt (Csyntax.fn_body f)) empty_state) eqn:T; inv H.
    econstructor; auto. simpl.
    pose transl_stmt_meets_spec. unfold b. destruct (b (Csyntax.fn_body f)).
    iIntros.

    
  (*   eapply transl_stmt_meets_spec; eauto. *)
  (* Qed. *)

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



           
                       Section TR_TOP.
    
    Variable ge: genv.
    Variable e: env.
    Variable le: temp_env.
    Variable m: mem.
    
    Definition tr_top (dst : destination) (r : Csyntax.expr) (sla : list statement * expr) : iProp Σ :=
      tr_expr le dst r sla ⨈
              match r with
              | Csyntax.Eval v ty =>
                ⌜ typeof sla.2 = ty /\  eval_expr ge e le m sla.2 v /\ sla.1 = nil /\ dst = For_val ⌝
              | _ => False
               end.             
    
  End TR_TOP.
  
  Lemma transl_expr_meets_spec : forall r dst ge e le m,
      |{{ True }}| transl_expr dst r |{{ res, RET res; tr_top ge e le m dst r res }}|.
  Proof.
    intros. pose transl_meets_spec. destruct a.
    
    induction r.
    - destruct v; unfold transl_expr.
      + apply error_spec.
      + destruct dst.
        * apply tRight. apply ret_spec_bis. iPureIntro. split.
          -- reflexivity.
          -- split.
             ++ constructor.
             ++ split; reflexivity.
        * apply tLeft. pose (proj1 transl_meets_spec).
      + reflexivity.
      + split.
        * constructor.
        * split. reflexivity. split; reflexivity.
        
             
                   

                         
                
      

        Lemma dest_below_rewrite_val Φ :
          (dest_below For_val -∗ Φ) -∗ Φ.
        Proof.
          iIntros "HA ".
          iAssert True as "HB"; trivial.
          iDestruct ("HA" with "HB") as "HA".
          iApply "HA".
        Qed.

        Lemma dest_below_rewrite_val_eq Φ :
          (dest_below For_val -∗ Φ) ∗-∗ Φ.
        Proof.    
          iSimpl; iSplit; iIntros "HA".
          - iApply "HA". trivial.
          - iIntros. iApply "HA".
        Qed.
        
        Lemma dest_below_rewrite_effects Φ :
          (dest_below For_effects -∗ Φ) ∗-∗ Φ.
        Proof.
          iSimpl; iSplit; iIntros "HA".
          - iApply "HA". trivial.
          - iIntros. iApply "HA".
        Qed.      

        Hint Rewrite dest_below_rewrite_effects dest_below_rewrite_val : dest_below.
        
        (* Ltac simpl_dest := *)
        (*   let ctx := iGetCtx in *)
        (*   let H := iFresh in *)
        (*   iAssert True as H; *)
        
        (* end. *)
        
        Lemma transl_meets_spec : (forall r dst le,
                                  |{{ True }}| transl_expr dst r |{{ res, RET res;
                                                                  dest_below dst -∗ tr_expr le dst r (fst res) (snd res) }}|)
                                  /\ (forall rl le,
                                    |{{ True }}| transl_exprlist rl |{{ res, RET res; tr_exprlist le rl (fst res) (snd res) }}|).
        Proof.
          apply expr_exprlist_ind. init_proof "HA HB"; iClear "HA".
          { destruct v; simpl; eauto; iApply "HB"; iIntros; destruct dst; eauto;
              iSplit; iIntros; try (iPureIntro; constructor); eauto. }
    { admit. }
   { iPoseProof H as "IH". 
     iApply mwp_bind.
     { iApply "IH". trivial.
       iIntros (res) "HA". 
       iDestruct ("HA" with dest_below_rewrite_val) as "HA".
       iApply dest_below_rewrite_val in "HA".
       iRewrite dest_below_rewrite_val_eq in "HA".
       iAuto. iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val l (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". trivial. iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold. iApply "HB".
       destruct dst; iSimpl; iIntros;
         iExists v.1; iExists v.2; iSplit; eauto; iPureIntro; split; auto;
           rewrite app_nil_r; reflexivity. } }
   
    (*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
    init_proof "HA HB". iClear "HA".
    iInduction r as [| | r | r | r | r | w r | w r1 r2 | r | r1 r2 | r1 r2 | r1 r2 r3 | | | r1 r2 | r1 r2 | r | r1 r2 | r |  |  | r] "IH" forall (Φ dst).
   { destruct v; simpl; eauto; iApply "HB"; iIntros; destruct dst; eauto;
       iSplit; iIntros; try (iPureIntro; constructor); eauto. }
   { iApply "HB". destruct dst; eauto. }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold. iApply "HB".
       destruct dst; iSimpl; iIntros;
         iExists v.1; iExists v.2; iSplit; eauto; iPureIntro; split; auto;
           rewrite app_nil_r; reflexivity. } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold.
       iApply (mwp_bind _ _ _ (fun r0 => tr_rvalof (Csyntax.typeof r) v.2 r0.1 r0.2)).
       { rewrite mwp_unfold. iApply transl_valof_meets_spec; eauto. }
       { iIntros. rewrite mwp_unfold.
         destruct dst; iSimpl; iApply "HB"; iSimpl; iIntros; iExists v.1; iExists v.2; iExists v0.1;
           iFrame; iPureIntro; simpl_list; auto with datatypes. } } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold.
       destruct dst; iSimpl; iApply "HB"; iSimpl; iIntros; iExists v.1; iExists v.2;
         iFrame; iPureIntro; simpl_list; auto with datatypes. } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold.
       destruct dst; iSimpl; iApply "HB"; iSimpl; iIntros; iExists v.1; iExists v.2;
         iFrame; iPureIntro; simpl_list; auto with datatypes. } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold.
       destruct dst; iSimpl; iApply "HB"; iSimpl; iIntros; iExists v.1; iExists v.2;
         iFrame; iPureIntro; simpl_list; auto with datatypes. } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r1 (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold.
       iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r3 (fst res) (snd res))).
       { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA". iApply "HA". eauto. }
       { iIntros (v0) "HC".
         destruct dst; iSimpl; iApply "HB"; iSimpl; iIntros; iExists v.1; iExists v.2;
           iExists v0.1; iExists v0.2;
             iFrame; iPureIntro; simpl_list; auto with datatypes. } } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold.
       destruct dst; iSimpl; iApply "HB"; iSimpl; iIntros; iExists v.1; iExists v.2;
         iFrame; iPureIntro; simpl_list; auto with datatypes. } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r1 (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold.
       destruct dst; iSimpl; try(iApply "HB"; iSimpl; iIntros; iExists v.1; iExists v.2;
                                 iFrame; iPureIntro; simpl_list; auto with datatypes).
       { iIntros (l) "HC".
         iApply (mwp_bind _ _ _ (fun res => l ↦ ty -∗ tr_expr le (For_set (sd_seqbool_val l ty)) r3 (fst res) (snd res)) with "[] [HA HB HC]").
         { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA HB". iApply "HA". iExists ty.
           iApply "HB". }
         { iIntros (v0) "HD". rewrite mwp_unfold. iApply "HB". iIntros. iSimpl.
           iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iExists l. iFrame.
           iPureIntro; auto. } }
       { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_effects r3 (fst res) (snd res))).
         { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA". iApply "HA". eauto. }
         { iIntros (v0) "HC". rewrite mwp_unfold. iApply "HB". iIntros. iSimpl.
           iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iFrame.
           iPureIntro; auto. } }
       { iApply (mwp_bind _ _ _ (fun res => (\s sd_temp sd) -∗ tr_expr le (For_set (sd_seqbool_set ty sd)) r3 (fst res) (snd res))).
         { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA". iApply "HA". }
         { iIntros (v0) "HC". rewrite mwp_unfold. iApply "HB". iIntros. iSimpl.
           iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iFrame.
           iPureIntro; auto. } } } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r1 (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold.
       destruct dst; iSimpl; try(iApply "HB"; iSimpl; iIntros; iExists v.1; iExists v.2;
                                 iFrame; iPureIntro; simpl_list; auto with datatypes).
       { iIntros (l) "HC".
         iApply (mwp_bind _ _ _ (fun res => l ↦ ty -∗ tr_expr le (For_set (sd_seqbool_val l ty)) r3 (fst res) (snd res)) with "[] [HA HB HC]").
         { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA HB". iApply "HA". iExists ty.
           iApply "HB". }
         { iIntros (v0) "HD". rewrite mwp_unfold. iApply "HB". iIntros. iSimpl.
           iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iExists l. iFrame.
           iPureIntro; auto. } }
       { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_effects r3 (fst res) (snd res))).
         { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA". iApply "HA". eauto. }
         { iIntros (v0) "HC". rewrite mwp_unfold. iApply "HB". iIntros. iSimpl.
           iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iFrame.
           iPureIntro; auto. } }
       { iApply (mwp_bind _ _ _ (fun res => (\s sd_temp sd) -∗ tr_expr le (For_set (sd_seqbool_set ty sd)) r3 (fst res) (snd res))).
         { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA". iApply "HA". }
         { iIntros (v0) "HC". rewrite mwp_unfold. iApply "HB". iIntros. iSimpl.
           iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iFrame.
           iPureIntro; auto. } } } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r1 (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". rewrite mwp_unfold.
       destruct dst; iSimpl.
       { iIntros (l) "HC". iApply (mwp_bind _ _ _ (fun res => l ↦ ty -∗ tr_expr le (For_set (SDbase ty ty l)) r3 (fst res) (snd res)) with "[] [HA HB HC]").
         { iApply "IH1". iIntros (res) "HA HB". iApply "HA". iExists ty. iApply "HB". }
         { iIntros (v0) "HD". rewrite mwp_unfold. iApply (mwp_bind).
           { iApply "IH2". iIntros (res) "HA". iApply "HA". }
           { iIntros (v1) "HE". iApply "HB". iIntros. iSimpl. iExists v.1. iExists v.2.
             iExists v0.1. iExists v0.2. iExists v1.1. iExists v1.2. iExists l. iFrame.
             iSplit. iIntros "HA". iApply "HE". iExists ty. iApply "HA".
             iPureIntro; auto. } } }
       { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_effects r3 (fst res) (snd res))).
         { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA". iApply "HA". eauto. }
         { iIntros (v0) "HC".
           iApply (mwp_bind _ _ _ (fun res => tr_expr le For_effects r4 (fst res) (snd res))).
           { rewrite mwp_unfold. iApply "IH2". iIntros (res) "HA". iApply "HA". eauto. }
           { iIntros (v1) "HD". rewrite mwp_unfold. iApply "HB". iIntros.
             iSimpl. iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iExists v1.1.
             iExists v1.2. iFrame. iPureIntro; auto. } } }
       { iIntros (l) "HC".
         iApply (mwp_bind _ _ _(fun res => l ↦ ty -∗ tr_expr le (For_set (SDcons ty ty l sd)) r3 (fst res) (snd res)) with "[] [HA HB HC]").
         { iApply "IH1". iIntros (res) "HA". iIntros. iApply "HA". iExists ty. auto. }
         { iIntros (v0) "HD".
           iApply (mwp_bind _ _ _(fun res => l ↦ ty -∗ tr_expr le (For_set (SDcons ty ty l sd)) r4 (fst res) (snd res)) with "[] [HA HB HC HD]").
           { iApply "IH2". iIntros (res) "HA". iIntros. iApply "HA". iExists ty. auto. }
           { iIntros (v1) "HE". iApply "HB". iIntros.
             iSimpl. iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iExists v1.1.
             iExists v1.2. iExists l. iFrame. iPureIntro; auto. } } } } }
   { destruct dst; iApply "HB"; iIntros; iPureIntro; auto. }
   { destruct dst; iApply "HB"; iIntros; iPureIntro; auto. }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r1 (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA". iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r3 (fst res) (snd res))).
       { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA". iApply "HA". eauto. }
       { iIntros (v0) "HC". destruct dst.
         { rewrite mwp_unfold. iSimpl. iIntros (l) "HD". iApply "HB". iIntros.
           iSimpl. iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iFrame.
           iIntros "False". iDestruct "False" as "[F1 F2]". iApply "F2".
           iExists l. iSplit.
           { iExists (Csyntax.typeof r1); eauto. }
           { iPureIntro; auto. } }
         { iApply "HB". iIntros. iSimpl.
           iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iFrame.
           iIntros "False". iDestruct "False" as "[F1 F2]". iApply "F1".
           iPureIntro; auto. }
         { iIntros (l) "HD". iApply "HB". iIntros.
           iSimpl. iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iFrame.
           iIntros "False". iDestruct "False" as "[F1 F2]". iApply "F2".
           iExists l. iSplit.
           { iExists (Csyntax.typeof r1); eauto. }
           { iPureIntro. admit. } } } } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r2 (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA".
       iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r3 (fst res) (snd res))).
       { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA". iApply "HA". eauto. }
       { iIntros (v0) "HC".
         iApply mwp_bind.
         { iApply transl_valof_meets_spec. trivial. iIntros (r) "HA". iApply "HA". }
         { iIntros (v1) "HD".
           { destruct dst.
             { iIntros (l) "HE". iApply "HB". iIntros. iSimpl.
               iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iExists v1.1.
               iExists v1.2. iFrame.
               iIntros "False". iDestruct "False" as "[F1 F2]". iApply "F2".
               iExists l. iSplit.
               { iExists (Csyntax.typeof r2); eauto. }
               { iPureIntro; auto. } }
             { iApply "HB". iIntros. iSimpl.
               iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iExists v1.1.
               iExists v1.2. iFrame.
               iIntros "False". iDestruct "False" as "[F1 F2]". iApply "F1".
               iPureIntro; auto. }
             { iIntros (l) "HE". iApply "HB". iIntros. iSimpl.
               iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iExists v1.1.
               iExists v1.2. iFrame.
               iIntros "False". iDestruct "False" as "[F1 F2]". iApply "F2".
               iExists l. iSplit.
               { iExists (Csyntax.typeof r2); eauto. }
               { iPureIntro. split; auto. admit. } } } } } } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r0 (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA".
       { destruct dst.
         { iIntros (l) "HE". iApply "HB". iIntros. iSimpl.
           iIntros "False". iDestruct "False" as "[F1 F2]". iApply "F2".
           iExists v.1. iExists v.2.
           iExists l. iFrame. iSplit.
           { iExists (Csyntax.typeof r0); eauto. }
           { iPureIntro; auto. } }
         { iApply mwp_bind.
           { iApply transl_valof_meets_spec. trivial. iIntros (r1) "HA". iApply "HA". }
           { iIntros (v0) "HC". iApply "HB". iIntros.
             iSimpl. iIntros "False". iDestruct "False" as "[F1 F2]". iApply "F1".
             iExists v.1. iExists v.2. iExists v0.1. iExists v0.2. iFrame.
             iPureIntro. auto. } }
         { iIntros (l) "HC". iApply "HB". iIntros. iSimpl.
           iIntros "False". iDestruct "False" as "[F1 F2]". iApply "F2".
           iExists v.1. iExists v.2.
           iExists l. iFrame. iSplit.
           { iExists (Csyntax.typeof r0); eauto. }
           { iPureIntro. split; auto. admit. } } } } }
   { iApply (mwp_bind _ _ _ (fun res => tr_expr le For_effects r1 (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA".
       iApply (mwp_bind _ _ _ (fun res => dest_below dst -∗ tr_expr le dst r3 (fst res) (snd res))).
       { rewrite mwp_unfold. iApply "IH1". iIntros (res) "HA". iApply "HA". }
       { iIntros (v0) "HC". iApply "HB". iIntros "HB".
         iSimpl. iExists v.1. iExists v.2. iExists v0.1.
         iFrame. iPureIntro; auto. } } }
   { iSimpl. iApply (mwp_bind _ _ _ (fun res => tr_expr le For_val r (fst res) (snd res))).
     { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }
     { iIntros (v) "HA".
       iApply (mwp_bind _ _ _ (fun res => tr_expr le For_effects r1 (fst res) (snd res))).
       { rewrite mwp_unfold. iApply "IH". iIntros (res) "HA". iApply "HA". eauto. }

        
          
      Axiom transl_meets_spec :
    forall r dst le,
      triple (transl_expr dst r)
             \[]
             (fun res =>
                dest_below dst -*> tr_expr le dst r (fst res) (snd res)) /\
      (forall rl le,
          triple (transl_exprlist rl)
                 \[]
                 (fun res =>
                    tr_exprlist le rl (fst res) (snd res))).
























  
  (** Triple *)

  Definition heap := list ident.
  Axiom empty : heap.
  Axiom disjoint : heap -> heap -> Prop.
  Axiom union : heap -> heap -> heap.
  Axiom singleton : ident -> heap.
  Definition hprop := heap -> Prop.
  
  Axiom Equal : heap -> heap -> Prop.

  Definition hempty := fun (h : heap) => Equal h empty.

  Definition hsingle (id : ident) : hprop :=
    fun h =>  Equal h (singleton id).
  
  Definition hstar (H1 H2:hprop) : hprop :=
    fun h => exists (h1 h2:heap),
        H1 h1
        /\ H2 h2
        /\ disjoint h1 h2
        /\ h = (union h1 h2).

  Definition hexists (A:Type) (J:A->hprop) : hprop :=
    fun h => exists x, J x h.

  Definition hor (J: Prop) (K : Prop) : hprop :=
    fun h => J \/ K.

  Definition himpl (P Q : hprop) : hprop :=
    fun h => forall h', disjoint h' h /\ P h' -> Q (union h h').

  Notation "P '-*>' Q" := (himpl P Q)
                            (at level 42,right associativity).

  Notation "H1 '\*' H2" := (hstar H1 H2)
                             (at level 41,right associativity).
  Notation "Q \*+ H" := (fun x => (Q x) \* H)
                          (at level 40).
  
  Definition hpure (P:Prop) : hprop :=
    fun h =>  Equal h empty /\ P.
  Notation "\[]" := (hempty)
                      (at level 0).
  Notation "\[ P ]" := (hpure P)
                         (at level 0, P at level 99, format "\[ P ]").
  
  Axiom run : forall X, mon X -> X * heap.

  Axiom triple : forall X, mon X -> hprop -> (X -> hprop) -> Prop.
  Arguments triple {_}.
  
  Axiom rule_let : forall X Y t1 (t2 : X -> mon Y) H Q1 Q,
      triple t1 H Q1 ->
      (forall (X:X), triple (t2 X) (Q1 X) Q) ->
      triple (bind t1 t2) H Q.
  Axiom rule_frame : forall {X} (FMX : mon X) H Q H',
      triple FMX H Q ->
      triple FMX (H \* H') (Q \*+ H').
  Axiom rule_gensym : forall ty,
      triple (gensym ty) \[] (fun l => hsingle l).
  Axiom rule_if : forall X t0 (t1 t2 : mon X) H Q,
      (t0 = true -> triple t1 H Q) ->
      (t0 = false -> triple t2 H Q) ->
      triple (if t0 then t1 else t2) H Q.
  Axiom rule_val : forall {X} (v : X) (H : hprop) (Q : X -> hprop),
      (forall (x : heap), H x -> Q v x) ->
      triple (ret v) H Q.
  Axiom rule_error : forall X s H (Q : X -> hprop),
      triple (error s) H Q.
  Axiom rule_consequence : forall {X} t (H' : hprop) (Q' : X -> hprop) (H : hprop) (Q : X -> hprop),
      (forall (x : heap), H x -> H' x) ->
      triple t H' Q' ->
      (forall x, (forall (v : X), Q' v x -> Q v x)) ->
      triple t H Q.
  Lemma rule_frame_consequence : forall {X} H2 H1 Q1 t (H : hprop) (Q : X -> hprop),
      (forall (x : heap), (H x) -> (H1 \* H2) x )->
      triple t H1 Q1 ->
      (forall x, (forall H, (Q1 \*+ H2) H x -> Q H x)) ->
      triple t H Q.
  Proof.
    intros. eapply (rule_consequence _ _ _ _ _ H0). apply rule_frame. exact H3. exact H4.
  Qed.
  
  Hint Resolve rule_let rule_frame rule_gensym rule_if rule_val rule_error.

  Definition tr_rvalof (ty : type) (e1 : expr) (ls : list statement) (e2 : expr) : hprop :=
    if type_is_volatile ty
    then
      hexists _ (fun t => \[ls = (make_set t e1 :: nil) /\ e2 = Etempvar t ty] \* In t)
    else
      \[e1 = e2 /\ ls = nil].
  
  Fixpoint tr_expr (le : temp_env) (dst : destination) (e : Csyntax.expr) (sl1 : list statement) (a1 : expr) : hprop :=
    match e with
    | Csyntax.Evar id ty => \[sl1 = final dst (Evar id ty) /\ a1 = Evar id ty]
                             
    | Csyntax.Ederef e1 ty =>
      hexists _ (fun sl2 =>
      hexists _ (fun a2 =>
       tr_expr le For_val e1 sl2 a2 \*
       \[sl1 = (sl2 ++ final dst (Ederef' a2 ty)) /\ a1 = Ederef' a2 ty]))
              
    | Csyntax.Efield e1 f ty =>
      hexists _ (fun sl2 =>
      hexists _ (fun a2 =>
      tr_expr le For_val e1 sl2 a2 \*
      \[sl1 = (sl2 ++ final dst (Efield a2 f ty)) /\ a1 = Efield a2 f ty]))

    (* | tr_val_value: forall le v ty a tmp, *)
        (*     typeof a = ty -> *)
        (*     (forall tge e le' m, *)
        (*         (forall id, In id tmp -> le'!id = le!id) -> *)
        (*         eval_expr tge e le' m a v) -> *)
        (*     tr_expr le For_val (Csyntax.Eval v ty) *)
        (*             nil a tmp *)
        (* | tr_val_set: forall le sd v ty a any tmp, *)
        (*     typeof a = ty -> *)
        (*     (forall tge e le' m, *)
        (*         (forall id, In id tmp -> le'!id = le!id) -> *)
        (*         eval_expr tge e le' m a v) -> *)
        (*     tr_expr le (For_set sd) (Csyntax.Eval v ty) *)
    (*             (do_set sd a) any tmp *)
              
    | Csyntax.Eval v ty =>
      match dst with
      | For_effects => \[sl1 = nil]
      | For_val =>
        (fun h =>
           (forall tge e le' m,
               (forall id, In id h -> le'!id = le!id) ->
               eval_expr tge e le' m a1 v)) \*
                                            \[typeof a1 = ty /\ sl1 = nil]
      | For_set sd =>
        (fun h =>
           (forall tge e le' m,
               (forall id, In id h -> le'!id = le!id) ->
               eval_expr tge e le' m a1 v)) \*
                                            \[typeof a1 = ty /\ sl1 = do_set sd a1]
      end
        
    | Csyntax.Esizeof ty' ty =>
      \[sl1 = final dst (Esizeof ty' ty) /\
        a1 = Esizeof ty' ty]

    | Csyntax.Ealignof ty' ty =>
      \[sl1 = final dst (Ealignof ty' ty) /\
        a1 = Ealignof ty' ty]
       
    | Csyntax.Evalof e1 ty =>
      hexists _ (fun sl2 =>
                   hexists _ (fun a2 =>
                                hexists _ (fun sl3 =>
                                             tr_expr le For_val e1 sl2 a2 \*
                                                     tr_rvalof (Csyntax.typeof e1) a2 sl3 a1 \*
                                                     \[sl1 = (sl2 ++ sl3 ++ final dst a1)])))

    | Csyntax.Eaddrof e1 ty =>
      hexists _ (fun sl2 =>
                   hexists _ (fun a2 =>
                                tr_expr le For_val e1 sl2 a2 \*
                                        \[sl1 = sl2 ++ final dst (Eaddrof' a2 ty) /\ a1 = Eaddrof' a2 ty]))

    | Csyntax.Eunop op e1 ty =>
      hexists _ (fun sl2 =>
                   hexists _ (fun a2 =>
                                tr_expr le For_val e1 sl2 a2 \*
                                        \[sl1 = sl2 ++ final dst (Eunop op a2 ty) /\ a1 = Eunop op a2 ty]))
              
    | Csyntax.Ebinop op e1 e2 ty =>
      hexists _ (fun sl2 =>
                   hexists _ (fun a2 =>
                                hexists _ (fun sl3 =>
                                             hexists _ (fun a3 =>
                                                          tr_expr le For_val e1 sl2 a2 \*
                                                                  tr_expr le For_val e2 sl3 a3 \*
                                                                  \[sl1 = sl2 ++ sl3 ++ final dst (Ebinop op a2 a3 ty) /\ a1 = Ebinop op a2 a3 ty]))))
              
    | Csyntax.Ecast e1 ty =>
      hexists _ (fun sl2 =>
                   hexists _ (fun a2 =>
                                tr_expr le For_val e1 sl2 a2 \*
                                        \[sl1 = sl2 ++ final dst (Ecast a2 ty) /\ a1 = Ecast a2 ty]))

    | Csyntax.Eseqand e1 e2 ty =>
      match dst with
      | For_val =>
        hexists _ (fun sl2 =>
          hexists _ (fun a2 =>
          hexists _ (fun sl3 =>
          hexists _ (fun a3 =>            
          hexists _ (fun t =>
           tr_expr le For_val e1 sl2 a2 \*
           tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl3 a3 \*
           In t \*
           \[ sl1 = sl2 ++ makeif a2 (makeseq sl3) (Sset t (Econst_int Int.zero ty)) :: nil /\
           a1 = Etempvar t ty]))))) 
                  
      | For_effects =>
        hexists _ (fun sl2 =>
        hexists _ (fun a2 =>
        hexists _ (fun sl3 =>
        hexists _ (fun a3 =>            
        tr_expr le For_val e1 sl2 a2 \*
        tr_expr le For_effects e2 sl3 a3 \*
        \[ sl1 = sl2 ++ makeif a2 (makeseq sl3) Sskip :: nil]))))
                
      | For_set sd =>
          hexists _ (fun sl2 =>
          hexists _ (fun a2 =>
          hexists _ (fun sl3 =>
          hexists _ (fun a3 =>            
          tr_expr le For_val e1 sl2 a2 \*
          tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl3 a3 \*
          In (sd_temp sd) \*        
          \[sl1 = sl2 ++ makeif a2 (makeseq sl3) (makeseq (do_set sd (Econst_int Int.zero ty)))
                                                                                  :: nil]))))
      end

    | Csyntax.Eseqor e1 e2 ty =>
      match dst with
      | For_val =>
        hexists _ (fun sl2 =>
        hexists _ (fun a2 =>
        hexists _ (fun sl3 =>
        hexists _ (fun a3 =>            
        hexists _ (fun t =>
        tr_expr le For_val e1 sl2 a2 \*
        tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl3 a3 \*
        In t  \*
        \[sl1 = sl2 ++ makeif a2 (Sset t (Econst_int Int.one ty)) (makeseq sl3) :: nil /\
        a1 = Etempvar t ty]))))) 
                  
      | For_effects =>
        hexists _ (fun sl2 =>
        hexists _ (fun a2 =>
        hexists _ (fun sl3 =>
        hexists _ (fun a3 =>            
        tr_expr le For_val e1 sl2 a2 \*
        tr_expr le For_effects e2 sl3 a3 \*
        \[sl1 = sl2 ++ makeif a2 Sskip (makeseq sl3) :: nil]))))
                
      | For_set sd =>
        hexists _ (fun sl2 =>
        hexists _ (fun a2 =>
        hexists _ (fun sl3 =>
        hexists _ (fun a3 =>            
        tr_expr le For_val e1 sl2 a2 \*
        tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl3 a3 \*
        In (sd_temp sd) \*        
        \[sl1 = sl2 ++ makeif a2 (makeseq (do_set sd (Econst_int Int.one ty))) (makeseq sl3)
                    :: nil]))))
      end

    | Csyntax.Econdition e1 e2 e3 ty =>
      match dst with
      | For_val =>
        hexists _ (fun sl2 =>
        hexists _ (fun a2 =>
        hexists _ (fun sl3 =>
        hexists _ (fun a3 =>
        hexists _ (fun sl4 =>
        hexists _ (fun a4 =>
        hexists _ (fun t =>
        tr_expr le For_val e1 sl2 a2 \*
        (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de 
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1, 
          ce sera encore provable avec tr_expr_incl *)
        (fun h1 =>
        tr_expr le (For_set (SDbase ty ty t)) e2 sl3 a3 h1 /\
        tr_expr le (For_set (SDbase ty ty t)) e3 sl4 a4 h1) \*
        In t \*
        \[sl1 = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil /\
        a1 = Etempvar t ty])))))))
          
      | For_effects =>
        hexists _ (fun sl2 =>
        hexists _ (fun a2 =>
        hexists _ (fun sl3 =>
        hexists _ (fun a3 =>
        hexists _ (fun sl4 =>
        hexists _ (fun a4 =>
        tr_expr le For_val e1 sl2 a2 \*
        (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de 
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1, 
          ce sera encore provable avec tr_expr_incl *)
        (fun h1 => 
        tr_expr le For_effects e2 sl3 a3 h1 /\
        tr_expr le For_effects e3 sl4 a4 h1) \*
        \[sl1 = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil]))))))
                
      | For_set sd =>
        fun h =>
        hexists _ (fun sl2 =>
        hexists _ (fun a2 =>
        hexists _ (fun sl3 =>
        hexists _ (fun a3 =>
        hexists _ (fun sl4 =>
        hexists _ (fun a4 =>
        hexists _ (fun t =>
        tr_expr le For_val e1 sl2 a2 \*
        (** Il y avait une utilisation de tmp3 et tmp4 qui n'était pas forcement disjoint l'un de 
          l'autre mais bien de la partie ci-dessus. tmp3 et tmp4 doivent logiquemen inclus dans h1, 
          ce sera encore provable avec tr_expr_incl *)
        (fun h1 => 
        tr_expr le (For_set (SDcons ty ty t sd)) e2 sl3 a3 h1 /\
        tr_expr le (For_set (SDcons ty ty t sd)) e3 sl4 a4 h1) \*
        In t \*
        \[sl1 = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil]))))))) h
      end
        
    | Csyntax.Eassign e1 e2 ty =>
      hexists _ (fun sl2 =>
      hexists _ (fun a2 =>
      hexists _ (fun sl3 =>
      hexists _ (fun a3 =>
      tr_expr le For_val e1 sl2 a2 \*
      tr_expr le For_val e2 sl3 a3 \*
      fun h =>
      ( sl1 = sl2 ++ sl3 ++ make_assign a2 a3 :: nil /\  dst = For_effects) \/
      (hexists _ (fun t =>
      In t \*
      \[sl1 = sl2 ++ sl3 ++ Sset t (Ecast a3 (Csyntax.typeof e1)) ::
      make_assign a2 (Etempvar t (Csyntax.typeof e1)) ::
      final dst (Etempvar t (Csyntax.typeof e1))]) h)))))

    | Csyntax.Eassignop op e1 e2 tyres ty =>
      hexists _ (fun sl2 =>
      hexists _ (fun a2 =>
      hexists _ (fun sl3 =>
      hexists _ (fun a3 =>
      hexists _ (fun sl4 =>
      hexists _ (fun a4 =>
      tr_expr le For_val e1 sl2 a2 \*
      tr_expr le For_val e2 sl3 a3 \*
      tr_rvalof (Csyntax.typeof e1) a2 sl4 a4 \*
      fun h =>
      ((dst = For_effects /\
      sl1 = sl2 ++ sl3 ++ sl4 ++ make_assign a2 (Ebinop op a4 a3 tyres) :: nil) \/
      hexists _ (fun t => In t \*
      \[sl1 = sl2 ++ sl3 ++ sl4 ++
      Sset t (Ecast (Ebinop op a4 a3 tyres) (Csyntax.typeof e1)) ::
      make_assign a2 (Etempvar t (Csyntax.typeof e1)) ::
      final dst (Etempvar t (Csyntax.typeof e1)) /\
      a1 = (Etempvar t (Csyntax.typeof e1))]) h)))))))
      
    | Csyntax.Epostincr id e1 ty =>
      fun h =>
      (hexists _ (fun sl2 =>
      hexists _ (fun a2 =>
      hexists _ (fun sl3 =>
      hexists _ (fun a3 =>
      tr_expr le For_val e1 sl2 a2 \*
      tr_rvalof (Csyntax.typeof e1) a2 sl3 a3 \*
      \[sl1 = sl2 ++ sl3 ++
      make_assign a2 (transl_incrdecr id a3 (Csyntax.typeof e1)) :: nil])))) h) \/
      (hexists _ (fun sl2 =>
      hexists _ (fun a2 =>
      hexists _ (fun t =>                         
      tr_expr le For_val e1 sl2 a2 \*
      In t \*
      \[sl1 = sl2 ++ make_set t a2 ::
      make_assign a2 (transl_incrdecr id (Etempvar t (Csyntax.typeof e1)) (Csyntax.typeof e1)) ::
      final dst (Etempvar t (Csyntax.typeof e1)) /\
      a1 = Etempvar t (Csyntax.typeof e1)]))) h)
      
    | Csyntax.Ecomma e1 e2 ty =>
      hexists _ (fun sl2 =>
                   hexists _ (fun a2 =>
                                hexists _ (fun sl3 =>
                                             tr_expr le For_effects e1 sl2 a2 \*
                                                     tr_expr le dst e2 sl3 a1 \*
                                                     \[sl1 = sl2 ++ sl3])))

    | Csyntax.Ecall e1 el2 ty =>
      match dst with
      | For_effects =>
        hexists _ (fun sl2 =>
        hexists _ (fun a2 =>
        hexists _ (fun sl3 =>
        hexists _ (fun al3 =>                         
        tr_expr le For_val e1 sl2 a2 \*
        tr_exprlist le el2 sl3 al3 \*
        \[ sl1 = sl2 ++ sl3 ++ Scall None a2 al3 :: nil]))))
      | _ =>
        fun h =>
        hexists _ (fun sl2 =>
        hexists _ (fun a2 =>
        hexists _ (fun sl3 =>
        hexists _ (fun al3 =>
        hexists _ (fun t =>                         
        tr_expr le For_val e1 sl2 a2 \*
        tr_exprlist le el2 sl3 al3 \*
        In t \*
        \[sl1 = sl2 ++ sl3 ++ Scall (Some t) a2 al3 :: final dst (Etempvar t ty) /\
        a1 = Etempvar t ty]))))) h
      end

    | Csyntax.Ebuiltin ef tyargs el ty =>
      match dst with
      | For_effects =>
        hexists _ (fun sl2 =>
        hexists _ (fun al2 =>
        tr_exprlist le el sl2 al2 \*
        \[sl1 = sl2 ++ Sbuiltin None ef tyargs al2 :: nil]))
      | _ =>
        fun h =>
        hexists _ (fun sl2 =>
        hexists _ (fun al2 =>
        hexists _ (fun t =>
        tr_exprlist le el sl2 al2 \*
        In t \*
        \[sl1 = sl2 ++ Sbuiltin (Some t) ef tyargs al2 :: final dst (Etempvar t ty) /\
        a1 = Etempvar t ty]))) h
      end

    | Csyntax.Eparen e1 tycast ty =>
      match dst with
      | For_val =>
        hexists _ (fun a2 =>
        hexists _ (fun t =>
        tr_expr le (For_set (SDbase tycast ty t)) e1 sl1 a2 \*
        In t \*
        \[a1 = Etempvar t ty]))
      | For_effects =>
        hexists _ (fun a2 =>  tr_expr le For_effects e1 sl1 a2)
      | For_set sd =>
        hexists _ (fun a2 =>
        hexists _ (fun t =>
        tr_expr le (For_set (SDcons tycast ty t sd)) e1 sl1 a2 \* In t))
      end

    | _ => fun h => False
    end
  with tr_exprlist (le : temp_env) (e : Csyntax.exprlist) (sl1 : list statement) (a1 : list expr) : hprop :=
         match e with
         | Csyntax.Enil => \[sl1 = nil /\ a1 = nil]
         | Csyntax.Econs e1 el2 =>
           hexists _ (fun sl2 =>
           hexists _ (fun a2 =>
           hexists _ (fun sl3 =>
           hexists _ (fun al3 =>
           tr_expr le For_val e1 sl2 a2 \*
           tr_exprlist le el2 sl3 al3 \*
           \[sl1 = sl2 ++ sl3 /\ a1 = a2 :: al3]))))
         end.


  Axiom ok1 : forall x X, hsingle X x -> In X x.
  Axiom ok2 : forall x, Equal x x.
  Axiom ok3 : forall x, disjoint x empty.
  Axiom ok4 : forall x, x = union x empty.
  Axiom ok5 : forall x, Equal x empty <-> x = empty.
  Axiom ok6 : forall x, disjoint empty x.
  Axiom ok7 : forall x, x = union empty x.
  Axiom ok8 : forall x1 x2 x3, Equal x3 empty -> x1 = union x2 x3 -> x1 = x2.
  Axiom union_sym : forall x y, union x y = union y x.
  Axiom disjoint_sym : forall x y, disjoint x y -> disjoint y x.
  Axiom hstar_assoc : forall (H1 H2 H3:hprop) (h:heap),
      ((H1 \* (H2 \* H3)) h) <-> (((H1 \* H2) \* H3) h).
  Axiom hstar_comm : forall (H1 H2:hprop) (h:heap),
      ((H1 \* H2) h) ->
      ((H2 \* H1) h).

  Hint Resolve ok1 ok2 ok3 ok4 ok5 ok6 ok7 app_nil_r app_assoc.
  
  
  Lemma transl_valof_meets_spec: forall ty a,
      triple (transl_valof ty a) \[] (fun r => tr_rvalof ty a (fst r) (snd r)).
  Proof.
    intros. unfold transl_valof. unfold tr_rvalof.  apply rule_if; intro.
    - eapply rule_let.
      + apply rule_gensym.
      + intros. rewrite H. apply rule_val.
        intros. exists X. exists empty. exists x. repeat split; auto.
    - apply rule_val. intros. rewrite H. split; auto.
  Qed.

  

  Definition dest_below (dst: destination) : hprop:=
    match dst with
    | For_set sd => hsingle (sd_temp sd)
    | _ => \[]
    end.


  Axiom transl_meets_spec :
    forall r dst le,
      triple (transl_expr dst r)
             \[]
             (fun res =>
                dest_below dst -*> tr_expr le dst r (fst res) (snd res)) /\
      (forall rl le,
          triple (transl_exprlist rl)
                 \[]
                 (fun res =>
                    tr_exprlist le rl (fst res) (snd res))).
  
  


  Section TR_TOP.
    
    Variable ge: genv.
    Variable e: env.
    Variable le: temp_env.
    Variable m: mem.
    
    Definition tr_top (dst : destination) (r : Csyntax.expr) (sl : list statement) (a : expr) : hprop :=
      fun h => tr_expr le dst r sl a h \/
               match r with
               | Csyntax.Eval v ty =>
                 typeof a = ty /\  eval_expr ge e le m a v /\ sl = nil /\ dst = For_val
               | _ => False
               end.             
    
  End TR_TOP.

  Axiom transl_expr_meets_spec :
    forall r dst ge e le m,
      triple (transl_expr dst r)
             \[]
             (fun res => tr_top ge e le m dst r (fst res) (snd res)).

  (* Inductive tr_expression: Csyntax.expr -> statement -> expr -> Prop := *)
  (*       | tr_expression_intro: forall r sl a tmps, *)
  (*           (forall ge e le m, tr_top ge e le m For_val r sl a tmps) -> *)
  (*           tr_expression r (makeseq sl) a. *)
  
  Definition tr_expression (r : Csyntax.expr) (s : statement) (a: expr) : hprop :=
    hexists _ (fun sl =>
    \[ s = makeseq sl] \*
    (hexists _ (fun ge =>              
     hexists _ (fun e =>              
     hexists _ (fun le =>
     hexists _ (fun m =>
                  tr_top ge e le m For_val r sl a)))))).

  
  Definition tr_expr_stmt (r : Csyntax.expr) (s : statement) : hprop :=
    hexists _ (fun sl =>
    hexists _ (fun a =>             
     \[ s = makeseq sl] \*
    (hexists _ (fun ge =>              
     hexists _ (fun e =>              
     hexists _ (fun le =>
                  hexists _ (fun m => tr_top ge e le m For_effects r sl a))))))).

  Definition tr_if (r : Csyntax.expr) (s1 : statement) (s2 : statement) (s3 : statement) : hprop :=
    hexists _ (fun sl =>
    hexists _ (fun a =>
    \[ s3 = makeseq ( sl ++ makeif a s1 s2 :: nil)] \*                          
    (hexists _ (fun ge =>              
     hexists _ (fun e =>              
     hexists _ (fun le =>
     hexists _ (fun m =>
                  tr_top ge e le m For_val r sl a))))))).

  
  Fixpoint tr_stmt (r : Csyntax.statement) (s : statement) :=
    match r with
    | Csyntax.Sskip =>
      \[ s = Sskip ]
    | Csyntax.Sdo r =>
      tr_expr_stmt r s                   
    | Csyntax.Ssequence s1 s2 =>
      hexists _ (fun ts1 =>
      hexists _ (fun ts2 =>
                   tr_stmt s1 ts1 \* tr_stmt s2 ts2 \* \[ s = Ssequence ts1 ts2]))              
    | Csyntax.Sifthenelse r1 s1 s2 =>
      match s with
      | Ssequence s' Sskip =>
        hexists _ (fun a =>
                     \[ s1 = Csyntax.Sskip /\ s2 = Csyntax.Sskip] \* tr_expression r1 s' a)                
      | Ssequence s' (Sifthenelse a ts1 ts2) =>
        hexists _ (fun a =>
                     tr_expression r1 s' a \* tr_stmt s1 ts1 \* tr_stmt s2 ts2)
      | _ => fun h => False
      end        
    | Csyntax.Swhile r1 s1 =>
      match s with
      | Sloop (Ssequence s' ts1) Sskip =>
        tr_if r1 Sskip Sbreak s' \*
        tr_stmt s1 ts1
      | _ => fun h => False
      end              
    | Csyntax.Sdowhile r s1 =>
      match s with
      | Sloop ts1 s' =>
        tr_if r Sskip Sbreak s' \*
              tr_stmt s1 ts1
      | _ => fun h => False
      end
    | Csyntax.Sfor s1 r s3 s4 =>
      match s with
      | Sloop (Ssequence s' ts4) ts3 =>
        tr_if r Sskip Sbreak s' \*
        tr_stmt s3 ts3 \*
        tr_stmt s4 ts4 \*
        \[ s1 = Csyntax.Sskip]
      | Ssequence ts1 (Sloop (Ssequence s' ts4) ts3) =>
        tr_if r Sskip Sbreak s' \*
        tr_stmt s1 ts1 \*
        tr_stmt s3 ts3 \*
        tr_stmt s4 ts4 \*
        \[ s1 <> Csyntax.Sskip]
      | _ => fun h => False
      end        
    | Csyntax.Sbreak =>
      \[ s = Sbreak]       
    | Csyntax.Scontinue =>
      \[ s = Scontinue]       
    | Csyntax.Sreturn None =>
      \[ s = Sreturn None]       
    | Csyntax.Sreturn (Some r) =>
      match s with
      | Ssequence s' (Sreturn (Some a)) =>
        tr_expression r s' a
      | _ => fun h => False
      end
    | Csyntax.Sswitch r ls =>
      match s with
      | Ssequence s' (Sswitch a tls) =>
        tr_expression r s' a \*
        tr_lblstmts ls tls
      | _ => fun h => False
      end
    | Csyntax.Slabel lbl s' =>
      hexists _ (fun ts =>
                   tr_stmt s' ts \* \[ s = Slabel lbl ts])
    | Csyntax.Sgoto lbl =>
      \[ s = Sgoto lbl]
    end
  with tr_lblstmts (r : Csyntax.labeled_statements) (ls : labeled_statements) : hprop :=
         match r with
         | Csyntax.LSnil => \[ ls = LSnil]
         | Csyntax.LScons c s ls' =>
           hexists _ (fun ts =>
           hexists _ (fun tls =>
            tr_stmt s ts \*
            tr_lblstmts ls' tls \*
            \[ls = LScons c ts tls]))
         end.
  
  Axiom transl_expression_meets_spec:
    forall r,
      triple (transl_expression r) \[] (fun res => tr_expression r (fst res) (snd res)).

  Axiom transl_expr_stmt_meets_spec :
    forall r,
      triple (transl_expr_stmt r)
             \[]
             (fun res => tr_expr_stmt r res).

  Axiom transl_if_meets_spec :
    forall r s1 s2,
      triple (transl_if r s1 s2)
             \[]
             (fun res => tr_if r s1 s2 res).

  Axiom transl_stmt_meets_spec : forall s,
    triple (transl_stmt s)
           \[]
           (fun res => tr_stmt s res).
  
  Axiom transl_lblstmt_meets_spec : forall s,
        triple (transl_lblstmt s)
               \[]
               (fun res => tr_lblstmts s res).

  Inductive tr_function: Csyntax.function -> Clight.function -> Prop :=
  | tr_function_intro: forall f tf h,
      tr_stmt f.(Csyntax.fn_body) tf.(fn_body) h ->
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

  Lemma transl_function_spec:
    forall f tf,
      transl_function f = OK tf ->
      tr_function f tf.
  Proof.
    unfold transl_function; intros.
    destruct (transl_stmt (Csyntax.fn_body f) (initial_generator tt)) eqn:T; inv H.
    econstructor; auto. simpl.
    pose transl_stmt_meets_spec. Admitted.
  (*   eapply transl_stmt_meets_spec; eauto. *)
  (* Qed. *)

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

  
  (* Fixpoint tr_expr (le : temp_env) (dst : destination) (e : Csyntax.expr) (sl1 : list statement) (a1 : expr) (tmp : list ident) : Prop := *)
  (*   match e with *)
  (*   | Csyntax.Evar id ty => sl1 = final dst (Evar id ty) /\ a1 = Evar id ty *)
  (*   | Csyntax.Ederef e1 ty => exists sl2 a2, tr_expr le For_val e1 sl2 a2 tmp /\ sl1 = (sl2 ++ final dst (Ederef' a2 ty)) /\ a1 = Ederef' a2 ty *)
  (*   | Csyntax.Efield e1 f ty => exists sl2 a2, tr_expr le For_val e1 sl2 a2 tmp /\ *)
  (*                                              sl1 = (sl2 ++ final dst (Efield a2 f ty)) /\ *)
  (*                                              a1 = Efield a2 f ty *)
  (*   | Csyntax.Eval v ty => *)
  (*     match dst with *)
  (*     | For_effects => sl1 = nil *)
  (*     | For_val => (forall tge e le' m, *)
  (*                      (forall id, In id tmp -> le'!id = le!id) -> *)
  (*                      eval_expr tge e le' m a1 v) /\ *)
  (*                  typeof a1 = ty /\ *)
  (*                  sl1 = nil *)
  (*     | For_set sd => *)
  (*       (forall tge e le' m, *)
  (*           (forall id, In id tmp -> le'!id = le!id) -> *)
  (*           eval_expr tge e le' m a1 v) *)
  (*       /\ typeof a1 = ty *)
  (*       /\ sl1 = do_set sd a1 *)
  (*     end *)
  (*   | Csyntax.Esizeof ty' ty => sl1 = final dst (Esizeof ty' ty) /\ *)
  (*                               a1 = Esizeof ty' ty *)
  (*   | Csyntax.Ealignof ty' ty => sl1 = final dst (Ealignof ty' ty) /\ *)
  (*                                a1 = Ealignof ty' ty *)
  (*   | Csyntax.Evalof e1 ty => *)
  (*     exists sl2 a2 sl3 tmp2 tmp3, *)
  (*     tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*     tr_rvalof (Csyntax.typeof e1) a2 sl3 a1 tmp3 /\ *)
  (*     list_disjoint tmp2 tmp3 /\ *)
  (*     incl tmp2 tmp /\ *)
  (*     incl tmp3 tmp /\ *)
  (*     sl1 = (sl2 ++ sl3 ++ final dst a1) *)
  (*   | Csyntax.Eaddrof e1 ty => *)
  (*     exists sl2 a2, *)
  (*     tr_expr le For_val e1 sl2 a2 tmp /\ *)
  (*     sl1 = sl2 ++ final dst (Eaddrof' a2 ty) /\ *)
  (*     a1 = Eaddrof' a2 ty *)
  (*   | Csyntax.Eunop op e1 ty => *)
  (*     exists sl2 a2, tr_expr le For_val e1 sl2 a2 tmp /\ *)
  (*                    sl1 = sl2 ++ final dst (Eunop op a2 ty) /\ *)
  (*                    a1 = Eunop op a2 ty     *)
  (*   | Csyntax.Ebinop op e1 e2 ty => *)
  (*     exists sl2 a2 sl3 a3 tmp2 tmp3, tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*                                     tr_expr le For_val e2 sl3 a3 tmp3 /\ *)
  (*                                     list_disjoint tmp2 tmp3 /\ *)
  (*                                     incl tmp2 tmp /\ *)
  (*                                     incl tmp3 tmp /\ *)
  (*                                     sl1 = sl2 ++ sl3 ++ final dst (Ebinop op a2 a3 ty) /\ *)
  (*                                     a1 = Ebinop op a2 a3 ty *)
  (*   | Csyntax.Ecast e1 ty => *)
  (*     exists sl2 a2, tr_expr le For_val e1 sl2 a2 tmp /\ *)
  (*                    sl1 = sl2 ++ final dst (Ecast a2 ty) /\ *)
  (*                    a1 = Ecast a2 ty *)
  (*   | Csyntax.Eseqand e1 e2 ty => *)
  (*     match dst with *)
  (*     | For_val => *)
  (*       exists sl2 a2 tmp2 sl3 a3 tmp3 t, *)
  (*       tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*       tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl3 a3 tmp3 /\ *)
  (*       list_disjoint tmp2 tmp3 /\ *)
  (*       incl tmp2 tmp /\ *)
  (*       incl tmp3 tmp /\ *)
  (*       In t tmp /\ *)
  (*       sl1 = sl2 ++ makeif a2 (makeseq sl3) (Sset t (Econst_int Int.zero ty)) :: nil /\ *)
  (*       a1 = Etempvar t ty *)
  (*     | For_effects => *)
  (*       exists sl2 a2 tmp2 sl3 a3 tmp3, *)
  (*       tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*       tr_expr le For_effects e2 sl3 a3 tmp3 /\ *)
  (*       list_disjoint tmp2 tmp3 /\ *)
  (*       incl tmp2 tmp /\ *)
  (*       incl tmp3 tmp /\ *)
  (*       sl1 = sl2 ++ makeif a2 (makeseq sl3) Sskip :: nil *)
  (*     | For_set sd => *)
  (*       exists sl2 a2 tmp2 sl3 a3 tmp3, *)
  (*       tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*       tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl3 a3 tmp3 /\ *)
  (*       list_disjoint tmp2 tmp3 /\ *)
  (*       incl tmp2 tmp /\ *)
  (*       incl tmp3 tmp /\ *)
  (*       In (sd_temp sd) tmp /\ *)
  (*       sl1 = sl2 ++ makeif a2 (makeseq sl3) (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil *)
  (*     end *)
  (*   | Csyntax.Eseqor e1 e2 ty => *)
  (*     match dst with *)
  (*     | For_val => *)
  (*       exists sl2 a2 tmp2 sl3 a3 tmp3 t, *)
  (*       tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*       tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl3 a3 tmp3 /\ *)
  (*       list_disjoint tmp2 tmp3 /\ *)
  (*       incl tmp2 tmp /\ *)
  (*       incl tmp3 tmp /\ *)
  (*       In t tmp /\ *)
  (*       sl1 = sl2 ++ makeif a2 (Sset t (Econst_int Int.one ty)) (makeseq sl3) :: nil /\ *)
  (*       a1 = Etempvar t ty *)
  (*     | For_effects => *)
  (*       exists sl2 a2 tmp2 sl3 a3 tmp3, *)
  (*       tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*       tr_expr le For_effects e2 sl3 a3 tmp3 /\ *)
  (*       list_disjoint tmp2 tmp3 /\ *)
  (*       incl tmp2 tmp /\ *)
  (*       incl tmp3 tmp /\ *)
  (*       sl1 = sl2 ++ makeif a2 Sskip (makeseq sl3) :: nil *)
  (*     | For_set sd => *)
  (*       exists sl2 a2 tmp2 sl3 a3 tmp3, *)
  (*       tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*       tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl3 a3 tmp3 /\ *)
  (*       list_disjoint tmp2 tmp3 /\ *)
  (*       incl tmp2 tmp /\ *)
  (*       incl tmp3 tmp /\ *)
  (*       In (sd_temp sd) tmp /\ *)
  (*       sl1 = sl2 ++ makeif a2 (makeseq (do_set sd (Econst_int Int.one ty))) (makeseq sl3) :: nil *)
  (*     end *)
  (*   | Csyntax.Econdition e1 e2 e3 ty => *)
  (*     match dst with *)
  (*     | For_val => *)
  (*       exists sl2 a2 tmp2 sl3 a3 tmp3 sl4 a4 tmp4 t, *)
  (*       tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*       tr_expr le (For_set (SDbase ty ty t)) e2 sl3 a3 tmp3 /\ *)
  (*       tr_expr le (For_set (SDbase ty ty t)) e3 sl4 a4 tmp4 /\ *)
  (*       list_disjoint tmp2 tmp3 /\ *)
  (*       list_disjoint tmp2 tmp4 /\ *)
  (*       incl tmp2 tmp /\ *)
  (*       incl tmp3 tmp /\ *)
  (*       incl tmp4 tmp /\ *)
  (*       In t tmp /\ *)
  (*       sl1 = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil /\ *)
  (*       a1 = Etempvar t ty *)
  (*     | For_effects => *)
  (*       exists sl2 a2 tmp2 sl3 a3 tmp3 sl4 a4 tmp4, *)
  (*       tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*       tr_expr le For_effects e2 sl3 a3 tmp3 /\ *)
  (*       tr_expr le For_effects e3 sl4 a4 tmp4 /\ *)
  (*       list_disjoint tmp2 tmp3 /\ *)
  (*       list_disjoint tmp2 tmp4 /\ *)
  (*       incl tmp2 tmp /\ *)
  (*       incl tmp3 tmp /\ *)
  (*       incl tmp4 tmp /\ *)
  (*       sl1 = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil *)
  (*     | For_set sd => *)
  (*       exists sl2 a2 tmp2 sl3 a3 tmp3 sl4 a4 tmp4 t, *)
  (*       tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
  (*       tr_expr le (For_set (SDcons ty ty t sd)) e2 sl3 a3 tmp3 /\ *)
  (*       tr_expr le (For_set (SDcons ty ty t sd)) e3 sl4 a4 tmp4 /\ *)
  (*       list_disjoint tmp2 tmp3 /\ *)
        (*       list_disjoint tmp2 tmp4 /\ *)
        (*       incl tmp2 tmp /\ *)
        (*       incl tmp3 tmp /\ *)
        (*       incl tmp4 tmp /\ *)
        (*       In t tmp /\ *)
        (*       sl1 = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil *)
        (*     end *)
        (*   | Csyntax.Eassign e1 e2 ty => *)
        (*     exists sl2 a2 tmp2 sl3 a3 tmp3, *)
        (*     tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
        (*     tr_expr le For_val e2 sl3 a3 tmp3 /\ *)
        (*     list_disjoint tmp2 tmp3 /\ *)
        (*     incl tmp2 tmp /\ *)
        (*     incl tmp3 tmp /\ *)
        (*     (( sl1 = sl2 ++ sl3 ++ make_assign a2 a3 :: nil /\  dst = For_effects) \/ *)
        (*      ( exists t, In t tmp /\ ~In t tmp2 /\ ~In t tmp3 /\ *)
        (*                  sl1 = sl2 ++ sl3 ++ Sset t (Ecast a3 (Csyntax.typeof e1)) :: *)
        (*                            make_assign a2 (Etempvar t (Csyntax.typeof e1)) :: *)
        (*                            final dst (Etempvar t (Csyntax.typeof e1)))) *)
        (*   | Csyntax.Eassignop op e1 e2 tyres ty => *)
        (*     exists sl2 a2 tmp2 sl3 a3 tmp3 sl4 a4 tmp4, *)
        (*     tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
        (*     tr_expr le For_val e2 sl3 a3 tmp3 /\ *)
        (*     tr_rvalof (Csyntax.typeof e1) a2 sl4 a4 tmp4 /\ *)
        (*     list_disjoint tmp2 tmp3 /\ *)
        (*     list_disjoint tmp2 tmp4 /\ *)
        (*     list_disjoint tmp3 tmp4 /\ *)
        (*     incl tmp2 tmp /\ *)
        (*     incl tmp3 tmp /\ *)
        (*     incl tmp4 tmp /\ *)
        (*     ((dst = For_effects /\ sl1 = sl2 ++ sl3 ++ sl4 ++ make_assign a2 (Ebinop op a4 a3 tyres) :: nil) \/ *)
        (*      (exists t, In t tmp /\ ~In t tmp2 /\ ~In t tmp3 /\ ~In t tmp4 /\ *)
        (*                 sl1 = sl2 ++ sl3 ++ sl4 ++ Sset t (Ecast (Ebinop op a4 a3 tyres) (Csyntax.typeof e1)) :: *)
        (*                           make_assign a2 (Etempvar t (Csyntax.typeof e1)) :: final dst (Etempvar t (Csyntax.typeof e1)) /\ *)
        (*                 a1 = (Etempvar t (Csyntax.typeof e1))))         *)
        (*   | Csyntax.Epostincr id e1 ty => *)
        (*     (exists sl2 a2 tmp2 sl3 a3 tmp3, tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
        (*                                      tr_rvalof (Csyntax.typeof e1) a2 sl3 a3 tmp3 /\ *)
        (*                                      incl tmp2 tmp /\ *)
        (*                                      incl tmp3 tmp /\ *)
        (*                                      list_disjoint tmp2 tmp3 /\ *)
        (*                                      sl1 = sl2 ++ sl3 ++ make_assign a2 (transl_incrdecr id a3 (Csyntax.typeof e1)) :: nil) \/ *)
        (*     (exists sl2 a2 tmp2 t, tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
        (*                            incl tmp2 tmp /\ *)
        (*                            In t tmp /\ *)
        (*                            ~In t tmp2 /\ *)
        (*                            sl1 = sl2 ++ make_set t a2 :: make_assign a2 (transl_incrdecr id (Etempvar t (Csyntax.typeof e1)) (Csyntax.typeof e1)) *)
        (*                                      :: final dst (Etempvar t (Csyntax.typeof e1)) /\ *)
        (*                            a1 = Etempvar t (Csyntax.typeof e1)) *)
        (*   | Csyntax.Ecomma e1 e2 ty => *)
        (*     exists sl2 a2 tmp2 sl3 tmp3, tr_expr le For_effects e1 sl2 a2 tmp2 /\ *)
        (*                                  tr_expr le dst e2 sl3 a1 tmp3 /\ *)
        (*                                  list_disjoint tmp2 tmp3 /\ *)
        (*                                  incl tmp2 tmp /\ *)
        (*                                  incl tmp3 tmp /\ *)
        (*                                  sl1 = sl2 ++ sl3 *)
        (*   | Csyntax.Ecall e1 el2 ty => *)
        (*     match dst with *)
        (*     | For_effects => *)
        (*       exists sl2 a2 tmp2 sl3 al3 tmp3, tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
        (*                                        tr_exprlist le el2 sl3 al3 tmp3 /\ *)
        (*                                        list_disjoint tmp2 tmp3 /\ *)
        (*                                        incl tmp2 tmp /\ *)
        (*                                        incl tmp3 tmp /\ *)
        (*                                        sl1 = sl2 ++ sl3 ++ Scall None a2 al3 :: nil *)
        (*     | _ => *)
        (*       exists sl2 a2 tmp2 sl3 al3 tmp3 t, tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
        (*                                          tr_exprlist le el2 sl3 al3 tmp3 /\ *)
        (*                                          list_disjoint tmp2 tmp3 /\ *)
        (*                                          In t tmp /\ *)
        (*                                          incl tmp2 tmp /\ *)
        (*                                          incl tmp3 tmp /\ *)
        (*                                          sl1 = sl2 ++ sl3 ++ Scall (Some t) a2 al3 :: final dst (Etempvar t ty) /\ *)
        (*                                          a1 = Etempvar t ty *)
        (*     end *)
        (*   | Csyntax.Ebuiltin ef tyargs el ty => *)
        (*     match dst with *)
        (*     | For_effects => *)
        (*       exists sl2 al2 tmp2, tr_exprlist le el sl2 al2 tmp2 /\ *)
        (*                            incl tmp2 tmp /\ *)
        (*                            sl1 = sl2 ++ Sbuiltin None ef tyargs al2 :: nil *)
        (*     | _ => *)
        (*       exists sl2 al2 tmp2 t, tr_exprlist le el sl2 al2 tmp2 /\ *)
        (*                              In t tmp /\ *)
        (*                              incl tmp2 tmp /\ *)
        (*                              sl1 = sl2 ++ Sbuiltin (Some t) ef tyargs al2 :: final dst (Etempvar t ty) /\ *)
        (*                              a1 = Etempvar t ty *)
        (*     end *)
        (*   | Csyntax.Eparen e1 tycast ty => *)
        (*     match dst with *)
        (*     | For_val => *)
        (*       exists a2 t, tr_expr le (For_set (SDbase tycast ty t)) e1 sl1 a2 tmp /\ *)
        (*                    In t tmp /\ *)
        (*                    a1 = Etempvar t ty *)
        (*     | For_effects => *)
        (*       exists a2, tr_expr le For_effects e1 sl1 a2 tmp *)
        (*     | For_set sd => *)
        (*       exists a2 t, tr_expr le (For_set (SDcons tycast ty t sd)) e1 sl1 a2 tmp /\ *)
        (*                    In t tmp *)
        (*     end *)
        (*   | _ => False *)
        (*   end *)
        (* with tr_exprlist (le : temp_env) (e : Csyntax.exprlist) (sl1 : list statement) (a1 : list expr) (tmp : list ident) : Prop := *)
        (*        match e with *)
        (*        | Csyntax.Enil => sl1 = nil /\ a1 = nil *)
        (*        | Csyntax.Econs e1 el2 => *)
        (*          exists sl2 a2 tmp2 sl3 al3 tmp3, *)
        (*          tr_expr le For_val e1 sl2 a2 tmp2 /\ *)
        (*          tr_exprlist le el2 sl3 al3 tmp3 /\ *)
        (*          list_disjoint tmp2 tmp3 /\ *)
        (*          incl tmp2 tmp /\ *)
        (*          incl tmp3 tmp /\ *)
        (*          sl1 = sl2 ++ sl3 /\ *)
        (*          a1 = a2 :: al3 *)
        (*        end. *)


        (* Inductive tr_expr: temp_env -> destination -> Csyntax.expr -> list statement -> expr -> list ident -> Prop := *)
        (* | tr_var: forall le dst id ty tmp, *)
        (*     tr_expr le dst (Csyntax.Evar id ty) *)
        (*             (final dst (Evar id ty)) (Evar id ty) tmp *)
        (* | tr_deref: forall le dst e1 ty sl1 a1 tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp -> *)
        (*     tr_expr le dst (Csyntax.Ederef e1 ty) *)
        (*             (sl1 ++ final dst (Ederef' a1 ty)) (Ederef' a1 ty) tmp *)
        (* | tr_field: forall le dst e1 f ty sl1 a1 tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp -> *)
        (*     tr_expr le dst (Csyntax.Efield e1 f ty) *)
        (*             (sl1 ++ final dst (Efield a1 f ty)) (Efield a1 f ty) tmp *)
        (* | tr_val_effect: forall le v ty any tmp, *)
        (*     tr_expr le For_effects (Csyntax.Eval v ty) nil any tmp *)
        (* | tr_val_value: forall le v ty a tmp, *)
        (*     typeof a = ty -> *)
        (*     (forall tge e le' m, *)
        (*         (forall id, In id tmp -> le'!id = le!id) -> *)
        (*         eval_expr tge e le' m a v) -> *)
        (*     tr_expr le For_val (Csyntax.Eval v ty) *)
        (*             nil a tmp *)
        (* | tr_val_set: forall le sd v ty a any tmp, *)
        (*     typeof a = ty -> *)
        (*     (forall tge e le' m, *)
        (*         (forall id, In id tmp -> le'!id = le!id) -> *)
        (*         eval_expr tge e le' m a v) -> *)
        (*     tr_expr le (For_set sd) (Csyntax.Eval v ty) *)
        (*             (do_set sd a) any tmp *)
        (* | tr_sizeof: forall le dst ty' ty tmp, *)
        (*     tr_expr le dst (Csyntax.Esizeof ty' ty) *)
        (*             (final dst (Esizeof ty' ty)) *)
        (*             (Esizeof ty' ty) tmp *)
        (* | tr_alignof: forall le dst ty' ty tmp, *)
        (*     tr_expr le dst (Csyntax.Ealignof ty' ty) *)
        (*             (final dst (Ealignof ty' ty)) *)
        (*             (Ealignof ty' ty) tmp *)
        (* | tr_valof: forall le dst e1 ty tmp sl1 a1 tmp1 sl2 a2 tmp2, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_rvalof (Csyntax.typeof e1) a1 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     tr_expr le dst (Csyntax.Evalof e1 ty) *)
        (*             (sl1 ++ sl2 ++ final dst a2) *)
        (*             a2 tmp *)
        (* | tr_addrof: forall le dst e1 ty tmp sl1 a1, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp -> *)
        (*     tr_expr le dst (Csyntax.Eaddrof e1 ty) *)
        (*             (sl1 ++ final dst (Eaddrof' a1 ty)) *)
        (*             (Eaddrof' a1 ty) tmp *)
        (* | tr_unop: forall le dst op e1 ty tmp sl1 a1, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp -> *)
        (*     tr_expr le dst (Csyntax.Eunop op e1 ty) *)
        (*             (sl1 ++ final dst (Eunop op a1 ty)) *)
        (*             (Eunop op a1 ty) tmp *)
        (* | tr_binop: forall le dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le For_val e2 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     tr_expr le dst (Csyntax.Ebinop op e1 e2 ty) *)
        (*             (sl1 ++ sl2 ++ final dst (Ebinop op a1 a2 ty)) *)
        (*             (Ebinop op a1 a2 ty) tmp *)
        (* | tr_cast: forall le dst e1 ty sl1 a1 tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp -> *)
        (*     tr_expr le dst (Csyntax.Ecast e1 ty) *)
        (*             (sl1 ++ final dst (Ecast a1 ty)) *)
        (*             (Ecast a1 ty) tmp *)
        (* | tr_seqand_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> In t tmp -> *)
        (*     tr_expr le For_val (Csyntax.Eseqand e1 e2 ty) *)
        (*             (sl1 ++ makeif a1 (makeseq sl2) *)
        (*                  (Sset t (Econst_int Int.zero ty)) :: nil) *)
        (*             (Etempvar t ty) tmp *)
        (* | tr_seqand_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le For_effects e2 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     tr_expr le For_effects (Csyntax.Eseqand e1 e2 ty) *)
        (*             (sl1 ++ makeif a1 (makeseq sl2) Sskip :: nil) *)
        (*             any tmp *)
        (* | tr_seqand_set: forall le sd e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> In (sd_temp sd) tmp -> *)
        (*     tr_expr le (For_set sd) (Csyntax.Eseqand e1 e2 ty) *)
        (*             (sl1 ++ makeif a1 (makeseq sl2) *)
        (*                  (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil) *)
        (*             any tmp *)
        (* | tr_seqor_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> In t tmp -> *)
        (*     tr_expr le For_val (Csyntax.Eseqor e1 e2 ty) *)
        (*             (sl1 ++ makeif a1 (Sset t (Econst_int Int.one ty)) *)
        (*                  (makeseq sl2) :: nil) *)
        (*             (Etempvar t ty) tmp *)
        (* | tr_seqor_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le For_effects e2 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     tr_expr le For_effects (Csyntax.Eseqor e1 e2 ty) *)
        (*             (sl1 ++ makeif a1 Sskip (makeseq sl2) :: nil) *)
        (*             any tmp *)
        (* | tr_seqor_set: forall le sd e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> In (sd_temp sd) tmp -> *)
        (*     tr_expr le (For_set sd) (Csyntax.Eseqor e1 e2 ty) *)
        (*             (sl1 ++ makeif a1 (makeseq (do_set sd (Econst_int Int.one ty))) *)
        (*                  (makeseq sl2) :: nil) *)
        (*             any tmp *)
        (* | tr_condition_val: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le (For_set (SDbase ty ty t)) e2 sl2 a2 tmp2 -> *)
        (*     tr_expr le (For_set (SDbase ty ty t)) e3 sl3 a3 tmp3 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     list_disjoint tmp1 tmp3 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp ->  incl tmp3 tmp -> In t tmp -> *)
        (*     tr_expr le For_val (Csyntax.Econdition e1 e2 e3 ty) *)
        (*             (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil) *)
        (*             (Etempvar t ty) tmp *)
        (* | tr_condition_effects: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le For_effects e2 sl2 a2 tmp2 -> *)
        (*     tr_expr le For_effects e3 sl3 a3 tmp3 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     list_disjoint tmp1 tmp3 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> *)
        (*     tr_expr le For_effects (Csyntax.Econdition e1 e2 e3 ty) *)
        (*             (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil) *)
        (*             any tmp *)
        (* | tr_condition_set: forall le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le (For_set (SDcons ty ty t sd)) e2 sl2 a2 tmp2 -> *)
        (*     tr_expr le (For_set (SDcons ty ty t sd)) e3 sl3 a3 tmp3 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     list_disjoint tmp1 tmp3 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp -> *)
        (*     tr_expr le (For_set sd) (Csyntax.Econdition e1 e2 e3 ty) *)
        (*             (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil) *)
        (*             any tmp *)
        (* | tr_assign_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le For_val e2 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     tr_expr le For_effects (Csyntax.Eassign e1 e2 ty) *)
        (*             (sl1 ++ sl2 ++ make_assign a1 a2 :: nil) *)
        (*             any tmp *)
        (* | tr_assign_val: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le For_val e2 sl2 a2 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     In t tmp -> ~In t tmp1 -> ~In t tmp2 -> *)
        (*     ty1 = Csyntax.typeof e1 -> *)
        (*     ty2 = Csyntax.typeof e2 -> *)
        (*     tr_expr le dst (Csyntax.Eassign e1 e2 ty) *)
        (*             (sl1 ++ sl2 ++ *)
        (*                  Sset t (Ecast a2 ty1) :: *)
        (*                  make_assign a1 (Etempvar t ty1) :: *)
        (*                  final dst (Etempvar t ty1)) *)
        (*             (Etempvar t ty1) tmp *)
        (* | tr_assignop_effects: forall le op e1 e2 tyres ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le For_val e2 sl2 a2 tmp2 -> *)
        (*     ty1 = Csyntax.typeof e1 -> *)
        (*     tr_rvalof ty1 a1 sl3 a3 tmp3 -> *)
        (*     list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> *)
        (*     tr_expr le For_effects (Csyntax.Eassignop op e1 e2 tyres ty) *)
        (*             (sl1 ++ sl2 ++ sl3 ++ make_assign a1 (Ebinop op a3 a2 tyres) :: nil) *)
        (*             any tmp *)
        (* | tr_assignop_val: forall le dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp ty1, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le For_val e2 sl2 a2 tmp2 -> *)
        (*     tr_rvalof ty1 a1 sl3 a3 tmp3 -> *)
        (*     list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> *)
        (*     In t tmp -> ~In t tmp1 -> ~In t tmp2 -> ~In t tmp3 -> *)
        (*     ty1 = Csyntax.typeof e1 -> *)
        (*     tr_expr le dst (Csyntax.Eassignop op e1 e2 tyres ty) *)
        (*             (sl1 ++ sl2 ++ sl3 ++ *)
        (*                  Sset t (Ecast (Ebinop op a3 a2 tyres) ty1) :: *)
        (*                  make_assign a1 (Etempvar t ty1) :: *)
        (*                  final dst (Etempvar t ty1)) *)
        (*             (Etempvar t ty1) tmp *)
        (* | tr_postincr_effects: forall le id e1 ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_rvalof ty1 a1 sl2 a2 tmp2 -> *)
        (*     ty1 = Csyntax.typeof e1 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     tr_expr le For_effects (Csyntax.Epostincr id e1 ty) *)
        (*             (sl1 ++ sl2 ++ make_assign a1 (transl_incrdecr id a2 ty1) :: nil) *)
        (*             any tmp *)
        (* | tr_postincr_val: forall le dst id e1 ty sl1 a1 tmp1 t ty1 tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     incl tmp1 tmp -> In t tmp -> ~In t tmp1 -> *)
        (*     ty1 = Csyntax.typeof e1 -> *)
        (*     tr_expr le dst (Csyntax.Epostincr id e1 ty) *)
        (*             (sl1 ++ make_set t a1 :: *)
        (*                  make_assign a1 (transl_incrdecr id (Etempvar t ty1) ty1) :: *)
        (*                  final dst (Etempvar t ty1)) *)
        (*             (Etempvar t ty1) tmp *)
        (* | tr_comma: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp, *)
        (*     tr_expr le For_effects e1 sl1 a1 tmp1 -> *)
        (*     tr_expr le dst e2 sl2 a2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     tr_expr le dst (Csyntax.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp *)
        (* | tr_call_effects: forall le e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 any tmp, *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_exprlist le el2 sl2 al2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     tr_expr le For_effects (Csyntax.Ecall e1 el2 ty) *)
        (*             (sl1 ++ sl2 ++ Scall None a1 al2 :: nil) *)
        (*             any tmp *)
        (* | tr_call_val: forall le dst e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 t tmp, *)
        (*     dst <> For_effects -> *)
        (*     tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*     tr_exprlist le el2 sl2 al2 tmp2 -> *)
        (*     list_disjoint tmp1 tmp2 -> In t tmp -> *)
        (*     incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*     tr_expr le dst (Csyntax.Ecall e1 el2 ty) *)
        (*             (sl1 ++ sl2 ++ Scall (Some t) a1 al2 :: final dst (Etempvar t ty)) *)
        (*             (Etempvar t ty) tmp *)
        (* | tr_builtin_effects: forall le ef tyargs el ty sl al tmp1 any tmp, *)
        (*     tr_exprlist le el sl al tmp1 -> *)
        (*     incl tmp1 tmp -> *)
        (*     tr_expr le For_effects (Csyntax.Ebuiltin ef tyargs el ty) *)
        (*             (sl ++ Sbuiltin None ef tyargs al :: nil) *)
        (*             any tmp *)
        (* | tr_builtin_val: forall le dst ef tyargs el ty sl al tmp1 t tmp, *)
        (*     dst <> For_effects -> *)
        (*     tr_exprlist le el sl al tmp1 -> *)
        (*     In t tmp -> incl tmp1 tmp -> *)
        (*     tr_expr le dst (Csyntax.Ebuiltin ef tyargs el ty) *)
        (*             (sl ++ Sbuiltin (Some t) ef tyargs al :: final dst (Etempvar t ty)) *)
        (*             (Etempvar t ty) tmp *)
        (* | tr_paren_val: forall le e1 tycast ty sl1 a1 t tmp, *)
        (*     tr_expr le (For_set (SDbase tycast ty t)) e1 sl1 a1 tmp -> *)
        (*     In t tmp -> *)
        (*     tr_expr le For_val (Csyntax.Eparen e1 tycast ty) *)
        (*             sl1 *)
        (*             (Etempvar t ty) tmp *)
        (* | tr_paren_effects: forall le e1 tycast ty sl1 a1 tmp any, *)
        (*     tr_expr le For_effects e1 sl1 a1 tmp -> *)
        (*     tr_expr le For_effects (Csyntax.Eparen e1 tycast ty) sl1 any tmp *)
        (* | tr_paren_set: forall le t sd e1 tycast ty sl1 a1 tmp any, *)
        (*     tr_expr le (For_set (SDcons tycast ty t sd)) e1 sl1 a1 tmp -> *)
        (*     In t tmp -> *)
        (*     tr_expr le (For_set sd) (Csyntax.Eparen e1 tycast ty) sl1 any tmp *)

        (* with tr_exprlist: temp_env -> Csyntax.exprlist -> list statement -> list expr -> list ident -> Prop := *)
        (*      | tr_nil: forall le tmp, *)
        (*          tr_exprlist le Csyntax.Enil nil nil tmp *)
        (*      | tr_cons: forall le e1 el2 sl1 a1 tmp1 sl2 al2 tmp2 tmp, *)
        (*          tr_expr le For_val e1 sl1 a1 tmp1 -> *)
        (*          tr_exprlist le el2 sl2 al2 tmp2 -> *)
        (*          list_disjoint tmp1 tmp2 -> *)
        (*          incl tmp1 tmp -> incl tmp2 tmp -> *)
        (*          tr_exprlist le (Csyntax.Econs e1 el2) (sl1 ++ sl2) (a1 :: al2) tmp. *)

        (* Scheme tr_expr_ind2 := Minimality for tr_expr Sort Prop *)
        (*   with tr_exprlist_ind2 := Minimality for tr_exprlist Sort Prop. *)
        (* Combined Scheme tr_expr_exprlist from tr_expr_ind2, tr_exprlist_ind2. *)

        (* Useful invariance properties. *)


        (* Lemma tr_rvalof_monotone: *)
        (*   forall ty a sl b tmps, tr_rvalof ty a sl b tmps -> *)
        (*                          forall tmps', incl tmps tmps' -> tr_rvalof ty a sl b tmps'. *)
        (* Proof. *)
        (*   unfold tr_rvalof. intros. *)
        (*   induction (type_is_volatile ty); intros; auto. *)
        (*   * unfold incl in *. destruct H as (t&P1&P2&P3). exists t. split; auto. *)
        (* Qed.   *)

        (** ** Top-level translation *)

        (** The "top-level" translation is equivalent to [tr_expr] above
  for source terms.  It brings additional flexibility in the matching
  between Csyntax values and Cminor expressions: in the case of
  [tr_expr], the Cminor expression must not depend on memory,
  while in the case of [tr_top] it can depend on the current memory
  state. *)

        Section TR_TOP.

          Variable ge: genv.
          Variable e: env.
          Variable le: temp_env.
          Variable m: mem.

          Inductive tr_top: destination -> Csyntax.expr -> list statement -> expr -> list ident -> Prop :=
          | tr_top_val_val: forall v ty a tmp,
              typeof a = ty -> eval_expr ge e le m a v ->
              tr_top For_val (Csyntax.Eval v ty) nil a tmp
          | tr_top_base: forall dst r sl a tmp,
              tr_expr le dst r sl a tmp ->
              tr_top dst r sl a tmp.

        End TR_TOP.

        (** Translation of statements *)

        Inductive tr_expression: Csyntax.expr -> statement -> expr -> Prop :=
        | tr_expression_intro: forall r sl a tmps,
            (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
            tr_expression r (makeseq sl) a.

        Inductive tr_expr_stmt: Csyntax.expr -> statement -> Prop :=
        | tr_expr_stmt_intro: forall r sl a tmps,
            (forall ge e le m, tr_top ge e le m For_effects r sl a tmps) ->
            tr_expr_stmt r (makeseq sl).

        Inductive tr_if: Csyntax.expr -> statement -> statement -> statement -> Prop :=
        | tr_if_intro: forall r s1 s2 sl a tmps,
            (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
            tr_if r s1 s2 (makeseq (sl ++ makeif a s1 s2 :: nil)).

        Inductive tr_stmt: Csyntax.statement -> statement -> Prop :=
        | tr_skip:
            tr_stmt Csyntax.Sskip Sskip
        | tr_do: forall r s,
            tr_expr_stmt r s ->
            tr_stmt (Csyntax.Sdo r) s
        | tr_seq: forall s1 s2 ts1 ts2,
            tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
            tr_stmt (Csyntax.Ssequence s1 s2) (Ssequence ts1 ts2)
        | tr_ifthenelse_empty: forall r s' a,
            tr_expression r s' a ->
            tr_stmt (Csyntax.Sifthenelse r Csyntax.Sskip Csyntax.Sskip) (Ssequence s' Sskip)
        | tr_ifthenelse: forall r s1 s2 s' a ts1 ts2,
            tr_expression r s' a ->
            tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
            tr_stmt (Csyntax.Sifthenelse r s1 s2) (Ssequence s' (Sifthenelse a ts1 ts2))
        | tr_while: forall r s1 s' ts1,
            tr_if r Sskip Sbreak s' ->
            tr_stmt s1 ts1 ->
            tr_stmt (Csyntax.Swhile r s1)
                    (Sloop (Ssequence s' ts1) Sskip)
        | tr_dowhile: forall r s1 s' ts1,
            tr_if r Sskip Sbreak s' ->
            tr_stmt s1 ts1 ->
            tr_stmt (Csyntax.Sdowhile r s1)
                    (Sloop ts1 s')
        | tr_for_1: forall r s3 s4 s' ts3 ts4,
            tr_if r Sskip Sbreak s' ->
            tr_stmt s3 ts3 ->
            tr_stmt s4 ts4 ->
            tr_stmt (Csyntax.Sfor Csyntax.Sskip r s3 s4)
                    (Sloop (Ssequence s' ts4) ts3)
        | tr_for_2: forall s1 r s3 s4 s' ts1 ts3 ts4,
            tr_if r Sskip Sbreak s' ->
            s1 <> Csyntax.Sskip ->
            tr_stmt s1 ts1 ->
            tr_stmt s3 ts3 ->
            tr_stmt s4 ts4 ->
            tr_stmt (Csyntax.Sfor s1 r s3 s4)
                    (Ssequence ts1 (Sloop (Ssequence s' ts4) ts3))
        | tr_break:
            tr_stmt Csyntax.Sbreak Sbreak
        | tr_continue:
            tr_stmt Csyntax.Scontinue Scontinue
        | tr_return_none:
            tr_stmt (Csyntax.Sreturn None) (Sreturn None)
        | tr_return_some: forall r s' a,
            tr_expression r s' a ->
            tr_stmt (Csyntax.Sreturn (Some r)) (Ssequence s' (Sreturn (Some a)))
        | tr_switch: forall r ls s' a tls,
            tr_expression r s' a ->
            tr_lblstmts ls tls ->
            tr_stmt (Csyntax.Sswitch r ls) (Ssequence s' (Sswitch a tls))
        | tr_label: forall lbl s ts,
            tr_stmt s ts ->
            tr_stmt (Csyntax.Slabel lbl s) (Slabel lbl ts)
        | tr_goto: forall lbl,
            tr_stmt (Csyntax.Sgoto lbl) (Sgoto lbl)

        with tr_lblstmts: Csyntax.labeled_statements -> labeled_statements -> Prop :=
             | tr_ls_nil:
                 tr_lblstmts Csyntax.LSnil LSnil
             | tr_ls_cons: forall c s ls ts tls,
                 tr_stmt s ts ->
                 tr_lblstmts ls tls ->
                 tr_lblstmts (Csyntax.LScons c s ls) (LScons c ts tls).



  (** * Correctness proof with respect to the specification. *)

  (** ** Properties of the monad *)


  Remark bind_inversion:
    forall (A B: Type) (f: mon A) (g: A -> mon B) (y: B) (z1 z3: generator) I,
      bind f g z1 = Res y z3 I ->
      exists x, exists z2, exists I1, exists I2,
              f z1 = Res x z2 I1 /\ g x z2 = Res y z3 I2.
  Proof.
    intros until I. unfold bind. destruct (f z1).
    congruence.
    caseEq (g a g'); intros; inv H0.
    econstructor; econstructor; econstructor; econstructor; eauto.
  Qed.

  Remark bind2_inversion:
    forall (A B Csyntax: Type) (f: mon (A*B)) (g: A -> B -> mon Csyntax) (y: Csyntax) (z1 z3: generator) I,
      bind2 f g z1 = Res y z3 I ->
      exists x1, exists x2, exists z2, exists I1, exists I2,
                f z1 = Res (x1,x2) z2 I1 /\ g x1 x2 z2 = Res y z3 I2.
  Proof.
    unfold bind2. intros.
    exploit bind_inversion; eauto.
    intros [[x1 x2] [z2 [I1 [I2 [P Q]]]]]. simpl in Q.
    exists x1; exists x2; exists z2; exists I1; exists I2; auto.
  Qed.

  Ltac monadInv1 H :=
    match type of H with
    | (Res _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
    | (@ret _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
    | (@error _ _ _ = Res _ _ _) =>
      inversion H
    | (bind ?F ?G ?Z = Res ?X ?Z' ?I) =>
      let x := fresh "x" in (
        let z := fresh "z" in (
          let I1 := fresh "I" in (
            let I2 := fresh "I" in (
              let EQ1 := fresh "EQ" in (
                let EQ2 := fresh "EQ" in (
                  destruct (bind_inversion _ _ F G X Z Z' I H) as [x [z [I1 [I2 [EQ1 EQ2]]]]];
                  clear H;
                  try (monadInv1 EQ2)))))))
    | (bind2 ?F ?G ?Z = Res ?X ?Z' ?I) =>
      let x := fresh "x" in (
        let y := fresh "y" in (
          let z := fresh "z" in (
            let I1 := fresh "I" in (
              let I2 := fresh "I" in (
                let EQ1 := fresh "EQ" in (
                  let EQ2 := fresh "EQ" in (
                    destruct (bind2_inversion _ _ _ F G X Z Z' I H) as [x [y [z [I1 [I2 [EQ1 EQ2]]]]]];
                    clear H;
                    try (monadInv1 EQ2))))))))
    end.

  Ltac monadInv H :=
    match type of H with
    | (@ret _ _ _ = Res _ _ _) => monadInv1 H
    | (@error _ _ _ = Res _ _ _) => monadInv1 H
    | (bind ?F ?G ?Z = Res ?X ?Z' ?I) => monadInv1 H
    | (bind2 ?F ?G ?Z = Res ?X ?Z' ?I) => monadInv1 H
    | (?F _ _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
    | (?F _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
    | (?F _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
    | (?F _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
    | (?F _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
    | (?F _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
    | (?F _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
    | (?F _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
    end.

  (** ** Freshness and separation properties. *)

  Definition within (id: ident) (g1 g2: generator) : Prop :=
    Ple (gen_next g1) id /\ Plt id (gen_next g2).

  Lemma gensym_within:
    forall ty g1 id g2 I,
      gensym ty g1 = Res id g2 I -> within id g1 g2.
  Proof.
    intros. monadInv H. split. apply Ple_refl. apply Plt_succ.
  Qed.

  Lemma within_widen:
    forall id g1 g2 g1' g2',
      within id g1 g2 ->
      Ple (gen_next g1') (gen_next g1) ->
      Ple (gen_next g2) (gen_next g2') ->
      within id g1' g2'.
  Proof.
    intros. destruct H. split.
    eapply Ple_trans; eauto.
    eapply Plt_Ple_trans; eauto.
  Qed.

  Definition contained (l: list ident) (g1 g2: generator) : Prop :=
    forall id, In id l -> within id g1 g2.

  Lemma contained_nil:
    forall g1 g2, contained nil g1 g2.
  Proof.
    intros; red; intros; contradiction.
  Qed.

  Lemma contained_widen:
    forall l g1 g2 g1' g2',
      contained l g1 g2 ->
      Ple (gen_next g1') (gen_next g1) ->
      Ple (gen_next g2) (gen_next g2') ->
      contained l g1' g2'.
  Proof.
    intros; red; intros. eapply within_widen; eauto.
  Qed.

  Lemma contained_cons:
    forall id l g1 g2,
      within id g1 g2 -> contained l g1 g2 -> contained (id :: l) g1 g2.
  Proof.
    intros; red; intros. simpl in H1; destruct H1. subst id0. auto. auto.
  Qed.

  Lemma contained_app:
    forall l1 l2 g1 g2,
      contained l1 g1 g2 -> contained l2 g1 g2 -> contained (l1 ++ l2) g1 g2.
  Proof.
    intros; red; intros. destruct (in_app_or _ _ _ H1); auto.
  Qed.

  Lemma contained_disjoint:
    forall g1 l1 g2 l2 g3,
      contained l1 g1 g2 -> contained l2 g2 g3 -> list_disjoint l1 l2.
  Proof.
    intros; red; intros. red; intro; subst y.
    exploit H; eauto. intros [A B]. exploit H0; eauto. intros [Csyntax D].
    elim (Plt_strict x). apply Plt_Ple_trans with (gen_next g2); auto.
  Qed.

  Lemma contained_notin:
    forall g1 l g2 id g3,
      contained l g1 g2 -> within id g2 g3 -> ~In id l.
  Proof.
    intros; red; intros. exploit H; eauto. intros [Csyntax D]. destruct H0 as [A B].
    elim (Plt_strict id). apply Plt_Ple_trans with (gen_next g2); auto.
  Qed.

  Definition dest_below (dst: destination) (g: generator) : Prop :=
    match dst with
    | For_set sd => Plt (sd_temp sd) g.(gen_next)
    | _ => True
    end.

  Remark dest_for_val_below: forall g, dest_below For_val g.
  Proof. intros; simpl; auto. Qed.

  Remark dest_for_effect_below: forall g, dest_below For_effects g.
  Proof. intros; simpl; auto. Qed.

  Lemma dest_for_set_seqbool_val:
    forall tmp ty g1 g2,
      within tmp g1 g2 -> dest_below (For_set (sd_seqbool_val tmp ty)) g2.
  Proof.
    intros. destruct H. simpl. auto.
  Qed.

  Lemma dest_for_set_seqbool_set:
    forall sd ty g, dest_below (For_set sd) g -> dest_below (For_set (sd_seqbool_set ty sd)) g.
  Proof.
    intros. assumption.
  Qed.

  Lemma dest_for_set_condition_val:
    forall tmp tycast ty g1 g2, within tmp g1 g2 -> dest_below (For_set (SDbase tycast ty tmp)) g2.
  Proof.
    intros. destruct H. simpl. auto.
  Qed.

  Lemma dest_for_set_condition_set:
    forall sd tmp tycast ty g1 g2, dest_below (For_set sd) g2 -> within tmp g1 g2 -> dest_below (For_set (SDcons tycast ty tmp sd)) g2.
  Proof.
    intros. destruct H0. simpl. auto.
  Qed.

  Lemma sd_temp_notin:
    forall sd g1 g2 l, dest_below (For_set sd) g1 -> contained l g1 g2 -> ~In (sd_temp sd) l.
  Proof.
    intros. simpl in H. red; intros. exploit H0; eauto. intros [A B].
    elim (Plt_strict (sd_temp sd)). apply Plt_Ple_trans with (gen_next g1); auto.
  Qed.

  Lemma dest_below_le:
    forall dst g1 g2,
      dest_below dst g1 -> Ple g1.(gen_next) g2.(gen_next) -> dest_below dst g2.
  Proof.
    intros. destruct dst; simpl in *; auto. eapply Plt_Ple_trans; eauto.
  Qed.

  Hint Resolve gensym_within within_widen contained_widen
       contained_cons contained_app contained_disjoint
       contained_notin contained_nil
       dest_for_set_seqbool_val dest_for_set_seqbool_set
       dest_for_set_condition_val dest_for_set_condition_set
       sd_temp_notin dest_below_le
       incl_refl incl_tl incl_app incl_appl incl_appr incl_same_head
       in_eq in_cons
       Ple_trans Ple_refl: gensym.

  Hint Resolve dest_for_val_below dest_for_effect_below.

  (** ** Correctness of the translation functions *)

  Lemma finish_meets_spec_1:
    forall dst sl a sl' a',
      finish dst sl a = (sl', a') -> sl' = sl ++ final dst a.
  Proof.
    intros. destruct dst; simpl in *; inv H. apply app_nil_end. apply app_nil_end. auto.
  Qed.

  Lemma finish_meets_spec_2:
    forall dst sl a sl' a',
      finish dst sl a = (sl', a') -> a' = a.
  Proof.
    intros. destruct dst; simpl in *; inv H; auto.
  Qed.

  Ltac UseFinish :=
    match goal with
    | [ H: finish _ _ _ = (_, _) |- _ ] =>
      try (rewrite (finish_meets_spec_2 _ _ _ _ _ H));
      try (rewrite (finish_meets_spec_1 _ _ _ _ _ H));
      repeat rewrite app_ass
    end.

  (* *)
(* Fixpoint add_set_dest (sd: set_destination) (tmps: list ident) := *)
(*   match sd with *)
(*   | SDbase ty tmp => tmp :: tmps *)
(*   | SDcons ty tmp sd' => tmp :: add_set_dest sd' tmps *)
(*   end. *)
(*    *)

  Definition add_dest (dst: destination) (tmps: list ident) :=
    match dst with
    | For_set sd => sd_temp sd :: tmps
    | _ => tmps
    end.

  Lemma add_dest_incl:
    forall dst tmps, incl tmps (add_dest dst tmps).
  Proof.
    intros. destruct dst; simpl; eauto with coqlib.
  Qed.

  Lemma incl_trans : forall X (a b c : list X), incl a b -> incl b c -> incl a c.
  Proof.
    repeat intro. apply H in H1. now apply H0 in H1.
  Qed.

  Hint Resolve incl_trans.
    
  Lemma tr_expr_incl:
    forall r le dst sl a tmps tmps',
      tr_expr le dst r sl a tmps ->
      incl tmps tmps' ->
      tr_expr le dst r sl a tmps'.
  Proof.
    induction r; intros.
    - destruct dst; inversion H; split; eauto.
    - auto.
    - destruct H as (sl2&a2&P0&P1&P2). exists sl2. exists a2. split; auto.
      apply (IHr _ _ _ _ _ _ P0); auto.
    - destruct H as (sl2&a2&tmp2&sl3&tmp3&P0&P1&P2&P3&P4&P5). exists sl2. exists a2. exists tmp2.
      exists sl3. exists tmp3. repeat split; eauto.
    - destruct H as (sl2&a2&P0&P1&P5). exists sl2. exists a2. split; auto. eapply IHr; eauto.
    - destruct H as (sl2&a2&P0&P1&P2). exists sl2. exists a2. split; auto. eapply IHr; eauto.
    - destruct H as (sl2&a2&P0&P1&P2). exists sl2. exists a2. split; auto. eapply IHr; eauto.
    - destruct H as (sl2&a2&sl3&a3&tmp3&tmp4&P0&P1&P2&P3&P4&P5&P6).
      exists sl2. exists a2. exists sl3. exists a3. exists tmp3. exists tmp4. repeat split; eauto.

    - destruct H as (sl2&a2&P0&P1&P2).
      exists sl2. exists a2. split;auto. eapply IHr; eauto.
    - destruct dst.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&t&P0&P1&P2&P3&P4&P5&P6&P7).
      exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3. exists t.
      repeat split; eauto.
      + destruct H as (sl2&a2&sl3&a3&tmp3&tmp4&P0&P1&P2&P3&P4&P5).
        exists sl2. exists a2. exists sl3. exists a3. exists tmp3. exists tmp4.
        repeat split; eauto.
      + destruct H as (sl2&a2&sl3&a3&tmp3&tmp4&P0&P1&P2&P3&P4&P5&P6).
        exists sl2. exists a2. exists sl3. exists a3. exists tmp3. exists tmp4.
        repeat split; eauto.
    - destruct dst.
      + destruct H as (sl2&a2&sl3&a3&tmp3&tmp4&t&P0&P1&P2&P3&P4&P5&P6&P7).
        exists sl2. exists a2. exists sl3. exists a3. exists tmp3. exists tmp4. exists t.
        repeat split; eauto.
      + destruct H as (sl2&a2&sl3&a3&tmp3&tmp4&t&P0&P1&P2&P3&P4).
        exists sl2. exists a2. exists sl3. exists a3. exists tmp3. exists tmp4.
        repeat split; eauto.
      + destruct H as (sl2&a2&sl3&a3&tmp3&tmp4&t&P0&P1&P2&P3&P4&P5).
        exists sl2. exists a2. exists sl3. exists a3. exists tmp3. exists tmp4.
        repeat split; eauto.
    - destruct dst.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0&P1&P2&P3&P4&P5&P6&P7&P8&P9&P10).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3.
        exists sl4. exists a4. exists tmp4. exists t.
        repeat split; eauto.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0&P1&P2&P3&P4&P5&P6&P7).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3.
        exists sl4. exists a4. exists tmp4. repeat split; eauto.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0&P1&P2&P3&P4&P5&P6&P7&P8&P9).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3.
        exists sl4. exists a4. exists tmp4. exists t. repeat split; eauto.
    - auto.
    - auto.
    - destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0&P1).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3.
        repeat split; eauto. destruct P1.
      + now left.
      + right. destruct H as (t1&H&P&X&C). exists t1. repeat split; eauto.
    - destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0&P1&P2&P3&P4&P5&P6&P7&P8).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3.
        exists sl4. exists a4. exists tmp4. repeat split; eauto.
        destruct P8.
        + now left.
        + right. destruct H as (t1&H&P&X&C&A&B). exists t1. repeat split; eauto.
    - destruct H.
      + left. destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0&P1).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3.
        repeat split; eauto.
      + right. destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t).
        exists sl2. exists a2. exists tmp2. exists sl3. repeat split; eauto.
    - destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. repeat split; eauto.
    - destruct dst.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0&P1&P2&P3&P4).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3.
        exists sl4. repeat split; eauto.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0&P1).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3.
        repeat split; eauto.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4&t&P0&P1&P2&P3&P4).
        exists sl2. exists a2. exists tmp2. exists sl3. exists a3. exists tmp3.
        exists sl4. repeat split; eauto.
    - destruct dst.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4).
        exists sl2. exists a2. exists tmp2. exists sl3. repeat split; eauto.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3).
        exists sl2. exists a2. exists tmp2. repeat split; eauto.
      + destruct H as (sl2&a2&tmp2&sl3&a3&tmp3&sl4&a4&tmp4).
        exists sl2. exists a2. exists tmp2. exists sl3. repeat split; eauto.
    - auto.
    - destruct dst.
      + destruct H as (sl2&a2&tmp2&sl3&a3).
        exists sl2. exists a2. repeat split; eauto.
      + destruct H. exists x. repeat split; eauto.
      + destruct H as (f&b&c&d). exists f. exists b. split; eauto.
Qed.

  Lemma tr_expr_add_dest:
    forall r le dst sl a tmps,
      tr_expr le dst r sl a tmps ->
      tr_expr le dst r sl a (add_dest dst tmps).
  Proof.
    intros. eapply tr_expr_incl. exact H. red. intros. destruct dst; eauto. now right.
  Qed.


  Lemma transl_valof_meets_spec:
    forall ty a g sl b g' I,
      transl_valof ty a g = Res (sl, b) g' I ->
      exists tmps, tr_rvalof ty a sl b tmps /\ contained tmps g g'.
  Proof.
    unfold transl_valof; intros. unfold tr_rvalof.
    destruct (type_is_volatile ty) eqn:?; monadInv H.
    * exists (x :: nil). split; auto.
      ** exists x. intuition.
      ** unfold contained. intros. apply gensym_within in EQ. inversion H; subst; auto. inversion H0.
    * exists nil. split; auto. unfold contained. intros. inversion H.
  Qed.

  Scheme expr_ind2 := Induction for Csyntax.expr Sort Prop
    with exprlist_ind2 := Induction for Csyntax.exprlist Sort Prop.
  Combined Scheme expr_exprlist_ind from expr_ind2, exprlist_ind2.

  Lemma transl_meets_spec:
    (forall r dst g sl a g' I,
        transl_expr dst r g = Res (sl, a) g' I ->
        dest_below dst g ->
        exists tmps, (forall le, tr_expr le dst r sl a (add_dest dst tmps)) /\ contained tmps g g')
    /\
    (forall rl g sl al g' I,
        transl_exprlist rl g = Res (sl, al) g' I ->
        exists tmps, (forall le, tr_exprlist le rl sl al tmps) /\ contained tmps g g').
  Proof.
    apply expr_exprlist_ind; simpl add_dest; intros.
    (* val *)
    simpl in H. destruct v; monadInv H; exists (@nil ident); split; auto with gensym.
    Opaque makeif.
    intros. destruct dst; simpl in *; inv H2. split; auto.
    constructor. auto. intros; constructor.
    constructor.
    constructor; auto. intros. destruct dst; simpl in *. inversion H2; subst. split;auto.
    intros. econstructor. inversion H2. split; auto. split; auto. inversion H2; subst.
    econstructor. split; auto. inversion H2; subst. constructor. inversion H2. constructor.
    intros; simpl in *. destruct dst; simpl in *. split; auto. inversion H2. constructor.
    split; inversion H2; auto. inversion H2. auto. split; inversion H2. constructor.
    split; auto. intros; simpl in *. destruct dst; simpl in *. split; inversion H2. constructor.
    split; auto. inversion H2; auto. split. inversion H2. constructor. split; inversion H2; auto.
    (* var *)
    monadInv H; econstructor; split; auto with gensym. UseFinish. constructor. now reflexivity.
    reflexivity.
    (* field *)
    monadInv H0. exploit H; eauto. auto. intros [tmp [A B]]. UseFinish.
    econstructor; split; eauto.
    (* intros. simpl. exists x. exists y. split; eauto. *)
    (* destruct dst; eauto. simpl. *)
    intros; apply tr_expr_add_dest. simpl in *. exists x. exists y.
    split; auto.
    (* valof *)
    monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
    exploit transl_valof_meets_spec; eauto. intros [tmp2 [Csyntax D]]. UseFinish.
    exists (tmp1 ++ tmp2); split.
    intros; apply tr_expr_add_dest. simpl in *. exists x. exists y. exists x0. exists tmp1.
    exists tmp2. repeat split; auto. eapply contained_disjoint; eauto.
    red. intros. apply in_app. now left.
    red. intros. apply in_app. now right. eapply (contained_widen) in B.
    eapply (contained_widen) in D. apply contained_app; eauto. auto. auto. reflexivity. auto.
    (* deref *)
    monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish.
    econstructor; split; eauto. intros; apply tr_expr_add_dest. econstructor; eauto.
    (* addrof *)
    monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish.
    econstructor; split; eauto. intros; apply tr_expr_add_dest. econstructor; eauto.
    (* unop *)
    monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish.
    econstructor; split; eauto. intros; apply tr_expr_add_dest. econstructor; eauto.
    (* binop *)
    monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
    exploit H0; eauto. intros [tmp2 [Csyntax D]]. UseFinish.
    exists (tmp1 ++ tmp2); split.
    intros; apply tr_expr_add_dest. simpl in *. exists x. exists y. exists x0. exists y0.
    exists tmp1. exists tmp2. repeat split; auto.
    eapply contained_disjoint; eauto.
    red. intros. apply in_app. now left.
    red. intros. apply in_app. now right. eapply (contained_widen) in B.
    eapply (contained_widen) in D. apply contained_app; eauto. auto. auto. reflexivity. auto.
    (* cast *)
    monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish.
    econstructor; split; eauto. intros; apply tr_expr_add_dest. econstructor; eauto.
    (* seqand *)
    monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
    destruct dst; monadInv EQ0.
    (* for value *)
    exploit H0; eauto with gensym. intros [tmp2 [C D]].
    simpl add_dest in *.
    exists (x0 :: tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x1. exists y0. exists (x0 :: tmp2).
    exists x0. repeat split; eauto.
    apply list_disjoint_cons_r; eauto with gensym.
    repeat intro. apply in_cons. apply in_app. now left.
    apply incl_cons. now left.
    repeat intro. apply in_cons. apply in_app. now right.
    apply contained_cons; eauto with gensym.
    (* for effects *)
    exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
    simpl add_dest in *.
    exists (tmp1 ++ tmp2); split; eauto with gensym.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists tmp2.
    repeat split; eauto with gensym.
    (* for set *)
    exploit H0; eauto with gensym. intros [tmp2 [C D]].
    simpl add_dest in *.
    exists (tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0.
    exists (sd_temp sd :: tmp2).
    repeat split; eauto with gensym.
    apply list_disjoint_cons_r; eauto with gensym.
    apply contained_app; eauto with gensym.
    (* seqor *)
    monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
    destruct dst; monadInv EQ0.
    (* for value *)
    exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
    simpl add_dest in *.
    exists (x0 :: tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x1. exists y0. exists (x0 :: tmp2).
    exists x0. repeat split; eauto with gensym.
    apply list_disjoint_cons_r; eauto with gensym.
    apply contained_cons. eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for effects *)
    exploit H0; eauto with gensym. intros [tmp2 [C D]].
    simpl add_dest in *.
    exists (tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists tmp2.
    repeat split; eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for set *)
    exploit H0; eauto with gensym. intros [tmp2 [C D]].
    simpl add_dest in *.
    exists (tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0.
    exists (sd_temp sd :: tmp2).
    repeat split; eauto with gensym.
    apply list_disjoint_cons_r; eauto with gensym.
    apply contained_app; eauto with gensym.
    (* condition *)
    monadInv H2. exploit H; eauto. intros [tmp1 [A B]].
    destruct dst; monadInv EQ0.
    (* for value *)
    exploit H0; eauto with gensym. intros [tmp2 [C D]].
    exploit H1; eauto with gensym. intros [tmp3 [E F]].
    simpl add_dest in *.
    exists (x0 :: tmp1 ++ tmp2 ++ tmp3); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x1. exists y0. exists (x0 :: tmp2).
    exists x2. exists y1. exists (x0 :: tmp3). exists x0.
    repeat split; eauto with gensym.
    apply list_disjoint_cons_r; eauto with gensym.
    apply list_disjoint_cons_r; eauto with gensym.
    apply contained_cons. eauto with gensym.
    apply contained_app. eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for effects *)
    exploit H0; eauto. intros [tmp2 [Csyntax D]].
    exploit H1; eauto. intros [tmp3 [E F]].
    simpl add_dest in *.
    exists (tmp1 ++ tmp2 ++ tmp3); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists tmp2.
    exists x1. exists y1. exists tmp3.
    repeat split; eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for test *)
    exploit H0; eauto with gensym. intros [tmp2 [C D]].
    exploit H1; eauto 10 with gensym. intros [tmp3 [E F]].
    simpl add_dest in *.
    exists (x0 :: tmp1 ++ tmp2 ++ tmp3); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x1. exists y0. exists (x0 :: tmp2).
    exists x2. exists y1. exists (x0 :: tmp3). exists x0.
    repeat split; eauto with gensym.
    apply list_disjoint_cons_r; eauto with gensym.
    apply list_disjoint_cons_r; eauto with gensym.
    apply contained_cons; eauto with gensym.
    apply contained_app; eauto with gensym.
    apply contained_app; eauto with gensym.
    (* sizeof *)
    monadInv H. UseFinish.
    exists (@nil ident); split; auto with gensym. constructor. reflexivity. reflexivity.
    (* alignof *)
    monadInv H. UseFinish.
    exists (@nil ident); split; auto with gensym. constructor. reflexivity. reflexivity.
    (* assign *)
    monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
    exploit H0; eauto. intros [tmp2 [Csyntax D]].
    destruct dst; monadInv EQ2; simpl add_dest in *.
    (* for value *)
    exists (x1 :: tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists (tmp2).
    repeat split; eauto with gensym. right. exists x1.
    repeat split; eauto with gensym.
    apply contained_cons. eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for effects *)
    exists (tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists (tmp2).
    repeat split; eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for set *)
    exists (x1 :: tmp1 ++ tmp2); split.
    repeat rewrite app_ass. simpl.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists (tmp2).
    repeat split; eauto with gensym. right. exists x1.
    repeat split; eauto with gensym.
    apply contained_cons. eauto with gensym.
    apply contained_app; eauto with gensym.
    (* assignop *)
    monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
    exploit H0; eauto. intros [tmp2 [Csyntax D]].
    exploit transl_valof_meets_spec; eauto. intros [tmp3 [E F]].
    destruct dst; monadInv EQ3; simpl add_dest in *.
    (* for value *)
    exists (x2 :: tmp1 ++ tmp2 ++ tmp3); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists (tmp2).
    exists x1. exists y1. exists tmp3.
    repeat split; eauto with gensym.
    right. exists x2.
    repeat split; eauto with gensym.
    
    apply contained_cons. eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for effects *)
    exists (tmp1 ++ tmp2 ++ tmp3); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists (tmp2).
    exists x1. exists y1. exists tmp3.
    repeat split; eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for set *)
    exists (x2 :: tmp1 ++ tmp2 ++ tmp3); split.
    repeat rewrite app_ass. simpl.
    intros. exists x. exists y. exists tmp1. exists x0. exists y0. exists (tmp2).
    exists x1. exists y1. exists tmp3.
    repeat split; eauto with gensym. right.
    repeat split; eauto with gensym. exists x2.
    repeat split; eauto with gensym.
    apply contained_cons. eauto with gensym.
    apply contained_app; eauto with gensym.
    (* postincr *)
    monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
    destruct dst; monadInv EQ0; simpl add_dest in *.
    (* for value *)
    exists (x0 :: tmp1); split.
    intros. simpl. right. exists x. exists y. exists tmp1. exists x0.
    repeat split; eauto with gensym.
    apply contained_cons; eauto with gensym.
    (* for effects *)
    exploit transl_valof_meets_spec; eauto. intros [tmp2 [Csyntax D]].
    exists (tmp1 ++ tmp2); split.
    intros. simpl. left. exists x. exists y. exists tmp1. exists x0. exists y0. exists tmp2.
    repeat split; eauto with gensym.
    eauto with gensym.
    (* for set *)
    repeat rewrite app_ass; simpl.
    exists (x0 :: tmp1); split.
    intros. simpl. right. exists x. exists y. exists tmp1. exists x0.
    repeat split; eauto with gensym.
    apply contained_cons; eauto with gensym.
    (* comma *)
    monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
    exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
    exists (tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists (add_dest For_effects tmp1). exists x0.
    exists (add_dest dst tmp2).
    repeat split; eauto with gensym.
    destruct dst; simpl; eauto with gensym.
    apply list_disjoint_cons_r; eauto with gensym.
    simpl. eapply incl_tran. 2: apply add_dest_incl. auto with gensym.
    destruct dst; simpl; auto with gensym.
    apply contained_app; eauto with gensym.
    (* call *)
    monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
    exploit H0; eauto. intros [tmp2 [Csyntax D]].
    destruct dst; monadInv EQ2; simpl add_dest in *.
    (* for value *)
    exists (x1 :: tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists tmp2. exists x1.
    repeat split; eauto with gensym.
    apply contained_cons. eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for effects *)
    exists (tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists tmp2.
    repeat split; eauto with gensym.
    apply contained_app; eauto with gensym.
    (* for set *)
    exists (x1 :: tmp1 ++ tmp2); split.
    repeat rewrite app_ass.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists tmp2. exists x1.
    repeat split; eauto with gensym.
    apply contained_cons. eauto with gensym.
    apply contained_app; eauto with gensym.
    (* builtin *)
    monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
    destruct dst; monadInv EQ0; simpl add_dest in *.
    (* for value *)
    exists (x0 :: tmp1); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0.
    repeat split; eauto with gensym.
    apply contained_cons; eauto with gensym.
    (* for effects *)
    exists tmp1; split.
    econstructor; eauto with gensym.
    auto.
    (* for set *)
    exists (x0 :: tmp1); split.
    repeat rewrite app_ass.
    intros. simpl. exists x. exists y. exists tmp1. exists x0.
    repeat split; eauto with gensym.
    apply contained_cons; eauto with gensym.
    (* loc *)
    monadInv H.
    (* paren *)
    monadInv H0.
    (* nil *)
    monadInv H; exists (@nil ident); split; auto with gensym. constructor. reflexivity. reflexivity.
    (* cons *)
    monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
    exploit H0; eauto. intros [tmp2 [Csyntax D]].
    exists (tmp1 ++ tmp2); split.
    intros. simpl. exists x. exists y. exists tmp1. exists x0. exists y0. exists tmp2.
    repeat split; eauto with gensym.
    eauto with gensym.
  Qed.

  Lemma transl_expr_meets_spec:
    forall r dst g sl a g' I,
      transl_expr dst r g = Res (sl, a) g' I ->
      dest_below dst g ->
      exists tmps, forall ge e le m, tr_top ge e le m dst r sl a tmps.
  Proof.
    intros. exploit (proj1 transl_meets_spec); eauto. intros [tmps [A B]].
    exists (add_dest dst tmps); intros. apply tr_top_base. auto.
  Qed.

  Lemma transl_expression_meets_spec:
    forall r g s a g' I,
      transl_expression r g = Res (s, a) g' I ->
      tr_expression r s a.
  Proof.
    intros. monadInv H. exploit transl_expr_meets_spec; eauto.
    intros [tmps A]. econstructor; eauto.
  Qed.

  Lemma transl_expr_stmt_meets_spec:
    forall r g s g' I,
      transl_expr_stmt r g = Res s g' I ->
      tr_expr_stmt r s.
  Proof.
    intros. monadInv H. exploit transl_expr_meets_spec; eauto.
    intros [tmps A]. econstructor; eauto.
  Qed.

  Lemma transl_if_meets_spec:
    forall r s1 s2 g s g' I,
      transl_if r s1 s2 g = Res s g' I ->
      tr_if r s1 s2 s.
  Proof.
    intros. monadInv H. exploit transl_expr_meets_spec; eauto.
    intros [tmps A]. econstructor; eauto.
  Qed.

  Lemma transl_stmt_meets_spec:
    forall s g ts g' I, transl_stmt s g = Res ts g' I -> tr_stmt s ts
  with transl_lblstmt_meets_spec:
         forall s g ts g' I, transl_lblstmt s g = Res ts g' I -> tr_lblstmts s ts.
  Proof.
    generalize transl_expression_meets_spec transl_expr_stmt_meets_spec transl_if_meets_spec; intros T1 T2 T3.
    Opaque transl_expression transl_expr_stmt.
    clear transl_stmt_meets_spec.
    induction s; simpl; intros until I; intros TR;
      try (monadInv TR); try (constructor; eauto).
    destruct (is_Sskip s1); destruct (is_Sskip s2) eqn:?; monadInv EQ3; try (constructor; eauto).
    eapply tr_ifthenelse_empty; eauto.
    destruct (is_Sskip s1); monadInv EQ4.
    apply tr_for_1; eauto.
    apply tr_for_2; eauto.
    destruct o; monadInv TR; constructor; eauto.
    clear transl_lblstmt_meets_spec.
    induction s; simpl; intros until I; intros TR;
      monadInv TR; constructor; eauto.
  Qed.

  Relational presentation for the transformation of functions, fundefs, and variables.

  Inductive tr_function: Csyntax.function -> Clight.function -> Prop :=
  | tr_function_intro: forall f tf,
      tr_stmt f.(Csyntax.fn_body) tf.(fn_body) ->
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

  Lemma transl_function_spec:
    forall f tf,
      transl_function f = OK tf ->
      tr_function f tf.
  Proof.
    unfold transl_function; intros.
    destruct (transl_stmt (Csyntax.fn_body f) (initial_generator tt)) eqn:T; inv H.
    constructor; auto. simpl. eapply transl_stmt_meets_spec; eauto.
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
    
  

End SPEC.
