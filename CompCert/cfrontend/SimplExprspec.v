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
           (sla : list statement * expr) : iProp := ⌜ True ⌝ ∗
    match e with
    | Csyntax.Evar id ty =>
                 \⌜ sla = (final dst (Evar id ty),Evar id ty) ⌝
    | Csyntax.Ederef e1 ty =>
      ∃ sla2, tr_expr le For_val e1 sla2 ∗
      \⌜sla = (sla2.1 ++ final dst (Ederef' sla2.2 ty),Ederef' sla2.2 ty)⌝
| Csyntax.Efield e1 f ty =>
  ∃ sla2, tr_expr le For_val e1 sla2 ∗
  \⌜ sla = (sla2.1 ++ final dst (Efield sla2.2 f ty),Efield sla2.2 f ty) ⌝

| Csyntax.Eval v ty =>
  match dst with
  | For_effects => ⌜sla.1 = nil⌝
  | For_val =>
    (∀ tge e le' m, (∀ id, \s id -∗ ⌜ le'!id = le!id ⌝) -∗ ⌜ eval_expr tge e le' m sla.2 v ⌝) ∗ ⌜ typeof sla.2 = ty /\ sla.1 = nil ⌝
  | For_set sd => ∃ a,
    (∀ tge e le' m, (∀ id, \s id -∗ ⌜ le'!id = le!id ⌝) -∗ ⌜ eval_expr tge e le' m a v ⌝) ∗ ⌜ typeof a = ty /\ sla.1 = do_set sd a ⌝
  end
| Csyntax.Esizeof ty' ty =>
  \⌜ sla = (final dst (Esizeof ty' ty), Esizeof ty' ty)⌝
| Csyntax.Ealignof ty' ty =>
  \⌜ sla = (final dst (Ealignof ty' ty), Ealignof ty' ty) ⌝
| Csyntax.Evalof e1 ty =>
  ∃ sla2 sl3,
    tr_expr le For_val e1 sla2  ∗
    tr_rvalof (Csyntax.typeof e1) sla2.2 (sl3,sla.2)  ∗
    \⌜ sla.1 = (sla2.1 ++ sl3 ++ final dst sla.2) ⌝
| Csyntax.Eaddrof e1 ty =>
  ∃ sla2, tr_expr le For_val e1 sla2  ∗
  \⌜ sla = (sla2.1 ++ final dst (Eaddrof' sla2.2 ty), Eaddrof' sla2.2 ty) ⌝
| Csyntax.Eunop ope e1 ty =>
  ∃ sla2, tr_expr le For_val e1 sla2  ∗
  \⌜ sla = (sla2.1 ++ final dst (Eunop ope sla2.2 ty), Eunop ope sla2.2 ty) ⌝
| Csyntax.Ebinop ope e1 e2 ty =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
  tr_expr le For_val e2 sla3  ∗
  \⌜ sla = (sla2.1 ++ sla3.1 ++ final dst (Ebinop ope sla2.2 sla3.2 ty), Ebinop ope sla2.2 sla3.2 ty) ⌝
| Csyntax.Ecast e1 ty =>
  ∃ sla2, tr_expr le For_val e1 sla2  ∗
  \⌜ sla = (sla2.1 ++ final dst (Ecast sla2.2 ty), Ecast sla2.2 ty ) ⌝
| Csyntax.Eseqand e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 t,
    (<absorb>\s t ∧ (tr_expr le For_val e1 sla2  ∗
                     tr_expr le (For_set (sd_seqbool_val t ty)) e2 sla3))
      ∗ \⌜ sla = (sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (Sset t (Econst_int Int.zero ty)) :: nil, Etempvar t ty ) ⌝
| For_effects =>
  ∃ sla2 sla3, tr_expr le For_val e1 sla2  ∗
               tr_expr le For_effects e2 sla3  ∗
               \⌜  sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) Sskip :: nil ⌝
| For_set sd =>
  ∃ sla2 sla3,
    (<absorb> \s (sd_temp sd) ∧
    (tr_expr le For_val e1 sla2  ∗
            tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sla3))
      ∗ ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil ⌝
  end
| Csyntax.Eseqor e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 t,
    (<absorb> \s t ∧
    (tr_expr le For_val e1 sla2  ∗
             tr_expr le (For_set (sd_seqbool_val t ty)) e2 sla3))
      ∗ \⌜ sla = (sla2.1 ++ makeif sla2.2 (Sset t (Econst_int Int.one ty)) (makeseq sla3.1) :: nil, Etempvar t ty) ⌝
| For_effects =>
  ∃ sla2 sla3,
    tr_expr le For_val e1 sla2  ∗
    tr_expr le For_effects e2 sla3  ∗
    \⌜ sla.1 = sla2.1 ++ makeif sla2.2 Sskip (makeseq sla3.1) :: nil ⌝
| For_set sd =>
  ∃ sla2 sla3,
    (<absorb> \s (sd_temp sd) ∧
    (tr_expr le For_val e1 sla2  ∗
             tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sla3))
      ∗ ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq (do_set sd (Econst_int Int.one ty))) (makeseq sla3.1) :: nil ⌝
  end

| Csyntax.Econdition e1 e2 e3 ty =>
  match dst with
  | For_val =>
    ∃ sla2 sla3 sla4 t,
    (<absorb> \s t ∧
    (tr_expr le For_val e1 sla2 ∗
    (tr_expr le (For_set (SDbase ty ty t)) e2 sla3 ∧
    tr_expr le (For_set (SDbase ty ty t)) e3 sla4))) ∗
    \⌜ sla = (sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil,Etempvar t ty)⌝
| For_effects =>
  ∃ sla2 sla3 sla4,
    tr_expr le For_val e1 sla2  ∗
    tr_expr le For_effects e2 sla3 ∗
    tr_expr le For_effects e3 sla4 ∗
    \⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil ⌝
| For_set sd =>
  ∃ sla2 sla3 sla4 t,
    (<absorb> \s t ∧
    (tr_expr le For_val e1 sla2  ∗
    (tr_expr le (For_set (SDcons ty ty t sd)) e2 sla3 ∧
    tr_expr le (For_set (SDcons ty ty t sd)) e3 sla4))) ∗
    ⌜ sla.1 = sla2.1 ++ makeif sla2.2 (makeseq sla3.1) (makeseq sla4.1) :: nil ⌝
  end
| Csyntax.Eassign e1 e2 ty =>
  ∃ sla2 sla3,
  tr_expr le For_val e1 sla2  ∗
  tr_expr le For_val e2 sla3  ∗
  (⌜ sla.1 = sla2.1 ++ sla3.1 ++ make_assign sla2.2 sla3.2 :: nil /\  dst = For_effects ⌝ ∨ (∃ t, \s t ∗ ⌜ sla.1 = sla2.1 ++ sla3.1 ++ Sset t (Ecast sla3.2 (Csyntax.typeof e1)) :: make_assign sla2.2 (Etempvar t (Csyntax.typeof e1)) :: final dst (Etempvar t (Csyntax.typeof e1)) ⌝))
| Csyntax.Eassignop ope e1 e2 tyres ty =>
  ∃ sla2 sla3 sla4,
    tr_expr le For_val e1 sla2  ∗
    tr_expr le For_val e2 sla3  ∗
    tr_rvalof (Csyntax.typeof e1) sla2.2 sla4  ∗
    (⌜ dst = For_effects /\
     sla.1 = sla2.1 ++ sla3.1 ++ sla4.1 ++ make_assign sla2.2 (Ebinop ope sla4.2 sla3.2 tyres) :: nil ⌝ ∨ (∃ t, \s t ∗ ⌜ sla = (sla2.1 ++ sla3.1 ++ sla4.1 ++ Sset t (Ecast (Ebinop ope sla4.2 sla3.2 tyres) (Csyntax.typeof e1)) :: make_assign sla2.2 (Etempvar t (Csyntax.typeof e1)) :: final dst (Etempvar t (Csyntax.typeof e1)), (Etempvar t (Csyntax.typeof e1))) ⌝))
| Csyntax.Epostincr id e1 ty =>
  ((∃ sla2 sla3,
        tr_expr le For_val e1 sla2  ∗
                tr_rvalof (Csyntax.typeof e1) sla2.2 sla3  ∗
                ⌜ sla.1 = sla2.1 ++ sla3.1 ++
                                 make_assign sla2.2 (transl_incrdecr id sla3.2 (Csyntax.typeof e1)) :: nil ⌝) ∨
   (∃ sla2 t,
       tr_expr le For_val e1 sla2  ∗
               \s t  ∗
               ⌜ sla = (sla2.1 ++ make_set t sla2.2 ::
                               make_assign sla2.2 (transl_incrdecr id (Etempvar t (Csyntax.typeof e1)) (Csyntax.typeof e1)) ::
                               final dst (Etempvar t (Csyntax.typeof e1)),Etempvar t (Csyntax.typeof e1))⌝))

| Csyntax.Ecomma e1 e2 ty =>
  ∃ sla2 sl3,
    tr_expr le For_effects e1 sla2  ∗
    tr_expr le dst e2 (sl3,sla.2)  ∗
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
    (<absorb> \s t ∧
    (tr_expr le For_val e1 sla2  ∗
    tr_exprlist le el2 slal3))  ∗
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
    (<absorb> \s t  ∧
    tr_expr le (For_set (SDbase tycast ty t)) e1 (sla.1,a2)) ∗
    ⌜ sla.2 = Etempvar t ty ⌝
| For_effects =>
  ∃ a2, tr_expr le For_effects e1 (sla.1,a2)
| For_set sd =>
  ∃ a2 t,
    tr_expr le (For_set (SDcons tycast ty t sd)) e1 (sla.1,a2) ∧ \s t
  end

| _ => False
  end
  with tr_exprlist (le : temp_env) (e : Csyntax.exprlist) (sla : list statement * list expr) : iProp := ⌜ True ⌝ ∗
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

  Lemma tr_expr_abs : forall (Q : iProp) le dst r res,
      tr_expr le dst r res ∗ Q -∗ tr_expr le dst r res.
  Proof.
    induction r; iIntros "* [[HC HA] HB]"; iSplitL "HC HB"; trivial.
  Qed.

  Lemma tr_exprlist_abs : forall (Q : iProp) le r res,
      tr_exprlist le r res ∗ Q -∗ tr_exprlist le r res.
  Proof.
    induction r; iIntros "* [[HC HA] HB]"; iSplitL "HC HB"; trivial.
  Qed.
  
  Lemma transl_meets_spec :
    (forall r dst,
        {{ emp }} transl_expr dst r {{ res, RET res; (∀ le, dest_below dst -∗ tr_expr le dst r res)}})
    /\
    (forall rl,
        {{ emp }} transl_exprlist rl {{ res, RET res; (∀ le, tr_exprlist le rl res) }}).
  Proof.
    pose transl_valof_meets_spec.
    apply tr_expr_exprlist; intros; rewrite /transl_expr; rewrite /transl_exprlist;
      fold transl_exprlist; fold transl_expr; tac2; rewrite /tr_expr; fold tr_expr; tac2.
    - destruct v; tac2; iApply ret_spec_complete; destruct dst; iIntros; eauto; iSplitR; auto;
        try (iExists _); try iSplit; eauto; iIntros; simpl;
          iPureIntro; eauto; intros; constructor; reflexivity. 
    - iApply ret_spec_complete. iIntros "[HA HB]"; iFrame.
      destruct dst; iIntros; iPureIntro; auto.
    - apply forall_wand_true_pre. iApply ret_spec_complete. iIntros "HA" (?) "HB".
      iSplitL "HB"; auto. iExists v.
      iSplitL "HA". iApply "HA". iPureIntro.
      destruct dst; simpl; eauto; rewrite app_nil_r; reflexivity.
    - frameR; apply b.
    - iApply ret_spec_complete.
      iIntros "[HA HB]" (?) "HC". iSplitL "HC"; auto. iExists v; iExists v0.1.
      iSplitL "HB". iApply "HB". trivial.
      destruct dst; iSimpl; iSplitL "HA"; try(rewrite <- surjective_pairing; iApply "HA");
        iPureIntro; try(rewrite app_nil_r; reflexivity); rewrite app_assoc; reflexivity.
    - iApply ret_spec_complete. 
      iIntros "HA" (le) "HB". iSplitL "HB"; auto. iExists v. iSplitL "HA". iApply "HA". trivial.
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - iApply ret_spec_complete.
      iIntros "HA" (le) "HB". iSplitL "HB"; auto. iExists v. iSplitL "HA". iApply "HA". trivial.
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - iApply ret_spec_complete.
      iIntros "HA" (le) "HB". iSplitL "HB"; auto. iExists v. iSplitL "HA". iApply "HA". trivial. 
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - frameR. apply H0.
    - iApply ret_spec_complete.
      iIntros "[HA HC]" (le) "HB". iSplitL "HB"; auto.
      repeat iExists _.
      iSplitL "HC". iApply "HC". trivial.
      iSplitL "HA". iApply "HA". trivial.
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r; reflexivity).
      rewrite app_assoc. reflexivity.
    - iApply ret_spec_complete.
      iIntros "HA" (le) "HB". iSplitL "HB"; auto. iExists _. iSplitL "HA". iApply "HA". trivial. 
      iPureIntro. destruct dst; simpl; try (rewrite app_nil_r); reflexivity.
    - destruct dst; repeat tac2.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[HA [HC HD]]" (?) "_". iSplit; auto. repeat iExists _.
        iSplitL. iSplit. iExists ty. iFrame.
        iSplitL "HD". iApply "HD". trivial.
        iApply "HA". iExists ty. iApply "HC".
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[HA HC]" (le) "HB". iSplit; auto. repeat iExists _. 
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iApply "HA".  trivial.
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + iApply ret_spec_complete. iIntros "[HA HC]" (le) "HB". iSplitR; auto.
        repeat iExists _.
        iSplitL. iSplit. iFrame.
        iSplitL "HC". iApply "HC". trivial.
        iApply "HA". iFrame.
        iPureIntro. reflexivity.
    - destruct dst; repeat tac2.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[HA [HC HD]]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL. iSplit. iExists ty. iFrame.
        iSplitL "HD". iApply "HD". trivial.
        iApply "HA". iExists ty. iApply "HC".
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[HA HC]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iApply "HA".  trivial.
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + iApply ret_spec_complete. iIntros "[HA HC]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL. iSplit. iFrame.
        iSplitL "HC". iApply "HC". trivial.
        iApply "HA". iFrame.
        iPureIntro. reflexivity.
    - destruct dst; repeat tac2.
      + frameR. apply H0.
      + frameR. apply H1.
      + iApply ret_spec_complete.
        iIntros "[HA [HC [HE HD]]]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL; eauto. iSplit. iExists ty. iFrame.
        iSplitL "HD". iApply "HD". trivial.
        iSplit.
        * iDestruct ("HC" $! le with "[HE]") as "HC". iExists ty. iFrame. iClear "HB".
          iApply tr_expr_abs. iFrame. iApply "HA".
        * iDestruct ("HA" $! le with "[HE]") as "HA". iExists ty. iFrame. iClear "HB".
          iApply tr_expr_abs. iFrame. iApply "HC".
      + frameR. apply H0.
      + frameR. apply H1.
      + iApply ret_spec_complete.
        iIntros "[HA [HC HD]]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HD". iApply "HD". trivial.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iApply "HA". trivial.
        iPureIntro. reflexivity.
      + frameR. apply H0.
      + frameR. apply H1.
      + iApply ret_spec_complete.
        iIntros "[HA [HD [HE HC]]]" (le) "HB". iSplitL "HB"; auto. repeat iExists _.
        iSplitL; eauto. iSplit. iExists ty. iFrame.
        iSplitL "HC". iApply "HC". trivial.
        iSplit.
        * iDestruct ("HD" with "[HE]") as "HC". iExists ty. iFrame.
          iApply tr_expr_abs. iFrame. iApply "HA".
        * iDestruct ("HA" with "[HE]") as "HA". iExists ty. iFrame.
          iApply tr_expr_abs. iFrame. iApply "HD".
    - iApply ret_spec_complete. iIntros "[HA HB]". iSplitL "HB"; auto. iPureIntro.
      destruct dst; reflexivity.
    - iApply ret_spec_complete. iIntros "[HA HB]". iSplitL "HB"; auto. iPureIntro.
      destruct dst; reflexivity.
    - frameR. eapply H0.
    - destruct dst; tac2.
      + iApply ret_spec_complete.
        iIntros "[HA [HD HC]]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HD". iApply "HD". trivial.
        iRight. iExists v1. 
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA". 
        iPureIntro. reflexivity.
      + iApply ret_spec_complete.
        iIntros "[HA HC]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iApply "HA". trivial.
        iLeft. iPureIntro. split; reflexivity.
      + iApply ret_spec_complete.
        iIntros "[HA [HD HC]]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HD". iApply "HD". trivial. iRight.
        iExists v1. iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA". 
        iPureIntro. simpl. admit.
    - frameR. apply H0.
    - frameR. apply transl_valof_meets_spec.
    - destruct dst; tac2.
      + iApply ret_spec_complete.
        iIntros "[HA [HD [HE HC]]]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HE". iApply "HE". trivial.
        iSplitL "HD". iApply "HD".
        iRight. iExists v2.
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA". 
        iPureIntro. reflexivity.
      + iApply ret_spec_complete.
        iIntros "[HA [HD HC]]" (le) "HB". iSplit; auto. repeat iExists _.
         iSplitL "HC". iApply "HC". trivial.
         iSplitL "HD". iApply "HD". trivial.
         iFrame. iLeft.
         iPureIntro. split; reflexivity.
      + iApply ret_spec_complete.
        iIntros "[HA [HD [HE HC]]]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HE". iApply "HE". trivial.
        iSplitL "HD". iApply "HD".
        iRight. iExists v2.
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA". 
        iPureIntro. simpl. admit.
    - destruct dst; tac2.
      + iApply ret_spec_complete.
        iIntros "[HA HC]" (le) "HB". iSplit; auto.
        iRight. iExists v. iExists v0.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA".
        iPureIntro. reflexivity.
      + frameR. apply b.
      + iApply ret_spec_complete.
        iIntros "[HA HC]" (le)  "HB". iSplit; auto.
        iLeft. iExists v. iExists v0.
        iSplitL "HC". iApply "HC". trivial.
        iFrame.
        iPureIntro. reflexivity.
      + iApply ret_spec_complete.
        iIntros "[HA HC]" (le) "HB". iSplit; auto.
        iRight.
        iExists v. iExists v0.
        iSplitL "HC". iApply "HC". trivial.
        iSplitL "HA". iExists (Csyntax.typeof l). iApply "HA".
        iPureIntro. simpl. admit.
    - frameR. apply H0.
    - iApply ret_spec_complete. 
      iIntros "[HA HC]" (le) "HB". iSplit; auto. repeat iExists _.
      iSplitL "HC". iApply "HC". trivial.
      iSplitL. simpl. rewrite <- surjective_pairing.
      iApply "HA". iApply "HB".
      iFrame. iPureIntro. reflexivity.
    - destruct dst; tac2; fold tr_exprlist; fold tr_expr.
      + iApply ret_spec_complete. 
        iIntros "[HA [HD HC]]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL; eauto. iSplit. iExists ty. iFrame.
        iSplitL "HC". iApply "HC". trivial.
        iClear "HB". iApply tr_exprlist_abs. iSplitL "HD". iApply "HD". iApply "HA".
      + iApply ret_spec_complete. 
        iIntros "[HA HD]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HD". iApply "HD". trivial.
        iSplitL "HA". iApply "HA". trivial.
      + iApply ret_spec_complete. 
        iIntros "[HA [HD HC]]" (le) "HB". iSplit; auto. repeat iExists _. iFrame.
        iSplitL; eauto.
        iSplit. iExists ty. iFrame.
        iSplitL "HC". iApply "HC"; trivial.
        iApply tr_exprlist_abs. iSplitL "HD". iApply "HD". iApply "HA".
        iPureIntro. simpl. admit. 
    - fold tr_exprlist. destruct dst; tac2.
      + iApply ret_spec_complete. 
        iIntros "[HA HC]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HC". iApply "HC".
        iSplitL "HA". iExists ty. iApply "HA".
        iFrame.
        iPureIntro. reflexivity.
      + iApply ret_spec_complete.
        iIntros "HA" (le) "HB". iSplit; auto.
      + iApply ret_spec_complete. 
        iIntros "[HA HC]" (le) "HB". iSplit; auto. repeat iExists _.
        iSplitL "HC". iApply "HC".
        iSplitL "HA". iExists ty. iApply "HA".
        iFrame.
        iPureIntro. simpl. admit. 
    - iApply ret_spec_bis. eauto.
    - rewrite /tr_exprlist; fold tr_exprlist; fold tr_expr; tac2.
      iApply ret_spec_complete. 
      iIntros "[HA HB]" (le). iSplit; auto. repeat iExists _.
      iSplitL "HB". iApply "HB". trivial.
      iSplitL "HA". iApply "HA".
      iPureIntro. reflexivity.          
  Admitted. 
  
  Section TR_TOP.

    Variable ge: genv.
    Variable e: Clight.env.
    Variable le: temp_env.
    Variable m: mem.
    
    Definition tr_top_base dst r sl a := tr_expr le dst r (sl,a).

    Definition tr_top_val_val (dst : destination) expr (sl : list statement) a : Prop :=
      match sl with
      | nil => exists v ty, typeof a = ty /\ eval_expr ge e le m a v /\ dst = For_val
                  /\ expr = Csyntax.Eval v ty
      | _ => False
    end.

    Definition tr_top dst expr sl a := tr_top_base dst expr sl a ∨ \⌜tr_top_val_val dst expr sl a⌝.

  End TR_TOP.

    
(** ** Translation of statements *)

  Lemma transl_expr_meets_spec:
    forall r dst,
      {{ emp }} transl_expr dst r {{ res, RET res;  dest_below dst -∗ ∀ ge e le m, tr_top  ge e le m dst r res.1 res.2 }}.
  Proof.
    intros. exploit (proj1 transl_meets_spec); eauto. intro. iIntros (?) "_ HA".
    iApply H; eauto. iIntros (res) "HB". iApply "HA". iIntros. rewrite /tr_top.
    iLeft. rewrite /tr_top_base.
    rewrite (surjective_pairing res). iApply "HB". iFrame. 
  Qed.

  Lemma test2 : forall (P : iProp) (Q : Prop), (forall tmps, P () tmps -> Q) -> (P -∗ ⌜Q⌝).
  Proof.
    intros. split. red. red. MonPred.unseal. intros. repeat red.
    intros. exists emp. red. exists ∅. exists ∅. repeat split; auto.
    - repeat red. intros. inversion_star h P. inversion P1. inversion H4. subst.
      exists ∅. exists h0.
      repeat split; auto.
      + apply (H h0). destruct a. apply P2.
    - inversion H0. inversion H3. rewrite heap_union_empty_l. reflexivity.
  Qed.
  
  Inductive tr_expression: Csyntax.expr -> statement -> expr -> Prop :=
  | tr_expression_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a () tmps) ->
      tr_expression r (makeseq sl) a.
  
  Import adequacy.
  Lemma transl_expression_meets_spec: forall r,
      {{ emp }} transl_expression r {{ res, RET res; ⌜ tr_expression r res.1 res.2 ⌝ }}.
  Proof.
    intro. unfold transl_expression. pose (H := proj1 transl_meets_spec). tac2.
    - apply (H r For_val).
    - iApply ret_spec_complete. iStopProof. apply test2. intros.
      apply (tr_expression_intro _ _ _ tmps). intros. apply soundness2. apply soundness3 in H0.
      iIntros "HA". iDestruct (H0 with "HA") as "HA". unfold tr_top.
      iLeft. unfold tr_top_base. simpl. rewrite <- surjective_pairing. iApply "HA"; eauto.
  Qed.
  
  Inductive tr_expr_stmt: Csyntax.expr -> statement -> Prop :=
  | tr_expr_stmt_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_effects r sl a () tmps) ->
      tr_expr_stmt r (makeseq sl).
  
  Lemma transl_expr_stmt_meets_spec: forall r,
      {{ emp }} transl_expr_stmt r {{ res, RET res; ⌜ tr_expr_stmt r res ⌝}}.
  Proof.
    intro. unfold transl_expr_stmt. epose transl_meets_spec. destruct a; tac2.
    - apply H.
    - iApply ret_spec_complete. iStopProof. apply test2. intros.
      apply (tr_expr_stmt_intro _ _ v.2 tmps). intros.
      apply soundness3 in H1. apply soundness2.
      iIntros "HA". iDestruct (H1 with "HA") as "HA". unfold tr_top. iLeft.
      unfold tr_top_base. simpl. rewrite <- surjective_pairing. iApply "HA".
      trivial.
  Qed.

  Inductive tr_if: Csyntax.expr -> statement -> statement -> statement -> Prop :=
  | tr_if_intro: forall r s1 s2 sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a () tmps) ->
      tr_if r s1 s2 (makeseq (sl ++ makeif a s1 s2 :: nil)).
  
  Lemma transl_if_meets_spec: forall r s1 s2,
      {{ emp }} transl_if r s1 s2 {{ res, RET res; ⌜ tr_if r s1 s2 res ⌝ }}.
  Proof.
    intros. epose transl_meets_spec. destruct a; unfold transl_if; tac2.
    - apply H.
    - iApply ret_spec_complete. iStopProof. apply test2. intros.
      apply (tr_if_intro _ _ _ _ _ tmps). intros.
      apply soundness3 in H1. apply soundness2.
      iIntros "HA". iDestruct (H1 with "HA") as "HA". unfold tr_top. iLeft.
      unfold tr_top_base. simpl. rewrite <- surjective_pairing. iApply "HA".
      trivial.
  Qed.

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

  Lemma transl_stmt_meets_spec : forall s,
      {{ emp }} transl_stmt s {{ res, RET res; ⌜ tr_stmt s res ⌝}}
  with transl_lblstmt_meets_spec:
         forall s,
           {{ emp }} transl_lblstmt s {{ res, RET res; ⌜ tr_lblstmts s res ⌝ }}. 
  Proof.
    pose transl_expression_meets_spec. pose transl_if_meets_spec. pose transl_expr_stmt_meets_spec.
    clear transl_stmt_meets_spec.
    intro. induction s; rewrite /transl_stmt; fold transl_stmt; tac2.
    - iApply ret_spec_bis. iPureIntro. constructor.
    - apply (post_weaker _ _ _ _ (b1 e)). iIntros. iPureIntro. apply (tr_do _ _ a).
    - iApply ret_spec_complete. iIntros "[% %]".
      iPureIntro. apply (tr_seq _ _  _ _ H0 H).
    - tac2. frameR. apply transl_expression_meets_spec.
      destruct (is_Sskip s1); destruct (is_Sskip s2) eqn:?; iApply ret_spec_complete;
        iIntros "[% [% %]]"; iPureIntro; subst.
      1 : apply (tr_ifthenelse_empty _ _ _ H).
      all : apply (tr_ifthenelse _ _ _ _ _ _ _ H H1 H0).
    - iApply ret_spec_complete.
      iIntros "[% %]". iPureIntro. apply (tr_while _ _ _ _ H0 H).
    - iApply ret_spec_complete.
      iIntros "[% %]". iPureIntro. apply (tr_dowhile _ _ _ _ H0 H).
    - frameR. apply transl_if_meets_spec.
    - destruct (is_Sskip); iApply ret_spec_complete;
        iIntros "[% [% [% %]]]"; iPureIntro; subst.
      + apply (tr_for_1 _ _ _ _ _ _ H1 H0 H).
      + apply (tr_for_2 _ _ _ _ _ _ _ _ H1 n H2 H0 H).
    - iApply ret_spec_bis. iPureIntro. constructor.
    - iApply ret_spec_bis. iPureIntro. constructor.
    - destruct o; tac2.
      + iApply ret_spec_complete. iIntros. iPureIntro. apply (tr_return_some _ _ _ a).
      + iApply ret_spec_bis. iPureIntro. constructor. 
    - fold transl_lblstmt. frameR. apply transl_lblstmt_meets_spec.
    - iApply ret_spec_complete. iIntros "[% %]". iPureIntro. constructor; auto.
    - iApply ret_spec_complete. iIntros "%". iPureIntro. constructor; auto.
    - iApply ret_spec_bis. iPureIntro. constructor.
    - induction s; rewrite /transl_lblstmt; fold transl_lblstmt; fold transl_stmt; tac2.
      + iApply ret_spec_bis. iPureIntro. constructor.
      + iApply ret_spec_complete. iIntros "[% %]". iPureIntro. constructor; auto.
  Qed.

 
  (** Relational presentation for the transformation of functions, fundefs, and variables. *)
  
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
    destruct (run (transl_stmt (Csyntax.fn_body f)) ∅) eqn:?. rewrite Heqe in H. inversion H.
    destruct p.
    rewrite Heqe in H. simpl in *. inversion H.
    apply tr_function_intro; auto; simpl.
    eapply (adequacy_pure (transl_stmt (Csyntax.fn_body f)) _ ∅ s0 s emp).
    2: apply Heqe.
    iIntros "HA". iSplitL; eauto.
    iApply (transl_stmt_meets_spec (Csyntax.fn_body f)). 
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
