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

(** Correctness proof for expression simplification. *)
Require Import FunInd.
Require Import Coqlib (* Maps *) Errors Integers.
Require Import MoSel Locally SimplExpr SimplExprspec.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Ctypes Cop Csyntax Csem Cstrategy Clight.
Import Maps.PTree.


Local Open Scope gensym_monad_scope.
Notation "a ! b" := (get b a) (at level 1).
(** ** Relational specification of the translation. *)

Definition match_prog (p: Csyntax.program) (tp: Clight.program) :=
  match_program (fun ctx f tf => tr_fundef f tf) eq p tp
  /\ prog_types tp = prog_types p.

Lemma transf_program_match:
  forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof.
  unfold transl_program; intros. monadInv H. split; auto.
  unfold program_of_program; simpl. destruct x; simpl.
  eapply match_transform_partial_program_contextual. eexact EQ. 
  intros. apply transl_fundef_spec; auto. 
Qed.

(** ** Semantic preservation *)

Section PRESERVATION.

  Variable prog: Csyntax.program.
  Variable tprog: Clight.program.
  Hypothesis TRANSL: match_prog prog tprog.

  Let ge := Csem.globalenv prog.
  Let tge := Clight.globalenv tprog.

  (** Invariance properties. *)

  Lemma comp_env_preserved:
    Clight.genv_cenv tge = Csem.genv_cenv ge.
  Proof.
    simpl. destruct TRANSL. generalize (prog_comp_env_eq tprog) (prog_comp_env_eq prog). 
    congruence.
  Qed.
  
  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match (proj1 TRANSL)).
  
  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof (Genv.senv_match (proj1 TRANSL)).

  Lemma function_ptr_translated:
    forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ tr_fundef f tf.
  Proof.
    intros.
    edestruct (Genv.find_funct_ptr_match (proj1 TRANSL)) as (ctx & tf & A & B & C); eauto.
  Qed.

  Lemma functions_translated:
    forall v f,
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ tr_fundef f tf.
  Proof.
    intros.
    edestruct (Genv.find_funct_match (proj1 TRANSL)) as (ctx & tf & A & B & C); eauto.
  Qed.

  Lemma type_of_fundef_preserved:
    forall f tf, tr_fundef f tf ->
            type_of_fundef tf = Csyntax.type_of_fundef f.
  Proof.
    intros. inv H.
    inv H0; simpl. unfold type_of_function, Csyntax.type_of_function. congruence.
    auto.
  Qed.

  Lemma function_return_preserved:
    forall f tf, tr_function f tf ->
            fn_return tf = Csyntax.fn_return f.
  Proof.
    intros. inv H; auto.
  Qed.

  (** Properties of smart constructors. *)

  Lemma eval_Ederef':
    forall ge e le m a t l ofs,
      eval_expr ge e le m a (Vptr l ofs) ->
      eval_lvalue ge e le m (Ederef' a t) l ofs.
  Proof.
    intros. unfold Ederef'; destruct a; auto using eval_Ederef.
    destruct (type_eq t0 (typeof a)); auto using eval_Ederef.
    inv H.
    - auto. 
    - inv H0.
  Qed.

  Lemma typeof_Ederef':
    forall a t, typeof (Ederef' a t) = t.
  Proof.
    unfold Ederef'; intros; destruct a; auto. destruct (type_eq t0 (typeof a)); auto. 
  Qed.

  Lemma eval_Eaddrof':
    forall ge e le m a t l ofs,
      eval_lvalue ge e le m a l ofs ->
      eval_expr ge e le m (Eaddrof' a t) (Vptr l ofs).
  Proof.
    intros. unfold Eaddrof'; destruct a; auto using eval_Eaddrof.
    destruct (type_eq t0 (typeof a)); auto using eval_Eaddrof.
    inv H; auto.
  Qed.

  Lemma typeof_Eaddrof':
    forall a t, typeof (Eaddrof' a t) = t.
  Proof.
    unfold Eaddrof'; intros; destruct a; auto. destruct (type_eq t0 (typeof a)); auto. 
  Qed.

  (** Translation of simple expressions. *)

  Lemma pair_equal_spec :
    forall (A B : Type) (a1 a2 : A) (b1 b2 : B),
      (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
  Proof.
    intros. split; intro H; inversion H; subst; eauto.
  Qed.

  Import adequacy.
  
  Local Set Warnings "-deprecated".
  
  Ltac apply_ind_simple_nil l h :=
    match goal with
    | H : Datatypes.negb _ = true |- _ => apply negb_true_iff in H; apply_ind_simple_nil l h
    | H :  _ && _ = true |- _ =>
      let P0 := fresh "P" in
      let P1 := fresh "P" in
      apply andb_true_iff in H as (P0&P1); apply_ind_simple_nil l h
    | H : forall _ _ _ _, bi_emp_valid (tr_expr _ _ l _ _ -∗ _)
                     |- _ => iDestruct (H with h) as h; iDestruct (h with "[] []") as "%"; auto
    | H : forall _ _ _ , bi_emp_valid (tr_exprlist _ l _ _ -∗ _)
                    |- _ => iDestruct (H with h) as h; iDestruct (h with "[]") as "%"; auto
    | _ => idtac
    end.
  
  Ltac apply_ind_core f list_ident :=
    match list_ident with
    | [] => idtac
    | ?h :: ?t =>
      let env := iGetCtx in
      let P := reduction.pm_eval (envs_lookup h env) in
      match P with
      | Some (false, ?P) =>
        match P with
        | tr_expr _ _ ?l _ _ => f l h; apply_ind_core f t
        | tr_exprlist _ ?l _ _ => f l h; apply_ind_core f t
        | tr_rvalof _ ?l _ _ => f l h; apply_ind_core f t
        | _ => apply_ind_core f t
        end
      | _ => idtac "bug2" P
      end
    | _ => idtac "bug1" list_ident
    end.
    
  Ltac apply_ind f :=
    iStartProof;
    let env := iGetCtx in
    let list_ident := eval compute in (rev (envs_dom env)) in
        apply_ind_core f list_ident.
  
  Lemma tr_simple_nil:
    (forall r dst sl le a,
        ⊢ tr_expr le dst r sl a -∗
          ⌜ dst = For_val \/ dst = For_effects ⌝ -∗
                                              ⌜ simple r = true ⌝ -∗
                                                                ⌜sl = nil ⌝)
    /\(forall rl le sl al, ⊢ tr_exprlist le rl sl al -∗ ⌜ simplelist rl = true ⌝ -∗ ⌜ sl = nil ⌝).
  Proof.
    apply tr_expr_exprlist; intros; simpl in *; try discriminate; auto;
      iIntros; norm_all; apply_ind apply_ind_simple_nil; try(destruct a0; subst; norm_all).
    - unfold tr_rvalof; rewrite P0; norm_all; subst; auto.
    - unfold tr_rvalof; rewrite P0; norm_all; subst; auto.
    - destruct a; auto.
    - subst; auto.
  Qed.

  Lemma tr_simple_expr_nil:
    (forall r dst sl le a,
        ⊢ tr_expr le dst r sl a -∗
        ⌜ dst = For_val \/ dst = For_effects ⌝ -∗
        ⌜ simple r = true ⌝ -∗
        ⌜sl = nil ⌝).
  Proof. apply (proj1 tr_simple_nil). Qed.

  Lemma tr_simple_exprlist_nil:
    (forall rl le sl al, ⊢ tr_exprlist le rl sl al -∗
                      ⌜ simplelist rl = true ⌝ -∗ ⌜ sl = nil ⌝).
  Proof. apply (proj2 tr_simple_nil). Qed.
  

  (** Translation of [deref_loc] and [assign_loc] operations. *)

  Remark deref_loc_translated:
    forall ty m b ofs t v,
      Csem.deref_loc ge ty m b ofs t v ->
      match chunk_for_volatile_type ty with
      | None => t = E0 /\ Clight.deref_loc ty m b ofs v
      | Some chunk => volatile_load tge chunk m b ofs t v
      end.
  Proof.
    intros. unfold chunk_for_volatile_type. inv H.
    (* By_value, not volatile *)
    rewrite H1. split; auto. eapply deref_loc_value; eauto.
    (* By_value, volatile *)
    rewrite H0; rewrite H1. eapply volatile_load_preserved with (ge1 := ge); auto. apply senv_preserved.
    (* By reference *)
    rewrite H0. destruct (type_is_volatile ty); split; auto; eapply deref_loc_reference; eauto.
    (* By copy *)
    rewrite H0. destruct (type_is_volatile ty); split; auto; eapply deref_loc_copy; eauto.
  Qed.

  Remark assign_loc_translated:
    forall ty m b ofs v t m',
      Csem.assign_loc ge ty m b ofs v t m' ->
      match chunk_for_volatile_type ty with
      | None => t = E0 /\ Clight.assign_loc tge ty m b ofs v m'
      | Some chunk => volatile_store tge chunk m b ofs v t m'
      end.
  Proof.
    intros. unfold chunk_for_volatile_type. inv H.
    (* By_value, not volatile *)
    rewrite H1. split; auto. eapply assign_loc_value; eauto.
    (* By_value, volatile *)
    rewrite H0; rewrite H1. eapply volatile_store_preserved with (ge1 := ge); auto. apply senv_preserved.
    (* By copy *)
    rewrite H0. rewrite <- comp_env_preserved in *.
    destruct (type_is_volatile ty); split; auto; eapply assign_loc_copy; eauto.
  Qed.

  Ltac apply_ind_simple l h :=
    match goal with
    | H : forall _ _ _, bi_emp_valid (tr_expr _ _ l _ _ -∗ _) |- _ =>
      iDestruct (H with h) as "[% [% %]]"; iClear h
    | H : forall _ _ _ _, bi_emp_valid (tr_expr _ _ l _ _ -∗ _) |- _ =>
      iDestruct (H with h) as "[% [% %]]"; iClear h
    | _ => fail "No rec"
    end.

  (** Evaluation of simple expressions and of their translation *)
  Lemma tr_simple:
    forall e m,
      (forall r v,
          eval_simple_rvalue ge e m r v ->
          forall le dst sl a,
            ⊢ tr_expr le dst r sl a -∗
              ⌜ match dst with
                | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
                | For_effects => sl = nil
                | For_set sd =>
                  exists b, sl = do_set sd b /\ Csyntax.typeof r = typeof b /\ eval_expr tge e le m b v
                end⌝)
      /\
      (forall l b ofs,
          eval_simple_lvalue ge e m l b ofs ->
          forall le sl a, ⊢ tr_expr le For_val l sl a -∗                                               
                       ⌜ sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs ⌝).
  Proof.
    Opaque makeif.
    intros e m.
    apply (eval_simple_rvalue_lvalue_ind ge e m); intros; simpl; iIntros; norm_all;
      apply_ind apply_ind_simple.
    
    (* value *)
    - destruct dst; simpl in *; norm_all.
      + repeat (iSplit; auto). iDestruct (locally_delete with "HD") as "HA". iFrame.
      + iDestruct "HB" as "[_ HA]". norm_all. repeat iExists _. repeat iSplit; auto.
        iDestruct (locally_delete with "HD") as "HA". iFrame.
        
    (* rvalof *)
    - unfold tr_rvalof. subst. rewrite H2. norm_all. subst.
      destruct dst; simpl; eauto; repeat iExists _; repeat iSplit; auto; iPureIntro; econstructor;
        eauto; exploit deref_loc_translated; eauto; unfold chunk_for_volatile_type.
      + rewrite H2. intros [P0 P1]. rewrite <- H6; auto.
      + rewrite H2. intros [P0 P1]. rewrite <- H6; auto.    
        
    - destruct dst; simpl in *; subst; auto; repeat iExists _; repeat iSplit; iPureIntro; simpl;
        auto. rewrite (typeof_Eaddrof' _ ty); auto. eapply eval_Eaddrof'; auto.
      rewrite (typeof_Eaddrof' _ ty); auto. eapply eval_Eaddrof'; auto.
      
    - destruct dst; simpl in *; subst; auto; repeat iExists _; repeat iSplit; iPureIntro; simpl;
        auto; econstructor; eauto; rewrite <- H5; auto.
      
    - rewrite <- comp_env_preserved in H3.
      subst. iPureIntro. rewrite H7 in H3. rewrite H10 in H3.
      destruct dst; simpl; simpl_list; auto.
      + repeat split; auto. econstructor; eauto. 
      + eexists. repeat split; auto. econstructor; eauto.
        
    - subst. iPureIntro. rewrite H5 in H1. destruct dst; simpl in *; auto.
      + repeat split; auto. econstructor; eauto.
      + eexists. repeat split; eauto. econstructor; eauto.
        
    - iPureIntro. subst.
      destruct dst; simpl in *; simpl_list; auto; repeat eexists; pose (P := comp_env_preserved);
        simpl in P; rewrite <- P; apply eval_Esizeof.
      
    - iPureIntro. subst. destruct dst; simpl in *; auto; repeat eexists; repeat split; auto;
                           pose (P := comp_env_preserved); simpl in P; rewrite <- P; constructor.
      
    - destruct a0 as (P0&P1&P2). subst. iPureIntro. repeat split; auto. constructor. apply H.
    - destruct a0 as (_&P1&P2). subst. iPureIntro. repeat split; auto. apply eval_Evar_global; auto.
      rewrite symbols_preserved; auto.
      
    - subst. iPureIntro. repeat split. rewrite typeof_Ederef'. auto. apply eval_Ederef'; auto. 
    - subst. iPureIntro. repeat split. rewrite <- comp_env_preserved in *.
      eapply eval_Efield_struct; eauto. rewrite <- H8. eauto.
    - subst. iPureIntro. repeat split; auto. rewrite <- comp_env_preserved in *. rewrite H7 in H1.
      eapply eval_Efield_union; eauto.
  Qed.
  
  Lemma tr_simple_rvalue:
    forall e m r v,
      eval_simple_rvalue ge e m r v ->
      forall le dst sl a,
        ⊢ tr_expr le dst r sl a -∗
          ⌜ match dst with
            | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
            | For_effects => sl = nil
            | For_set sd =>
              exists b, sl = do_set sd b /\ Csyntax.typeof r = typeof b /\ eval_expr tge e le m b v
            end⌝.
  Proof.
    intros e m. exact (proj1 (tr_simple e m)).
  Qed.

  Lemma tr_simple_lvalue:
    forall e m l b ofs,
      eval_simple_lvalue ge e m l b ofs ->
      forall le sl a, ⊢ tr_expr le For_val l sl a -∗                                               
                   ⌜ sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs ⌝.
  Proof.
    intros e m. exact (proj2 (tr_simple e m)).
  Qed.

  Lemma tr_simple_exprlist:
    forall le rl sl al,
      ⊢ tr_exprlist le rl sl al -∗
        ∀ e m tyl vl,
          ⌜ eval_simple_list ge e m rl tyl vl ⌝ -∗
            ⌜ sl = nil /\ eval_exprlist tge e le m al tyl vl ⌝.
  Proof.
    induction rl.
    - iIntros. inversion a. 
      iPureIntro. repeat split; eauto. inversion a0. subst. constructor.
    - simpl. iIntros. norm_all. inversion a. subst. iDestruct (IHrl with "HD []") as "[% %]"; eauto.
      iDestruct (tr_simple_rvalue with "HB") as "[% [% %]]"; eauto.
      iPureIntro. subst. split; auto. econstructor; eauto. rewrite <- H2. eauto.
  Qed.

  (** Commutation between the translation of expressions and left contexts. *)

  Lemma typeof_context:
    forall k1 k2 C, leftcontext k1 k2 C ->
               forall e1 e2, Csyntax.typeof e1 = Csyntax.typeof e2 ->
                        Csyntax.typeof (C e1) = Csyntax.typeof (C e2).
  Proof.
    induction 1; intros; auto.
  Qed.

  
  Ltac apply_ind_invariant l h :=
    match goal with
    | H : forall _ _ _ _, bi_emp_valid (tr_expr _ _ l _ _ -∗ _) |- _ =>
      iDestruct (H with h) as h
    | H : forall _ _ _, bi_emp_valid (tr_exprlist _ l _ _ -∗ _) |- _ =>
      iDestruct (H with h) as h
    | _ => fail "No rec"
    end.

  
  Lemma tr_expr_invariant :
    (forall r dst sl a le, ⊢ tr_expr le dst r sl a -∗ locally le (fun le' => tr_expr le' dst r sl a))
    /\
    (forall rl le sl al, ⊢ tr_exprlist le rl sl al -∗ locally le (fun le' => tr_exprlist le' rl sl al)).
  Proof.
    Ltac iApplyA := iDestruct ("HA" with "[]") as "HA"; eauto.
    Ltac iApplyB := iDestruct ("HB" with "[]") as "HB"; eauto.
    Ltac iApplyC := iDestruct ("HC" with "[]") as "HC"; eauto.
    Ltac iApplyD := iDestruct ("HD" with "[]") as "HD"; eauto.
    apply tr_expr_exprlist; intros; iIntros; simpl;
      try iApply locally_modout; norm_all; try iModIntro; apply_ind apply_ind_invariant.
    
    - destruct dst; norm_all. 
      + iApply locally_frame_r; auto.
        do 3 (iApply locally_forall; iIntros). iApply locally_doublon. iApply "HE".
      + iApply locally_simpl. iIntros "*". auto.
      + iApply locally_and. iSplit. iDestruct "HC" as "[HA _]". iApply locally_simpl; auto.
        iDestruct "HC" as "[_ HA]". norm_all. iApply locally_exists. iApply locally_sep_indep_r.
        iSplitL "HF"; eauto. do 3 (iApply locally_forall; iIntros). iApply locally_doublon.
        iApply "HF". iSplit; auto.
        
    - iApply locally_simpl. iIntros "*". auto.
    - iApply (locally_frame_l with "HE"). iFrame. repeat iApply locally_exists.
      iApply locally_sep_indep_r. iSplitL; auto. 
    - iApply (locally_frame_l with "HE"). repeat iApply locally_exists. iApply locally_sep_indep_r.
      iSplitL "HG"; auto.
    - iApply (locally_frame_l with "HE"). iFrame. repeat iApply locally_exists.
      iApply locally_sep_indep_r. iSplitL; auto. 
    - iApply (locally_frame_l with "HE"). repeat iApply locally_exists. iApply locally_sep_indep_r.
      iSplitL; auto. 
    - iApply (locally_frame_l with "HE"). repeat iApply locally_exists. iApply locally_sep_indep_r.
      iSplitL; auto. 
    - iApply (locally_frame_l with "HE"). iFrame. 
      repeat iApply locally_exists. iApply (locally_delete_2 with "HG HI").
      iIntros. iFrame. auto.
      
    - iApply (locally_frame_l with "HE"). repeat iApply locally_exists.
      iApply locally_sep_indep_r. iSplitL; auto.
    - destruct dst; norm_all; apply_ind apply_ind_invariant.
      + repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros.
        iFrame. subst. auto.
      + repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros. iFrame. auto.
      + repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros. iFrame. auto.
        
    - destruct dst; norm_all; apply_ind apply_ind_invariant.
      + repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros. iFrame. auto.
      + repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros. iFrame. auto.
      + repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros. iFrame. auto.

    - destruct dst; norm_all; apply_ind apply_ind_invariant.
      + repeat iApply locally_exists. iApply (locally_sep with "HE"). iApply locally_sep_indep_r.
        iSplitL; auto. iApply locally_and. iSplit. iDestruct "HG" as "[HB _]". iApply (H0 with "HB").
        iDestruct "HG" as "[_ HB]". iApply (H1 with "HB").
      + repeat iApply locally_exists. iApply (locally_delete_3 with "HE HG HI"). iIntros. iFrame.
        auto.
      + iApply (locally_frame_l with "HE"). iFrame. repeat iApply locally_exists.
        iApply (locally_sep with "HG"). iApply locally_sep_indep_r. iSplitL; auto.
        iApply locally_and. iSplit. iDestruct "HI" as "[HB _]". iApply (H0 with "HB").
        iDestruct "HI" as "[_ HB]". iApply (H1 with "HB").

    - iApply locally_simpl. auto.
    - iApply locally_simpl. auto.
    - destruct dst; norm_all; apply_ind apply_ind_invariant.
      + repeat iApply locally_exists. iApply (locally_sep with "HE"). 
        iApply (locally_sep with "HG"). iApply locally_simpl. iFrame. auto.
      + repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros. iFrame. auto.
      + repeat iApply locally_exists. iApply (locally_sep with "HE"). iApply (locally_sep with "HG").
        iApply locally_simpl. iIntros. iSplitL "HI"; auto.
        
    - destruct dst; norm_all; apply_ind apply_ind_invariant.
      + iApply (locally_frame_l with "HE"). repeat iApply locally_exists.
        iApply (locally_delete_2 with "HG HI"). iIntros. iFrame. auto.
      + repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros. iFrame. auto.
      + iApply (locally_frame_l with "HE"). iFrame. repeat iApply locally_exists.
        iApply (locally_delete_2 with "HI HG"). iIntros "* $ $". iSplitL "HK"; auto.
        
    - destruct dst; norm_all; apply_ind apply_ind_invariant.
      + repeat iApply locally_exists. iApply (locally_sep with "HE").
        iApply (locally_frame_l with "HH"). repeat iApply locally_exists. iApply locally_simpl. auto.
      + repeat iApply locally_exists. iApply (locally_sep with "HE"). repeat iApply locally_exists.
        iApply locally_simpl. auto.
      + repeat iApply locally_exists. iApply (locally_sep with "HE").
        iApply (locally_frame_l with "HH"). iApply locally_exists. iApply locally_simpl.
        iIntros "** //". iSplitL; auto.

    - repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros "* $ $ //".

    - destruct dst; norm_all; apply_ind apply_ind_invariant.
      + iApply (locally_frame_l with "HE"). repeat iApply locally_exists.
        iApply (locally_delete_2 with "HI HK"). iIntros "* $ $ //". iSplitL; auto.
      + repeat iApply locally_exists. iApply (locally_delete_2 with "HE HG"). iIntros "* $ $ //".
      + iApply (locally_frame_l with "HE"). repeat iApply locally_exists. 
        iApply (locally_delete_2 with "HI HK"). iIntros "* $ $ //". iSplitL; auto.
        
    - destruct dst; norm_all; apply_ind apply_ind_invariant.
      + iApply (locally_frame_l with "HE"). repeat iApply locally_exists.
        iApply (locally_sep with "HG"). iApply locally_simpl. auto.
      + repeat iApply locally_exists. iApply (locally_sep with "HE"). iApply locally_simpl. auto.
      + iApply (locally_frame_l with "HE"). iFrame. repeat iApply locally_exists.
        iApply (locally_sep with "HG"). iApply locally_simpl. iIntros. iSplitL "HI"; auto.
        
    - iApply locally_simpl. auto.
    - destruct dst; norm_all; apply_ind apply_ind_invariant.
      + repeat iApply locally_exists. iApply (locally_sep with "HE"). iApply locally_simpl. auto.
      + iApply locally_exists. iFrame. 
      + repeat iApply locally_exists. instantiate (2 := x0).
        destruct (Pos.eq_dec x0 (sd_temp sd)); norm_all; apply_ind apply_ind_invariant.
        * iFrame.
        * iApply locally_sep_indep_r. iFrame. 
    - iApply locally_simpl. auto.
    - repeat iApply locally_exists. iApply (locally_delete_2 with "HB HD"). iIntros "* $ $ //".
  Qed.
    
      
Scheme leftcontext_ind2 := Minimality for leftcontext Sort Prop
  with leftcontextlist_ind2 := Minimality for leftcontextlist Sort Prop.
Combined Scheme leftcontext_leftcontextlist_ind from leftcontext_ind2, leftcontextlist_ind2.


Lemma tr_expr_leftcontext_rec:
  (forall from to C, leftcontext from to C ->
  forall le e dst sl a,
  ⊢ tr_expr le dst (C e) sl a -∗
  ∃ dst' sl1 sl2 a',
    tr_expr le dst' e sl1 a'
    ∗ ⌜ sl = sl1 ++ sl2 ⌝
    ∗ (∀ e',
    \⌜ Csyntax.typeof e' = Csyntax.typeof e ⌝ -∗
    (∀ sl3,
        locally le (fun le' => tr_expr le' dst' e' sl3 a'
                              -∗ tr_expr le' dst (C e') (sl3 ++ sl2) a))))
    /\ (
    forall from C, leftcontextlist from C ->
    forall le e sl a,
    ⊢ tr_exprlist le (C e) sl a -∗
    ∃ dst' sl1 sl2 a',
      tr_expr le dst' e sl1 a'
    ∗ ⌜sl = sl1 ++ sl2⌝
    ∗ (∀ e',
    \⌜ Csyntax.typeof e' = Csyntax.typeof e ⌝ -∗
    (∀ sl3,
        locally le (fun le' => tr_expr le' dst' e' sl3 a' -∗ tr_exprlist le' (C e') (sl3 ++ sl2) a)))
    ).
Proof.
  
  Ltac init H0 e' H :=
    iDestruct (H0 with H) as (dst' sl1 sl0 a') "[HA [% HHHHH]]"; subst;
    repeat iExists _; iSplitL "HA"; eauto; iSplit;
    [iPureIntro; simpl; try rewrite <- app_assoc; auto |
     iIntros "* % *"; iDestruct ("HHHHH" $! e' with "[]") as "HHHHH"; auto;
     iApply (locally_conseq with "HHHHH")].
    
  Ltac finish_him := iIntros "**"; try iModIntro; iFrame; repeat iExists _; iFrame;
                     try rewrite <- app_assoc; auto.
    
    apply leftcontext_leftcontextlist_ind; intros; simpl; iIntros; norm_all.

    (*base*)
    - repeat iExists _. iSplitL; eauto. iSplit. iPureIntro; apply app_nil_end.
      iIntros "* % *". iApply locally_simpl. rewrite <- app_nil_end. eauto.
      
    (* deref *)
    - init H0 e' "HF". iApply locally_simpl. finish_him.
      
    (* field *)
    - init H0 e' "HF". iApply locally_simpl. finish_him.

    (* rvalof *)
    - init H0 e' "HF". rewrite (typeof_context _ _ _ H _ _ a0). iApply locally_simpl. finish_him. 

    (* addrof *)
    - init H0 e' "HF". iApply locally_simpl. finish_him.
      
    - init H0 e' "HF". iApply locally_simpl. finish_him.
      
    (* binop left *)
    - iDestruct (proj1 tr_expr_invariant with "HH") as "HC".
      init H0 e' "HF". iApply (locally_apply with "HC"). finish_him.
      
    (* binop right *)
    - iAssert (⌜x = nil⌝) as "%". iApply (tr_simple_expr_nil with "HF"); eauto. 
      iDestruct (proj1 tr_expr_invariant with "HF") as "HC".
      init H1 e' "HH". iApply (locally_apply with "HC"). finish_him.
      
    (* cast *)
    - init H0 e' "HF". iApply locally_simpl. finish_him.
      
    (* seqand *)
    - destruct dst; norm_all; iDestruct (proj1 tr_expr_invariant with "HF") as "HB"; init H0 e' "HD";
        iApply (locally_apply with "HB"); finish_him.
      
    (* seqor *)
    - destruct dst; norm_all; iDestruct (proj1 tr_expr_invariant with "HF") as "HF"; init H0 e' "HD";
        iApply (locally_apply with "HF"); finish_him.
      
    (* condition *)
    - destruct dst; norm_all.
      + iDestruct (locally_and with "[HF]") as "HB". iSplit.
        iDestruct "HF" as "[HB _]". iApply (proj1 tr_expr_invariant with "HB").
        iDestruct "HF" as "[_ HB]". iApply (proj1 tr_expr_invariant with "HB").
        init H0 e' "HD". iApply (locally_apply with "HB"). finish_him.
      + iDestruct (proj1 tr_expr_invariant with "HF") as "HF".
        iDestruct (proj1 tr_expr_invariant with "HH") as "HH".
        init H0 e' "HD".  iApply (locally_delete_2 with "HH HF"). finish_him.
      + iDestruct (locally_and with "[HH]") as "HH". iSplit.
        iDestruct "HH" as "[HB _]". iApply (proj1 tr_expr_invariant with "HB").
        iDestruct "HH" as "[_ HB]". iApply (proj1 tr_expr_invariant with "HB").
        init H0 e' "HF". iApply (locally_apply with "HH"). finish_him.
        
    - destruct dst; norm_all.
      + iDestruct (proj1 tr_expr_invariant with "HF") as "HF".
        init H0 e' "HD". iApply (locally_apply with "HF"). rewrite (typeof_context _ _ _ H _ _ a). 
        finish_him.
      + iDestruct (proj1 tr_expr_invariant with "HF") as "HF". init H0 e' "HD".
        iApply (locally_apply with "HF"). finish_him.
      + iDestruct (proj1 tr_expr_invariant with "HF") as "HF". init H0 e' "HD".
        iApply (locally_apply with "HF"). rewrite (typeof_context _ _ _ H _ _ a). finish_him.
        
    - destruct dst; norm_all; iDestruct (tr_simple_expr_nil with "HD [] []") as "%"; auto;
        iDestruct (proj1 tr_expr_invariant with "HD") as "HD"; init H1 e' "HF";
         iApply (locally_apply with "HD"); finish_him.
              
    - destruct dst; norm_all.
      + iDestruct (proj1 tr_expr_invariant with "HH") as "HH". init H0 e' "HF".
        rewrite (typeof_context _ _ _ H e' e _). iApply (locally_apply with "HH"); finish_him. auto.
      + iDestruct (proj1 tr_expr_invariant with "HF") as "HF". init H0 e' "HD".
        rewrite (typeof_context _ _ _ H e' e _). iApply (locally_apply with "HF"); finish_him. auto.
      + iDestruct (proj1 tr_expr_invariant with "HH") as "HH". init H0 e' "HF".
        rewrite (typeof_context _ _ _ H e' e _). iApply (locally_apply with "HH"); finish_him. auto.
         
    - destruct dst; norm_all.
      + iDestruct (tr_simple_expr_nil with "HF [] []") as "%"; auto.
        iDestruct (proj1 tr_expr_invariant with "HF") as "HF". init H1 e' "HH".
        iApply (locally_apply with "HF"); finish_him.
      + iDestruct (tr_simple_expr_nil with "HD [] []") as "%"; auto.
        iDestruct (proj1 tr_expr_invariant with "HD") as "HD". init H1 e' "HF".
        iApply (locally_apply with "HD"); finish_him.
      + iDestruct (tr_simple_expr_nil with "HF [] []") as "%"; auto.
        iDestruct (proj1 tr_expr_invariant with "HF") as "HF". init H1 e' "HH".
        iApply (locally_apply with "HF"); finish_him.
      
    - destruct dst; norm_all; init H0 e' "HD"; iApply locally_simpl;
        rewrite (typeof_context _ _ _ H e e' _); auto; iIntros "* HA !>"; repeat iExists _; iFrame;
          repeat iExists _; iSplitL; auto; rewrite app_ass; auto.
      
    - destruct dst; norm_all.
      + iDestruct (proj2 tr_expr_invariant with "HJ") as "HJ". init H0 e' "HH".
        iApply (locally_apply with "HJ"). finish_him.
      + iDestruct (proj2 tr_expr_invariant with "HF") as "HF". init H0 e' "HD".
        iApply (locally_apply with "HF"). finish_him.
      + iDestruct (proj2 tr_expr_invariant with "HJ") as "HJ". init H0 e' "HH".
        iApply (locally_apply with "HJ"). finish_him. 

    - destruct dst; norm_all.
      + iDestruct (tr_simple_expr_nil with "HH [] []") as "%"; auto.
        iDestruct (proj1 tr_expr_invariant with "HH") as "HH". init H1 e' "HJ". 
        iApply (locally_apply with "HH"). finish_him.
      + iDestruct (tr_simple_expr_nil with "HD [] []") as "%"; auto.
        iDestruct (proj1 tr_expr_invariant with "HD") as "HD". init H1 e' "HF".
        iApply (locally_apply with "HD"). finish_him.
      + iDestruct (tr_simple_expr_nil with "HH [] []") as "%"; auto.
        iDestruct (proj1 tr_expr_invariant with "HH") as "HH". init H1 e' "HJ". 
        iApply (locally_apply with "HH"). finish_him.
        
    - destruct dst; norm_all.
      + init H0 e' "HF"; iApply locally_simpl; finish_him.
      + init H0 e' "HD"; iApply locally_simpl; finish_him.
      + init H0 e' "HF"; iApply locally_simpl; finish_him.
        
    - iDestruct (proj1 tr_expr_invariant with "HF") as "HF". init H0 e' "HD".
      iApply (locally_apply with "HF"). finish_him.
              
    - destruct dst; norm_all.
      + init H0 e' "HD". iApply locally_simpl. finish_him. 
      + init H0 e' "HB". iApply locally_simpl. finish_him. 
      + destruct (Pos.eq_dec x0 (sd_temp sd)) eqn:?; norm_all.
        * init H0 e' "HB". iApply locally_simpl. finish_him.
          instantiate (2 := (sd_temp sd)). rewrite Heqs. iFrame.
        * init H0 e' "HD". iApply locally_simpl. finish_him.
          instantiate (2 := x0). rewrite Heqs. iFrame.
    - iDestruct (proj2 tr_expr_invariant with "HD") as "HD". init H0 e' "HB".
      iApply (locally_apply with "HD"). finish_him.
    - iDestruct (tr_simple_expr_nil with "HB [] []") as "%"; auto.
      iDestruct (proj1 tr_expr_invariant with "HB") as "HB". init H1 e' "HD".
      iApply (locally_apply with "HB"). finish_him.
  Qed.

Theorem tr_expr_leftcontext:
  (forall from to C, leftcontext from to C ->
  (forall from to C, leftcontext from to C ->
  forall le e dst sl a,
  ⊢ tr_expr le dst (C e) sl a -∗
  ∃ dst' sl1 sl2 a',
    tr_expr le dst' e sl1 a'
    ∗ ⌜ sl = sl1 ++ sl2 ⌝
    ∗ (∀ e',
    \⌜ Csyntax.typeof e' = Csyntax.typeof e ⌝ -∗
    (∀ sl3,
        locally le (fun le' => tr_expr le' dst' e' sl3 a'
                              -∗ tr_expr le' dst (C e') (sl3 ++ sl2) a))))).
Proof.
  intros. eapply (proj1 tr_expr_leftcontext_rec); eauto.
Qed.

(** Semantics of smart constructors *)

Remark sem_cast_deterministic:
  forall v ty ty' m1 v1 m2 v2,
  sem_cast v ty ty' m1 = Some v1 ->
  sem_cast v ty ty' m2 = Some v2 ->
  v1 = v2.
Proof.
  unfold sem_cast; intros. destruct (classify_cast ty ty'); try congruence.
- destruct v; try congruence.
  destruct Archi.ptr64; try discriminate.
  destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)); inv H.
  destruct (Mem.weak_valid_pointer m2 b (Ptrofs.unsigned i)); inv H0.
  auto.
- destruct v; try congruence. 
  destruct (negb Archi.ptr64); try discriminate.
  destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)); inv H.
  destruct (Mem.weak_valid_pointer m2 b (Ptrofs.unsigned i)); inv H0.
  auto.
  destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)); inv H.
  destruct (Mem.weak_valid_pointer m2 b (Ptrofs.unsigned i)); inv H0.
  auto.
Qed.

Lemma eval_simpl_expr_sound:
  forall e le m a v, eval_expr tge e le m a v ->
  match eval_simpl_expr a with Some v' => v' = v | None => True end.
Proof.
  induction 1; simpl; auto.
  destruct (eval_simpl_expr a); auto. subst.
  destruct (sem_cast v1 (typeof a) ty Mem.empty) as [v'|] eqn:C; auto.
  eapply sem_cast_deterministic; eauto.
  inv H; simpl; auto.
Qed.

Lemma static_bool_val_sound:
  forall v t m b, bool_val v t Mem.empty = Some b -> bool_val v t m = Some b.
Proof.
  assert (A: forall b ofs, Mem.weak_valid_pointer Mem.empty b ofs = false).
  { unfold Mem.weak_valid_pointer, Mem.valid_pointer, proj_sumbool; intros.
    rewrite ! pred_dec_false; auto; apply Mem.perm_empty. }  
  intros until b; unfold bool_val.
  destruct (classify_bool t0); destruct v; destruct Archi.ptr64 eqn:SF; auto.
- rewrite A; congruence.
- simpl; rewrite A; congruence.
Qed.

Lemma step_makeif:
  forall f a s1 s2 k e le m v1 b,
  eval_expr tge e le m a v1 ->
  bool_val v1 (typeof a) m = Some b ->
  star step1 tge (State f (makeif a s1 s2) k e le m)
             E0 (State f (if b then s1 else s2) k e le m).
Proof.
  intros. functional induction (makeif a s1 s2).
- exploit eval_simpl_expr_sound; eauto. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (typeof a) m = Some true) by (apply static_bool_val_sound; auto).
  replace b with true by congruence. constructor.
- exploit eval_simpl_expr_sound; eauto. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (typeof a) m = Some false) by (apply static_bool_val_sound; auto).
  replace b with false by congruence. constructor.
- apply star_one. eapply step_ifthenelse; eauto.
- apply star_one. eapply step_ifthenelse; eauto.
Qed.

Lemma step_make_set:
  forall id a ty m b ofs t v e le f k,
  Csem.deref_loc ge ty m b ofs t v ->
  eval_lvalue tge e le m a b ofs ->
  typeof a = ty ->
  step1 tge (State f (make_set id a) k e le m)
          t (State f Sskip k e (Maps.PTree.set id v le) m).
Proof.
  intros. exploit deref_loc_translated; eauto. rewrite <- H1.
  unfold make_set. destruct (chunk_for_volatile_type (typeof a)) as [chunk|].
(* volatile case *)
  intros. change (Maps.PTree.set id v le) with (set_opttemp (Some id) v le). econstructor.
  econstructor. constructor. eauto.
  simpl. unfold sem_cast. simpl. eauto. constructor.
  simpl. econstructor; eauto.
(* nonvolatile case *)
  intros [A B]. subst t0. constructor. eapply eval_Elvalue; eauto.
Qed.

Lemma step_make_assign:
  forall a1 a2 ty m b ofs t v m' v2 e le f k,
  Csem.assign_loc ge ty m b ofs v t m' ->
  eval_lvalue tge e le m a1 b ofs ->
  eval_expr tge e le m a2 v2 ->
  sem_cast v2 (typeof a2) ty m = Some v ->
  typeof a1 = ty ->
  step1 tge (State f (make_assign a1 a2) k e le m)
          t (State f Sskip k e le m').
Proof.
  intros. exploit assign_loc_translated; eauto. rewrite <- H3.
  unfold make_assign. destruct (chunk_for_volatile_type (typeof a1)) as [chunk|].
(* volatile case *)
  intros. change le with (set_opttemp None Vundef le) at 2. econstructor.
  econstructor. constructor. eauto.
  simpl. unfold sem_cast. simpl. eauto.
  econstructor; eauto. rewrite H3; eauto. constructor.
  simpl. econstructor; eauto.
(* nonvolatile case *)
  intros [A B]. subst t0. econstructor; eauto. congruence.
Qed.

Fixpoint Kseqlist (sl: list statement) (k: cont) :=
  match sl with
  | nil => k
  | s :: l => Kseq s (Kseqlist l k)
  end.

Remark Kseqlist_app:
  forall sl1 sl2 k,
  Kseqlist (sl1 ++ sl2) k = Kseqlist sl1 (Kseqlist sl2 k).
Proof.
  induction sl1; simpl; congruence.
Qed.

Lemma push_seq:
  forall f sl k e le m,
  star step1 tge (State f (makeseq sl) k e le m)
              E0 (State f Sskip (Kseqlist sl k) e le m).
Proof.
  intros. unfold makeseq. generalize Sskip. revert sl k.
  induction sl; simpl; intros.
  apply star_refl.
  eapply star_right. apply IHsl. constructor. traceEq.
Qed.

Lemma step_tr_rvalof:
  forall ty m b ofs t v e le a sl a' f k,
  Csem.deref_loc ge ty m b ofs t v ->
  eval_lvalue tge e le m a b ofs ->
  typeof a = ty ->
  ⊢ tr_rvalof ty a sl a' -∗
  ∃ le',
    ⌜star step1 tge (State f Sskip (Kseqlist sl k) e le m)
                 t (State f Sskip k e le' m)
  /\ eval_expr tge e le' m a' v
  /\ typeof a' = typeof a ⌝.
Proof.
  iIntros "* % % % HA". unfold tr_rvalof.
  destruct (type_is_volatile ty) eqn:?; norm_all.
  - subst. iExists (Maps.PTree.set _ v le). iSplitR.
    + iPureIntro. simpl. eapply star_two. econstructor. eapply step_make_set; eauto. traceEq.
    + iPureIntro. split. constructor. apply Maps.PTree.gss. reflexivity.
  - subst. exploit deref_loc_translated; eauto. intro.
    unfold chunk_for_volatile_type in H1. rewrite Heqb0 in H1. destruct H1. subst.
    iExists le. iSplit; eauto.
    iPureIntro. apply star_refl. iPureIntro. split. eapply eval_Elvalue; eauto.
    reflexivity.
Qed.

    
(** Matching between continuations *)

Inductive match_cont : Csem.cont -> cont -> Prop :=
  | match_Kstop:
      match_cont Csem.Kstop Kstop
  | match_Kseq: forall s k ts tk,
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kseq s k) (Kseq ts tk)
  | match_Kwhile2: forall r s k s' ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kwhile2 r s k)
                 (Kloop1 (Ssequence s' ts) Sskip tk)
  | match_Kdowhile1: forall r s k s' ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kdowhile1 r s k)
                 (Kloop1 ts s' tk)
  | match_Kfor3: forall r s3 s k ts3 s' ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s3 ts3 ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kfor3 r s3 s k)
                 (Kloop1 (Ssequence s' ts) ts3 tk)
  | match_Kfor4: forall r s3 s k ts3 s' ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s3 ts3 ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kfor4 r s3 s k)
                 (Kloop2 (Ssequence s' ts) ts3 tk)
  | match_Kswitch2: forall k tk,
      match_cont k tk ->
      match_cont (Csem.Kswitch2 k) (Kswitch tk)
  | match_Kcall: forall f e C ty k optid tf le sl tk a dest tmps,
      tr_function f tf ->
      leftcontext RV RV C ->
      (forall v m, tr_top tge e (set_opttemp optid v le) m dest (C (Csyntax.Eval v ty)) sl a tmps) ->
      match_cont_exp dest a k tk ->
      match_cont (Csem.Kcall f e C ty k)
                 (Kcall optid tf e le (Kseqlist sl tk))
(* *)
(*   | match_Kcall_some: forall f e C ty k dst tf le sl tk a dest tmps, *)
(*       transl_function f = Errors.OK tf -> *)
(*       leftcontext RV RV C -> *)
(*       (forall v m, tr_top tge e (PTree.set dst v le) m dest (C (C.Eval v ty)) sl a tmps) -> *)
(*       match_cont_exp dest a k tk -> *)
(*       match_cont (Csem.Kcall f e C ty k) *)
(*                  (Kcall (Some dst) tf e le (Kseqlist sl tk)) *)
(* *)

with match_cont_exp : destination -> expr -> Csem.cont -> cont -> Prop :=
  | match_Kdo: forall k a tk,
      match_cont k tk ->
      match_cont_exp For_effects a (Csem.Kdo k) tk
  | match_Kifthenelse_empty: forall a k tk,
      match_cont k tk ->
      match_cont_exp For_val a (Csem.Kifthenelse Csyntax.Sskip Csyntax.Sskip k) (Kseq Sskip tk)
  | match_Kifthenelse_1: forall a s1 s2 k ts1 ts2 tk,
      tr_stmt s1 ts1 ->
      tr_stmt s2 ts2 ->
      match_cont k tk ->
      match_cont_exp For_val a (Csem.Kifthenelse s1 s2 k) (Kseq (Sifthenelse a ts1 ts2) tk)
  | match_Kwhile1: forall r s k s' a ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont_exp For_val a
         (Csem.Kwhile1 r s k)
         (Kseq (makeif a Sskip Sbreak)
           (Kseq ts (Kloop1 (Ssequence s' ts) Sskip tk)))
  | match_Kdowhile2: forall r s k s' a ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont_exp For_val a
        (Csem.Kdowhile2 r s k)
        (Kseq (makeif a Sskip Sbreak) (Kloop2 ts s' tk))
  | match_Kfor2: forall r s3 s k s' a ts3 ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s3 ts3 ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont_exp For_val a
        (Csem.Kfor2 r s3 s k)
        (Kseq (makeif a Sskip Sbreak)
          (Kseq ts (Kloop1 (Ssequence s' ts) ts3 tk)))
  | match_Kswitch1: forall ls k a tls tk,
      tr_lblstmts ls tls ->
      match_cont k tk ->
      match_cont_exp For_val a (Csem.Kswitch1 ls k) (Kseq (Sswitch a tls) tk)
  | match_Kreturn: forall k a tk,
      match_cont k tk ->
      match_cont_exp For_val a (Csem.Kreturn k) (Kseq (Sreturn (Some a)) tk).

Lemma match_cont_call:
  forall k tk,
  match_cont k tk ->
  match_cont (Csem.call_cont k) (call_cont tk).
Proof.
  induction 1; simpl; auto. constructor. econstructor; auto.
Qed.


(** Matching between states *)

Inductive match_states: Csem.state -> Clight.state -> Prop :=
  | match_exprstates: forall f r k e m tf sl tk le dest a tmps,
      tr_function f tf ->
      tr_top tge e le m dest r sl a tmps ->
      match_cont_exp dest a k tk ->
      match_states (Csem.ExprState f r k e m)
                   (State tf Sskip (Kseqlist sl tk) e le m)
  | match_regularstates: forall f s k e m tf ts tk le,
      tr_function f tf ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_states (Csem.State f s k e m)
                   (State tf ts tk e le m)
  | match_callstates: forall fd args k m tfd tk,
      tr_fundef fd tfd ->
      match_cont k tk ->
      match_states (Csem.Callstate fd args k m)
                   (Callstate tfd args tk m)
  | match_returnstates: forall res k m tk,
      match_cont k tk ->
      match_states (Csem.Returnstate res k m)
                   (Returnstate res tk m)
  | match_stuckstate: forall S,
      match_states Csem.Stuckstate S.

(** Additional results on translation of statements *)

Lemma tr_select_switch:
  forall n ls tls,
  tr_lblstmts ls tls ->
  tr_lblstmts (Csem.select_switch n ls) (select_switch n tls).
Proof.
 assert (DFL: forall ls tls,
      tr_lblstmts ls tls ->
      tr_lblstmts (Csem.select_switch_default ls) (select_switch_default tls)).
  { induction 1; simpl. constructor. destruct c; auto. constructor; auto. }
  assert (CASE: forall n ls tls,
      tr_lblstmts ls tls ->
      match Csem.select_switch_case n ls with
      | None =>
          select_switch_case n tls = None
      | Some ls' =>
          exists tls', select_switch_case n tls = Some tls' /\ tr_lblstmts ls' tls'
      end).
  { induction 1; simpl; intros.
    auto.
    destruct c; auto. destruct (zeq z n); auto.
    econstructor; split; eauto. constructor; auto. }
  intros. unfold Csem.select_switch, select_switch.
  specialize (CASE n ls tls H).
  destruct (Csem.select_switch_case n ls) as [ls'|].
  destruct CASE as [tls' [P Q]]. rewrite P. auto.
  rewrite CASE. apply DFL; auto.
Qed.


Lemma tr_seq_of_labeled_statement:
  forall ls tls,
  tr_lblstmts ls tls ->
  tr_stmt (Csem.seq_of_labeled_statement ls) (seq_of_labeled_statement tls).
Proof.
  induction 1; simpl; constructor; auto.
Qed.

(** Commutation between translation and the "find label" operation. *)

Section FIND_LABEL.

Variable lbl: label.

Definition nolabel (s: statement) : Prop :=
  forall k, find_label lbl s k = None.

Fixpoint nolabel_list (sl: list statement) : Prop :=
  match sl with
  | nil => True
  | s1 :: sl' => nolabel s1 /\ nolabel_list sl'
  end.

Lemma nolabel_list_app:
  forall sl2 sl1, nolabel_list sl1 -> nolabel_list sl2 -> nolabel_list (sl1 ++ sl2).
Proof.
  induction sl1; simpl; intros. auto. tauto.
Qed.

Lemma makeseq_nolabel:
  forall sl, nolabel_list sl -> nolabel (makeseq sl).
Proof.
  assert (forall sl s, nolabel s -> nolabel_list sl -> nolabel (makeseq_rec s sl)).
  induction sl; simpl; intros. auto. destruct H0. apply IHsl; auto.
  red. intros; simpl. rewrite H. apply H0.
  intros. unfold makeseq. apply H; auto. red. auto.
Qed.

Lemma makeif_nolabel:
  forall a s1 s2, nolabel s1 -> nolabel s2 -> nolabel (makeif a s1 s2).
Proof.
  intros. functional induction (makeif a s1 s2); auto.
  red; simpl; intros. rewrite H; auto.
  red; simpl; intros. rewrite H; auto.
Qed.

Lemma make_set_nolabel:
  forall t a, nolabel (make_set t a).
Proof.
  unfold make_set; intros; red; intros.
  destruct (chunk_for_volatile_type (typeof a)); auto.
Qed.

Lemma make_assign_nolabel:
  forall l r, nolabel (make_assign l r).
Proof.
  unfold make_assign; intros; red; intros.
  destruct (chunk_for_volatile_type (typeof l)); auto.
Qed.

Lemma tr_rvalof_nolabel:
  forall ty a sl a', ⊢ tr_rvalof ty a sl a' -∗ ⌜ nolabel_list sl ⌝.
Proof.
  iIntros. unfold tr_rvalof.
  destruct (type_is_volatile ty) eqn:?; norm_all; subst; iPureIntro; repeat constructor.
  apply make_set_nolabel. 
Qed.

Lemma nolabel_do_set:
  forall sd a, nolabel_list (do_set sd a).
Proof.
  induction sd; intros; simpl; split; auto; red; auto.
Qed.

Lemma nolabel_final:
  forall dst a, nolabel_list (final dst a).
Proof.
  destruct dst; simpl; intros. auto. auto. apply nolabel_do_set.
Qed.

Ltac NoLabelTac :=
  match goal with
  | [ |- nolabel_list nil ] => exact I
  | [ |- nolabel_list (final _ _) ] => apply nolabel_final (*; NoLabelTac*)
  | [ |- nolabel_list (_ :: _) ] => simpl; split; NoLabelTac
  | [ |- nolabel_list (_ ++ _) ] => apply nolabel_list_app; NoLabelTac
  | [ H: _ -> nolabel_list ?x |- nolabel_list ?x ] => apply H; NoLabelTac
  | [ |- nolabel (makeseq _) ] => apply makeseq_nolabel; NoLabelTac
  | [ |- nolabel (makeif _ _ _) ] => apply makeif_nolabel; NoLabelTac
  | [ |- nolabel (make_set _ _) ] => apply make_set_nolabel
  | [ |- nolabel (make_assign _ _) ] => apply make_assign_nolabel
  | [ |- nolabel_list (do_set _ _) ] => apply nolabel_do_set
  | [ |- nolabel _ ] => intro; simpl; auto
  | [ |- _ /\ _ ] => split; NoLabelTac
  | _ => auto
  end.

Ltac apply_ind_label l h :=
  match type of l with
  | Csyntax.expr =>
    match goal with
    | H : forall _ _ _ _, bi_emp_valid (tr_expr _ _ l _ _ -∗ _) |- _ => iDestruct (H with h) as "%"
    end
  | exprlist =>
    match goal with
    | H : forall _ _ _, bi_emp_valid (tr_exprlist _ l _ _ -∗ _) |- _ => iDestruct (H with h) as "%"
    end
  | expr => iDestruct (tr_rvalof_nolabel with h) as "%"
  end.


Lemma tr_find_label_expr:
  (forall r le dst sl a, ⊢ tr_expr le dst r sl a -∗ ⌜ nolabel_list sl ⌝)
/\(forall rl le sl al, ⊢ tr_exprlist le rl sl al -∗ ⌜ nolabel_list sl ⌝).
Proof.
  apply tr_expr_exprlist; intros; simpl; iIntros; norm_all; apply_ind apply_ind_label; subst;
    try(iPureIntro; NoLabelTac; fail).
  - destruct dst; norm_all; subst; NoLabelTac. iDestruct "HB" as "[_ HA]". norm_all.
    subst; iPureIntro; NoLabelTac.
  - destruct dst; norm_all; apply_ind apply_ind_label; subst; iPureIntro; NoLabelTac.
  - destruct dst; norm_all; apply_ind apply_ind_label; subst; iPureIntro; NoLabelTac.
  - destruct dst; norm_all; apply_ind apply_ind_label; subst.
    + iDestruct (H0 with "[HF]") as "%". iDestruct "HF" as "[HD _]"; auto.
      iDestruct (H1 with "[HF]") as "%". iDestruct "HF" as "[_ HD]"; auto.
      subst. iPureIntro. NoLabelTac.
    + subst. iPureIntro. NoLabelTac.
    + iDestruct (H0 with "[HH]") as "%". iDestruct "HH" as "[HC _]"; auto.
      iDestruct (H1 with "[HH]") as "%". iDestruct "HH" as "[_ HC]"; auto.
      subst. iPureIntro. NoLabelTac.
  - destruct dst; norm_all; apply_ind apply_ind_label; subst; iPureIntro; NoLabelTac.
  - destruct dst; norm_all; apply_ind apply_ind_label; subst; iPureIntro; NoLabelTac.  
  - destruct dst; norm_all; apply_ind apply_ind_label; subst; iPureIntro; NoLabelTac.
  - destruct dst; norm_all; apply_ind apply_ind_label; subst; iPureIntro; NoLabelTac.      
  - destruct dst; norm_all; apply_ind apply_ind_label; subst; iPureIntro; NoLabelTac.
  - destruct dst; norm_all; apply_ind apply_ind_label; auto.
    destruct (Pos.eq_dec x0 (sd_temp sd)); norm_all; apply_ind apply_ind_label; auto.
  - destruct a. subst. NoLabelTac.
Qed.
                                        
Lemma tr_find_label_top:
  forall e le m dst r sl a tmp,
    tr_top tge e le m dst r sl a tmp -> nolabel_list sl.
Proof.
  intros. inv H; NoLabelTac.
  apply (soundness1 tmp). iIntros "HA". apply soundness3 in H0.
  iDestruct (H0 with "HA") as "HA". iDestruct (proj1 tr_find_label_expr with "HA") as "$"; auto.
Qed.
                                                                                                  
Lemma tr_find_label_expression:
  forall r s a, tr_expression r s a -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H. 
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  eapply (tr_find_label_top empty_env (Maps.PTree.empty val) Mem.empty); eauto.
  apply H.
Qed.

Lemma tr_find_label_expr_stmt:
  forall r s, tr_expr_stmt r s -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  eapply (tr_find_label_top empty_env (Maps.PTree.empty val) Mem.empty); eauto.
  apply H. 
Qed.

Lemma tr_find_label_if:
  forall r s, tr_if r Sskip Sbreak s -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq (sl ++ makeif a Sskip Sbreak :: nil))).
  apply makeseq_nolabel.
  apply nolabel_list_app.
  eapply (tr_find_label_top empty_env (Maps.PTree.empty val) Mem.empty); eauto.
  NoLabelTac. apply H.
Qed.

Lemma tr_find_label:
  forall s k ts tk
    (TR: tr_stmt s ts)
    (MC: match_cont k tk),
  match Csem.find_label lbl s k with
  | None =>
      find_label lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk',
          find_label lbl ts tk = Some (ts', tk')
       /\ tr_stmt s' ts'
       /\ match_cont k' tk'
  end
with tr_find_label_ls:
  forall s k ts tk
    (TR: tr_lblstmts s ts)
    (MC: match_cont k tk),
  match Csem.find_label_ls lbl s k with
  | None =>
      find_label_ls lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk',
          find_label_ls lbl ts tk = Some (ts', tk')
       /\ tr_stmt s' ts'
       /\ match_cont k' tk'
  end.
Proof.
  induction s; intros; inversion TR; subst; clear TR; simpl.
  auto.
  eapply tr_find_label_expr_stmt; eauto.
(* seq *)
  exploit (IHs1 (Csem.Kseq s2 k)); eauto. constructor; eauto.
  destruct (Csem.find_label lbl s1 (Csem.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; auto.
  intro EQ. rewrite EQ. eapply IHs2; eauto.
(* if empty *)
  rename s' into sr.
  rewrite (tr_find_label_expression _ _ _ H3).
  auto.
(* if not empty *)
  rename s' into sr.
  rewrite (tr_find_label_expression _ _ _ H2).
  exploit (IHs1 k); eauto.
  destruct (Csem.find_label lbl s1 k) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ. eapply IHs2; eauto.
(* while *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H1); auto.
  exploit (IHs (Kwhile2 e s k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s (Kwhile2 e s k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ. auto.
(* dowhile *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H1); auto.
  exploit (IHs (Kdowhile1 e s k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s (Kdowhile1 e s k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ. auto.
(* for skip *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H4); auto.
  exploit (IHs3 (Csem.Kfor3 e s2 s3 k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s3 (Csem.Kfor3 e s2 s3 k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ.
  exploit (IHs2 (Csem.Kfor4 e s2 s3 k)); eauto. econstructor; eauto.
(* for not skip *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H3); auto.
  exploit (IHs1 (Csem.Kseq (Csyntax.Sfor Csyntax.Sskip e s2 s3) k)); eauto.
    econstructor; eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s1
               (Csem.Kseq (Csyntax.Sfor Csyntax.Sskip e s2 s3) k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ; rewrite EQ.
  exploit (IHs3 (Csem.Kfor3 e s2 s3 k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s3 (Csem.Kfor3 e s2 s3 k)) as [[s'' k''] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ'. rewrite EQ'.
  exploit (IHs2 (Csem.Kfor4 e s2 s3 k)); eauto. econstructor; eauto.
(* break, continue, return 0 *)
  auto. auto. auto.
(* return 1 *)
  rewrite (tr_find_label_expression _ _ _ H0). auto.
(* switch *)
  rewrite (tr_find_label_expression _ _ _ H1). apply tr_find_label_ls. auto. constructor; auto.
(* labeled stmt *)
  destruct (ident_eq lbl l). exists ts0; exists tk; auto. apply IHs; auto.
(* goto *)
  auto.

  induction s; intros; inversion TR; subst; clear TR; simpl.
(* nil *)
  auto.
(* case *)
  exploit (tr_find_label s (Csem.Kseq (Csem.seq_of_labeled_statement s0) k)); eauto.
  econstructor; eauto. apply tr_seq_of_labeled_statement; eauto.
  destruct (Csem.find_label lbl s
    (Csem.Kseq (Csem.seq_of_labeled_statement s0) k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; auto.
  intro EQ. rewrite EQ. eapply IHs; eauto.
Qed.

End FIND_LABEL.

(** Anti-stuttering measure *)

(** There are some stuttering steps in the translation:
- The execution of [Sdo a] where [a] is side-effect free,
  which is three transitions in the source:
<<
    Sdo a, k  --->  a, Kdo k ---> rval v, Kdo k ---> Sskip, k
>>
  but the translation, which is [Sskip], makes no transitions.
- The reduction [Ecomma (Eval v) r2 --> r2].
- The reduction [Eparen (Eval v) --> Eval v] in a [For_effects] context.

The following measure decreases for these stuttering steps. *)

Fixpoint esize (a: Csyntax.expr) : nat :=
  match a with
  | Csyntax.Eloc _ _ _ => 1%nat
  | Csyntax.Evar _ _ => 1%nat
  | Csyntax.Ederef r1 _ => S(esize r1)
  | Csyntax.Efield l1 _ _ => S(esize l1)
  | Csyntax.Eval _ _ => O
  | Csyntax.Evalof l1 _ => S(esize l1)
  | Csyntax.Eaddrof l1 _ => S(esize l1)
  | Csyntax.Eunop _ r1 _ => S(esize r1)
  | Csyntax.Ebinop _ r1 r2 _ => S(esize r1 + esize r2)%nat
  | Csyntax.Ecast r1 _ => S(esize r1)
  | Csyntax.Eseqand r1 _ _ => S(esize r1)
  | Csyntax.Eseqor r1 _ _ => S(esize r1)
  | Csyntax.Econdition r1 _ _ _ => S(esize r1)
  | Csyntax.Esizeof _ _ => 1%nat
  | Csyntax.Ealignof _ _ => 1%nat
  | Csyntax.Eassign l1 r2 _ => S(esize l1 + esize r2)%nat
  | Csyntax.Eassignop _ l1 r2 _ _ => S(esize l1 + esize r2)%nat
  | Csyntax.Epostincr _ l1 _ => S(esize l1)
  | Csyntax.Ecomma r1 r2 _ => S(esize r1 + esize r2)%nat
  | Csyntax.Ecall r1 rl2 _ => S(esize r1 + esizelist rl2)%nat
  | Csyntax.Ebuiltin ef _ rl _ => S(esizelist rl)%nat
  | Csyntax.Eparen r1 _ _ => S(esize r1)
  end

with esizelist (el: Csyntax.exprlist) : nat :=
  match el with
  | Csyntax.Enil => O
  | Csyntax.Econs r1 rl2 => (esize r1 + esizelist rl2)%nat
  end.

Definition measure (st: Csem.state) : nat :=
  match st with
  | Csem.ExprState _ r _ _ _ => (esize r + 1)%nat
  | Csem.State _ Csyntax.Sskip _ _ _ => 0%nat
  | Csem.State _ (Csyntax.Sdo r) _ _ _ => (esize r + 2)%nat
  | Csem.State _ (Csyntax.Sifthenelse r _ _) _ _ _ => (esize r + 2)%nat
  | _ => 0%nat
  end.

Lemma leftcontext_size:
  forall from to C,
  leftcontext from to C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esize (C e1) < esize (C e2))%nat
with leftcontextlist_size:
  forall from C,
  leftcontextlist from C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esizelist (C e1) < esizelist (C e2))%nat.
Proof.
  induction 1; intros; simpl; auto with arith.
  exploit leftcontextlist_size; eauto. auto with arith.
  exploit leftcontextlist_size; eauto. auto with arith.
  induction 1; intros; simpl; auto with arith. exploit leftcontext_size; eauto. auto with arith.
Qed.

(** Forward simulation for expressions. *)

Lemma locally_finish {A} : forall le t (v : A),
    ⊢ \s t -∗ locally (set t v le) (λ le', ⌜le' ! t = Some v⌝).
Proof.
  unfold_locally.
  destruct H2. red in H. intros. exists heap_empty, h1. subst h1.
  repeat split; auto with heap_scope. erewrite <- H0. apply gss. apply lookup_singleton.
  rewrite heap_union_empty_l; auto.
Qed.

Ltac apply_ind_dest l h :=
    match goal with
    | H : forall _ _ _ _, bi_emp_valid (tr_expr _ _ l _ _ -∗ _) |- _ =>
      iDestruct (H with h) as h
    | _ => fail "No rec"
    end.


Lemma tr_expr_dest : forall r le dst sl a, ⊢ tr_expr le dst r sl a -∗ <absorb> dest_below dst.
Proof.
  induction r; iIntros; simpl; destruct dst; norm_all; apply_ind apply_ind_dest; simpl; auto.
  - iDestruct "HB" as "[$ _]".
  - contradiction.
  - destruct (Pos.eq_dec x0 (sd_temp sd)); norm_all; subst; apply_ind apply_ind_dest; simpl; auto.
    iExists x1. auto.
Qed.

Lemma pure_next_step P (R : Prop) (Q : iProp) :
  (forall tmp, Q () tmp -> R) -> (⊢P -∗ Q) -> (P -∗ ⌜R⌝)%stdpp.
Proof.
  intros. apply instance_heap. intros. apply (H tmps). apply soundness2.
  apply soundness3 in H1. iIntros "HA". iDestruct (H1 with "HA") as "HA". iApply (H0 with "HA").
Qed.

Ltac iConstructor :=
  iStopProof; eapply pure_next_step;
  [ let tmp := fresh in
    let H := fresh in
    intros tmp H; econstructor; eauto; econstructor; eapply H| idtac].
    
Lemma estep_simulation:
  forall S1 t S2, Cstrategy.estep ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  Ltac dest_val_effect H dest :=
    assert (dest = For_val \/ dest = For_effects) as P0; [destruct dest; auto; inv H | inv P0].
  
  (* expr *)
  - assert (tr_expr le dest r sl a () tmps).
   + inv H9; auto. contradiction.
   + exploit tr_simple_rvalue; eauto. apply soundness3 in H1. intro.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H1 with "HA") as "HA".
     iDestruct (H2 with "HA") as "%"; auto. destruct dest.
     (* for val *)
      * destruct H3 as (SL1&TY1&EV1). subst sl. iExists _. 
        iSplit; iPureIntro.
        -- right; split.
           ++ apply star_refl.
           ++ destruct r; simpl; (contradiction || lia).
        -- econstructor; eauto. instantiate (1 := ∅). econstructor; auto.
      (* for effects *)
      * iClear "HA". subst sl. iExists _.
        iSplit.
        -- iPureIntro. right; split.
           ++ apply star_refl.
           ++ destruct r; simpl; (contradiction || lia).
        -- iPureIntro. econstructor; eauto. instantiate (1 := ∅). econstructor; auto.
           simpl. apply soundness2. auto.
      * inv H10.
        
 (* rval volatile *)
  - inv H11; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto. intro. apply soundness3 in H2.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H2 with "HA") as "HA".
     iDestruct (H4 with "HA") as (dst'' sl1 sl2 a') "[P [% R]]".
     simpl. iDestruct "P" as ">P". norm_all.
     iDestruct (tr_simple_lvalue with "HG") as "[% [% %]]"; eauto. subst. 
     unfold tr_rvalof. rewrite H3. norm_all. subst.
     iExists _. iSplit. 
     * iPureIntro. left. eapply plus_two. constructor. eapply step_make_set; eauto. traceEq.
     * fold Kseqlist. iClear "HG". iConstructor.
       iIntros "[HA [HB HC]]".
       iDestruct ("HC" $! (Eval v (Csyntax.typeof l)) with "[]") as "HC"; eauto.
       iDestruct (locally_set with "[HB] HC") as "[HC HB]"; eauto.
       iApply (locally_out with "HC"). simpl. destruct dst''.
       -- iModIntro. iSplit; auto. iIntros. iApply locally_conseq_pure. intros. constructor.
          eapply H5. simpl. iApply locally_finish. iFrame.
       -- iPureIntro. auto.
       -- iModIntro. iSplit. iFrame. iExists _. iSplitL "HB"; eauto. iIntros.
          iApply locally_conseq_pure. intros. constructor. eapply H5. simpl. iApply locally_finish.
          iFrame. eauto.
          
 (* seqand true *)
 - inv H9; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H2.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H2 with "HA") as "HA". 
     iDestruct (H3 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H2. clear H3.
     simpl. iDestruct "P" as ">P".
     destruct dst'; norm_all; iDestruct (tr_simple_rvalue with "HE") as "[% [% %]]"; eauto; subst;
       iClear "HE"; iExists _; iSplit;
         try (iPureIntro; left; simpl Kseqlist;
              eapply plus_left; [constructor |
                                 eapply star_trans;
                                 [ apply step_makeif with (b := true) (v1 := v); auto; congruence|
                                   apply push_seq | reflexivity] |
                                 reflexivity]);
         rewrite <- Kseqlist_app; iConstructor; iIntros "[HA HB]";
           iDestruct ("HB" $! (Eparen r2 type_bool ty) with "[]") as "HC"; eauto;
             iApply (locally_out with "HC"); simpl; iModIntro; eauto.
     iExists _. iExists (sd_temp sd).
     destruct Pos.eq_dec; auto. contradiction.
     
 (* seqand false *)
 - inv H9; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H2.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H2 with "HA") as "HA". 
     iDestruct (H3 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H2. clear H3. simpl. 
     destruct dst'; norm_all; iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto; subst;
       iClear "HG"; iExists _; iSplit.
     * iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
       eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
       apply star_one. constructor. constructor. reflexivity. reflexivity.
     * iDestruct (tr_expr_dest with "HI") as ">HG".
       iDestruct ("R" $! (Eval (Vint Int.zero) ty) with "[]") as "HC"; eauto.
       iDestruct (locally_set with "HG HC") as "[HC HB]".
       iConstructor. change sl2 with (nil ++ sl2). iIntros "[HB HA]".
       iApply (locally_out with "HB"). simpl.
       iModIntro. iSplitL; auto. iIntros.
       iApply locally_conseq_pure. intros. constructor. eapply H2.
       iApply locally_finish. iFrame. 
     * iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
       apply step_makeif with (b := false) (v1 := v); auto. congruence. reflexivity.
     * iConstructor. change sl2 with (nil ++ sl2). iIntros "[HA HB]".
       iDestruct ("HA" $! (Eval (Vint Int.zero) ty) with "[]") as "HA"; eauto.
       iApply (locally_out with "HA"). simpl. eauto.
     * iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
       eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
       apply push_seq. reflexivity. reflexivity.
     * rewrite <- Kseqlist_app. iConstructor. iIntros "[HB HA]".
       iDestruct ("HB" $! (Eval (Vint Int.zero) ty) with "[]") as "HB"; eauto.
       iApply (locally_out with "HB"). simpl. iDestruct (tr_expr_dest with "HA") as ">HA".
       iFrame. iModIntro. iExists (Econst_int Int.zero ty). iSplitL; eauto.
       iIntros. iApply locally_simpl. iIntros. iPureIntro. constructor.
          
 (* seqor true *)
 - inv H9; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H2.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H2 with "HA") as "HA". 
     iDestruct (H3 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". simpl. clear H2. clear H3. simpl. 
     destruct dst'; norm_all; iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto; subst;
       iClear "HG"; iExists _; iSplit.
       * iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
         eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
         apply star_one. constructor. constructor. reflexivity. reflexivity.
       * iDestruct ("R" $! (Eval (Vint Int.one) ty) with "[]") as "HC"; eauto.
         iDestruct (tr_expr_dest with "HI") as ">HG". iConstructor.
         change sl2 with (nil ++ sl2). iIntros "[HB HC]".
         iDestruct (locally_set with "HC HB") as "[HB HC]".
         change sl2 with (nil ++ sl2). iApply (locally_out with "HB").
         simpl. iModIntro. iSplitL "HC"; auto. iIntros.
         iApply locally_conseq_pure. intros. econstructor. eapply H2.
         iApply locally_finish. iFrame.
       * iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
         apply step_makeif with (b := true) (v1 := v); auto. congruence. reflexivity.
       * iConstructor. change sl2 with (nil ++ sl2). iIntros "[HB HA]".
         iDestruct ("HB" $! (Eval (Vint Int.one) ty) with "[]") as "HB"; eauto.
         iApply (locally_out with "HB"). simpl. auto.
       * iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
         eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
         apply push_seq. reflexivity. reflexivity.
       * rewrite <- Kseqlist_app.
         iDestruct (tr_expr_dest with "HI") as ">HG".
         iConstructor. iIntros "[HA HB]".
         iDestruct ("HA" $! (Eval (Vint Int.one) ty) with "[]") as "HA"; eauto.
         iApply (locally_out with "HA"). simpl. iModIntro. iFrame.
         iExists (Econst_int Int.one ty). iSplitL; eauto.
         iIntros. iApply locally_simpl. iIntros. iPureIntro. constructor.

 (* seqor false *)
 - inv H9; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H2.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H2 with "HA") as "HA". 
     iDestruct (H3 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H2. clear H3. simpl.
     destruct dst'; norm_all; iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto;
       subst; iClear "HG"; iExists _; iSplit.
     * iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
       eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
       apply push_seq. constructor. constructor.
     * rewrite <- Kseqlist_app. iConstructor. iIntros "[HA HB]".
       iDestruct ("HA" $! (Eparen r2 type_bool ty) with "[]") as "HA"; eauto.
       iApply (locally_out with "HA").
       simpl. iModIntro. repeat iExists _. iFrame. eauto.
     * iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
       eapply star_trans.
       apply step_makeif with (b := false) (v1 := v); auto. congruence. apply push_seq.
       reflexivity. reflexivity.
     * rewrite <- Kseqlist_app. iConstructor. iIntros "[HA HB]".
       iDestruct ("HA" $! (Eparen r2 type_bool ty) with "[]") as "HA"; eauto.
       iApply (locally_out with "HA").
       simpl. iModIntro. iExists _. eauto.
     * iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
       eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
       apply push_seq. reflexivity. reflexivity.
     * rewrite <- Kseqlist_app.
       iConstructor. iIntros "[HA HB]".
       iDestruct ("HA" $! (Eparen r2 type_bool ty) with "[]") as "HA"; eauto.
       iApply (locally_out with "HA").
       simpl. iModIntro. iExists _. iExists (sd_temp sd).
       destruct (Pos.eq_dec (sd_temp sd) (sd_temp sd)); auto. contradiction.

 (* condition *)
 - inv H9; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H2.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H2 with "HA") as "HA". 
     iDestruct (H3 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H2. clear H3. simpl.
     destruct dst'; norm_all.
     * iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto. subst.
       iClear "HG". destruct b; iExists _; iSplit.
       -- iPureIntro. left. eapply plus_left. constructor.
          eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. reflexivity.
       -- rewrite <- Kseqlist_app. iConstructor. iIntros "[HB HA]".
          iDestruct ("HB" $! (Eparen r2 ty ty) with "[]") as "HD"; eauto.
          iApply (locally_out with "HD"). simpl. iModIntro.
          repeat iExists _. iDestruct "HA" as "[HA _]". iFrame. eauto.
       -- iPureIntro. left. eapply plus_left. constructor.
          eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. reflexivity.
       -- rewrite <- Kseqlist_app. iConstructor. iIntros "[HB HA]". 
          iDestruct ("HB" $! (Eparen r3 ty ty) with "[]") as "HD"; eauto.
          iApply (locally_out with "HD"). simpl. iModIntro.
          repeat iExists _. iDestruct "HA" as "[_ HA]". eauto.
     * iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto. subst.
       iClear "HG". destruct b; iExists _; iSplit.
       -- iPureIntro. left. eapply plus_left. constructor.
          eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. traceEq.
       -- rewrite <- Kseqlist_app. iConstructor. iIntros "[HC [HA HB]]".
          iDestruct ("HC" $! (Eparen r2 ty ty) with "[]") as "HD"; eauto.
          iApply (locally_out with "HD"). simpl. iClear "HB". iModIntro.
          repeat iExists _. iFrame.
       -- iPureIntro. left. eapply plus_left. constructor.
          eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. traceEq.
       -- rewrite <- Kseqlist_app. iConstructor. iIntros "[HC [HA HB]]".
          iDestruct ("HC" $! (Eparen r3 ty ty) with "[]") as "HD"; eauto.
          iApply (locally_out with "HD"). simpl. iClear "HA". iModIntro.
          repeat iExists _. iFrame.
     * iDestruct (tr_simple_rvalue with "HI") as "[% [% %]]"; eauto. subst.
       iClear "HI". destruct b; iExists _; iSplit.
       -- iPureIntro.  left. eapply plus_left. constructor. simpl.
          eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. traceEq.
       -- rewrite <- Kseqlist_app. iConstructor. iIntros "[HC [HA HB]]". 
          iDestruct ("HC" $! (Eparen r2 ty ty) with "[]") as "HD"; eauto.
          iApply (locally_out with "HD"). simpl. iModIntro.
          iExists _. iExists x5. destruct (Pos.eq_dec x5 (sd_temp sd)).
          subst. iDestruct "HB" as "[HB _]". iApply tr_expr_abs.
          iDestruct (tr_expr_dest with "HB") as ">HB". iModIntro.
          simpl. iDestruct (singleton_false with "HA HB") as "HA". iExFalso. iApply "HA".
          iDestruct "HB" as "[HB _]". iFrame.
       -- iPureIntro. left. eapply plus_left. constructor. simpl.
          eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. traceEq.
       -- rewrite <- Kseqlist_app. iConstructor. iIntros "[HC [HA HB]]". 
          iDestruct ("HC" $! (Eparen r3 ty ty) with "[]") as "HD"; eauto.
          iApply (locally_out with "HD"). simpl. iModIntro. iExists _. iExists x5.
          destruct (Pos.eq_dec x5 (sd_temp sd)).
          subst. iDestruct "HB" as "[HB _]". iApply tr_expr_abs.
          iDestruct (tr_expr_dest with "HB") as ">HB".
          simpl. iDestruct (singleton_false with "HA HB") as "HA". iExFalso. iApply "HA".
          iDestruct "HB" as "[_ HB]". iFrame.
          
 (* assign *)
 - inv H12; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H4.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H4 with "HA") as "HA". 
     iDestruct (H5 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H4. clear H5.
     simpl. iDestruct "P" as ">P". destruct dst'; norm_all.
     * iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto.
       iDestruct (proj1 tr_expr_invariant with "HE") as "HE".
       iDestruct (locally_set with "[HI] HE") as "[HA HE]"; auto.
       iDestruct (locally_delete with "HA") as "HA".
       iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto. subst. simpl.
       iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor.
          eapply star_left. constructor. econstructor. eauto. rewrite <- H8; eauto. 
          eapply star_left. constructor.
          apply star_one. eapply step_make_assign; eauto. 
          constructor. eapply Maps.PTree.gss. simpl. eapply cast_idempotent; eauto. 
          reflexivity. reflexivity. traceEq.
       -- iConstructor. iIntros "[HA [_ [HC [HD HE]]]]". 
          iDestruct ("HC" $! (Eval v' (Csyntax.typeof l)) with "[]") as "HB"; eauto.
          iDestruct (locally_set with "HD HB") as "[HB HC]".
          change sl2 with (nil ++ sl2). iApply (locally_out with "HB"). simpl.
          iClear "HA". iClear "HE". iModIntro.
          iSplitL; eauto. iIntros. iApply locally_conseq_pure. intros. econstructor. eapply H4.
          iApply locally_finish. iFrame.
     * iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto.
       iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto. subst. simpl.
       iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor.
          apply star_one. eapply step_make_assign; eauto.
          rewrite <- H7; eauto. traceEq.
       -- iConstructor. change sl2 with (nil ++ sl2). iIntros "[HA [HB HC]]". 
          iDestruct ("HC" $! (Eval v' (Csyntax.typeof l)) with "[]") as "HC"; eauto.
          iApply (locally_out with "HC"). simpl. eauto.
     * iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto.
       iDestruct (proj1 tr_expr_invariant with "HE") as "HA".
       iDestruct (locally_set with "[HI] HA") as "[HA HC]"; auto.
       iDestruct (locally_delete with "HA") as "HA".
       iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto. subst. simpl.
       iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor.
          eapply star_left. constructor. econstructor. eauto. rewrite <- H8; eauto. 
          eapply star_left. constructor.
          apply star_one. eapply step_make_assign; eauto. 
          constructor. eapply Maps.PTree.gss. simpl. eapply cast_idempotent; eauto. 
          reflexivity. reflexivity. traceEq.
       -- iConstructor. iIntros "[HA [HB [HC [HD HE]]]]". 
          iDestruct ("HC" $! (Eval v' (Csyntax.typeof l)) with "[]") as "HC"; eauto.
          iDestruct (locally_set with "HD HC") as "[HC HD]".
          change sl2 with (nil ++ sl2). iApply (locally_out with "HC"). simpl.
          iClear "HA". iClear "HE". iModIntro. iFrame. repeat iExists _.
          iSplitL; eauto. iIntros. iApply locally_conseq_pure. intros. econstructor. eapply H4.
          iApply locally_finish. iFrame.
          iPureIntro. split; eauto.

 (* assignop *)
 - inv H15; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H6.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H6 with "HA") as "HA". 
     iDestruct (H7 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H6. clear H7.
     simpl. iDestruct "P" as ">P". destruct dst'; norm_all.
     * unfold tr_rvalof. destruct (type_is_volatile (Csyntax.typeof l)) eqn:?; norm_all.
       -- iDestruct (tr_simple_lvalue with "HG") as "[% [% %]]"; eauto.
          iDestruct (proj1 tr_expr_invariant with "HI") as "HB".
          (* iDestruct (locally_set with "[HK] HB") as "[HB HC]"; eauto. *)
          iDestruct (locally_set with "[HT] HB") as "[HB HD]"; eauto.
          iDestruct (locally_delete with "HB") as "HB".
          iDestruct (tr_simple_rvalue with "HB") as "[% [% %]]"; eauto. subst.
          iDestruct (proj1 tr_expr_invariant with "HG") as "HA".
          iDestruct (locally_set with "[HD] HA") as "[HA HD]"; eauto.
          iDestruct (locally_set with "[HM] HA") as "[HA HC]"; eauto.
          iDestruct (locally_delete with "HA") as "HA".
          iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto.
          iExists _. iSplit.
          ++ iPureIntro.
             left. rewrite app_ass. rewrite Kseqlist_app.
             eapply star_plus_trans. eapply star_two.
             econstructor. eapply step_make_set; eauto. traceEq.
             simpl. eapply plus_four. econstructor. econstructor.
             econstructor. econstructor. constructor. apply Maps.PTree.gss.
             eauto. rewrite <- H17. rewrite comp_env_preserved. simpl. eauto. eassumption.
             econstructor. eapply step_make_assign; eauto.
             econstructor. apply Maps.PTree.gss. simpl. eapply cast_idempotent; eauto.
             reflexivity. traceEq.
          ++ iClear "HB". iDestruct ("R" $! (Eval v4 (Csyntax.typeof l)) with "[]") as "HB"; eauto.
             iDestruct (locally_set with "HD HB") as "[HB HD]".
             iDestruct (locally_set with "HC HB") as "[HB HC]".
             iClear "HA". iClear "HD". iConstructor. iIntros "[_ [HA HB]]". 
             change sl2 with (nil ++ sl2).
             iApply (locally_out with "HA"). simpl. iModIntro. iSplitL "HB"; eauto.
             iIntros "*". iApply locally_conseq_pure. intros. econstructor. apply H9.
             iApply locally_finish. iFrame.
       -- iDestruct (tr_simple_lvalue with "HG") as "[% [% %]]"; eauto.
          iDestruct (proj1 tr_expr_invariant with "HG") as "HA".
          iDestruct (locally_set with "[HM] HA") as "[HA HC]"; auto.
          iDestruct (locally_delete with "HA") as "HA".
          iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto.
          iDestruct (tr_simple_rvalue with "HI") as "[% [% %]]"; eauto.
          iDestruct (proj1 tr_expr_invariant with "HI") as "HB".
          iDestruct (locally_set with "HC HB") as "[HB HC]".
          iDestruct (locally_delete with "HB") as "HB".
          iDestruct (tr_simple_rvalue with "HB") as "[% [% %]]"; eauto. subst. simpl.
          exploit deref_loc_translated; eauto. intros. unfold chunk_for_volatile_type in H6.
          rewrite Heqb0 in H6. destruct H6.
          iExists _. iSplit.
          ++ iPureIntro.
             left. eapply star_plus_trans. apply star_refl. 
             simpl. eapply plus_four. econstructor. econstructor.
             econstructor. econstructor. eapply eval_Elvalue; eauto. rewrite <- H12. eauto.
             eauto. rewrite <- H12. rewrite <- H23. rewrite comp_env_preserved. eauto.
             eassumption. econstructor. eapply step_make_assign; eauto.
             constructor. apply Maps.PTree.gss. simpl. eapply cast_idempotent; eauto.
             reflexivity. traceEq.
          ++ iClear "HE". instantiate (1 := v4). iClear "HA". iClear "HB".
             iConstructor. iIntros "[HA HB]". 
             iDestruct ("HA" $! (Eval v4 (Csyntax.typeof l)) with "[]") as "HA"; eauto.
             iDestruct (locally_set with "[HB] HA") as "[HA HB]"; eauto.
             change sl2 with (nil ++ sl2).
             iApply (locally_out with "HA"). 
             simpl. iModIntro. iSplitL "HB"; eauto.
             iIntros "*". iApply locally_conseq_pure. intros. econstructor. apply H8.
             iApply locally_finish. iFrame.
     * unfold tr_rvalof. destruct (type_is_volatile (Csyntax.typeof l)) eqn:?; norm_all.
       -- iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
          iDestruct (proj1 tr_expr_invariant with "HE") as "HA".
          iDestruct (locally_set with "[HL] HA") as "[HA HC]"; eauto.
          iDestruct (locally_delete with "HA") as "HA".
          iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto.
          iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto.
          iDestruct (proj1 tr_expr_invariant with "HG") as "HB".
          iDestruct (locally_set with "[HC] HB") as "[HB HC]"; eauto.
          iDestruct (locally_delete with "HB") as "HB".
          iDestruct (tr_simple_rvalue with "HB") as "[% [% %]]"; eauto. subst. simpl.
          iExists _. iSplit.
          ++ iPureIntro.
             left. eapply star_plus_trans. eapply star_two. econstructor.
             eapply step_make_set; eauto. traceEq.
             eapply plus_two. simpl. econstructor. eapply step_make_assign; eauto.
             econstructor. constructor. apply Maps.PTree.gss. eauto.
             rewrite comp_env_preserved. simpl. rewrite <- H22. auto. reflexivity. traceEq.
          ++ iClear "HA". iClear "HB".
             iDestruct ("R" $! (Eval v4 (Csyntax.typeof l)) with "[]") as "HA"; eauto.
             iDestruct (locally_set with "HC HA") as "[HA HC]". iClear "HC".
             iConstructor. iIntros "HA". change sl2 with (nil ++ sl2).
             iApply (locally_out with "HA"). simpl. iModIntro. auto.
       -- iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
          iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto.
          exploit deref_loc_translated; eauto. intros. unfold chunk_for_volatile_type in H18.
          rewrite Heqb0 in H18. destruct H18. subst. simpl.
          iExists _. iSplit.
          ++ iPureIntro.
             left. eapply star_plus_trans. apply star_refl. 
             eapply plus_two. simpl. econstructor. eapply step_make_assign; eauto.
             econstructor. eapply eval_Elvalue; eauto. rewrite <- H11. eauto. eauto.
             rewrite <- H11. rewrite <- H15. rewrite comp_env_preserved. auto.
             reflexivity. traceEq.
          ++ iClear "HE". iClear "HG". iConstructor. iIntros "HC". 
             iDestruct ("HC" $! (Eval v4 (Csyntax.typeof l)) with "[]") as "HC"; eauto.
             change sl2 with (nil ++ sl2).
             iApply (locally_out with "HC"). simpl. iModIntro. auto.
     * unfold tr_rvalof. destruct (type_is_volatile (Csyntax.typeof l)) eqn:?; norm_all.
       -- iDestruct (tr_simple_lvalue with "HG") as "[% [% %]]"; eauto.
          iDestruct (proj1 tr_expr_invariant with "HI") as "HB".
          iDestruct (locally_set with "[HT] HB") as "[HB HC]"; eauto.
          iDestruct (locally_delete with "HB") as "HB".
          iDestruct (tr_simple_rvalue with "HB") as "[% [% %]]"; eauto. subst.
          iDestruct (proj1 tr_expr_invariant with "HG") as "HA".
          iDestruct (locally_set with "[HC] HA") as "[HA HC]"; eauto.
          iDestruct (locally_set with "[HM] HA") as "[HA HD]"; eauto.
          iDestruct (locally_delete with "HA") as "HA".
          iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto.
          iExists _. iSplit.
          ++ iPureIntro.
             left. rewrite app_ass. rewrite Kseqlist_app.
             eapply star_plus_trans. eapply star_two.
             econstructor. eapply step_make_set; eauto. traceEq.
             simpl. eapply plus_four. econstructor. econstructor.
             econstructor. econstructor. constructor. apply Maps.PTree.gss.
             eauto. rewrite <- H17. rewrite comp_env_preserved. simpl. eauto. eassumption.
             econstructor. eapply step_make_assign; eauto.
             econstructor. apply Maps.PTree.gss. simpl. eapply cast_idempotent; eauto.
             reflexivity. traceEq.
          ++ iClear "HA". iClear "HB".
             iDestruct ("R" $! (Eval v4 (Csyntax.typeof l)) with "[]") as "HA"; eauto.
             iDestruct (locally_set with "[HC] HA") as "[HA HC]"; eauto.
             iDestruct (locally_set with "[HD] HA") as "[HA HD]"; eauto.
             iClear "HC". iConstructor. iIntros "[HF [HA HB]]". change sl2 with (nil ++ sl2).
             iApply (locally_out with "HA"). simpl. iModIntro. iFrame. iExists _.
             iSplitL "HB"; eauto. iIntros "*". iApply locally_conseq_pure. intros. econstructor.
             apply H9. iApply locally_finish. iFrame. eauto.
       -- iDestruct (tr_simple_lvalue with "HG") as "[% [% %]]"; eauto.
          iDestruct (proj1 tr_expr_invariant with "HG") as "HA".
          iDestruct (locally_set with "[HM] HA") as "[HA HC]"; auto.
          iDestruct (locally_delete with "HA") as "HA".
          iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto.
          iDestruct (tr_simple_rvalue with "HI") as "[% [% %]]"; eauto.
          iDestruct (proj1 tr_expr_invariant with "HI") as "HB".
          iDestruct (locally_set with "HC HB") as "[HB HC]".
          iDestruct (locally_delete with "HB") as "HB".
          iDestruct (tr_simple_rvalue with "HB") as "[% [% %]]"; eauto. subst. simpl.
          exploit deref_loc_translated; eauto. intros. unfold chunk_for_volatile_type in H6.
          rewrite Heqb0 in H6. destruct H6.
          iExists _. iSplit.
          ++ iPureIntro.
             left. eapply star_plus_trans. apply star_refl. 
             simpl. eapply plus_four. econstructor. econstructor.
             econstructor. econstructor. eapply eval_Elvalue; eauto. rewrite <- H12. eauto.
             eauto. rewrite <- H12. rewrite <- H23. rewrite comp_env_preserved. eauto.
             eassumption. econstructor. eapply step_make_assign; eauto.
             constructor. apply Maps.PTree.gss. simpl. eapply cast_idempotent; eauto.
             reflexivity. traceEq.
          ++ instantiate (1 := v4).
             iDestruct ("R" $! (Eval v4 (Csyntax.typeof l)) with "[]") as "R"; eauto.
             iDestruct (locally_set with "[HC] R") as "[R HC]"; eauto.
             iClear "HA". iClear "HB".
             iConstructor. iIntros "[HA [HB HC]]". change sl2 with (nil ++ sl2).
             iApply (locally_out with "HB"). 
             simpl. iModIntro. iFrame. iExists _. iSplitL "HC"; eauto.
             iIntros "*". iApply locally_conseq_pure. intros. econstructor. apply H8.
             iApply locally_finish. iFrame. eauto.
             
 (* assignop stuck *)
 - inv H12; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H4.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H4 with "HA") as "HA". 
     iDestruct (H5 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H4. clear H5.
     simpl. iDestruct "P" as ">P". destruct dst'; norm_all.
     * iDestruct (tr_simple_lvalue with "HG") as "[% [% %]]"; eauto.
       iDestruct (tr_simple_rvalue with "HI") as "[% [% %]]"; eauto.
       iDestruct (step_tr_rvalof with "HK") as (le') "[% [% %]]"; eauto.
       subst. simpl.
       iExists _. iSplit.
       ++ iPureIntro.
          right; split. rewrite app_ass. rewrite Kseqlist_app. eexact H15. lia.
       ++ iPureIntro. econstructor.
     * iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
       iDestruct (tr_simple_rvalue with "HG") as "[% [% %]]"; eauto.
       iDestruct (step_tr_rvalof with "HI") as (le') "[% [% %]]"; eauto.
       subst. simpl. iExists _. iSplit.
       ++ iPureIntro. right; split. rewrite app_ass. rewrite Kseqlist_app. eexact H14. lia.
       ++ iPureIntro. econstructor.
     * iDestruct (tr_simple_lvalue with "HG") as "[% [% %]]"; eauto.
       iDestruct (tr_simple_rvalue with "HI") as "[% [% %]]"; eauto.
       iDestruct (step_tr_rvalof with "HK") as (le') "[% [% %]]"; eauto.
       subst. simpl. iExists _. iSplit.
       ++ iPureIntro. right; split. rewrite app_ass. rewrite Kseqlist_app. eexact H15. lia.
       ++ iPureIntro. econstructor.
     
  (* postincr *)
 - inv H14; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto. intro. apply soundness3 in H5.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H5 with "HA") as "HA". 
     iDestruct (H6 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H5. clear H6.
     simpl. iDestruct "P" as ">P". norm_all. destruct dst'; norm_all.
     * iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
       iDestruct (proj1 tr_expr_invariant with "HE") as "HA".
       iDestruct (locally_set with "[HI] HA") as "[HA HB]"; auto.
       iDestruct (locally_delete with "HA") as "HA".
       iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto.
       subst. simpl. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_four. constructor.
          eapply step_make_set; eauto. constructor. eapply step_make_assign; eauto.
          unfold transl_incrdecr. destruct id; simpl in H2.
          econstructor. constructor. apply Maps.PTree.gss. constructor.
          rewrite comp_env_preserved; simpl; eauto.
          econstructor. constructor. apply Maps.PTree.gss. constructor.
          rewrite comp_env_preserved; simpl; eauto.
          destruct id; auto. traceEq.
       -- iClear "HA". iClear "HG". iConstructor. iIntros "[HA HB]". 
          iDestruct ("HA" $! (Eval v1 (Csyntax.typeof l)) with "[]") as "HA"; eauto.
          iDestruct (locally_set with "HB HA") as "[HA HB]". change sl2 with (nil ++ sl2).
          iApply (locally_out with "HA"). simpl. iModIntro. iSplitL "HB"; eauto.
          iIntros "*". iApply locally_conseq_pure. intros. econstructor. apply H5.
          iApply locally_finish. iFrame.
     * iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
       unfold tr_rvalof. destruct (type_is_volatile (Csyntax.typeof l)) eqn:?; norm_all.
       -- iDestruct (proj1 tr_expr_invariant with "HE") as "HA".
          iDestruct (locally_set with "[HM] HA") as "[HA HB]"; eauto.
          iDestruct (locally_delete with "HA") as "HA".
          iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto.
          subst. iExists _. iSplit.
          ++ iPureIntro. left. rewrite app_ass; rewrite Kseqlist_app. eapply star_plus_trans.
             eapply star_two. econstructor. eapply step_make_set; eauto. traceEq.
             eapply plus_two. simpl. constructor. eapply step_make_assign; eauto.
             unfold transl_incrdecr. destruct id; simpl in H2.
             econstructor. constructor. apply Maps.PTree.gss. econstructor.
             rewrite comp_env_preserved. simpl. eauto.
             econstructor. econstructor. apply Maps.PTree.gss. econstructor.
             rewrite comp_env_preserved. simpl; eauto.
             destruct id; auto. reflexivity. traceEq.
          ++ iClear "HA". iDestruct ("R" $! (Eval v1 (Csyntax.typeof l)) with "[]") as "HA"; eauto.
             iDestruct (locally_set with "HB HA") as "[HA HB]". iClear "HB".
             iConstructor. iIntros "HA". change sl2 with (nil ++ sl2).
             iApply (locally_out with "HA"). simpl. iModIntro. eauto.
       -- iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
          exploit deref_loc_translated; eauto. intros. unfold chunk_for_volatile_type in H17.
          rewrite Heqb0 in H17. destruct H17. subst. iExists _. iSplit.
          ++ iPureIntro. left. rewrite app_ass; rewrite Kseqlist_app.
             eapply star_plus_trans. eapply star_refl.
             eapply plus_two. simpl. constructor.
             eapply step_make_assign; eauto.
             unfold transl_incrdecr. destruct id; simpl in H2.
             econstructor. econstructor; eauto. rewrite <- H8. eauto. econstructor.
             rewrite comp_env_preserved. simpl. rewrite <- H8. eauto.
             econstructor. econstructor. eauto. rewrite <- H8. eauto. econstructor.
             rewrite comp_env_preserved. simpl. rewrite <- H8. eauto.
             unfold transl_incrdecr. destruct id; simpl in H2. eauto. eauto. reflexivity.
             traceEq.
          ++ iConstructor. iIntros "[HA HB]". 
             iDestruct ("HB" $! (Eval v1 (Csyntax.typeof l)) with "[]") as "HB"; eauto.
             change sl2 with (nil ++ sl2). iApply (locally_out with "HB"). simpl. eauto.
     * iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
       iDestruct (proj1 tr_expr_invariant with "HE") as "HA".
       iDestruct (locally_set with "[HI] HA") as "[HA HB]"; auto.
       iDestruct (locally_delete with "HA") as "HA".
       iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto.
       subst. simpl. iExists _. iSplit.
       -- iPureIntro.
          left. eapply plus_four. constructor.
          eapply step_make_set; eauto. constructor.
          eapply step_make_assign; eauto.
          unfold transl_incrdecr. destruct id; simpl in H2.
          econstructor. constructor. apply Maps.PTree.gss. constructor.
          rewrite comp_env_preserved; simpl; eauto.
          econstructor. constructor. apply Maps.PTree.gss. constructor.
          rewrite comp_env_preserved; simpl; eauto.
          destruct id; auto. traceEq.
       -- iClear "HA". iConstructor. iIntros "[HB [HA HC]]". 
          iDestruct ("HA" $! (Eval v1 (Csyntax.typeof l)) with "[]") as "HA"; eauto.
          iDestruct (locally_set with "HC HA") as "[HA HC]".
          change sl2 with (nil ++ sl2).
          iApply (locally_out with "HA"). simpl. iModIntro. iFrame. iExists _. iSplitL "HC"; eauto.
          iIntros "*". iApply locally_conseq_pure. intros. econstructor. apply H5.
          iApply locally_finish. iFrame. eauto.

 (* postincr stuck *)
 - inv H11; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H3.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H3 with "HA") as "HA". 
     iDestruct (H4 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H3. clear H4.
     simpl. iDestruct "P" as ">P"; norm_all. destruct dst'; norm_all.
     * iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
       subst. simpl. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_two. constructor. eapply step_make_set; eauto. traceEq.
       -- iPureIntro. econstructor.
     * iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
       iDestruct (step_tr_rvalof with "HG") as (le') "[% [% %]]"; eauto. subst.
       iExists _. iSplit.
       -- iPureIntro. right; split. simpl. rewrite app_ass; rewrite Kseqlist_app. eexact H8. lia.
       -- iPureIntro. econstructor.
     * iDestruct (tr_simple_lvalue with "HE") as "[% [% %]]"; eauto.
       subst. simpl. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_two. constructor. eapply step_make_set; eauto. traceEq.
       -- iPureIntro. econstructor.

 (* comma *)
 - inv H9; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H1.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H1 with "HA") as "HA". 
     iDestruct (H2 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H1. clear H2.
     simpl. iDestruct "P" as (sl0 a2 sl3) ">P"; norm_all.
     iDestruct (tr_simple_rvalue with "HE") as "%"; eauto. iClear "HE".
     iExists _. iSplit.
     * iPureIntro. right; split. apply star_refl. apply plus_lt_compat_r.
        apply (leftcontext_size _ _ _ H). simpl. omega.
     * iConstructor. iIntros "[HB HD]". iDestruct ("HD" $! r2 with "[]") as "HD"; eauto.
       subst. iApply (locally_out with "HD"). simpl. iFrame.

 (* paren *)
 - inv H9; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H2.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H2 with "HA") as "HA". 
     iDestruct (H3 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H2. clear H3.
     simpl. iDestruct "P" as ">P". destruct dst'; norm_all.
     * iDestruct (tr_simple_rvalue with "HE") as (b) "[% [% %]]"; eauto. subst; simpl.
       iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor. apply star_one. econstructor.
          econstructor; eauto. rewrite <- H5; eauto. traceEq.
       -- iDestruct ("R" $! (Eval v ty) with "[]") as "R"; eauto.
          iDestruct (tr_expr_dest with "HE") as ">HA".
          iDestruct (locally_set with "HA R") as "[R HA]".
          iConstructor. iIntros "[HA HB]". change sl2 with (nil ++ sl2).
          iApply (locally_out with "HA"). simpl. iModIntro. iSplitL "HB"; eauto.
          iIntros "*". iApply locally_conseq_pure. intros. econstructor. apply H2.
          iApply locally_finish. iFrame.
     * iDestruct (tr_simple_rvalue with "P") as "%"; eauto. subst; simpl.
       iExists _. iSplit.
       -- iPureIntro. right; split. apply star_refl. simpl. apply plus_lt_compat_r.
          apply (leftcontext_size _ _ _ H). simpl. lia.
       -- iConstructor. iIntros "[HA HB]".
          iDestruct ("HB" $! (Eval v ty) with "[]") as "HC"; eauto.
          change sl2 with (nil ++ sl2).
          iApply (locally_out with "HC"). simpl. eauto.
     * destruct (Pos.eq_dec x0 (sd_temp sd)); norm_all.
       -- subst. 
          iDestruct (tr_simple_rvalue with "P") as (b) "[% [% %]]"; eauto. subst; simpl.
          iExists _. iSplit.
          ++ iPureIntro. left. eapply plus_left. constructor. apply star_one. econstructor.
             econstructor; eauto. rewrite <- H3; eauto. traceEq.
          ++ iDestruct ("R" $! (Eval v ty) with "[]") as "R"; eauto.
             iDestruct (tr_expr_dest with "P") as ">HA".
             iDestruct (locally_set with "HA R") as "[R HA]".
             iConstructor. iIntros "[HA HB]". change sl2 with (nil ++ sl2). 
             iApply (locally_out with "HA"). simpl. iModIntro. iSplit; iFrame. iExists _.
             iSplitL; auto. iIntros "*". iApply locally_conseq_pure. intros. econstructor. apply H2.
             iApply locally_finish. iFrame. eauto.
       -- iDestruct (tr_simple_rvalue with "HE") as (b) "[% [% %]]"; eauto. subst; simpl.
          iExists _. iSplit.
          ++ iPureIntro. left. eapply plus_left. constructor. apply star_one. econstructor.
             econstructor; eauto. rewrite <- H3; eauto. traceEq.
          ++ iDestruct ("R" $! (Eval v ty) with "[]") as "R"; eauto.
             iDestruct (tr_expr_dest with "HE") as ">HA".
             iDestruct (locally_set with "HA R") as "[R HA]".
             iConstructor. iIntros "[HA [HB HC]]". change sl2 with (nil ++ sl2). 
             iApply (locally_out with "HB"). simpl. iModIntro. iSplit; iFrame. iExists _.
             iSplitL "HC"; auto. iIntros "*". iApply locally_conseq_pure. intros. econstructor.
             apply H2. iApply locally_finish. iFrame. eauto.
          
 (* call *)
 - inv H12; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H5.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H5 with "HA") as "HA". 
     iDestruct (H6 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H5. clear H6.
     simpl. iDestruct "P" as ">P". destruct dst'; norm_all.
     * iDestruct (tr_simple_rvalue with "HI") as "[% [% %]]"; eauto.
       iDestruct (tr_simple_exprlist with "HK []") as "[% %]"; eauto.
       subst. simpl. exploit functions_translated; eauto. intros [tfd [J K]].
       iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor. apply star_one.
          econstructor; eauto. rewrite <- H9; eauto.
          exploit type_of_fundef_preserved; eauto. congruence. traceEq.
       -- iClear "HI HK HE". iStopProof. apply instance_heap. intros.
          econstructor; eauto. econstructor; eauto. intros. econstructor.
          apply soundness2. apply soundness3 in H5. iIntros "HA".
          iDestruct (H5 with "HA") as "[HA HD]".
          iDestruct ("HD" $! (Eval v ty) with "[]") as "HD"; eauto.
          change sl2 with (nil ++ sl2). unfold set_opttemp.
          iDestruct (locally_set with "[HA] HD") as "[HD HA]"; auto.
          iApply (locally_out with "HD"). iModIntro. iSplitL "HA".
          iIntros. iApply locally_conseq_pure. intros. econstructor. eapply H6.
          iApply locally_finish. iFrame. eauto.
     * iDestruct (tr_simple_rvalue with "HE") as "[% [% %]]"; eauto.
       iDestruct (tr_simple_exprlist with "HG []") as "[% %]"; eauto.
       subst. simpl. exploit functions_translated; eauto. intros [tfd [J K]].
       iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor. apply star_one.
          econstructor; eauto. rewrite <- H8; eauto.
          exploit type_of_fundef_preserved; eauto. congruence. traceEq.
       -- iStopProof. apply instance_heap. intros.
          econstructor; eauto. econstructor; eauto. intros. econstructor.
          apply soundness2. apply soundness3 in H5. iIntros "HA".
          iDestruct (H5 with "HA") as "[HA [HB HC]]".
          iDestruct ("HC" $! (Eval v ty) with "[]") as "HD"; eauto.
          change sl2 with (nil ++ sl2). unfold set_opttemp.
          iApply (locally_out with "HD"). eauto.
     * iDestruct (tr_simple_rvalue with "HI") as "[% [% %]]"; eauto.
       iDestruct (tr_simple_exprlist with "HK []") as "[% %]"; eauto.
       subst. simpl. exploit functions_translated; eauto. intros [tfd [J K]].
       iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor. apply star_one.
          econstructor; eauto. rewrite <- H9; eauto.
          exploit type_of_fundef_preserved; eauto. congruence. traceEq.
       -- iClear "HI HK". iStopProof. apply instance_heap. intros.
          econstructor; eauto. econstructor; eauto. intros. econstructor.
          apply soundness2. apply soundness3 in H5. iIntros "HA".
          iDestruct (H5 with "HA") as "[HA [HB HD]]".
          iDestruct ("HD" $! (Eval v ty) with "[]") as "HD"; eauto.
          change sl2 with (nil ++ sl2). unfold set_opttemp.
          iDestruct (locally_set with "[HB] HD") as "[HD HB]"; auto.
          iApply (locally_out with "HD"). iModIntro. iSplit; iFrame. iExists _. iSplitL "HB".
          iIntros. iApply locally_conseq_pure. intros. econstructor. eapply H6.
          iApply locally_finish. iFrame. eauto.

 (* ebuiltin *)
 - inv H9; simpl in *; auto.
   + inv H; discriminate.
   + exploit tr_expr_leftcontext; eauto.
     intro. apply soundness3 in H2.
     apply (soundness1 tmps). iIntros "HA". iDestruct (H2 with "HA") as "HA". 
     iDestruct (H3 with "HA") as (dst' sl1 sl2 a') "[P [% R]]". clear H2. clear H3.
     simpl. iDestruct "P" as ">P". destruct dst'; norm_all.
     * iDestruct (tr_simple_exprlist with "HG []") as "[% %]"; eauto.
       subst; simpl. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor.  apply star_one. econstructor; eauto.
          eapply external_call_symbols_preserved; eauto. apply senv_preserved. traceEq.
       -- iClear "HE HG". iConstructor. iIntros "[HB HD]".
          iDestruct ("HD" $! (Eval vres ty) with "[]") as "HD"; eauto.
          change sl2 with (nil ++ sl2). unfold set_opttemp.
          iDestruct (locally_set with "[HB] HD") as "[HD HB]"; auto.
          iApply (locally_out with "HD"). iModIntro. iSplitL "HB"; eauto.
          iIntros. iApply locally_conseq_pure. intros. econstructor. eapply H2.
          iApply locally_finish. iFrame.
     * iDestruct (tr_simple_exprlist with "HE []") as "[% %]"; eauto.
       subst. simpl. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor. apply star_one. econstructor; eauto.
          eapply external_call_symbols_preserved; eauto. apply senv_preserved. traceEq.
       -- iClear "HE". iConstructor. iIntros "HD".
          iDestruct ("HD" $! (Eval vres ty) with "[]") as "HD"; eauto.
          change sl2 with (nil ++ sl2). unfold set_opttemp.
          iApply (locally_out with "HD"). iModIntro. eauto.
     * iDestruct (tr_simple_exprlist with "HG []") as "[% %]"; eauto.
       subst; simpl. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. constructor.  apply star_one. econstructor; eauto.
          eapply external_call_symbols_preserved; eauto. apply senv_preserved. traceEq.
       -- iClear "HG". iConstructor. iIntros "[HA [HB HD]]".
          iDestruct ("HD" $! (Eval vres ty) with "[]") as "HD"; eauto.
          change sl2 with (nil ++ sl2). unfold set_opttemp.
          iDestruct (locally_set with "[HB] HD") as "[HD HB]"; auto.
          iApply (locally_out with "HD"). iModIntro. iSplit; iFrame. iExists _. iSplitL "HB"; eauto.
          iIntros. iApply locally_conseq_pure. intros. econstructor. eapply H2.
          iApply locally_finish. iFrame. eauto.
Qed.

(** Forward simulation for statements. *)

Lemma tr_top_val_for_val_inv:
  forall e le m v ty sl a tmp,
  tr_top tge e le m For_val (Csyntax.Eval v ty) sl a tmp ->
  sl = nil /\ typeof a = ty /\ eval_expr tge e le m a v.
Proof.
  intros. inv H; eauto. apply (soundness1 tmp). iIntros "HA". apply soundness3 in H0.
  iDestruct (H0 with "HA") as ">[HA [% %]]".
  repeat iSplit; eauto. iDestruct (locally_delete with "HA") as "HA". iFrame.
Qed.
    
Lemma alloc_variables_preserved:
  forall e m params e' m',
  Csem.alloc_variables ge e m params e' m' ->
  alloc_variables tge e m params e' m'.
Proof.
  induction 1; econstructor; eauto. rewrite comp_env_preserved; auto.
Qed.

Lemma bind_parameters_preserved:
  forall e m params args m',
  Csem.bind_parameters ge e m params args m' ->
  bind_parameters tge e m params args m'.
Proof.
  induction 1; econstructor; eauto. inv H0.
- eapply assign_loc_value; eauto.
- inv H4. eapply assign_loc_value; eauto.
- rewrite <- comp_env_preserved in *. eapply assign_loc_copy; eauto.
Qed.

Lemma blocks_of_env_preserved:
  forall e, blocks_of_env tge e = Csem.blocks_of_env ge e.
Proof.
  intros; unfold blocks_of_env, Csem.blocks_of_env.
  unfold block_of_binding, Csem.block_of_binding.
  rewrite comp_env_preserved. auto.
Qed.

Lemma red_absorb : forall P tmp, (<absorb> \⌜P⌝ : iProp) () tmp -> P.
Proof.
  intros. apply soundness3 in H. apply (soundness1 tmp).
  iIntros "HA". iDestruct (H with "HA") as ">$".
Qed.

Lemma red_pure : forall P tmp, (⌜P⌝ : iProp) () tmp -> P.
Proof.
  intros. apply soundness3 in H. apply (soundness1 tmp).
  iIntros "HA". iDestruct (H with "HA") as "$".
Qed.
  
Lemma sstep_simulation:
  forall S1 t S2, Csem.sstep ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* do 1 *)
  inv H6. inv H0.
  econstructor; split.
  right; split. apply push_seq.
  simpl. unfold lt. rewrite plus_n_Sm. reflexivity. 
  econstructor; eauto. constructor. auto.
  (* do 2 *)
  inv H7. inv H6. simpl in H. apply red_absorb in H. subst.
  econstructor; split.
  right; split. apply star_refl. simpl. lia.
  econstructor; eauto. constructor.
  (* seq *)
  inv H6. econstructor; split. left. apply plus_one. constructor.
  econstructor; eauto. constructor; auto.
(* skip seq *)
  inv H6; inv H7. econstructor; split.
  left. apply plus_one; constructor.
  econstructor; eauto.
(* continue seq *)
  inv H6; inv H7. econstructor; split.
  left. apply plus_one; constructor.
  econstructor; eauto. constructor.
(* break seq *)
  inv H6; inv H7. econstructor; split.
  left. apply plus_one; constructor.
  econstructor; eauto. constructor.
(* ifthenelse *)
  inv H6.
(* ifthenelse empty *)
  inv H3. econstructor; split.
  left. eapply plus_left. constructor. apply push_seq.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
(* ifthenelse non empty *)
  inv H2. econstructor; split.
  left. eapply plus_left. constructor. apply push_seq. traceEq.
  econstructor; eauto. econstructor; eauto.
(* ifthenelse *)
  inv H8.
(* ifthenelse empty *)
  exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split; simpl.
  right. destruct b; econstructor; eauto.
  eapply star_left. apply step_skip_seq. econstructor. traceEq.
  eapply star_left. apply step_skip_seq. econstructor. traceEq.
  destruct b; econstructor; eauto. econstructor; eauto. econstructor; eauto.
  (* ifthenelse non empty *)
  exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split.
  left. eapply plus_two. constructor.
  apply step_ifthenelse with (v1 := v) (b := b); auto. traceEq.
  destruct b; econstructor; eauto.
(* while *)
  inv H6. inv H1. econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_left. constructor.
  apply push_seq.
  reflexivity. traceEq. rewrite Kseqlist_app.
  econstructor; eauto. simpl.  econstructor; eauto. econstructor; eauto.
(* while false *)
  inv H8.
  exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
  eapply star_two. constructor. apply step_break_loop1.
  reflexivity. reflexivity. traceEq.
  constructor; auto. constructor.
(* while true *)
  inv H8.
  exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := true); auto.
  constructor.
  reflexivity. traceEq.
  constructor; auto. constructor; auto.
(* skip-or-continue while *)
  assert (ts = Sskip \/ ts = Scontinue). destruct H; subst s0; inv H7; auto.
  inv H8.
  econstructor; split.
  left. eapply plus_two. apply step_skip_or_continue_loop1; auto.
  apply step_skip_loop2. traceEq.
  constructor; auto. constructor; auto.
(* break while *)
  inv H6. inv H7.
  econstructor; split.
  left. apply plus_one. apply step_break_loop1.
  constructor; auto. constructor.

(* dowhile *)
  inv H6.
  econstructor; split.
  left. apply plus_one. apply step_loop.
  constructor; auto. constructor; auto.
(* skip_or_continue dowhile *)
  assert (ts = Sskip \/ ts = Scontinue). destruct H; subst s0; inv H7; auto.
  inv H8. inv H4.
  econstructor; split.
  left. eapply plus_left. apply step_skip_or_continue_loop1. auto.
  apply push_seq.
  traceEq.
  rewrite Kseqlist_app.
  econstructor; eauto. simpl. econstructor; auto. econstructor; eauto.
(* dowhile false *)
  inv H8.
  exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := false); auto.
  constructor.
  reflexivity. traceEq.
  constructor; auto. constructor.
(* dowhile true *)
  inv H8.
  exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := true); auto.
  constructor.
  reflexivity. traceEq.
  constructor; auto. constructor; auto.
(* break dowhile *)
  inv H6. inv H7.
  econstructor; split.
  left. apply plus_one. apply step_break_loop1.
  constructor; auto. constructor.

(* for start *)
  inv H7. congruence.
  econstructor; split.
  left; apply plus_one. constructor.
  econstructor; eauto. constructor; auto. econstructor; eauto.
(* for *)
  inv H6; try congruence. inv H2.
  econstructor; split.
  left. eapply plus_left. apply step_loop.
  eapply star_left. constructor. apply push_seq.
  reflexivity. traceEq.
  rewrite Kseqlist_app. econstructor; eauto. simpl. constructor; auto. econstructor; eauto.
(* for false *)
  inv H8. exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
  eapply star_two. constructor. apply step_break_loop1.
  reflexivity. reflexivity. traceEq.
  constructor; auto. constructor.
(* for true *)
  inv H8. exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := true); auto.
  constructor.
  reflexivity. traceEq.
  constructor; auto. constructor; auto.
(* skip_or_continue for3 *)
  assert (ts = Sskip \/ ts = Scontinue). destruct H; subst x; inv H7; auto.
  inv H8.
  econstructor; split.
  left. apply plus_one. apply step_skip_or_continue_loop1. auto.
  econstructor; eauto. econstructor; auto.
(* break for3 *)
  inv H6. inv H7.
  econstructor; split.
  left. apply plus_one. apply step_break_loop1.
  econstructor; eauto. constructor.
(* skip for4 *)
  inv H6. inv H7.
  econstructor; split.
  left. apply plus_one. constructor.
  econstructor; eauto. constructor; auto.


(* return none *)
  inv H7. econstructor; split.
  left. apply plus_one. econstructor; eauto. rewrite blocks_of_env_preserved; eauto.
  constructor. apply match_cont_call; auto.
(* return some 1 *)
  inv H6. inv H0. econstructor; split.
  left; eapply plus_left. constructor. apply push_seq. traceEq.
  econstructor; eauto. constructor. auto.
(* return some 2 *)
  inv H9. exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split.
  left. eapply plus_two. constructor. econstructor. eauto.
  erewrite function_return_preserved; eauto. rewrite blocks_of_env_preserved; eauto.
  eauto. traceEq.
  constructor. apply match_cont_call; auto.
(* skip return *)
  inv H8.
  assert (is_call_cont tk). inv H9; simpl in *; auto.
  econstructor; split.
  left. apply plus_one. apply step_skip_call; eauto. rewrite blocks_of_env_preserved; eauto.
  constructor. auto.
  
(* switch *)
  inv H6. inv H1.
  econstructor; split.
  left; eapply plus_left. constructor. apply push_seq. traceEq.
  econstructor; eauto. constructor; auto.
(* expr switch *)
  inv H8. exploit tr_top_val_for_val_inv; eauto. intros [P0 [P1 P2]]. subst.
  econstructor; split.
  left; eapply plus_two. constructor. econstructor; eauto. traceEq.
  econstructor; eauto.
  apply tr_seq_of_labeled_statement. apply tr_select_switch. auto.
  constructor; auto.

(* skip-or-break switch *)
  assert (ts = Sskip \/ ts = Sbreak). destruct H; subst x; inv H7; auto.
  inv H8.
  econstructor; split.
  left; apply plus_one. apply step_skip_break_switch. auto.
  constructor; auto. constructor.

(* continue switch *)
  inv H6. inv H7.
  econstructor; split.
  left; apply plus_one. apply step_continue_switch.
  constructor; auto. constructor.

(* label *)
  inv H6. econstructor; split.
  left; apply plus_one. constructor.
  constructor; auto.

(* goto *)
  inv H7.
  inversion H6; subst.
  exploit tr_find_label. eauto. apply match_cont_call. eauto.
  instantiate (1 := lbl). rewrite H.
  intros [ts' [tk' [P [Q R]]]].
  econstructor; split.
  left. apply plus_one. econstructor; eauto.
  econstructor; eauto.

(* internal function *)
  inv H7. inversion H3; subst.
  econstructor; split.
  left; apply plus_one. eapply step_internal_function. econstructor.
  rewrite H6; rewrite H7; auto.
  rewrite H6; rewrite H7. eapply alloc_variables_preserved; eauto.
  rewrite H6. eapply bind_parameters_preserved; eauto.
  eauto.
  constructor; auto.

(* external function *)
  inv H5.
  econstructor; split.
  left; apply plus_one. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.

(* return *)
  inv H3.
  econstructor; split.
  left; apply plus_one. constructor.
  econstructor; eauto.
Qed.

(** Semantic preservation *)

Theorem simulation:
  forall S1 t S2, Cstrategy.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  ∃ S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
      /\ match_states S2 S2'.
Proof.
  intros S1 t S2 STEP. destruct STEP.
  apply estep_simulation; auto.
  apply sstep_simulation; auto.
Qed.
  

Lemma transl_initial_states:
  forall S,
  Csem.initial_state prog S ->
  exists S',  Clight.initial_state tprog S' /\ match_states S S'.
Proof.
intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_match (proj1 TRANSL)); eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto. 
  destruct TRANSL. destruct H as (A & B & C). simpl in B. auto. 
  eexact FIND.
  rewrite <- H3. apply type_of_fundef_preserved. auto.
  constructor. auto. constructor.
Qed.

Lemma transl_final_states:
  ∀ S S' r,
  match_states S S' -> Csem.final_state S r -> Clight.final_state S' r.
Proof.
  intros. inv H0. inv H. inv H4. constructor.
Qed.

Theorem transl_program_correct:
  forward_simulation (Cstrategy.semantics prog) (Clight.semantics1 tprog).
Proof.
  eapply forward_simulation_star_wf with (order := ltof _ measure).
  eapply senv_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  apply well_founded_ltof.
  exact simulation.
Qed.

End PRESERVATION.

(** ** Commutation with linking *)

Instance TransfSimplExprLink : TransfLink match_prog.
Proof.
  red; intros. eapply Ctypes.link_match_program; eauto. 
- intros.
Local Transparent Linker_fundef.
  simpl in *; unfold link_fundef in *. inv H3; inv H4; try discriminate.
  destruct ef; inv H2. exists (Internal tf); split; auto. constructor; auto.
  destruct ef; inv H2. exists (Internal tf); split; auto. constructor; auto.
  destruct (external_function_eq ef ef0 && typelist_eq targs targs0 &&
            type_eq tres tres0 && calling_convention_eq cconv cconv0); inv H2.
  exists (External ef targs tres cconv); split; auto. constructor.
Qed.
