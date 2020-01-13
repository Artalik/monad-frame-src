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
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Ctypes Cop Csyntax Csem Cstrategy Clight.
Import Maps.PTree.
Require Import MoSel SimplExpr SimplExprspec.

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

  Lemma tr_simple_nil:
    (forall r dst sl le a, tr_expr le dst r (sl,a) -∗
                                   ⌜ dst = For_val \/ dst = For_effects ⌝ -∗ ⌜ simple r = true ⌝ -∗ ⌜sl = nil ⌝)
    /\(forall rl le sl al, tr_exprlist le rl (sl,al) -∗
                                       ⌜ simplelist rl = true ⌝ -∗ ⌜ sl = nil ⌝).
  Proof.
    assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil).
    intros. destruct H; subst dst; auto.
    apply tr_expr_exprlist; intros; simpl in *; try discriminate; auto.
    - destruct dst; eauto.
      + iIntros "[_ [HA [% %]]] _ _". eauto.
      + iIntros "[_ %] % _". eauto.
      + iIntros "[_ HA] % _". destruct a0; discriminate.
    - iIntros "[_ [_ %]]". iPureIntro. intros. inversion H. destruct dst; auto.
    - iIntros "[_ HA]". iDestruct "HA" as (sla2) "[HA [HB %]]".
      rewrite (surjective_pairing sla2). iIntros.
      iDestruct (H with "[HA]") as "HC". iApply "HA".
      destruct dst.
      + iDestruct ("HC" $! a0 a1) as "HA". simpl in *. inversion H0. rewrite app_nil_r. iApply "HA". 
      + iDestruct ("HC" with "[]") as "HA"; eauto. inversion H0. rewrite app_nil_r.
        iApply ("HA" $! a1).
      + destruct a0; discriminate.
    - iIntros "[_ HA] % %". iDestruct "HA" as (sla2 sl3) "[HA [HB [HC %]]]".
      rewrite (surjective_pairing sla2).
      iDestruct (H with "HA") as "HD".
      apply andb_true_iff in a1 as (P0&P1).
      unfold tr_rvalof. apply negb_true_iff in P1. rewrite P1.
      iDestruct "HB" as "%". inversion H1; subst. destruct dst; simpl in *; try rewrite app_nil_r.
      + iApply ("HD" $! a0 P0).
      + iApply "HD"; eauto.
      + destruct a0; discriminate.
    - iIntros "[_ HA] % %". iDestruct "HA" as (sla2) "[HA [HB %]]".
      rewrite (surjective_pairing sla2).
      iDestruct (H with "HA") as "HD".
      inversion H0.
      destruct dst; simpl in *; try (rewrite app_nil_r; iApply "HD";eauto); destruct a0; discriminate.
    - iIntros "[_ HA] % %". iDestruct "HA" as (sla2) "[HA [HB %]]".
      rewrite (surjective_pairing sla2).
      iDestruct (H with "HA") as "HD".
      inversion H0.
      destruct dst; simpl in *; try (rewrite app_nil_r; iApply "HD";eauto); destruct a0; discriminate.
    - iIntros "[_ HA] % %". iDestruct "HA" as (sla2) "[HA [HB %]]".
      rewrite (surjective_pairing sla2).
      iDestruct (H with "HA") as "HD".
      inversion H0.
      destruct dst; simpl in *; try (rewrite app_nil_r; iApply "HD";eauto); destruct a0; discriminate.
    - iIntros "[_ HA] % %". iDestruct "HA" as (sla2 sl3) "[HA [HB [HC %]]]".
      rewrite (surjective_pairing sla2).
      iDestruct (H with "HA") as "HD".
      rewrite (surjective_pairing sl3).
      iDestruct (H0 with "HB") as "HB".
      apply andb_true_iff in a1 as (P0&P1).
      inversion H1.
      iDestruct ("HD" with "[]") as "%"; eauto.
      iDestruct ("HB" with "[]") as "%"; eauto.
      iPureIntro. rewrite (H2 P0). rewrite (H5 P1).
      destruct a0; subst; auto.
    - iIntros "[_ HA] % %". iDestruct "HA" as (sla2) "[HA [HB %]]".
      rewrite (surjective_pairing sla2).
      iDestruct (H with "HA") as "HD".
      inversion H0.
      destruct dst; simpl in *; try (rewrite app_nil_r; iApply "HD";eauto); destruct a0; discriminate.
    - iIntros "[_ [HA %]] % %". inversion H.
      destruct dst; eauto.
    - iIntros "[_ [HA %]] % %". inversion H.
      destruct dst; eauto.
    - iIntros "[_ %] %". inversion H.
    - iIntros "[_ %] %". inversion H; eauto.
    - iIntros "[_ HA] %". iDestruct "HA" as (sla2 slal3) "[HA [HB %]]".
      rewrite (surjective_pairing sla2).
      iDestruct (H with "[HA]") as "HC". iApply "HA".
      rewrite (surjective_pairing slal3).
      iDestruct (H0 with "[HB]") as "HA". iApply "HB".
      iDestruct ("HC" with "[]") as "%"; eauto.
      apply andb_true_iff in a as (P0&P1).
      iDestruct ("HA" with "[]") as "%"; eauto.
      iPureIntro. inversion H1. rewrite (H2 P0). rewrite H3. eauto.
  Qed.

  Lemma tr_simple_expr_nil:
    (forall r dst sl le a, tr_expr le dst r (sl,a) -∗
                                   ⌜ dst = For_val \/ dst = For_effects ⌝ -∗ ⌜ simple r = true ⌝ -∗ ⌜sl = nil ⌝).
  Proof (proj1 tr_simple_nil).

  Lemma tr_simple_exprlist_nil:
    (forall rl le sl al, tr_exprlist le rl (sl,al) -∗
                                     ⌜ simplelist rl = true ⌝ -∗ ⌜ sl = nil ⌝).
  Proof (proj2 tr_simple_nil).

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

  (** Evaluation of simple expressions and of their translation *)

  Lemma tr_simple:
    forall e m,
      (forall r v,
          eval_simple_rvalue ge e m r v ->
          forall le dst sl a,
            (tr_expr le dst r (sl,a)) -∗
                                      ⌜ match dst with
                                        | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
                                        | For_effects => sl = nil
                                        | For_set sd =>
                                          exists b, sl = do_set sd b
                                                    /\ Csyntax.typeof r = typeof b
                                                    /\ eval_expr tge e le m b v
                                        end⌝)
      /\
      (forall l b ofs,
          eval_simple_lvalue ge e m l b ofs ->
          forall le sl a, tr_expr le For_val l (sl,a) -∗                                               
                                  ⌜ sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs ⌝).
  Proof.
    Opaque makeif.
    intros e m.
    apply (eval_simple_rvalue_lvalue_ind ge e m); intros; simpl.
    (* value *)
    - destruct dst; simpl in *; auto.
      + iIntros "[_ [HA [% %]]]". repeat (iSplit; auto). iApply "HA". eauto.
      + iIntros "[_ HA]"; auto. 
      + iIntros "[_ HA]". iDestruct "HA" as (a0) "[HA [% %]]". subst. iExists a0. repeat iSplit; eauto.
        iApply "HA". auto.
    (* rvalof *)
    - destruct dst; subst; simpl in *.
      + iIntros "[_ HA]". iDestruct "HA" as (sla2 sl3) "[HA [HB [_ %]]]".
        rewrite (surjective_pairing sla2).
        iDestruct (H0 with "HA") as "[% [% %]]".
        unfold tr_rvalof. rewrite H2. iDestruct "HB" as "%". inversion H7; subst.
        iPureIntro. repeat split; auto. do 2 rewrite app_nil_r. apply H4.
        eapply eval_Elvalue; eauto.
        exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H2.
        intros (P0&P1). rewrite <- H5. assumption.
      + iIntros "[_ HA]". iDestruct "HA" as (sla2 sl3) "[HA [HB [_ %]]]".
        rewrite (surjective_pairing sla2).
        iDestruct (H0 with "HA") as "[% [% %]]".
        unfold tr_rvalof. rewrite H2. iDestruct "HB" as "%". inversion H7; subst.
        iPureIntro. do 2 rewrite app_nil_r. apply H4.
      + iIntros "[_ HA]". iDestruct "HA" as (sla2 sl3) "[HA [HB [_ %]]]". iExists a.
        rewrite (surjective_pairing sla2).
        iDestruct (H0 with "HA") as "[% [% %]]".
        unfold tr_rvalof. rewrite H2. iDestruct "HB" as "%". inversion H7; subst.
        iPureIntro. repeat split; auto. rewrite H4. do 2 rewrite app_nil_l. reflexivity.
        eapply eval_Elvalue; eauto.
        exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H2.
        intros (P0&P1). rewrite <- H5. apply P1.
    - iIntros "[_ HA]". iDestruct "HA" as (sla2) "[HA [HB %]]". rewrite (surjective_pairing sla2).
      iDestruct (H0 with "HA") as "[% [% %]]". inversion H1.
      destruct dst; simpl in *; subst.
      + iPureIntro. repeat split; auto.
        * rewrite app_nil_r. apply H2.
        * rewrite (typeof_Eaddrof' sla2.2 ty). reflexivity.
        * apply eval_Eaddrof'; auto.
      + iPureIntro. rewrite app_nil_r. apply H2.
      + iExists (Eaddrof' sla2.2 ty). iPureIntro. repeat split.
        * rewrite H2. rewrite app_nil_l. reflexivity.
        * rewrite (typeof_Eaddrof' sla2.2 ty). reflexivity.
        * apply eval_Eaddrof'; auto.
    - iIntros "[_ HA]". iDestruct "HA" as (sla2) "[HA [HB %]]". rewrite (surjective_pairing sla2).
      iDestruct (H0 with "HA") as "[% [% %]]". inversion H2.
      destruct dst; simpl in *; subst.
      + iPureIntro. repeat split; auto.
        * rewrite app_nil_r. apply H3.
        * rewrite H4 in H1. econstructor; eauto.
      + iPureIntro. rewrite app_nil_r. apply H3.
      + iExists (Eunop op0 sla2.2 ty). iPureIntro. repeat split.
        * rewrite H3. rewrite app_nil_l. reflexivity.
        * rewrite H4 in H1. econstructor; eauto.
    - iIntros "[_ HA]". iDestruct "HA" as (sla2 sla3) "[HA [HB [HC %]]]". rewrite (surjective_pairing sla2).
      iDestruct (H0 with "HA") as "[% [% %]]". rewrite (surjective_pairing sla3).
      iDestruct (H2 with "HB") as "[% [% %]]". inversion H4.
      destruct dst; simpl in *; subst; rewrite H5 H8; try iExists (Ebinop op0 sla2.2 sla3.2 ty);
        do 2 rewrite app_nil_l; iPureIntro; repeat split; auto; econstructor; eauto; rewrite <- H6;
          auto; rewrite <- H9; rewrite comp_env_preserved; apply H3.
    - iIntros "[_ HA]". iDestruct "HA" as (sla2)  "[HA [HB %]]". rewrite (surjective_pairing sla2).
      iDestruct (H0 with "HA") as "[% [% %]]". inversion H2.
      destruct dst; simpl in *; subst; rewrite H3; try iExists (Ecast sla2.2 ty); iPureIntro;
        rewrite app_nil_l; repeat split; auto; econstructor; eauto; rewrite <- H4; auto.
    - iIntros "[_ [HA %]]". inversion H.
      destruct dst; simpl in *; subst; try iExists (Esizeof ty1 ty); iPureIntro; repeat split; eauto;
        pose (P := comp_env_preserved); simpl in P; rewrite <- P; apply eval_Esizeof.
    - iIntros "[_ [HA %]]". inversion H.
      destruct dst; simpl in *; subst; try iExists (Ealignof ty1 ty); iPureIntro; repeat split; eauto;
        pose (P := comp_env_preserved); simpl in P; rewrite <- P; constructor.
    - iIntros "[_ %]". contradiction H.
    - iIntros "[_ [_ %]]". inversion H0. iPureIntro. repeat split; auto. constructor. apply H.
    - iIntros "[_ [_ %]]". inversion H1. iPureIntro. repeat split; auto.
      apply eval_Evar_global; auto.
      rewrite symbols_preserved; auto.
    - iIntros "[_ HA]". iDestruct "HA" as (sla2)  "[HA [HB %]]". rewrite (surjective_pairing sla2).
      iDestruct (H0 with "HA") as "[% [% %]]". inversion H1. iPureIntro. subst. repeat split.
      rewrite app_nil_r. apply H2. rewrite typeof_Ederef'; auto. apply eval_Ederef'; auto. 
    - iIntros "[_ HA]". iDestruct "HA" as (sla2)  "[HA [HB %]]". rewrite (surjective_pairing sla2).
      iDestruct (H0 with "HA") as "[% [% %]]". inversion H4. subst. iPureIntro. repeat split.
      rewrite app_nil_r. apply H5. rewrite <- comp_env_preserved in *. rewrite H6 in H1.
      eapply eval_Efield_struct; eauto.
    - iIntros "[_ HA]". iDestruct "HA" as (sla2)  "[HA [HB %]]". rewrite (surjective_pairing sla2).
      iDestruct (H0 with "HA") as "[% [% %]]". inversion H3. subst. iPureIntro. repeat split.
      rewrite app_nil_r. apply H4. rewrite <- comp_env_preserved in *. rewrite H5 in H1.
      eapply eval_Efield_union; eauto.
Qed.
   
Lemma tr_simple_rvalue:
  forall e m r v,
    eval_simple_rvalue ge e m r v ->
  forall le dst sl a,
  (tr_expr le dst r (sl,a)) -∗
  ⌜match dst with
  | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
  | For_effects => sl = nil
  | For_set sd =>
      exists b, sl = do_set sd b
             /\ Csyntax.typeof r = typeof b
             /\ eval_expr tge e le m b v
  end⌝.
Proof.
  intros e m. exact (proj1 (tr_simple e m)).
Qed.

Lemma tr_simple_lvalue:
  forall e m l b ofs,
  eval_simple_lvalue ge e m l b ofs ->
  forall le sl a, tr_expr le For_val l (sl,a) -∗                                               
  ⌜ sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs ⌝.
Proof.
  intros e m. exact (proj2 (tr_simple e m)).
Qed.

Lemma tr_simple_exprlist:
  forall le rl sl al,
  tr_exprlist le rl (sl,al) -∗
  ∀ e m tyl vl,
  ⌜ eval_simple_list ge e m rl tyl vl ⌝ -∗
  ⌜ sl = nil /\ eval_exprlist tge e le m al tyl vl ⌝.
Proof.
  induction rl.
  - iIntros. destruct a. inversion H0.
    iPureIntro. repeat split; eauto. inversion a0. constructor.
  - simpl. iIntros (? ?) "[_ HA]". iIntros (? ? ? ?) "%". iDestruct "HA" as (sla2 slal3) "[HA [HB %]]".
    rewrite (surjective_pairing slal3).
    iDestruct (IHrl with "HB") as "HC".
    inversion a3. subst.
    iDestruct ("HC" with "[]") as "[% %]"; eauto.
    epose (P := tr_simple_rvalue _ _ _ _ H2).
    rewrite (surjective_pairing sla2).
    iDestruct (P with "HA") as "[% [% %]]".
    iPureIntro. inversion H. subst. split.
    + rewrite H4 H0; auto.
    + econstructor; eauto. rewrite <- H5. eauto.
Qed.

(** Commutation between the translation of expressions and left contexts. *)

Lemma typeof_context:
  forall k1 k2 C, leftcontext k1 k2 C ->
  forall e1 e2, Csyntax.typeof e1 = Csyntax.typeof e2 ->
  Csyntax.typeof (C e1) = Csyntax.typeof (C e2).
Proof.
  induction 1; intros; auto.
Qed.

Scheme leftcontext_ind2 := Minimality for leftcontext Sort Prop
  with leftcontextlist_ind2 := Minimality for leftcontextlist Sort Prop.
Combined Scheme leftcontext_leftcontextlist_ind from leftcontext_ind2, leftcontextlist_ind2.
Notation "\s l" := (∃ t, l ↦ t) (at level 10).
Lemma tr_expr_leftcontext_rec:
 (
  forall from to C, leftcontext from to C ->
  forall le e dst sl a,
  tr_expr le dst (C e) (sl,a) -∗
  ∃ dst' sl1 sl2 a',
  tr_expr le dst' e (sl1,a')
  ∗ ⌜ sl = sl1 ++ sl2 ⌝
  ∗ (∀ le' e' sl3,
        (tr_expr le' dst' e' (sl3,a') ∧
        (∀ id, (\s id -∗ False) -∗ ⌜ le'!id = le!id ⌝)) -∗
        \⌜ Csyntax.typeof e' = Csyntax.typeof e ⌝ -∗
        tr_expr le' dst (C e') ((sl3 ++ sl2),a))
 ) /\ (
  forall from C, leftcontextlist from C ->
  forall le e sl a,
  tr_exprlist le (C e) (sl,a) -∗
  ∃ dst' sl1 sl2 a',
  tr_expr le dst' e (sl1,a')
  ∗ ⌜sl = sl1 ++ sl2⌝
  ∗ (∀ le' e' sl3,
        (tr_expr le' dst' e' (sl3,a') ∧
        (∀ id, (\s id -∗ False) -∗ ⌜ le'!id = le!id⌝)) -∗
        \⌜ Csyntax.typeof e' = Csyntax.typeof e ⌝ -∗
        tr_exprlist le' (C e') ((sl3 ++ sl2),a))
).
Proof.
  Admitted.

Theorem tr_expr_leftcontext:
  forall C le r dst sl a,
  leftcontext RV RV C ->
  tr_expr le dst (C r) (sl,a) -∗
  ∃ dst' sl1 sl2 a',
  tr_expr le dst' r (sl1,a')
  ∗ ⌜ sl = sl1 ++ sl2 ⌝
  ∗ (∀ le' r' sl3,
        (tr_expr le' dst' r' (sl3,a') ∧
        (∀ id, (\s id -∗ False) -∗ ⌜ le'!id = le!id ⌝)) -∗
        \⌜ Csyntax.typeof r' = Csyntax.typeof r ⌝ -∗
        tr_expr le' dst (C r') ((sl3 ++ sl2),a)).
Proof.
  intros. eapply (proj1 tr_expr_leftcontext_rec); eauto.
Qed.

Theorem tr_top_leftcontext:
  forall e le m dst rtop sl a,
  tr_top tge e le m dst rtop sl a -∗
  ∀ r C,
  ⌜ rtop = C r ⌝ -∗
  ⌜ leftcontext RV RV C ⌝ -∗
  ∃ dst' sl1 sl2 a',
  tr_top tge e le m dst' r sl1 a'
  ∗ ⌜ sl = sl1 ++ sl2 ⌝
  ∗ (∀ le' m' r' sl3,
        (tr_expr le' dst' r' (sl3,a') ∧
        (∀ id, (\s id -∗ False) -∗ ⌜le'!id = le!id ⌝)) -∗
        \⌜ Csyntax.typeof r' = Csyntax.typeof r ⌝ -∗
        tr_top tge e le' m' dst (C r') (sl3 ++ sl2) a).
Proof.
  iIntros (? ? ? ? ? ? ?) "HA".
  iDestruct "HA" as "[HA|%]". iIntros (r C H0 H1).
  - subst. exploit tr_expr_leftcontext; eauto. intro.
    iDestruct (H with "HA") as (dst' sl1 sl2 a') "[HA [% HC]]".
    iExists dst', sl1, sl2, a'.
    iSplitL "HA". iLeft.
    + iApply "HA".
    + iSplit; eauto. iIntros "* HA HB". iLeft. unfold tr_top_base.
      iApply ("HC" with "[HA] [HB]"); eauto.
  - iIntros (r C H0 H1). unfold tr_top_val_val in H.
    destruct sl; auto. destruct H as (v&ty&P0&P1&P2&P3). subst.
    inv H1; inv H0.
    + iExists For_val, _, _, _. repeat iSplitL.
      * iRight. iPureIntro. unfold tr_top_val_val. instantiate (3 := nil). simpl.
        exists v, (typeof a). split; eauto.
      * eauto.
      * iIntros "* HA %".
        rewrite <- app_nil_end. iLeft. unfold tr_top_base.
        destruct r'; simpl; iDestruct "HA" as "[HA _]";
          iDestruct "HA" as "[HC HA]"; iSplitL "HC"; eauto.
    + inversion H.
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

Lemma test3 (P Q : iProp) : (emp ⊢ P -∗ Q) -> (P ⊢ Q).
Proof. intro.
  iIntros "HA". iDestruct H as "HB". iApply "HB"; eauto.
Qed.

Lemma test4 : forall (P Q : iProp) tmps,
    (P ∗ Q) () tmps -> exists (tmp0 tmp1 : heap),
      P () tmp0 /\ Q () tmp1 /\ tmp0  ##ₘ tmp1 /\ tmps = tmp0 \u tmp1.
Proof.
  MonPred.unseal. intros. destruct H as (h0&h1&P0&P1&P2&P3). repeat eexists; eauto.
Qed.

Lemma step_tr_rvalof:
  forall ty m b ofs t v e le a sl a' f k,
  Csem.deref_loc ge ty m b ofs t v ->
  eval_lvalue tge e le m a b ofs ->
  tr_rvalof ty a (sl,a') -∗
  ⌜ typeof a = ty ⌝ -∗
  ∃ le',
    ⌜star step1 tge (State f Sskip (Kseqlist sl k) e le m)
                 t (State f Sskip k e le' m)
  /\ eval_expr tge e le' m a' v
  /\ typeof a' = typeof a ⌝
  ∗ ∀ x, (\s x -∗ False) -∗ ⌜ le'!x = le!x ⌝.
Proof.
  iIntros (? ? ? ? ? ? ? ? ? ? ? ? ? H0 H1) "HA %". unfold tr_rvalof.
  destruct (type_is_volatile ty) eqn:?.
  - iDestruct "HA" as  (t1) "[% HA]". inversion H. subst. clear H.
    iExists (Maps.PTree.set t1 v le). iSplitR.
    + iPureIntro. simpl. split. eapply star_two. econstructor. eapply step_make_set; eauto. traceEq.
      split. constructor. apply Maps.PTree.gss.
      reflexivity.
    + iIntros (x) "HB". iStopProof. apply test3. apply test2. intros. apply Maps.PTree.gso.
      intro. apply (soundness1 _ tmps). iIntros "HA". apply soundness3 in H.
      iDestruct (H with "HA") as "[HA HB]". iDestruct ("HB" with "[HA]") as "HA".
      iExists (typeof a). rewrite H2. iApply "HA". iApply "HA".
  - iDestruct "HA" as "%". inversion H; subst. clear H.
    exploit deref_loc_translated; eauto. intro.
    unfold chunk_for_volatile_type in H. rewrite Heqb0 in H. destruct H. subst.
    iExists le. iSplit; eauto.
    iPureIntro. split.  apply star_refl.
    split. eapply eval_Elvalue; eauto.
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
      (forall v m, tr_top tge e (set_opttemp optid v le) m dest (C (Csyntax.Eval v ty)) sl a () tmps) ->
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
      tr_top tge e le m dest r sl a () tmps ->
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
  forall ty a sl a', tr_rvalof ty a (sl,a') -∗ ⌜ nolabel_list sl ⌝.
Proof.
  iIntros (ty a sl a') "HA". unfold tr_rvalof. destruct (type_is_volatile ty) eqn:?.
  - iDestruct "HA" as (t0) "[% HA]". inversion H; subst. clear H.
    iStopProof. apply test3. apply test2. intros. simpl. split; auto.
    apply make_set_nolabel.
  - iDestruct "HA" as "%". inversion H; subst. iPureIntro. constructor.
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
  | [ |- nolabel _ ] => iIntros; simpl; auto
  | [ |- _ /\ _ ] => split; NoLabelTac
  | _ => auto
  end.

Lemma test5 : forall (P Q : iProp) tmps, ((P ∧ Q) : iProp) () tmps -> (P () tmps ∧ Q () tmps).
Proof.
  MonPred.unseal. intros. destruct H. split; auto. 
Qed.

Lemma tr_find_label_expr:
  (forall r le dst sl a, tr_expr le dst r (sl,a) -∗ ⌜ nolabel_list sl ⌝)
/\(forall rl le sl al, tr_exprlist le rl (sl,al) -∗ ⌜ nolabel_list sl ⌝).
Proof.
  apply tr_expr_exprlist; intros; iIntros "HA".
  - destruct dst.
    1-2 : iDestruct (tr_simple_expr_nil with "HA") as "HA";
      iDestruct ("HA" with "[]") as "HA"; eauto;
        iDestruct ("HA" with "[]") as "%"; eauto; rewrite H; auto.
    iDestruct "HA" as "[_ HA]". iDestruct "HA" as (a0) "[_ [_ %]]".
    simpl in *. rewrite H. iPureIntro. apply nolabel_do_set.
  - destruct dst.
    1-2 : iDestruct (tr_simple_expr_nil with "HA") as "HA";
      iDestruct ("HA" with "[]") as "HA"; eauto;
        iDestruct ("HA" with "[]") as "%"; eauto; rewrite H; auto.
    iDestruct "HA" as "[_ [HA %]]".
    simpl in *. inversion H; subst. iPureIntro. apply nolabel_do_set.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      iDestruct (H with "HB") as "%". inversion H0; subst. clear H0.
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      iDestruct (H with "HB") as "%". inversion H0; subst. clear H0.
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      iDestruct (H with "HB") as "%". inversion H0; subst. clear H0.
      iPureIntro. NoLabelTac. 
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sl3) "[HB [HA [_ %]]]". rewrite (surjective_pairing sla2).
      iDestruct (H with "HB") as "%". simpl in *. rewrite H0.
      iDestruct (tr_rvalof_nolabel with "HA") as "%".
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sl3) "[HB [HA [_ %]]]". rewrite (surjective_pairing sla2).
      iDestruct (H with "HB") as "%". simpl in *. rewrite H0.
      iDestruct (tr_rvalof_nolabel with "HA") as "%".
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sl3) "[HB [HA [_ %]]]". rewrite (surjective_pairing sla2).
      iDestruct (H with "HB") as "%". simpl in *. rewrite H0.
      iDestruct (tr_rvalof_nolabel with "HA") as "%".
      iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA [_ %]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3).
      inversion H1; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%". 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA [_ %]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3).
      inversion H1; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%". 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA [_ %]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3).
      inversion H1; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%". 
      iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      inversion H0; subst.
      iDestruct (H with "HB") as "%". simpl in *. 
      iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3 t0) "[HB [HA [HC %]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). iDestruct ("HA" with "HC") as "HA".
      inversion H1; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%". 
      iPureIntro. NoLabelTac. red. unfold find_label. auto.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). 
      simpl in *; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%". 
      iPureIntro. NoLabelTac. red. unfold find_label. auto.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA [HC %]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). iDestruct ("HA" with "HC") as "HA".
      simpl in *; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%". 
      iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3 t0) "[HB [HA [HC %]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). iDestruct ("HA" with "HC") as "HA".
      inversion H1; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%". 
      iPureIntro. NoLabelTac. red. unfold find_label. auto.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). 
      simpl in *; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%". 
      iPureIntro. NoLabelTac. red. unfold find_label. auto.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA [HC %]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). iDestruct ("HA" with "HC") as "HA".
      simpl in *; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%". 
      iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr.
      iDestruct "HA" as (sla2 sla3 sla4 t0) "[HA [HB [HC %]]]".
      inversion H2; subst. clear H2. rewrite (surjective_pairing sla2).
      iDestruct (H with "HA") as "%". iClear "HA".
      iDestruct ("HC" with "HB") as "HA".
      iStopProof. apply test3. apply test2. intros. apply test5 in H3 as (P0&P1).
      apply (soundness1 _ tmps). apply soundness3 in P0. iIntros "HA".
      iDestruct (P0 with "HA") as "HA".
      rewrite (surjective_pairing sla3). iDestruct (H0 with "HA") as "%".
      iPureIntro.
      apply (soundness1 _ tmps). apply soundness3 in P1. iIntros "HA".
      iDestruct (P1 with "HA") as "HA".
      rewrite (surjective_pairing sla4). iDestruct (H1 with "HA") as "%".
      simpl in *; subst. iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr.
      iDestruct "HA" as (sla2 sla3 sla4) "[HA [HB [HC %]]]".
      simpl in *; subst. rewrite (surjective_pairing sla2). rewrite (surjective_pairing sla3).
      rewrite (surjective_pairing sla4).
      iDestruct (H with "HA") as "%". iClear "HA".
      iDestruct (H0 with "HB") as "%". iClear "HB".
      iDestruct (H1 with "HC") as "%". iClear "HC".
      simpl in *; subst. iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr.
      iDestruct "HA" as (sla2 sla3 sla4 t0) "[HA [HB [HC %]]]".
      inversion H2; subst. clear H2. rewrite (surjective_pairing sla2).
      iDestruct (H with "HA") as "%". iClear "HA".
      iDestruct ("HC" with "HB") as "HA".
      iStopProof. apply test3. apply test2. intros. apply test5 in H4 as (P0&P1).
      apply (soundness1 _ tmps). apply soundness3 in P0. iIntros "HA".
      iDestruct (P0 with "HA") as "HA".
      rewrite (surjective_pairing sla3). iDestruct (H0 with "HA") as "%".
      iPureIntro.
      apply (soundness1 _ tmps). apply soundness3 in P1. iIntros "HA".
      iDestruct (P1 with "HA") as "HA".
      rewrite (surjective_pairing sla4). iDestruct (H1 with "HA") as "%".
      simpl in *; subst. iPureIntro. NoLabelTac.      
  - destruct dst.
    1-2 : iDestruct (tr_simple_expr_nil with "HA") as "HA";
      iDestruct ("HA" with "[]") as "HA"; eauto;
        iDestruct ("HA" with "[]") as "%"; eauto; rewrite H; auto.
    iDestruct "HA" as "[_ HA]". iDestruct "HA" as "[_ %]".
    simpl in *. inversion H; subst. iPureIntro. apply nolabel_do_set.      
  - destruct dst.
    1-2 : iDestruct (tr_simple_expr_nil with "HA") as "HA";
      iDestruct ("HA" with "[]") as "HA"; eauto;
        iDestruct ("HA" with "[]") as "%"; eauto; rewrite H; auto.
    iDestruct "HA" as "[_ HA]". iDestruct "HA" as "[_ %]".
    simpl in *. inversion H; subst. iPureIntro. apply nolabel_do_set.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA HC]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). 
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%".
      iDestruct "HC" as "[[% %]|HC]".
      * inversion H4.
      * iDestruct "HC" as (t0) "[HC %]". simpl in *. subst. iPureIntro. NoLabelTac.
        red. intros.  unfold find_label. reflexivity.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA HC]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). 
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%".
      iDestruct "HC" as "[[% %]|HC]".
      * simpl in *. subst. iPureIntro. NoLabelTac.
      * iDestruct "HC" as (t0) "[HC %]". simpl in *. subst. iPureIntro. NoLabelTac.
        red. intros.  unfold find_label. reflexivity.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3) "[HB [HA HC]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). 
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%".
      iDestruct "HC" as "[[% %]|HC]".
      * inversion H4.
      * iDestruct "HC" as (t0) "[HC %]". simpl in *. subst. iPureIntro. NoLabelTac.
        red. intros.  unfold find_label. reflexivity.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3 sla4) "[HB [HA [HC HD]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). rewrite (surjective_pairing sla4). 
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%".
      simpl. iDestruct (tr_rvalof_nolabel with "HC") as "%".
      iDestruct "HD" as "[[% %]|HD]".
      * inversion H4.
      * iDestruct "HD" as (t0) "[HD %]". inversion H4. subst. iPureIntro. NoLabelTac.
        red. intros. unfold find_label. reflexivity.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3 sla4) "[HB [HA [HC HD]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). rewrite (surjective_pairing sla4). 
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%".
      simpl. iDestruct (tr_rvalof_nolabel with "HC") as "%".
      iDestruct "HD" as "[[% %]|HD]".
      * rewrite H5. iPureIntro. NoLabelTac.
      * iDestruct "HD" as (t0) "[HD %]". inversion H4. subst. iPureIntro. NoLabelTac.
        red. intros. unfold find_label. reflexivity.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr. 
      iDestruct "HA" as (sla2 sla3 sla4) "[HB [HA [HC HD]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing sla3). rewrite (surjective_pairing sla4). 
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%".
      simpl. iDestruct (tr_rvalof_nolabel with "HC") as "%".
      iDestruct "HD" as "[[% %]|HD]".
      * inversion H4.
      * iDestruct "HD" as (t0) "[HD %]". inversion H4. subst. iPureIntro. NoLabelTac.
        red. intros. unfold find_label. reflexivity.
  - destruct dst.
    + iDestruct "HA" as "[_ [HA|HA]]"; fold tr_expr.
      * iDestruct "HA" as (sla2 sla3) "[HB [HA %]]". rewrite (surjective_pairing sla2).
        rewrite (surjective_pairing sla3). simpl. iDestruct (tr_rvalof_nolabel with "HA") as "%".
        iDestruct (H with "HB") as "%". simpl in *; subst. iPureIntro. NoLabelTac.
      * iDestruct "HA" as (sla2 t0) "[HB [HA %]]". rewrite (surjective_pairing sla2).
        inversion H0; subst.
        iDestruct (H with "HB") as "%". simpl in *; subst. iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ [HA|HA]]"; fold tr_expr.
      * iDestruct "HA" as (sla2 sla3) "[HB [HA %]]". rewrite (surjective_pairing sla2).
        rewrite (surjective_pairing sla3). simpl. iDestruct (tr_rvalof_nolabel with "HA") as "%".
        iDestruct (H with "HB") as "%". simpl in *; subst. iPureIntro. NoLabelTac.
      * iDestruct "HA" as (sla2 t0) "[HB [HA %]]". rewrite (surjective_pairing sla2).
        inversion H0; subst.
        iDestruct (H with "HB") as "%". simpl in *; subst. iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ [HA|HA]]"; fold tr_expr.
      * iDestruct "HA" as (sla2 sla3) "[HB [HA %]]". rewrite (surjective_pairing sla2).
        rewrite (surjective_pairing sla3). simpl. iDestruct (tr_rvalof_nolabel with "HA") as "%".
        iDestruct (H with "HB") as "%". simpl in *; subst. iPureIntro. NoLabelTac.
      * iDestruct "HA" as (sla2 t0) "[HB [HA %]]". rewrite (surjective_pairing sla2).
        inversion H0; subst.
        iDestruct (H with "HB") as "%". simpl in *; subst. iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr.
      iDestruct "HA" as (sla2 sl3) "[HB [HA [_ %]]]". rewrite (surjective_pairing sla2).
      simpl. iDestruct (H with "HB") as "%". simpl in *; subst.
      iDestruct (H0 with "[HA]") as "%".
      * iApply "HA". trivial.
      * iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr.
      iDestruct "HA" as (sla2 sl3) "[HB [HA [_ %]]]". rewrite (surjective_pairing sla2).
      simpl. iDestruct (H with "HB") as "%". simpl in *; subst.
      iDestruct (H0 with "[HA]") as "%".
      * iApply "HA". trivial.
      * iPureIntro. NoLabelTac.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr.
      iDestruct "HA" as (sla2 sl3) "[HB [HA [HC %]]]". rewrite (surjective_pairing sla2).
      simpl. iDestruct (H with "HB") as "%". simpl in *; subst.
      iDestruct (H0 with "[HA HC]") as "%".
      * iApply "HA". trivial.
      * iPureIntro. NoLabelTac.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
      iDestruct "HA" as (sla2 slal3 t0) "[HB [HA [HC [_ %]]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing slal3). inversion H1; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%".
      iPureIntro. NoLabelTac.
      red. intros. unfold find_label. reflexivity.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
      iDestruct "HA" as (sla2 slal3) "[HB [HA %]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing slal3). simpl in *; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%".
      iPureIntro. NoLabelTac.
      red. intros. unfold find_label. reflexivity.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
      iDestruct "HA" as (sla2 slal3 t0) "[HB [HA [HC [_ %]]]]". rewrite (surjective_pairing sla2).
      rewrite (surjective_pairing slal3). inversion H1; subst.
      iDestruct (H with "HB") as "%".
      iDestruct (H0 with "HA") as "%".
      iPureIntro. NoLabelTac.
      red. intros. unfold find_label. reflexivity.
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
      iDestruct "HA" as (slal2 t0) "[HB [HA [_ %]]]". rewrite (surjective_pairing slal2).
      inversion H0; subst. iDestruct (H with "HB") as "%".
      iPureIntro. NoLabelTac.
      red. intros. unfold find_label. reflexivity.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
      iDestruct "HA" as (slal2) "[HB %]". rewrite (surjective_pairing slal2).
      simpl in *; subst. iDestruct (H with "HB") as "%".
      iPureIntro. NoLabelTac.
      red. intros. unfold find_label. reflexivity.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
      iDestruct "HA" as (slal2 t0) "[HB [HA [_ %]]]". rewrite (surjective_pairing slal2).
      inversion H0; subst. iDestruct (H with "HB") as "%".
      iPureIntro. NoLabelTac.
      red. intros. unfold find_label. reflexivity.
  - destruct dst; iDestruct "HA" as "[_ HA]"; iExFalso; iApply "HA".
  - destruct dst.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
      iDestruct "HA" as (a2 t0) "[HB [HA %]]". iDestruct ("HB" with "HA") as "HA". simpl.
      iDestruct (H with "HA") as "%". iPureIntro. apply H1.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
      iDestruct "HA" as (a2) "HA". simpl.
      iDestruct (H with "HA") as "%". iPureIntro. apply H0.
    + iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
      iDestruct "HA" as (a2 t0) "[HB HA]". iDestruct ("HB" with "HA") as "HA". simpl.
      iDestruct (H with "HA") as "%". iPureIntro. apply H0.
  - iDestruct "HA" as "[_ %]". inversion H. iPureIntro. NoLabelTac.
  - iDestruct "HA" as "[_ HA]"; fold tr_expr; fold tr_exprlist.
    iDestruct "HA" as (sla2 slal3) "[HA [HB %]]". inversion H1; subst.
    rewrite (surjective_pairing sla2). rewrite (surjective_pairing slal3).
    simpl. iDestruct (H with "HA") as "%". iDestruct (H0 with "HB") as "%".
    iPureIntro. NoLabelTac.
Qed.
                                        
Lemma tr_find_label_top:
  forall e le m dst r sl a,
    tr_top tge e le m dst r sl a -∗ ⌜ nolabel_list sl ⌝.
Proof.
  intros. iIntros "HA". unfold tr_top. iDestruct ("HA" with "") as "[HA|%]".
  - unfold tr_top_base. epose tr_find_label_expr. destruct a0. iApply (H with "HA").
  - unfold tr_top_val_val in H. destruct sl; auto.
Qed.

Lemma tr_find_label_expression:
  forall r s a, tr_expression r s a -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  pose (H0 tge empty_env (Maps.PTree.empty val) Mem.empty).
  apply soundness3 in m.
  apply (soundness1 _ tmps). iIntros "HA". iDestruct (m with "HA") as "HA".
  iApply tr_find_label_top; eauto.
  apply H.
Qed.

Lemma tr_find_label_expr_stmt:
  forall r s, tr_expr_stmt r s -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  pose (H0 tge empty_env (Maps.PTree.empty val) Mem.empty).
  apply soundness3 in m.
  apply (soundness1 _ tmps). iIntros "HA". iDestruct (m with "HA") as "HA".
  iApply tr_find_label_top; eauto.
  apply H.
Qed.

Lemma tr_find_label_if:
  forall r s, tr_if r Sskip Sbreak s -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq (sl ++ makeif a Sskip Sbreak :: nil))).
  apply makeseq_nolabel.
  apply nolabel_list_app.
  pose (H0 tge empty_env (Maps.PTree.empty val) Mem.empty).
  apply soundness3 in m.
  apply (soundness1 _ tmps). iIntros "HA". iDestruct (m with "HA") as "HA".
  iApply tr_find_label_top; eauto.
  simpl; split; auto. apply makeif_nolabel. red; simpl; auto. red; simpl; auto.
  apply H.
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

 
Lemma tr_val_gen:
  forall le dst v ty a,
  typeof a = ty ->
  (∀ tge e le' m,
      (∀ id, \s id -∗ ⌜ le'!id = le!id ⌝) -∗
                                          ⌜ eval_expr tge e le' m a v ⌝) -∗
  tr_expr le dst (Csyntax.Eval v ty) ((final dst a),a).
Proof.
  intros. destruct dst; simpl; iIntros "HA"; subst; eauto.
Qed.

Lemma test6_l : forall (P Q : iProp),
    (P ⊢ P) ->
    (((P ∧ Q) : iProp) ⊢ P).
Proof.
  MonPred.unseal. intros. split. red. intros i h P0. inversion P0. apply H0.
Qed.

Lemma test6_r : forall (P Q : iProp),
    (Q ⊢ Q) ->
    (((P ∧ Q) : iProp) ⊢ Q).
Proof.
  MonPred.unseal. intros. split. red. intros i h P0. inversion P0. apply H1.
Qed.


Lemma estep_simulation:
  forall S1 t S2, Cstrategy.estep ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.
 induction 1; intros; inv MS.
(* expr *)
 -  assert (tr_expr le dest r (sl,a) () tmps).
    + apply soundness2. apply soundness3 in H9. iIntros "HA".
      iDestruct (H9 with "HA") as "HA". unfold tr_top. iDestruct "HA" as "[HA|%]".
      iApply "HA". unfold tr_top_val_val in H1. destruct sl; auto.
      repeat destruct H1. destruct H2. destruct H2. subst. contradiction. contradiction.
    + exploit tr_simple_rvalue; eauto. apply soundness3 in H1. intro.
      apply (soundness1 _ tmps). iIntros "HA".
      iDestruct (H1 with "HA") as "HA". iDestruct (H2 with "HA") as "%".
      destruct dest.
      (* for val *)
      * destruct H3 as (SL1&TY1&EV1). subst sl. iExists _. 
        iSplit; iPureIntro.
        -- right; split.
           ++ apply star_refl.
           ++ destruct r; simpl; try (contradiction || omega || unfold lt; omega).
        -- eapply (match_exprstates _ _ _ _ _ _ _ _ _ _ _ ∅); eauto.
           apply soundness2. iIntros. unfold tr_top. unfold tr_top_val_val. iRight.
           iPureIntro. exists v. exists (Csyntax.typeof r). split; auto.
      (* for effects *)
      * subst sl. iExists _.
        iSplit; iPureIntro.
        -- right; split.
           ++ apply star_refl.
           ++ destruct r; simpl; try (contradiction || omega || unfold lt; omega).
        -- econstructor; eauto.
           instantiate (1 := ∅). apply soundness2.
           iIntros "HA". unfold tr_top. simpl. iLeft. unfold tr_top_base. simpl.
           eauto.
           (* for set *)
      * inversion H10.
        (* rval volatile *)
 - exploit tr_top_leftcontext; eauto.
   intro. apply soundness3 in H11.
   apply (soundness1 _ tmps). iIntros "HA". iDestruct (H11 with "HA") as "HA". 
   iDestruct (H2 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto. 
   iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct "HA" as (dst' sl1 sl2 a') "[P [% R]]".
   iDestruct "P" as "[HA|%]".
   + unfold tr_top_base. simpl.
     iDestruct "HA" as "[_ HA]".
     iDestruct "HA" as (sla2 sl3) "[HA [HB [HC %]]]".
     unfold tr_rvalof. rewrite H3. iDestruct "HB" as (t1) "[% HB]".
     inversion H6. subst.
     rewrite (surjective_pairing sla2).
     iDestruct (tr_simple_lvalue with "HA") as "[% [% %]]"; eauto.
     rewrite H4; simpl. clear H6. iClear "HA". iClear "HC".
     iExists _. iSplit. 
     * iPureIntro. left. eapply plus_two. constructor. eapply step_make_set; eauto. traceEq.
     * iStopProof. apply test3. apply test2.
       intros. apply test4 in H6. destruct H6 as (tmp0&tmp1&P0&P1&P2&P3). econstructor; eauto.
       change (final dst' (Etempvar t1 (Csyntax.typeof l)) ++ sl2) with (nil ++ (final dst' (Etempvar t1 (Csyntax.typeof l)) ++ sl2)).
       apply soundness2. instantiate (1 := tmps0).
       apply soundness3 in P1. iIntros "HA".
       rewrite P3. iDestruct (heap_ctx_split with "HA") as "[HA HB]"; eauto.
       iDestruct (P1 with "HB") as "HB". admit. (* iApply ("HB" with ""). *)    
         (* -- iApply tr_val_gen; auto. iIntros (? ? ? ?) "HB". *)
       (*    iDestruct ("HB" with "[HA]")  as "%". *)
       (*    apply soundness3 in P0. iDestruct (P0 with "HA") as "HA". *)
       (*    iExists (Csyntax.typeof l). iApply "HA". *)
       (*    iPureIntro. constructor. rewrite H6. apply Maps.PTree.gss. *)
       (* -- iIntros. iStopProof. apply test3. apply test2. intros. *)
       (*    apply Maps.PTree.gso. red. intros. subst. elim H5.  *)
       (*    iPureIntro. *)
       (*    apply (soundness1 _ tmps0). iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB [HC HD]]]". *)

   + unfold tr_top_val_val in H5. destruct sl1; auto. destruct H5 as (v'&ty&P0&P1&P2&P3).
     subst. inversion P3.
 (* seqand true *)
 - exploit tr_top_leftcontext; eauto. 
   intro. apply soundness3 in H9.
   apply (soundness1 _ tmps). iIntros "HA". iDestruct (H9 with "HA") as "HA". 
   iDestruct (H2 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
   iDestruct "HA" as "[HA|%]".
   + unfold tr_top_base. simpl. iDestruct "HA" as "[_ HA]". destruct dst'.
     * simpl. iDestruct "HA" as (sla2 sla3 t0) "[HA [HC [HD %]]]".
       eapply tr_simple_rvalue in H0.
       inversion H4. subst.
       rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. simpl. iExists _. iSplit.
       -- iPureIntro. left. simpl Kseqlist. eapply plus_left. constructor. eapply star_trans.
          apply step_makeif with (b := true) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. reflexivity.
       -- rewrite <- Kseqlist_app. iStopProof. apply test3. apply test2. intros.
          eapply match_exprstates; eauto.
          apply soundness2. apply soundness3 in H7. iIntros "HA".
          iDestruct (H7 with "HA") as "[HA [HB [HC HD]]]".
          iApply ("HD" with "[HA HB HC]"); eauto.
          simpl. repeat iSplit; auto. iExists sla3.2. iExists t0. iSplitL "HB". iIntros.
          rewrite <- surjective_pairing. iApply "HB". iFrame.
          iSplitL "HC". iFrame. eauto.
     * simpl. iDestruct "HA" as (sla2 sla3) "[HA [HC %]]".
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". subst. rewrite H5.
       iExists _. iSplit.
       -- iPureIntro. left. simpl Kseqlist. eapply plus_left. constructor. eapply star_trans.
          apply step_makeif with (b := true) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. reflexivity.
       -- rewrite <- Kseqlist_app. iStopProof. apply test3. apply test2. intros.
          eapply match_exprstates; eauto.
          apply soundness2. apply soundness3 in H3. iIntros "HA".
          iDestruct (H3 with "HA") as "[HA [HB HC]]".
          iApply ("HC" with "[HA HB]"); eauto.
          simpl. iSplitL; eauto. iSplitL "HA"; eauto. iExists sla3.2.
          rewrite <- surjective_pairing. iApply "HB".
     * iDestruct "HA" as (sla2 sla3) "[HA [HC [HD %]]]".
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". subst. rewrite H5.
       iExists _. iSplit.
       -- iPureIntro. left. simpl Kseqlist. eapply plus_left. constructor. eapply star_trans.
          apply step_makeif with (b := true) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. reflexivity.
       -- rewrite <- Kseqlist_app. iStopProof. apply test3. apply test2. intros.
          eapply match_exprstates; eauto.
          apply soundness2. apply soundness3 in H3. iIntros "HA".
          iDestruct (H3 with "HA") as "[HA [HB [HD HC]]]".
          iApply ("HC" with "[HA HB HD]"); eauto.
          simpl. iSplitL; eauto. iSplitL "HA"; eauto. iExists sla3.2. iExists (sd_temp sd).
          rewrite <- surjective_pairing. iFrame.
   + unfold tr_top_val_val in H4. destruct sl1; auto. destruct H4 as (v'&ty'&P0&P1&P2&P3).
     subst. inversion P3.
     
 (* seqand false *)
 - exploit tr_top_leftcontext; intro.
   apply (soundness1 _ tmps). iIntros "HA". apply soundness3 in H9. iDestruct (H9 with "HA") as "HA".
   iDestruct (H2 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct "HA" as (dst' sl1 sl2 a') "[P [% R]]".
   iDestruct "P" as "[[_ HA]|%]".
   + fold tr_expr. destruct dst'.
     * iDestruct "HA" as (sla2 sla3 t0) "[HA [HB [HC %]]]". inversion H4; subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
          eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
          apply star_one. constructor. constructor. reflexivity. reflexivity.
       -- iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
          change sl2 with (nil ++ sl2). apply soundness3 in H7. apply soundness2.
          iIntros "HA". iDestruct (H7 with "HA") as "[HA [HB [HC HD]]]".
          iApply ("HD" with "[HA HB HC]").
          ++ simpl. iSplitL "HA HB HC"; auto.
             ** iSplitL "HA" ; eauto. iSplitL; eauto. iIntros "* HA". 
                iStopProof. apply test3. apply test2. intros.
                constructor. rewrite H11. apply Maps.PTree.gss.
          ++ iIntros (? ? ? ?) "HA". iDestruct ("HA" with "[HC]") as "%".
             iFrame. iStopProof. apply test3. apply test2. intros.
             constructor. rewrite H11. apply Maps.PTree.gss.
          ++ iIntros. iPureIntro. apply Maps.PTree.gso. admit.
          ++ eauto.
     * iDestruct "HA" as (sla2 sla3) "[HA [HB %]]". simpl in H4. subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
          apply step_makeif with (b := false) (v1 := v); auto. congruence. reflexivity.
       -- iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
          change sl2 with (nil ++ sl2). apply soundness3 in H6. apply soundness2.
          iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB HC]]".
          iApply ("HC" with "[HA HB]"); eauto.
     * iDestruct "HA" as (sla2 sla3) "[HA [HB [HC %]]]". simpl in *. subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
          eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. reflexivity.
       --  rewrite <- Kseqlist_app.
           iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
           apply soundness3 in H6. apply soundness2.
          iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB [HC HD]]]".
          iApply ("HD" with "[HA HB HC]"). simpl. iSplitL "HA"; auto.
          iExists (Econst_int Int.zero ty).
          iSplit; eauto.
          ++ iIntros (? ? ? ?) "HA". iDestruct ("HA" with "[HC]") as "%".
             iFrame. iPureIntro.
             econstructor; eauto.
          ++ iIntros. eauto.
          ++ eauto.
   + unfold tr_top_val_val in H4. destruct sl1; auto. destruct H4 as (v'&ty0&P0&P1&P2&P3).
     subst. inversion P3.
 (* seqor true *)
 - exploit tr_top_leftcontext. intro. apply soundness3 in H9.
   apply (soundness1 _ tmps). iIntros "HA". iDestruct (H9 with "HA") as "HA". 
   iDestruct (H2 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
   iDestruct "HA" as "[[_ HA]|%]".
   + unfold tr_top_base. fold tr_expr. simpl. destruct dst'.
     * iDestruct "HA" as (sla2 sla3 t0) "[HA [HD [HC %]]]". inversion H4; subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
          eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
          apply star_one. constructor. constructor. reflexivity. reflexivity.
       -- iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
          change sl2 with (nil ++ sl2). apply soundness3 in H7. apply soundness2.
          iIntros "HA". iDestruct (H7 with "HA") as "[HA [HB [HC HD]]]".
          iApply ("HD" with "[HA HB HC]"). simpl. iSplitL "HA"; auto.
          iSplit; eauto.
          ++ iIntros (? ? ? ?) "HA". iDestruct ("HA" with "[HC]") as "%".
             iFrame. iStopProof. apply test3. apply test2. intros.
             constructor. rewrite H11. apply Maps.PTree.gss.
          ++ iIntros. iPureIntro. apply Maps.PTree.gso. admit.
          ++ eauto.
     * iDestruct "HA" as (sla2 sla3) "[HA [HC %]]". simpl in H4. subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
          apply step_makeif with (b := true) (v1 := v); auto. congruence. reflexivity.
       -- iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
          change sl2 with (nil ++ sl2). apply soundness3 in H6. apply soundness2.
          iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB HC]]".
          iApply ("HC" with "[HA HB]"); eauto.
     * iDestruct "HA" as (sla2 sla3) "[HA [HD [HC %]]]". simpl in *. subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
          eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. reflexivity.
       --  rewrite <- Kseqlist_app.
           iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
           apply soundness3 in H6. apply soundness2.
           iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB [HC HD]]]".
           iApply ("HD" with "[HA HB HC]"). simpl. iSplitL "HA"; auto.
           iExists (Econst_int Int.one ty).
           iSplit; eauto.
           ++ iIntros (? ? ? ?) "HA". iDestruct ("HA" with "[HC]") as "%".
              iFrame. iPureIntro.
              econstructor; eauto.
           ++ iIntros. eauto.
           ++ eauto.
   + unfold tr_top_val_val in H4. destruct sl1; auto. destruct H4 as (v'&ty0&P0&P1&P2&P3).
     subst. inversion P3.
     
 (* seqor false *)
 - exploit tr_top_leftcontext. intro. apply soundness3 in H9.
   apply (soundness1 _ tmps). iIntros "HA". iDestruct (H9 with "HA") as "HA". 
   iDestruct (H2 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
   iDestruct "HA" as "[[_ HA]|%]".
   + fold tr_expr. unfold tr_top_base.  simpl. destruct dst'.
     * iDestruct "HA" as (sla2 sla3 t0) "[HA [HD [HC %]]]". inversion H4; subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
          eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
          apply push_seq. constructor. constructor. 
       -- rewrite <- Kseqlist_app.
          iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
          apply soundness3 in H7. apply soundness2.
          iIntros "HA". iDestruct (H7 with "HA") as "[HA [HB [HC HD]]]".
          iApply ("HD" with "[HA HB HC]"). simpl. iSplitL "HA"; auto. iExists sla3.2.
          iExists t0.
          ++ rewrite <- surjective_pairing. iFrame. eauto.
          ++ eauto.
          ++ eauto.
     * iDestruct "HA" as (sla2 sla3) "[HA [HC %]]". simpl in H4. subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
          eapply star_trans.
          apply step_makeif with (b := false) (v1 := v); auto. congruence. apply push_seq.
          reflexivity. reflexivity.
       -- rewrite <- Kseqlist_app.
          iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
          apply soundness3 in H6. apply soundness2.
          iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB HC]]".
          iApply ("HC" with "[HA HB]"); eauto. simpl. iSplitL "HA"; eauto.
          iExists sla3.2. rewrite <- surjective_pairing. iApply "HB".
     * iDestruct "HA" as (sla2 sla3) "[HA [HD [HC %]]]". simpl in *. subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. iExists _. iSplit.
       -- iPureIntro. left. eapply plus_left. simpl Kseqlist. constructor.
          eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
          apply push_seq. reflexivity. reflexivity.
       --  rewrite <- Kseqlist_app.
           iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
           apply soundness3 in H6. apply soundness2.
           iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB [HC HD]]]".
           iApply ("HD" with "[HA HB HC]"); eauto. simpl. iSplitL "HA"; auto.
           iExists sla3.2. iExists (sd_temp sd). rewrite <- surjective_pairing. iFrame.
   + unfold tr_top_val_val in H4. destruct sl1; auto. destruct H4 as (v'&ty0&P0&P1&P2&P3).
     subst. inversion P3.
     
     (* condition *)
  - exploit tr_top_leftcontext. intro. apply soundness3 in H9.
   apply (soundness1 _ tmps). iIntros "HA". iDestruct (H9 with "HA") as "HA". 
   iDestruct (H2 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct ("HA" with "[]") as "HA"; eauto.
   iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
   iDestruct "HA" as "[[_ HA]|%]".
   + fold tr_expr. unfold tr_top_base.  simpl. destruct dst'.
     * iDestruct "HA" as (sla2 sla3 sla4 t0) "[HA [HD [HC %]]]".
       (* iDestruct ("HC" with "HD") as "HC". *)
       inversion H4; subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3; simpl Kseqlist. destruct b. 
       -- iExists _. iSplit.
          ++ iPureIntro. left. eapply plus_left. constructor.
             eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
             apply push_seq. reflexivity. reflexivity.
          ++ rewrite <- Kseqlist_app.
             iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
             apply soundness3 in H7. apply soundness2.
             iIntros "HA". iDestruct (H7 with "HA") as "[HA [HB [HC HD]]]".
             iApply ("HD" with "[HA HB HC]"); eauto. simpl. iSplitL "HA"; auto. iExists sla3.2.
             iExists t0. iSplitL "HC"; eauto.
             rewrite <- surjective_pairing. iIntros "HB".
             iDestruct ("HC" with "HB") as "HA". iStopProof. apply test6_l. eauto.
       -- iExists _. iSplit.
          ++ iPureIntro. left. eapply plus_left. constructor.
             eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
             apply push_seq. reflexivity. reflexivity.
          ++ rewrite <- Kseqlist_app.
             iStopProof. apply test3. apply test2. intros. eapply match_exprstates; eauto.
             apply soundness3 in H7. apply soundness2.
             iIntros "HA". iDestruct (H7 with "HA") as "[HA [HB [HC HD]]]".
             iApply ("HD" with "[HA HB HC]"); eauto. simpl. iSplitL "HA"; eauto. iExists sla4.2.
             iExists t0. rewrite <- surjective_pairing. iFrame. iSplitL; eauto.
             iIntros "HA". iDestruct ("HC" with "HA") as "HA". iStopProof. apply test6_r. eauto.
     * iDestruct "HA" as (sla2 sla3 sl4) "[HA [HC [HD %]]]". subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3; simpl Kseqlist. destruct b.
       -- iExists _. iSplit.
          ++ iPureIntro. left. eapply plus_left. constructor.
             eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
             apply push_seq. reflexivity. traceEq.
          ++ rewrite <- Kseqlist_app.
             iStopProof. apply test3. apply test2. intros. econstructor; eauto.
             apply soundness3 in H6. apply soundness2.
             iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB [HC HD]]]".
             iApply ("HD" with "[HA HB HC]"); eauto. simpl. iSplitL "HA HC"; eauto.
             iExists sla3.2. rewrite <- surjective_pairing. iFrame.
       -- iExists _. iSplit.
          ++ iPureIntro. left. eapply plus_left. constructor.
             eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
             apply push_seq. reflexivity. traceEq.
          ++ rewrite <- Kseqlist_app.
             iStopProof. apply test3. apply test2. intros. econstructor; eauto.
             apply soundness3 in H6. apply soundness2.
             iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB [HC HD]]]".
             iApply ("HD" with "[HA HB HC]"); eauto. simpl. iSplitL "HA HB"; eauto.
             iExists sl4.2. rewrite <- surjective_pairing. iFrame.
     * iDestruct "HA" as (sla2 sla3 sla4 t0) "[HA [HD [HC %]]]". subst.
       eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
       iDestruct (H0 with "HA") as "[% [% %]]". rewrite H3. destruct b.
       -- iExists _. iSplit.
          ++ iPureIntro.  left. eapply plus_left. constructor. simpl.
             eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
             apply push_seq. reflexivity. traceEq.
          ++ rewrite <- Kseqlist_app.
             iStopProof. apply test3. apply test2. intros. econstructor; eauto.
             apply soundness3 in H6. apply soundness2.
             iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB [HC HD]]]".
             iApply ("HD" with "[HA HB HC]"); eauto. simpl. iSplitL "HA"; auto.
             iExists sla3.2. iExists t0. rewrite <- surjective_pairing. iFrame.
             iIntros "HA". iDestruct ("HC" with "HA") as "HA". iStopProof. apply test6_l. eauto.
       -- iExists _. iSplit.
          ++ iPureIntro. left. eapply plus_left. constructor. simpl.
             eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
             apply push_seq. reflexivity. traceEq.
          ++ rewrite <- Kseqlist_app.
             iStopProof. apply test3. apply test2. intros. econstructor; eauto.
             apply soundness3 in H6. apply soundness2.
             iIntros "HA". iDestruct (H6 with "HA") as "[HA [HB [HC HD]]]".
             iApply ("HD" with "[HA HB HC]"); eauto. simpl. iSplitL "HA"; auto.
             iExists sla4.2. iExists t0. rewrite <- surjective_pairing. iFrame. iIntros "HA".
             iDestruct ("HC" with "HA") as "HA". iStopProof. apply test6_r. eauto.
   + unfold tr_top_val_val in H4. destruct sl1; auto. destruct H4 as (v'&ty0&P0&P1&P2&P3).
     subst. inversion P3.
     
  (* assign *)
  - exploit tr_top_leftcontext. intro. apply soundness3 in H12.
    apply (soundness1 _ tmps). iIntros "HA". iDestruct (H12 with "HA") as "HA". 
    iDestruct (H4 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
    iDestruct "HA" as "[[_ HA]|%]"; fold tr_expr. 
    + iDestruct "HA" as (sla2 sla3) "[HA [HC HD]]".
      destruct dst'; iDestruct "HD" as "[[% %]| HD]"; try discriminate.
      * admit.  (* Toujours (forall id, In id tmps -> le ! id = le' ! id *)
      * simpl in *. subst. clear H7.
        eapply tr_simple_lvalue in H0.
        eapply tr_simple_rvalue in H1. rewrite (surjective_pairing sla2).
        rewrite (surjective_pairing sla3).
        iDestruct (H0 with "HA") as "[% [% %]]". 
        iDestruct (H1 with "HC") as "[% [% %]]". rewrite H5. rewrite H8. simpl Kseqlist.
        iExists _. iSplit.
        -- iPureIntro. left. eapply plus_left. constructor.
           apply star_one. eapply step_make_assign; eauto.
           rewrite <- H9; eauto. traceEq.
        -- iStopProof. apply test3. apply test2. intros. econstructor; eauto.
           apply soundness3 in H14. apply soundness2.
           iIntros "HA". iDestruct (H14 with "HA") as "[HA [HB HC]]".
           change sl2 with (nil ++ sl2).
           iApply ("HC" with "[HA HB]"); eauto.
      * admit.
      * admit.
    + unfold tr_top_val_val in H6. destruct sl1; auto. destruct H6 as (v''&ty0&P0&P1&P2&P3).
      inversion P3.

  (* assignop *)
  - exploit tr_top_leftcontext. intro. apply soundness3 in H15.
    apply (soundness1 _ tmps). iIntros "HA". iDestruct (H15 with "HA") as "HA". 
    iDestruct (H6 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
    iDestruct "HA" as "[[_ HA]|%]"; fold tr_expr. 
    + iDestruct "HA" as (sla2 sla3 sla4) "[HA [HC [HD HE]]]".
      destruct dst'; iDestruct "HE" as "[[% %]| HE]"; try discriminate.
      * admit.  (* Toujours (forall id, In id tmps -> le ! id = le' ! id *)
      * admit.
      * admit.
      * admit.
    + unfold tr_top_val_val in H8. destruct sl1; auto. destruct H8 as (v''&ty0&P0&P1&P2&P3).
      inversion P3.

  (* assignop stuck *)
  - exploit tr_top_leftcontext; intro. apply soundness3 in H12.
    apply (soundness1 _ tmps). iIntros "HA". iDestruct (H12 with "HA") as "HA". 
    iDestruct (H4 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
    iDestruct "HA" as "[[_ HA]|%]"; fold tr_expr. 
    + iDestruct "HA" as (sla2 sla3 sla4) "[HA [HC [HD HE]]]".
      destruct dst'; iDestruct "HE" as "[[% %]| HE]"; try discriminate.
      * iDestruct "HE" as (t1) "[HE %]". inversion H6; subst.
        eapply tr_simple_lvalue in H0. rewrite (surjective_pairing sla2).
        iDestruct (H0 with "HA") as "[% [% %]]".
        eapply tr_simple_rvalue in H2. rewrite (surjective_pairing sla3).
        iDestruct (H2 with "HC") as "[% [% %]]".
        eapply step_tr_rvalof in H1. rewrite (surjective_pairing sla4).
        iDestruct (H1 with "HD") as "HD".
        iDestruct ("HD" with "[]") as (le') "[[% [% %]] HD]"; eauto. rewrite H5. rewrite H9.
        simpl Kseqlist. iExists _. iSplit.
        -- iPureIntro. right; split. rewrite app_ass. rewrite Kseqlist_app. eexact H15.
           simpl. unfold lt; omega.
        -- iPureIntro. constructor.
        -- eauto.
      * simpl in *. subst. clear H6.
        eapply tr_simple_lvalue in H0. rewrite (surjective_pairing sla2).
        iDestruct (H0 with "HA") as "[% [% %]]".
        eapply tr_simple_rvalue in H2. rewrite (surjective_pairing sla3).
        iDestruct (H2 with "HC") as "[% [% %]]".
        eapply step_tr_rvalof in H1. rewrite (surjective_pairing sla4).
        iDestruct (H1 with "HD") as "HD".
        iDestruct ("HD" with "[]") as (le') "[[% [% %]] HD]"; eauto. rewrite H5. rewrite H8.
        simpl Kseqlist. iExists _. iSplit.
        -- iPureIntro. right; split. rewrite app_ass. rewrite Kseqlist_app. eexact H14.
           simpl. unfold lt. omega.
        -- iPureIntro. constructor.
        -- auto.
      * iDestruct "HE" as (t1) "[HE %]". inversion H6; subst.
        eapply tr_simple_lvalue in H0. rewrite (surjective_pairing sla2).
        iDestruct (H0 with "HA") as "[% [% %]]".
        eapply tr_simple_rvalue in H2. rewrite (surjective_pairing sla3).
        iDestruct (H2 with "HC") as "[% [% %]]".
        eapply step_tr_rvalof in H1. rewrite (surjective_pairing sla4).
        iDestruct (H1 with "HD") as "HD".
        iDestruct ("HD" with "[]") as (le') "[[% [% %]] HD]"; eauto. rewrite H5. rewrite H9.
        simpl Kseqlist. iExists _. iSplit.
        -- iPureIntro. right; split. rewrite app_ass. rewrite Kseqlist_app. eexact H15.
           simpl. unfold lt; omega.
        -- iPureIntro. constructor.
        -- eauto.
      * iDestruct "HE" as (t1) "[HE %]". inversion H6; subst.
        eapply tr_simple_lvalue in H0. rewrite (surjective_pairing sla2).
        iDestruct (H0 with "HA") as "[% [% %]]".
        eapply tr_simple_rvalue in H2. rewrite (surjective_pairing sla3).
        iDestruct (H2 with "HC") as "[% [% %]]".
        eapply step_tr_rvalof in H1. rewrite (surjective_pairing sla4).
        iDestruct (H1 with "HD") as "HD".
        iDestruct ("HD" with "[]") as (le') "[[% [% %]] HD]"; eauto. rewrite H5. rewrite H9.
        simpl Kseqlist. iExists _. iSplit.
        -- iPureIntro. right; split. rewrite app_ass. rewrite Kseqlist_app. eexact H15.
           simpl. unfold lt; omega.
        -- iPureIntro. constructor.
        -- eauto.
    + unfold tr_top_val_val in H6. destruct sl1; auto. destruct H6 as (v'&ty0&P0&P1&P2&P3).
      inversion P3.

  (* postincr *)
  - exploit tr_top_leftcontext; intro. apply soundness3 in H14.
    apply (soundness1 _ tmps). iIntros "HA". iDestruct (H14 with "HA") as "HA". 
    iDestruct (H5 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
    iDestruct "HA" as "[[_ HA]|%]"; fold tr_expr. 
    + iDestruct "HA" as "[HA| HA]".
      * admit.
      * admit.
    + unfold tr_top_val_val in H7. destruct sl1; try contradiction.
      destruct H7 as (v&ty&P0&P1&P2&P3). inversion P3.

  (* postincr stuck *)
  - exploit tr_top_leftcontext; intro. apply soundness3 in H11.
    apply (soundness1 _ tmps). iIntros "HA". iDestruct (H11 with "HA") as "HA". 
    iDestruct (H3 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
    iDestruct "HA" as "[[_ HA]|%]"; fold tr_expr. 
    + iDestruct "HA" as "[HA|HA]".
      * iDestruct "HA" as (sla2 sla3) "[HA [HC %]]".
        eapply tr_simple_lvalue in H0. rewrite (surjective_pairing sla2).
        iDestruct (H0 with "HA") as "[% [% %]]".
        subst. 
        eapply step_tr_rvalof in H1; eauto. rewrite (surjective_pairing sla3).
        iDestruct (H1 with "HC") as "HC".
        iDestruct ("HC" with "[]") as (le') "[[% [% %]] HC]"; eauto. simpl in *. rewrite H5.
        rewrite H6. simpl Kseqlist.
        iExists _. iSplit; iPureIntro.
        -- right; split. rewrite app_ass; rewrite Kseqlist_app. eexact H4.
           unfold lt. omega.
        -- constructor.
      * iDestruct "HA" as (sla2 t1) "[HA [HC %]]". inversion H5. subst. 
        eapply tr_simple_lvalue in H0. rewrite (surjective_pairing sla2).
        iDestruct (H0 with "HA") as "[% [% %]]".
        rewrite H4. simpl Kseqlist. iExists _. iSplit.
        -- iPureIntro. left. eapply plus_two. constructor. eapply step_make_set; eauto.
           traceEq.
        -- iPureIntro. constructor.
    + unfold tr_top_val_val in H5. destruct sl1; auto. destruct H5 as (v'&ty0&P0&P1&P2&P3).
      inversion P3.

  (* comma *)
  - exploit tr_top_leftcontext; intro. apply soundness3 in H9.
    apply (soundness1 _ tmps). iIntros "HA". iDestruct (H9 with "HA") as "HA". 
    iDestruct (H1 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
    iDestruct "HA" as "[[_ HA]|%]"; fold tr_expr. 
    + iDestruct "HA" as (sla2 sl3) "[HA [HD [HC %]]]". simpl in *. subst.
      eapply tr_simple_rvalue in H0. rewrite (surjective_pairing sla2).
      iDestruct (H0 with "HA") as "%". rewrite H2. simpl Kseqlist. iClear "HA".
      iExists _. iSplit.
      * iPureIntro. right; split. apply star_refl. simpl. apply plus_lt_compat_r.
        apply (leftcontext_size _ _ _ H). simpl. omega.
      * iStopProof. apply test3. apply test2. intros. econstructor; eauto.
        apply soundness3 in H3. apply soundness2.
        iIntros "HA". iDestruct (H3 with "HA") as "[HB [HC HD]]".
        iApply ("HD" with "[HB HC]"); eauto. iApply "HB". iFrame.
    + unfold tr_top_val_val in H3. destruct sl1; auto. destruct H3 as (v'&ty0&P0&P1&P2&P3).
      inversion P3.

  (* paren *)
  - exploit tr_top_leftcontext; intro. apply soundness3 in H9.
    apply (soundness1 _ tmps). iIntros "HA". iDestruct (H9 with "HA") as "HA". 
    iDestruct (H2 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
    iDestruct "HA" as "[[_ HA]|%]"; fold tr_expr. 
    + destruct dst'.
      * iDestruct "HA" as (a2 t0) "[HA [HC %]]".
        eapply tr_simple_rvalue in H0. iDestruct ("HA" with "HC") as "HA".
        iDestruct (H0 with "HA") as (?) "[% [% %]]". simpl in *. subst. simpl Kseqlist.
        iExists _. iSplit.
        -- iPureIntro. left. eapply plus_left. constructor. apply star_one. econstructor.
           econstructor; eauto. rewrite <- H7; eauto. traceEq.
        -- admit.
      * iDestruct "HA" as (a2) "HA".
        eapply tr_simple_rvalue in H0. simpl.
        iDestruct (H0 with "HA") as "%". simpl in *. subst. simpl Kseqlist.
        iExists _. iSplit.
        -- iPureIntro. right; split. apply star_refl. simpl. apply plus_lt_compat_r.
           apply (leftcontext_size _ _ _ H). simpl.
           unfold lt. apply le_n_S. apply le_0_n.
        -- iStopProof. apply test3. apply test2. intros. econstructor; eauto.
           apply soundness3 in H3. apply soundness2.
           iIntros "HA". iDestruct (H3 with "HA") as "[HA HB]".
           change sl2 with (nil ++ sl2).
           iApply ("HB" with "[HA]"); eauto.
      * admit.
    + unfold tr_top_val_val in H4. destruct sl1; auto. destruct H4 as (v'&ty0&P0&P1&P2&P3).
      inversion P3.

  (* call *)
  - exploit tr_top_leftcontext; intro. apply soundness3 in H12.
    apply (soundness1 _ tmps). iIntros "HA". iDestruct (H12 with "HA") as "HA". 
    iDestruct (H5 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
    iDestruct "HA" as "[[_ HA]|%]"; fold tr_expr; fold tr_exprlist.
    + destruct dst'.
      * iDestruct "HA" as (sla2 slal3 t0) "[HA [HC [HD [_ %]]]]". inversion H7; subst.
        eapply tr_simple_rvalue in H1. rewrite (surjective_pairing sla2).
        iDestruct (H1 with "HA") as "[% [% %]]". rewrite H6.
        rewrite (surjective_pairing slal3).
        iDestruct (tr_simple_exprlist with "HC") as "HC"; eauto.
        iDestruct ("HC" with "[]") as "[% %]"; eauto. rewrite H10. simpl Kseqlist.
        apply functions_translated in H3. destruct H3 as (tf'&P0&P1).
        iExists _. iSplit.
        -- iPureIntro. left. eapply plus_left. constructor. apply star_one.
           econstructor; eauto. rewrite <- H8; eauto. exploit type_of_fundef_preserved; eauto.
           congruence. traceEq.
        -- iStopProof. apply test3. apply test2. intros. constructor; auto.
           econstructor; eauto. intros.
           apply soundness3 in H3. apply soundness2.
           iIntros "HA". iDestruct (H3 with "HA") as "[HA [HB HC]]".
           change sl2 with (nil ++ sl2).
           iApply ("HC" with "[HA HB]"); eauto. simpl. iSplitL "HA"; eauto.
           iSplit; eauto. iIntros (? ? ? ?) "HA".
           iDestruct ("HA" with "HB") as "%". iPureIntro. constructor. rewrite H15.
           apply Maps.PTree.gss. iIntros. admit.
      * iDestruct "HA" as (sla2 slal3) "[HA [HC %]]". simpl in *. subst.
        eapply tr_simple_rvalue in H1. rewrite (surjective_pairing sla2).
        iDestruct (H1 with "HA") as "[% [% %]]". rewrite H6.
        rewrite (surjective_pairing slal3).
        iDestruct (tr_simple_exprlist with "HC") as "HC"; eauto.
        iDestruct ("HC" with "[]") as "[% %]"; eauto. rewrite H9. simpl Kseqlist.
        apply functions_translated in H3. destruct H3 as (tf'&P0&P1).
        iExists _. iSplit.
        -- iPureIntro. left. eapply plus_left. constructor. apply star_one.
           econstructor; eauto. rewrite <- H7; eauto. exploit type_of_fundef_preserved; eauto.
           congruence. traceEq.
        -- iStopProof. apply test3. apply test2. intros. constructor; auto.
           econstructor; eauto. intros.
           apply soundness3 in H3. apply soundness2.
           iIntros "HA". iDestruct (H3 with "HA") as "[HA HB]".
           change sl2 with (nil ++ sl2).
           iApply ("HB" with "[HA]"); eauto.
      * admit.
    + unfold tr_top_val_val in H7. destruct sl1; auto. destruct H7 as (v'&ty0&P0&P1&P2&P3).
      inversion P3.

  (* builtin *)
  - exploit tr_top_leftcontext; intro. apply soundness3 in H9.
    apply (soundness1 _ tmps). iIntros "HA". iDestruct (H9 with "HA") as "HA". 
    iDestruct (H2 with "HA") as "HA". iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct ("HA" with "[]") as "HA"; eauto.
    iDestruct "HA" as (dst' sl1 sl2 a') "[HA [% HB]]". simpl. unfold tr_top.
    iDestruct "HA" as "[[_ HA]|%]"; fold tr_expr; fold tr_exprlist.
    + destruct dst'.
      * iDestruct "HA" as (slal2 t1) "[HA [HD [_ %]]]". inversion H4; subst.
        rewrite (surjective_pairing slal2).
        iDestruct (tr_simple_exprlist with "HA") as "HA"; eauto.
        iDestruct ("HA" with "[]") as "[% %]"; eauto. rewrite H3. simpl Kseqlist.
        iExists _. iSplit.
        -- iPureIntro. left. eapply plus_left. constructor. apply star_one.
           econstructor; eauto. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
           traceEq.
        -- iStopProof. apply test3. apply test2. intros. econstructor; eauto.
           apply soundness3 in H6. apply soundness2.
           iIntros "HA". iDestruct (H6 with "HA") as "[HA HB]".
           change sl2 with (nil ++ sl2).
           iApply ("HB" with "[HA]"); eauto. epose tr_val_gen.
           change [] with (final For_val (Etempvar t1 ty)).
           iApply tr_val_gen. reflexivity. iIntros. admit. admit.
      * iDestruct "HA" as (slal2) "[HA %]". simpl in *; subst.
        rewrite (surjective_pairing slal2).
        iDestruct (tr_simple_exprlist with "HA") as "HA"; eauto.
        iDestruct ("HA" with "[]") as "[% %]"; eauto. rewrite H3. simpl Kseqlist.
        iExists _. iSplit.
        -- iPureIntro. left. eapply plus_left. constructor. apply star_one.
           econstructor; eauto. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
           traceEq.
        -- iStopProof. apply test3. apply test2. intros. econstructor; eauto.
           apply soundness3 in H5. apply soundness2.
           iIntros "HA". iDestruct (H5 with "HA") as "HA".
           change sl2 with (nil ++ sl2). iApply "HA"; eauto.
      * iDestruct "HA" as (slal2 t1) "[HA [HD [HE %]]]". inversion H4; subst.
        rewrite (surjective_pairing slal2).
        iDestruct (tr_simple_exprlist with "HA") as "HA"; eauto.
        iDestruct ("HA" with "[]") as "[% %]"; eauto. rewrite H3. simpl Kseqlist.
        iExists _. iSplit.
        -- iPureIntro. left. eapply plus_left. constructor. apply star_one.
           econstructor; eauto. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
           traceEq.
        -- iStopProof. apply test3. apply test2. intros. econstructor; eauto.
           apply soundness3 in H6. apply soundness2.
           iIntros "HA". iDestruct (H6 with "HA") as "[HA [HC HB]]".
           change sl2 with (nil ++ sl2).
           iApply ("HB" with "[HA] [HC]"); eauto. 
           change (do_set sd (Etempvar t1 ty)) with (final (For_set sd) (Etempvar t1 ty)).
           iApply (tr_val_gen with "[HA]"). reflexivity. iIntros (? ? ? ?) "HB".
           iDestruct ("HB"  with "HA") as "%".
           iPureIntro. constructor. rewrite H7. apply Maps.PTree.gss.
           iIntros (?) "HA". simpl. admit.
    + unfold tr_top_val_val in H4. destruct sl1; auto. destruct H4 as (v'&ty0&P0&P1&P2&P3).
      inversion P3.
Admitted.


(** Forward simulation for statements. *)

Lemma tr_top_val_for_val_inv:
  forall e le m v ty sl a,
  tr_top tge e le m For_val (Csyntax.Eval v ty) sl a -∗
  ⌜sl = nil /\ typeof a = ty /\ eval_expr tge e le m a v⌝.
Proof.
  iIntros (? ? ? ? ? ? ?) "HA". iDestruct "HA" as "[HA|%]".
  - unfold tr_top_base. simpl. iDestruct "HA" as "[HA [HB [% %]]]".
    repeat iSplit; auto. iApply "HB". eauto.
  - unfold tr_top_val_val in H. destruct sl; auto.
    destruct H as (v0&ty0&P0&P1&P2&P3). inversion P3. subst.
    iPureIntro. repeat split; auto.
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
  inv H7. apply soundness3 in H6.
  apply (soundness1 _ tmps). iIntros "HA". iDestruct (H6 with "HA") as "[[_ %]|%]".
  iPureIntro. simpl in *; subst.
  econstructor; split.
  right; split. apply star_refl. simpl. unfold lt. reflexivity. 
  econstructor; eauto. constructor.
  unfold tr_top_val_val in H. destruct sl; auto. destruct H as (v0&ty0&P0&P1&P2&P3). inversion P2.
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
  exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H7. iIntros "HA". iDestruct (H7 with "HA") as "HA".
  iDestruct (H0 with "HA") as "[% [% %]]". subst. iPureIntro.
  econstructor; split; simpl.
  right. destruct b; econstructor; eauto.
  eapply star_left. apply step_skip_seq. econstructor. traceEq.
  eapply star_left. apply step_skip_seq. econstructor. traceEq.
  destruct b; econstructor; eauto. econstructor; eauto. econstructor; eauto.
  (* ifthenelse non empty *)
  exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H7. iIntros "HA". iDestruct (H7 with "HA") as "HA".
  iDestruct (H0 with "HA") as "[% [% %]]". subst. iPureIntro.
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
  exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H7. iIntros "HA". iDestruct (H7 with "HA") as "HA".
  iDestruct (H0 with "HA") as "[% [% %]]". subst. iPureIntro.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
  eapply star_two. constructor. apply step_break_loop1.
  reflexivity. reflexivity. traceEq.
  constructor; auto. constructor.
(* while true *)
  inv H8.
  exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H7. iIntros "HA". iDestruct (H7 with "HA") as "HA".
  iDestruct (H0 with "HA") as "[% [% %]]". subst. iPureIntro. 
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
  exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H7. iIntros "HA". iDestruct (H7 with "HA") as "HA".
  iDestruct (H0 with "HA") as "[% [% %]]". subst. iPureIntro.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := false); auto.
  constructor.
  reflexivity. traceEq.
  constructor; auto. constructor.
(* dowhile true *)
  inv H8.
  exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H7. iIntros "HA". iDestruct (H7 with "HA") as "HA".
  iDestruct (H0 with "HA") as "[% [% %]]". subst. iPureIntro.
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
  inv H8. exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H7. iIntros "HA". iDestruct (H7 with "HA") as "HA".
  iDestruct (H0 with "HA") as "[% [% %]]". subst. iPureIntro.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
  eapply star_two. constructor. apply step_break_loop1.
  reflexivity. reflexivity. traceEq.
  constructor; auto. constructor.
(* for true *)
  inv H8. exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H7. iIntros "HA". iDestruct (H7 with "HA") as "HA".
  iDestruct (H0 with "HA") as "[% [% %]]". subst. iPureIntro.
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
  inv H9. exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H8. iIntros "HA". iDestruct (H8 with "HA") as "HA".
  iDestruct (H1 with "HA") as "[% [% %]]". subst. iPureIntro.
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
  inv H8. exploit tr_top_val_for_val_inv; eauto. intro. apply (soundness1 _ tmps).
  apply soundness3 in H7. iIntros "HA". iDestruct (H7 with "HA") as "HA".
  iDestruct (H0 with "HA") as "[% [% %]]". subst. iPureIntro.
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
