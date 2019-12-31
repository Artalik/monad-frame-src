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
  - destruct dst.
    + iIntros "[% [% %]]". iPureIntro. intros; auto.
    + iIntros. iPureIntro. intros; auto.
    + iIntros "[% [% %]]". iPureIntro. intros. destruct H2; discriminate.
  - iIntros "[_ %]". iPureIntro. intros. inversion H. destruct dst; auto.
  - iIntros "HA". iDestruct "HA" as (sla2) "[HA [HB %]]".
    rewrite (surjective_pairing sla2). iIntros.
    iDestruct (H with "[HA]") as "HC". iApply "HA".
    destruct dst.
    + iDestruct ("HC" $! a0 a1) as "HA". simpl in *. inversion H0. rewrite app_nil_r. iApply "HA". 
    + iDestruct ("HC" with "[]") as "HA"; eauto. inversion H0. rewrite app_nil_r.
      iApply ("HA" $! a1).
    + destruct a0; discriminate.
  - iIntros "HA % %". iDestruct "HA" as (sla2 sl3) "[HA [HB [HC %]]]".
    rewrite (surjective_pairing sla2).
    iDestruct (H with "HA") as "HD".
    apply andb_true_iff in a1 as (P0&P1).
    unfold tr_rvalof. apply negb_true_iff in P1. rewrite P1.
    iDestruct "HB" as "%". inversion H1; subst. destruct dst; simpl in *; try rewrite app_nil_r.
    + iApply ("HD" $! a0 P0).
    + iApply "HD"; eauto.
    + destruct a0; discriminate.
  - iIntros "HA % %". iDestruct "HA" as (sla2) "[HA [HB %]]".
    rewrite (surjective_pairing sla2).
    iDestruct (H with "HA") as "HD".
    inversion H0.
    destruct dst; simpl in *; try (rewrite app_nil_r; iApply "HD";eauto); destruct a0; discriminate.
  - iIntros "HA % %". iDestruct "HA" as (sla2) "[HA [HB %]]".
    rewrite (surjective_pairing sla2).
    iDestruct (H with "HA") as "HD".
    inversion H0.
    destruct dst; simpl in *; try (rewrite app_nil_r; iApply "HD";eauto); destruct a0; discriminate.
  - iIntros "HA % %". iDestruct "HA" as (sla2) "[HA [HB %]]".
    rewrite (surjective_pairing sla2).
    iDestruct (H with "HA") as "HD".
    inversion H0.
    destruct dst; simpl in *; try (rewrite app_nil_r; iApply "HD";eauto); destruct a0; discriminate.
  - iIntros "HA % %". iDestruct "HA" as (sla2 sl3) "[HA [HB [HC %]]]".
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
  - iIntros "HA % %". iDestruct "HA" as (sla2) "[HA [HB %]]".
    rewrite (surjective_pairing sla2).
    iDestruct (H with "HA") as "HD".
    inversion H0.
    destruct dst; simpl in *; try (rewrite app_nil_r; iApply "HD";eauto); destruct a0; discriminate.
  - iIntros "[HA %] % %". inversion H.
    destruct dst; eauto.
  - iIntros "[HA %] % %". inversion H.
    destruct dst; eauto.
  - iIntros "% %". inversion a; eauto.
  - iIntros "HA %". iDestruct "HA" as (sla2 slal3) "[HA [HB %]]".
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
- destruct dst; simpl in *; iIntros "%".
  + destruct a0 as (P0&P1&P2). iPureIntro. repeat split; auto. 
  + iPureIntro. assumption.
  + iExists a. destruct a0 as (P0&P1&P2). iPureIntro. split; auto.
(* rvalof *)
- destruct dst; subst; simpl in *.
  + iIntros "HA". iDestruct "HA" as (sla2 sl3) "[HA [HB [_ %]]]".
    rewrite (surjective_pairing sla2).
    iDestruct (H0 with "HA") as "[% [% %]]".
    unfold tr_rvalof. rewrite H2. iDestruct "HB" as "%". inversion H7; subst.
    iPureIntro. repeat split; auto. do 2 rewrite app_nil_r. apply H4.
    eapply eval_Elvalue; eauto.
    exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H2.
    intros (P0&P1). rewrite <- H5. assumption.
  + iIntros "HA". iDestruct "HA" as (sla2 sl3) "[HA [HB [_ %]]]".
    rewrite (surjective_pairing sla2).
    iDestruct (H0 with "HA") as "[% [% %]]".
    unfold tr_rvalof. rewrite H2. iDestruct "HB" as "%". inversion H7; subst.
    iPureIntro. do 2 rewrite app_nil_r. apply H4.
  + iIntros "HA". iDestruct "HA" as (sla2 sl3) "[HA [HB [_ %]]]". iExists a.
    rewrite (surjective_pairing sla2).
    iDestruct (H0 with "HA") as "[% [% %]]".
    unfold tr_rvalof. rewrite H2. iDestruct "HB" as "%". inversion H7; subst.
    iPureIntro. repeat split; auto. rewrite H4. do 2 rewrite app_nil_l. reflexivity.
    eapply eval_Elvalue; eauto.
    exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H2.
    intros (P0&P1). rewrite <- H5. apply P1.
- iIntros "HA". iDestruct "HA" as (sla2) "[HA [HB %]]". rewrite (surjective_pairing sla2).
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
- iIntros "HA". iDestruct "HA" as (sla2) "[HA [HB %]]". rewrite (surjective_pairing sla2).
  iDestruct (H0 with "HA") as "[% [% %]]". inversion H2.
  destruct dst; simpl in *; subst.
  + iPureIntro. repeat split; auto.
    * rewrite app_nil_r. apply H3.
    * rewrite H4 in H1. econstructor; eauto.
  + iPureIntro. rewrite app_nil_r. apply H3.
  + iExists (Eunop op0 sla2.2 ty). iPureIntro. repeat split.
    * rewrite H3. rewrite app_nil_l. reflexivity.
    * rewrite H4 in H1. econstructor; eauto.
- iIntros "HA". iDestruct "HA" as (sla2 sla3) "[HA [HB [HC %]]]". rewrite (surjective_pairing sla2).
  iDestruct (H0 with "HA") as "[% [% %]]". rewrite (surjective_pairing sla3).
  iDestruct (H2 with "HB") as "[% [% %]]". inversion H4.
  destruct dst; simpl in *; subst; rewrite H5 H8; try iExists (Ebinop op0 sla2.2 sla3.2 ty);
    do 2 rewrite app_nil_l; iPureIntro; repeat split; auto; econstructor; eauto; rewrite <- H6;
      auto; rewrite <- H9; rewrite comp_env_preserved; apply H3.
- iIntros "HA". iDestruct "HA" as (sla2)  "[HA [HB %]]". rewrite (surjective_pairing sla2).
  iDestruct (H0 with "HA") as "[% [% %]]". inversion H2.
  destruct dst; simpl in *; subst; rewrite H3; try iExists (Ecast sla2.2 ty); iPureIntro;
    rewrite app_nil_l; repeat split; auto; econstructor; eauto; rewrite <- H4; auto.
- iIntros "[HA %]". inversion H.
  destruct dst; simpl in *; subst; try iExists (Esizeof ty1 ty); iPureIntro; repeat split; eauto;
    pose (P := comp_env_preserved); simpl in P; rewrite <- P; apply eval_Esizeof.
- iIntros "[HA %]". inversion H.
  destruct dst; simpl in *; subst; try iExists (Ealignof ty1 ty); iPureIntro; repeat split; eauto;
    pose (P := comp_env_preserved); simpl in P; rewrite <- P; constructor.
- iIntros. contradiction a0.
- iIntros "[_ %]". inversion H0. iPureIntro. repeat split; auto. constructor. apply H.
- iIntros "[_ %]". inversion H1. iPureIntro. repeat split; auto.
  apply eval_Evar_global; auto.
  rewrite symbols_preserved; auto.
- iIntros "HA". iDestruct "HA" as (sla2)  "[HA [HB %]]". rewrite (surjective_pairing sla2).
  iDestruct (H0 with "HA") as "[% [% %]]". inversion H1. iPureIntro. subst. repeat split.
  rewrite app_nil_r. apply H2. rewrite typeof_Ederef'; auto. apply eval_Ederef'; auto. 
- iIntros "HA". iDestruct "HA" as (sla2)  "[HA [HB %]]". rewrite (surjective_pairing sla2).
  iDestruct (H0 with "HA") as "[% [% %]]". inversion H4. subst. iPureIntro. repeat split.
  rewrite app_nil_r. apply H5. rewrite <- comp_env_preserved in *. rewrite H6 in H1.
  eapply eval_Efield_struct; eauto.
- iIntros "HA". iDestruct "HA" as (sla2)  "[HA [HB %]]". rewrite (surjective_pairing sla2).
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
  - iIntros. inversion a.
    iPureIntro. repeat split; eauto. inversion a0. constructor.
  - simpl. iIntros (? ?) "HA". iIntros (? ? ? ?) "%". iDestruct "HA" as (sla2 slal3) "[HA [HB %]]".
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
  tr_expr le dst (C e) (sl,a)-∗
  ∃ dst' sl1 sl2 a',
  tr_expr le dst' e (sl1,a')  ∗ ⌜ sl = sl1 ++ sl2 ⌝
  ∗ (∀ le' e' sl3,
        tr_expr le' dst' e' (sl3,a') -∗
        (∀ id, (\s id -∗ False) -∗ ⌜ le'!id = le!id ⌝) -∗
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
        tr_expr le' dst' e' (sl3,a') -∗
        (∀ id, (\s id -∗ False) -∗ ⌜ le'!id = le!id⌝) -∗
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
        tr_expr le' dst' r' (sl3,a') -∗
        (∀ id, (\s id -∗ False) -∗ ⌜ le'!id = le!id ⌝) -∗
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
        tr_expr le' dst' r' (sl3,a') -∗
        (∀ id, (\s id -∗ False) -∗ ⌜le'!id = le!id ⌝) -∗
        ⌜ Csyntax.typeof r' = Csyntax.typeof r ⌝ -∗
        tr_top tge e le' m' dst (C r') (sl3 ++ sl2) a).
Proof.
Admitted.

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
Admitted.

(** Matching between continuations *)

Inductive match_cont : Csem.cont -> cont -> Prop :=
  | match_Kstop:
      match_cont Csem.Kstop Kstop
  | match_Kseq: forall s k ts tk tmp,
      tr_stmt s ts () tmp ->
      match_cont k tk ->
      match_cont (Csem.Kseq s k) (Kseq ts tk)
  | match_Kwhile2: forall r s k s' ts tk tmp tmp',
      tr_if r Sskip Sbreak s' () tmp->
      tr_stmt s ts () tmp' ->
      match_cont k tk ->
      match_cont (Csem.Kwhile2 r s k)
                 (Kloop1 (Ssequence s' ts) Sskip tk)
  | match_Kdowhile1: forall r s k s' ts tk tmp,
      tr_if r Sskip Sbreak s' () tmp ->
      tr_stmt s ts () tmp ->
      match_cont k tk ->
      match_cont (Csem.Kdowhile1 r s k)
                 (Kloop1 ts s' tk)
  | match_Kfor3: forall r s3 s k ts3 s' ts tk tmp tmp' tmp'',
      tr_if r Sskip Sbreak s' () tmp->
      tr_stmt s3 ts3 () tmp' ->
      tr_stmt s ts () tmp'' ->
      match_cont k tk ->
      match_cont (Csem.Kfor3 r s3 s k)
                 (Kloop1 (Ssequence s' ts) ts3 tk)
  | match_Kfor4: forall r s3 s k ts3 s' ts tk tmp tmp' tmp'',
      tr_if r Sskip Sbreak s' () tmp ->
      tr_stmt s3 ts3 () tmp' ->
      tr_stmt s ts () tmp'' ->
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
  | match_Kifthenelse_1: forall a s1 s2 k ts1 ts2 tk tmp tmp',
      tr_stmt s1 ts1 () tmp -> tr_stmt s2 ts2 () tmp' ->
      match_cont k tk ->
      match_cont_exp For_val a (Csem.Kifthenelse s1 s2 k) (Kseq (Sifthenelse a ts1 ts2) tk)
  | match_Kwhile1: forall r s k s' a ts tk tmp tmp',
      tr_if r Sskip Sbreak s' () tmp ->
      tr_stmt s ts () tmp' ->
      match_cont k tk ->
      match_cont_exp For_val a
         (Csem.Kwhile1 r s k)
         (Kseq (makeif a Sskip Sbreak)
           (Kseq ts (Kloop1 (Ssequence s' ts) Sskip tk)))
  | match_Kdowhile2: forall r s k s' a ts tk tmp tmp',
      tr_if r Sskip Sbreak s' () tmp ->
      tr_stmt s ts () tmp' ->
      match_cont k tk ->
      match_cont_exp For_val a
        (Csem.Kdowhile2 r s k)
        (Kseq (makeif a Sskip Sbreak) (Kloop2 ts s' tk))
  | match_Kfor2: forall r s3 s k s' a ts3 ts tk tmp tmp' tmp'',
      tr_if r Sskip Sbreak s' () tmp ->
      tr_stmt s3 ts3 () tmp' ->
      tr_stmt s ts () tmp'' ->
      match_cont k tk ->
      match_cont_exp For_val a
        (Csem.Kfor2 r s3 s k)
        (Kseq (makeif a Sskip Sbreak)
          (Kseq ts (Kloop1 (Ssequence s' ts) ts3 tk)))
  | match_Kswitch1: forall ls k a tls tk tmp,
      tr_lblstmts ls tls () tmp ->
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
  | match_regularstates: forall f s k e m tf ts tk le tmp,
      tr_function f tf ->
      tr_stmt s ts () tmp ->
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
  tr_lblstmts ls tls -∗
  tr_lblstmts (Csem.select_switch n ls) (select_switch n tls).
Proof.
Admitted.

Lemma tr_seq_of_labeled_statement:
  forall ls tls,
  tr_lblstmts ls tls -∗
  tr_stmt (Csem.seq_of_labeled_statement ls) (seq_of_labeled_statement tls).
Proof.
  Admitted.

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
  Admitted.

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
  | [ |- nolabel _ ] => red; intros; simpl; auto
  | [ |- _ /\ _ ] => split; NoLabelTac
  | _ => auto
  end.

Lemma tr_find_label_expr:
  (forall le dst r sl a, tr_expr le dst r (sl,a) -∗ ⌜ nolabel_list sl ⌝)
/\(forall le rl sl al, tr_exprlist le rl (sl,al) -∗ ⌜ nolabel_list sl ⌝).
Proof.
  Admitted.
  
Lemma tr_find_label_top:
  forall e le m dst r sl a,
    tr_top tge e le m dst r sl a -∗ ⌜ nolabel_list sl ⌝.
Proof.
  Admitted.

Lemma tr_find_label_expression:
  forall r s a, tr_expression r s a -∗ ⌜ forall k, find_label lbl s k = None ⌝.
Proof.
Admitted.

Lemma tr_find_label_expr_stmt:
  forall r s, tr_expr_stmt r s -∗ ⌜ forall k, find_label lbl s k = None ⌝.
Proof.
  Admitted.

Lemma tr_find_label_if:
  forall r s, tr_if r Sskip Sbreak s -∗ ⌜ forall k, find_label lbl s k = None ⌝.
Proof.
Admitted.


Lemma tr_find_label:
  forall s k ts tk,
    tr_stmt s ts -∗
    ⌜ match_cont k tk ⌝ -∗
  match Csem.find_label lbl s k with
  | None =>
      ⌜ find_label lbl ts tk = None ⌝
  | Some (s', k') =>
      ∃ ts', ∃ tk',
          ⌜ find_label lbl ts tk = Some (ts', tk') ⌝
       ∗ tr_stmt s' ts'
       ∗ ⌜match_cont k' tk'⌝
  end
with tr_find_label_ls:
  forall s k ts tk,
    tr_lblstmts s ts -∗
                ⌜ match_cont k tk ⌝-∗
  match Csem.find_label_ls lbl s k with
  | None =>
      ⌜ find_label_ls lbl ts tk = None ⌝
  | Some (s', k') =>
      ∃ ts' tk',
          ⌜ find_label_ls lbl ts tk = Some (ts', tk') ⌝
       ∗ tr_stmt s' ts'
       ∗ ⌜match_cont k' tk'⌝
  end.
Proof.
Admitted.

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
Admitted.


Lemma estep_simulation:
  forall S1 t S2, Cstrategy.estep ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  ∃ S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.
Admitted.

(** Forward simulation for statements. *)

Lemma tr_top_val_for_val_inv:
  forall e le m v ty sl a,
  tr_top tge e le m For_val (Csyntax.Eval v ty) sl a -∗
  ⌜sl = nil /\ typeof a = ty /\ eval_expr tge e le m a v⌝.
Proof.
  Admitted.

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
  forall S1', match_states S1 S1' ->
  ∃ S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.
Admitted.

(** Semantic preservation *)

Theorem simulation:
  forall S1 t S2, Cstrategy.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  ∃ S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
      /\ match_states S2 S2'.
Proof.
Admitted.

Lemma transl_initial_states:
  forall S,
  Csem.initial_state prog S ->
  exists S',  Clight.initial_state tprog S' /\ match_states S S'.
Proof.
Admitted.

Lemma transl_final_states:
  ∀ S S' r,
  match_states S S' -> Csem.final_state S r -> Clight.final_state S' r.
Proof.
Admitted.

Lemma test : forall (P : iProp) Q tmps, Q /\ P () tmps <-> (\⌜Q⌝ ∗ P) () tmps.
Proof.
  intros.
  split; intro.
  - destruct H. apply soundness2. apply soundness3 in H0. iIntros "HA".
    iDestruct (H0 with "HA") as "HA". iFrame. iPureIntro. apply H.
  - apply soundness3 in H. split.
    + apply (soundness1 _ tmps). iIntros "HA". iDestruct (H with "HA") as "[HA HB]". iFrame.
    + apply soundness2. iIntros "HA". iDestruct (H with "HA") as "[HA HB]". iFrame.
Qed.

Print forward_simulation_star_wf.

Theorem transl_program_correct:
  forward_simulation (Cstrategy.semantics prog) (Clight.semantics1 tprog).
Proof.
  Locate forward_simulation_star_wf.
  Print forward_simulation. Print fsim_properties.
  Print forward_simulation_star_wf.
  eapply forward_simulation_star_wf with (order := ltof _ measure).
  eapply senv_preserved.
  - intros. eapply transl_initial_states in H. destruct H as (S'&P0&P1).
    exists S'. split; auto. eapply P1.
  - simpl. intros.
    eapply transl_final_states; eauto. 
  - apply well_founded_ltof.
  - simpl. intros. eapply simulation in H. instantiate (1 := s2) in H.
    instantiate (1 := ∅).
    apply soundness3 in H0. eapply (soundness1 _ ∅).
    iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iDestruct (H with "HA") as (s2') "[% HA]".
    pose init_heap. apply H0 in b.

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
