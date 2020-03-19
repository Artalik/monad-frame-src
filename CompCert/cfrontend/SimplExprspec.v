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
Require Import MoSel Locally.
Import Maps.PTree.
Export weakestpre_gensym.
Import adequacy.
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

  Definition dest_below (dst: destination) : iProp :=
    match dst with
    | For_set sd => \s (sd_temp sd)
    | _ => \⌜True⌝
    end.


  Definition final (dst: destination) (a: expr) : list statement :=
    match dst with
    | For_val => nil
    | For_effects => nil
    | For_set sd => do_set sd a
    end.
      
  (** Iris version *)
  Definition tr_rvalof (ty : type) (e1 : expr) (ls : list statement) (e : expr) : iProp :=
    if type_is_volatile ty
    then
      (∃ t, \⌜ ls = make_set t e1 :: nil /\ e = Etempvar t ty⌝ ∗ \s t)%I
    else
      \⌜ls =nil /\ e = e1⌝%I.

  
  Lemma test2 : forall (P : iProp) (Q : Prop), (forall tmps, P () tmps -> Q) -> (⊢P -∗ ⌜Q⌝).
  Proof.
    MonPred.unseal. intros. split. red. red. MonPred.unseal. intros. repeat red.
    intros. exists emp. red. exists ∅. exists ∅. repeat split; auto.
    - repeat red. intros. inversion_star H h P. clear H2.
      inv P1. inv H3. exists heap_empty, h0. repeat split; auto. destruct a. eapply H; eauto.
    - inversion H0. inversion H3. rewrite heap_union_empty_l. reflexivity.
  Qed.
  
  Lemma test3 (P Q : iProp) : (emp ⊢ P -∗ Q) -> (P ⊢ Q).
  Proof.
    intro. iIntros "HA". iDestruct H as "HB". iApply "HB"; eauto.
  Qed.
  
  Fixpoint tr_expr (le : temp_env) (dst : destination) (e : Csyntax.expr)
           (sl : list statement ) (a : expr) : iProp :=
    (<absorb> 
    match e with
     | Csyntax.Evar id ty =>
       dest_below dst ∗ \⌜ sl = final dst (Evar id ty) /\  a = Evar id ty ⌝ 
     | Csyntax.Ederef e1 ty =>
       dest_below dst ∗ 
       ∃ sl2 a2, tr_expr le For_val e1 sl2 a2 ∗
      \⌜sl = sl2 ++ final dst (Ederef' a2 ty) /\ a = Ederef' a2 ty⌝
    | Csyntax.Efield e1 f ty =>
      dest_below dst ∗ ∃ sl2 a2, tr_expr le For_val e1 sl2 a2 ∗
      \⌜ sl = sl2 ++ final dst (Efield a2 f ty) /\ a = Efield a2 f ty ⌝
| Csyntax.Eval v ty =>
  match dst with
  | For_effects => \⌜sl = nil⌝
  | For_val =>
    (∀ tge e m, locally le (fun le' => ⌜eval_expr tge e le' m a v⌝))
    ∗ \⌜ typeof a = ty /\ sl = nil ⌝
  | For_set sd =>
    (<absorb> dest_below dst) ∧
    ∃ a,
    (∀ tge e m, locally le (fun le' => ⌜eval_expr tge e le' m a v⌝))
      ∗ ⌜ typeof a = ty /\ sl = do_set sd a ⌝
                                       
  end
| Csyntax.Esizeof ty' ty =>
  dest_below dst ∗ \⌜ sl = final dst (Esizeof ty' ty) /\ a = Esizeof ty' ty⌝
| Csyntax.Ealignof ty' ty =>
  dest_below dst ∗ \⌜ sl = final dst (Ealignof ty' ty) /\ a = Ealignof ty' ty ⌝
| Csyntax.Evalof e1 ty =>
  dest_below dst ∗ 
  ∃ sl2 a2 sl3,
    tr_expr le For_val e1 sl2 a2  ∗
    tr_rvalof (Csyntax.typeof e1) a2 sl3 a  ∗
    \⌜ sl = (sl2 ++ sl3 ++ final dst a) ⌝
| Csyntax.Eaddrof e1 ty =>
  dest_below dst ∗ 
  ∃ sl2 a2, tr_expr le For_val e1 sl2 a2  ∗
  \⌜ sl = sl2 ++ final dst (Eaddrof' a2 ty) /\ a = Eaddrof' a2 ty ⌝
| Csyntax.Eunop ope e1 ty =>
  dest_below dst ∗ 
  ∃ sl2 a2, tr_expr le For_val e1 sl2 a2  ∗
  \⌜ sl = sl2 ++ final dst (Eunop ope a2 ty) /\ a = Eunop ope a2 ty ⌝
| Csyntax.Ebinop ope e1 e2 ty =>
  dest_below dst ∗ 
  ∃ sl2 a2 sl3 a3, tr_expr le For_val e1 sl2 a2  ∗
  tr_expr le For_val e2 sl3 a3  ∗
  \⌜ sl = sl2 ++ sl3 ++ final dst (Ebinop ope a2 a3 ty) /\ a = Ebinop ope a2 a3 ty ⌝
| Csyntax.Ecast e1 ty =>
  dest_below dst ∗ 
  ∃ sl2 a2, tr_expr le For_val e1 sl2 a2  ∗
  \⌜ sl = sl2 ++ final dst (Ecast a2 ty) /\ a = Ecast a2 ty ⌝
| Csyntax.Eseqand e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sl2 a2 sl3 a3 t,
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
    ∗ \⌜ sl = sl2 ++ makeif a2 (makeseq sl3) (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil ⌝
  end
| Csyntax.Eseqor e1 e2 ty =>
  match dst with
  | For_val =>
    ∃ sl2 a2 sl3 a3 t,
     tr_expr le For_val e1 sl2 a2  ∗
     tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl3 a3 ∗
     \⌜ sl = sl2 ++ makeif a2 (Sset t (Econst_int Int.one ty)) (makeseq sl3) :: nil /\
              a = Etempvar t ty ⌝
| For_effects =>
  ∃ sl2 a2 sl3 a3, tr_expr le For_val e1 sl2 a2  ∗
  tr_expr le For_effects e2 sl3 a3  ∗
  \⌜ sl = sl2 ++ makeif a2 Sskip (makeseq sl3) :: nil ⌝
| For_set sd =>
  ∃ sl2 a2 sl3 a3,
  tr_expr le For_val e1 sl2 a2 ∗
  tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl3 a3 ∗
    \⌜ sl = sl2 ++ makeif a2 (makeseq (do_set sd (Econst_int Int.one ty))) (makeseq sl3) :: nil ⌝
  end

| Csyntax.Econdition e1 e2 e3 ty =>
  match dst with
  | For_val =>
    ∃ sl2 a2 sl3 a3 sl4 a4 t,
     tr_expr le For_val e1 sl2 a2 ∗
     (tr_expr le (For_set (SDbase ty ty t)) e2 sl3 a3 ∧
     tr_expr le (For_set (SDbase ty ty t)) e3 sl4 a4) ∗
     \⌜ sl = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil /\ a = Etempvar t ty⌝
| For_effects =>
  ∃ sl2 a2 sl3 a3 sl4 a4,
    tr_expr le For_val e1 sl2 a2  ∗
    tr_expr le For_effects e2 sl3 a3 ∗
    tr_expr le For_effects e3 sl4 a4 ∗
    \⌜ sl = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil ⌝
    | For_set sd =>
      dest_below dst ∗ 
      ∃ sl2 a2 sl3 a3 sl4 a4 t,
     tr_expr le For_val e1 sl2 a2  ∗
    (tr_expr le (For_set (SDcons ty ty t sd)) e2 sl3 a3 ∧
     tr_expr le (For_set (SDcons ty ty t sd)) e3 sl4 a4) ∗
     \⌜ sl = sl2 ++ makeif a2 (makeseq sl3) (makeseq sl4) :: nil ⌝
  end
| Csyntax.Eassign e1 e2 ty =>
  match dst with
  | For_effects =>
    ∃ sl2 a2 sl3 a3,
    tr_expr le For_val e1 sl2 a2  ∗
    tr_expr le For_val e2 sl3 a3  ∗
    \⌜ sl = sl2 ++ sl3 ++ make_assign a2 a3 :: nil ⌝
| _ =>
  ∃ sl2 a2 sl3 a3 t,
    tr_expr le For_val e1 sl2 a2  ∗
    tr_expr le For_val e2 sl3 a3  ∗
    \s t ∗ dest_below dst ∗ 
    \⌜ sl = sl2 ++ sl3 ++ Sset t (Ecast a3 (Csyntax.typeof e1)) :: make_assign a2 (Etempvar t (Csyntax.typeof e1)) :: final dst (Etempvar t (Csyntax.typeof e1)) /\ a = Etempvar t (Csyntax.typeof e1)⌝
  end
| Csyntax.Eassignop ope e1 e2 tyres ty =>
  match dst with
  | For_effects =>
    ∃ sl2 a2 sl3 a3 sl4 a4,
    tr_expr le For_val e1 sl2 a2  ∗
    tr_expr le For_val e2 sl3 a3  ∗
    tr_rvalof (Csyntax.typeof e1) a2 sl4 a4  ∗
    \⌜sl = sl2 ++ sl3 ++ sl4 ++ make_assign a2 (Ebinop ope a4 a3 tyres) :: nil ⌝
| _ =>
  ∃ sl2 a2 sl3 a3 sl4 a4 t,
    tr_expr le For_val e1 sl2 a2  ∗
    tr_expr le For_val e2 sl3 a3  ∗
    tr_rvalof (Csyntax.typeof e1) a2 sl4 a4  ∗
    \s t ∗ dest_below dst ∗ 
    \⌜ sl = sl2 ++ sl3 ++ sl4 ++ Sset t (Ecast (Ebinop ope a4 a3 tyres) (Csyntax.typeof e1)) :: make_assign a2 (Etempvar t (Csyntax.typeof e1)) :: final dst (Etempvar t (Csyntax.typeof e1))
    /\ a = Etempvar t (Csyntax.typeof e1) ⌝
  end
| Csyntax.Epostincr id e1 ty =>
  ∃ sl2 a2,
    tr_expr le For_val e1 sl2 a2  ∗
    match dst with
    | For_effects =>
    ∃ sl3 a3, tr_rvalof (Csyntax.typeof e1) a2 sl3 a3  ∗
    \⌜ sl = sl2 ++ sl3 ++ make_assign a2 (transl_incrdecr id a3 (Csyntax.typeof e1)) :: nil ⌝
| _ =>
  ∃ t, \s t  ∗ dest_below dst ∗ 
        \⌜ sl = sl2 ++ make_set t a2 ::make_assign a2 (transl_incrdecr id (Etempvar t (Csyntax.typeof e1)) (Csyntax.typeof e1)) :: final dst (Etempvar t (Csyntax.typeof e1)) /\ a = Etempvar t (Csyntax.typeof e1)⌝
  end

| Csyntax.Ecomma e1 e2 ty =>
  ∃ sl2 a2 sl3,
    tr_expr le For_effects e1 sl2 a2  ∗
    tr_expr le dst e2 sl3 a ∗
    \⌜ sl = sl2 ++ sl3 ⌝

| Csyntax.Ecall e1 el2 ty =>
  match dst with
  | For_effects =>
    ∃ sl2 a2 sl3 al3,
    tr_expr le For_val e1 sl2 a2  ∗
    tr_exprlist le el2 sl3 al3  ∗
    \⌜  sl = sl2 ++ sl3 ++ Scall None a2 al3 :: nil ⌝
| _ =>
  ∃ sl2 a2 sl3 al3 t,
    \s t ∗ dest_below dst ∗ 
     tr_expr le For_val e1 sl2 a2  ∗
     tr_exprlist le el2 sl3 al3  ∗
     \⌜ sl = sl2 ++ sl3 ++ Scall (Some t) a2 al3 :: final dst (Etempvar t ty) /\
              a = Etempvar t ty⌝
  end

| Csyntax.Ebuiltin ef tyargs el ty =>
  match dst with
  | For_effects =>
    ∃ sl2 al2,
    tr_exprlist le el sl2 al2 ∗
    \⌜ sl = sl2 ++ Sbuiltin None ef tyargs al2 :: nil ⌝
| _ =>
  ∃ sl2 al2 t,
    tr_exprlist le el sl2 al2  ∗
    \s t  ∗ dest_below dst ∗ 
    \⌜ sl = sl2 ++ Sbuiltin (Some t) ef tyargs al2 :: final dst (Etempvar t ty) /\
    a = Etempvar t ty⌝
  end
| Csyntax.Eparen e1 tycast ty =>
  match dst with
  | For_val =>
    ∃ a2 t, tr_expr le (For_set (SDbase tycast ty t)) e1 sl a2 ∗ \⌜ a = Etempvar t ty ⌝
| For_effects =>
  ∃ a2, tr_expr le For_effects e1 sl a2
    | For_set sd =>
      ∃ a2 t0, if Pos.eq_dec t0 (sd_temp sd)
               then
                 tr_expr le (For_set (SDcons tycast ty t0 sd)) e1 sl a2
               else
                 tr_expr le (For_set (SDcons tycast ty t0 sd)) e1 sl a2 ∗ dest_below dst
     end

| _ => False
  end)
  with tr_exprlist (le : temp_env) (e : Csyntax.exprlist) (sl : list statement) (a : list expr) : iProp := 
         match e with
         | Csyntax.Enil => \⌜ sl = nil /\ a = nil⌝
         | Csyntax.Econs e1 el2 =>
           ∃ sl2 a2 sl3 al3,
    tr_expr le For_val e1 sl2 a2  ∗
            tr_exprlist le el2 sl3 al3  ∗
            \⌜ sl = sl2 ++ sl3 /\ a = a2 :: al3⌝
  end.

  Lemma transl_valof_meets_spec ty a :
    ⊢{{ emp }} transl_valof ty a {{ r, RET r; tr_rvalof ty a r.1 r.2 }}.
  Proof.
    unfold transl_valof. unfold tr_rvalof. 
    destruct (type_is_volatile ty); tac2. 
    iApply ret_spec_complete; eauto. 
    iApply ret_spec_bis; eauto.
  Qed.

  Local Set Warnings "-deprecated".
  
  Lemma tr_expr_abs : forall r le dst sl a, <absorb> tr_expr le dst r sl a ⊢ tr_expr le dst r sl a.
  Proof. induction r; iIntros "* >$". Qed.
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
    (forall r dst,
        ⊢ {{ emp }} transl_expr dst r {{ res, RET res; dest_below dst -∗ ∀ le, tr_expr le dst r res.1 res.2 }})
    /\
    (forall rl,
        ⊢{{ emp }} transl_exprlist rl {{ res, RET res; ∀ le, tr_exprlist le rl res.1 res.2 }}).
  Proof.

    Ltac iApplyA := iDestruct ("HA" with "[]") as "HA"; eauto.
    Ltac iApplyB := iDestruct ("HB" with "[]") as "HB"; eauto.
    Ltac iApplyC := iDestruct ("HC" with "[]") as "HC"; eauto.
    Ltac iApplyD := iDestruct ("HD" with "[]") as "HD"; eauto.
    
    pose transl_valof_meets_spec.
    apply tr_expr_exprlist; intros; rewrite /transl_expr; rewrite /transl_exprlist;
      fold transl_exprlist; fold transl_expr; tac2; rewrite /tr_expr; fold tr_expr; tac2.
    - edestruct v; try apply error_spec; iApply ret_spec_bis; iIntros; iModIntro; destruct dst; auto;
        iSplit; auto; repeat iExists _; repeat iSplit; iIntros;
          try iApply locally_simpl; iPureIntro; intros; try (split; eauto); econstructor.
    - iApply ret_spec_complete. iIntros "[_ HA] *". iFrame. destruct dst; eauto.
    - iApply ret_spec_complete. iIntros "[HA HB] *". iSplitL "HB"; eauto. repeat iExists _.
      destruct dst.
      + iSplitL; eauto; [iDestruct ("HA" with "[]") as "HA"; eauto | simpl; simpl_list; eauto].
      + iSplitL; eauto; [iDestruct ("HA" with "[]") as "HA"; eauto | simpl; simpl_list; eauto].
      + iSplitL; eauto. iDestruct ("HA" with "[]") as "HA"; eauto. 
    - frameR; apply b.
    - iApply ret_spec_complete.
      iIntros "[[HA HC] $] *". repeat iExists _.
      iSplitL "HC"; eauto. iApplyC.
      destruct dst; iSplitL "HA"; simpl; simpl_list; eauto.
      rewrite app_assoc. eauto.
    - iApply ret_spec_complete. 
      iIntros "[HA $] *". repeat iExists _. iSplitL; eauto.
      iApplyA. destruct dst; simpl; simpl_list; eauto.
    - iApply ret_spec_complete. 
      iIntros "[HA $] *". repeat iExists _. iSplitL; eauto. iApplyA.
      destruct dst; simpl; simpl_list; eauto.
    - iApply ret_spec_complete. 
      iIntros "[HA $] *" . repeat iExists _. iSplitL; eauto.
      iApplyA. destruct dst; simpl; simpl_list; eauto.
    - frameR. apply H0.
    - iApply ret_spec_complete. iIntros "[[HA HC] $] *". repeat iExists _.
      iSplitL "HC"; eauto. iApplyC.
      iSplitL "HA"; eauto. iApplyA. 
      destruct dst; simpl; simpl_list; eauto.
      rewrite app_assoc. auto. 
    - iApply ret_spec_complete.
      iIntros "[HA $] * ". repeat iExists _.
      iSplitL; auto. iApplyA.
      destruct dst; simpl; simpl_list; eauto.
    - destruct dst; repeat tac2.
      + frameR. apply H0.
      + iApply ret_spec_complete. iIntros "[[HA [HC HD]] _] * !>". repeat iExists _.
        iDestruct ("HA" with "[HC]") as "HA"; auto. 
        iSplitL "HD"; eauto. iApplyD.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[[HA HB] _] * !>". repeat iExists _.
        iSplitL "HB"; eauto. iApplyB. iSplitL "HA"; eauto. iApplyA.
      + frameR. apply H0.
      + iApply ret_spec_complete.
        iIntros "[[HA HB] HC] * !>". repeat iExists _.
        iSplitL "HB"; eauto. iApplyB. iDestruct ("HA" with "HC") as "HA". 
        iSplitL; eauto.
        
    - destruct dst; repeat tac2.
      + frameR. apply H0.
      + iApply ret_spec_complete. iIntros "[[HA [HC HD]] _] * !>". repeat iExists _.
        iDestruct ("HA" with "HC") as "HA". iSplitL "HD"; eauto. iApplyD.
      + frameR. apply H0.
      + iApply ret_spec_complete. iIntros "[[HA HC] _] *". iModIntro. repeat iExists _.
        iSplitL "HC"; eauto. iApplyC. iSplitL "HA"; eauto. iApplyA.
      + frameR. apply H0.
      + iApply ret_spec_complete. iIntros "[[HA HB] HC] * !>". repeat iExists _. 
        iSplitL "HB"; auto. iApplyB. iSplitL; eauto. iApply ("HA" with "HC").
        
    - destruct dst; repeat tac2.
      + frameR. apply H0.
      + frameR. apply H1.
      + iApply ret_spec_complete. iIntros "[[HA [HB [HC HD]]] _] * !>". repeat iExists _.
        iSplitL "HD"; eauto. iApplyD.
        iSplitL. iSplit; iApply tr_expr_abs.
        * iClear "HA". iModIntro. iDestruct ("HB" with "HC") as "HB". iApply "HB".
        * iClear "HB". iModIntro. iDestruct ("HA" with "HC") as "HB". iApply "HB".
        * simpl. auto.
      + frameR. apply H0.
      + frameR. apply H1.
      + iApply ret_spec_complete.
         iIntros "[[HA [HB HD]] _] * !>". repeat iExists _.
         iSplitL "HD"; eauto. iApplyD.
         iSplitL "HB"; eauto. iApplyB.
         iSplitL "HA"; eauto. iApplyA.
      + frameR. apply H0.
      + frameR. apply H1.
      + iApply ret_spec_complete.
        iIntros "[[HA [HB [HC HD]]] $] *". iModIntro. repeat iExists _.
        iSplitL "HD"; eauto. iApplyD.
        iSplitL. iSplit; iApply tr_expr_abs.
        * iClear "HA". iModIntro. iDestruct ("HB" with "HC") as "HB". iApply "HB".
        * iClear "HB". iModIntro. iDestruct ("HA" with "HC") as "HB". iApply "HB".
        * simpl. auto.        
    - iApply ret_spec_complete. iIntros "[HA $] *". iClear "HA". iModIntro. iPureIntro.
      destruct dst; simpl; simpl_list; eauto.
    - iApply ret_spec_complete. iIntros "[HA $] *". iClear "HA". iModIntro. iPureIntro.
      destruct dst; simpl; simpl_list; eauto.
    - frameR. eapply H0.
    - destruct dst; tac2.
      + iApply ret_spec_complete.
        iIntros "[[HA [HB HD]] $] *". repeat iExists _.
        iSplitL "HD"; eauto. iApplyD.
        iSplitL "HB"; eauto. iApplyB.
      + iApply ret_spec_complete.
        iIntros "[[HA HB] _] *". repeat iExists _.
        iSplitL "HB"; eauto. iApplyB.
        iSplitL; eauto. iApplyA.
      + iApply ret_spec_complete.
        iIntros "[[HA [HB HD]] $] *". repeat iExists _.
        iSplitL "HD"; eauto. iApplyD.
        iSplitL "HB"; eauto. iApplyB.
        iSplitL "HA"; eauto.        
        iPureIntro. simpl. split; auto.
        rewrite <- app_assoc. f_equal. rewrite <- app_assoc. f_equal.
    - frameR. apply H0.
    - frameR. apply transl_valof_meets_spec.
    - destruct dst; tac2.
      + iApply ret_spec_complete.
        iIntros "[[HA [HB [HD HC]]] $] *". repeat iExists _.
        iSplitL "HC"; eauto. iApplyC.
        iSplitL "HD"; eauto. iApplyD.
        iSplitL "HB"; eauto.
      + iApply ret_spec_complete.
        iIntros "[[HA [HD HB]] _] *". repeat iExists _.
        iSplitL "HB"; eauto. iApplyB.
        iSplitL "HD"; eauto. iApplyD.
      + iApply ret_spec_complete.
        iIntros "[[HA [HB [HD HC]]] $] * !>". repeat iExists _.
        iSplitL "HC"; eauto. iApplyC.
        iSplitL "HD"; eauto. iApplyD.
        iSplitL "HB". eauto.
        iSplitL "HA"; eauto.
        iPureIntro. simpl. split; auto.
        rewrite <- app_assoc. f_equal. rewrite <- app_assoc. f_equal.
        rewrite <- app_assoc. auto.
    - destruct dst; tac2.
      + iApply ret_spec_complete.
        iIntros "[[HA HB] $] *". repeat iExists _.
        iSplitL "HB"; eauto. iApplyB.
      + frameR. apply b.
      + iApply ret_spec_complete.
        iIntros "[[HA HB] _] *". repeat iExists _.
        iSplitL "HB"; eauto. iApplyB.
      + iApply ret_spec_complete.
        iIntros "[[HA HB] $] *". repeat iExists _.
        iSplitL "HB"; eauto. iApplyB.
        iExists v0. iSplitL "HA"; eauto.
        iPureIntro. simpl. split; auto.
        rewrite <- app_assoc. f_equal. 
    - frameR. apply H0.
    - iApply ret_spec_complete.
      iIntros "[[HA HB] HC] * !>". repeat iExists _.
      iSplitL "HB"; auto. iApplyB.
      iSplitL; eauto. iApply ("HA" with "HC"). 
    - destruct dst; tac2; fold tr_exprlist; fold tr_expr.
      + iApply ret_spec_complete. 
        iIntros "[[HA [HB HD]] $] * ". repeat iExists _.
        iSplitL "HA"; eauto.
        iSplitL "HD"; eauto. iApplyD.
      + iApply ret_spec_complete. 
        iIntros "[[HA HB] _] *". repeat iExists _.
        iSplitL "HB"; eauto. iApplyB.
      + iApply ret_spec_complete. 
        iIntros "[[HA [HB HD]] $] *". repeat iExists _.
        iSplitL "HA"; eauto.
        iSplitL "HD"; eauto. iApplyD.
        iSplitL; eauto. 
        iPureIntro. simpl. split; auto.
        rewrite <- app_assoc. f_equal. rewrite <- app_assoc. f_equal.
    - fold tr_exprlist. destruct dst; tac2.
      + iApply ret_spec_complete. 
        iIntros "[[HA HB] $] *". repeat iExists _.
        iSplitR "HA"; auto.
      + iApply ret_spec_complete.
        iIntros "[HA _] * ". repeat iExists _. iSplitL "HA"; eauto. 
      + iApply ret_spec_complete. 
        iIntros "[[HA HB] $] *". repeat iExists _.
        iSplitR "HA"; auto. iSplitL "HA"; eauto.
        iPureIntro. simpl. split; auto. rewrite <- app_assoc. f_equal.
    - iApply ret_spec_bis. eauto.
    - rewrite /tr_exprlist; fold tr_exprlist; fold tr_expr; tac2.
      iApply ret_spec_complete. 
      iIntros "[HA HB] * ". repeat iExists _.
      iSplitL "HB"; eauto. iApplyB.
  Qed.
  
  Section TR_TOP.

    Variable ge: genv.
    Variable e: Clight.env.
    Variable le: temp_env.
    Variable m: mem.

    Inductive tr_top: destination -> Csyntax.expr -> list statement -> expr -> heap -> Prop :=
  | tr_top_val_val: forall v ty a tmp,
      typeof a = ty -> eval_expr ge e le m a v ->
      tr_top For_val (Csyntax.Eval v ty) nil a tmp
  | tr_top_base: forall dst r sl a tmp,
      tr_expr le dst r sl a () tmp ->
      tr_top dst r sl a tmp.
    
  End TR_TOP.

    
(** Translation of statements *)

  
  Lemma transl_expr_meets_spec:
    forall r dst,
      ⊢ {{ emp }} transl_expr dst r {{ res, RET res;  dest_below dst -∗ ⌜ exists tmp, ∀ ge e le m, tr_top ge e le m dst r res.1 res.2 tmp ⌝ }}.
  Proof.
    intros. exploit (proj1 transl_meets_spec); eauto. intro.
    iIntros (?) "_ HA".
    iApply H; eauto. iIntros (res) "HB". iApply "HA". iIntros "HA".
    iDestruct ("HB" with "HA") as "HB".
    iStopProof. apply test3. apply test2. intros. exists tmps. intros. econstructor.
    apply soundness2. apply soundness3 in H0.
    iIntros "HA". iApply (H0 with "HA"). 
  Qed.
  
  Inductive tr_expression: Csyntax.expr -> statement -> expr -> Prop :=
  | tr_expression_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_expression r (makeseq sl) a.
  
  
  Lemma transl_expression_meets_spec: forall r,
      ⊢ {{ emp }} transl_expression r {{ res, RET res; ⌜ tr_expression r res.1 res.2 ⌝ }}.
  Proof.
    intro. unfold transl_expression. epose transl_expr_meets_spec. tac2.
    - apply (b r For_val).
    - iApply ret_spec_complete. iIntros "%". iPureIntro. destruct a; eauto. econstructor; eauto.
  Qed.

  
  Inductive tr_expr_stmt: Csyntax.expr -> statement -> Prop :=
  | tr_expr_stmt_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_effects r sl a tmps) ->
      tr_expr_stmt r (makeseq sl).
  
  Lemma transl_expr_stmt_meets_spec: forall r,
      ⊢ {{ emp }} transl_expr_stmt r {{ res, RET res; ⌜ tr_expr_stmt r res ⌝}}.
  Proof.
    intro. unfold transl_expr_stmt. epose transl_expr_meets_spec. tac2.
    - apply b.
    - iApply ret_spec_complete. iIntros "%". iPureIntro. destruct a; auto.
      econstructor. eapply H.
  Qed.

  Inductive tr_if: Csyntax.expr -> statement -> statement -> statement -> Prop :=
  | tr_if_intro: forall r s1 s2 sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_if r s1 s2 (makeseq (sl ++ makeif a s1 s2 :: nil)).
  
  Lemma transl_if_meets_spec: forall r s1 s2,
      ⊢ {{ emp }} transl_if r s1 s2 {{ res, RET res; ⌜ tr_if r s1 s2 res ⌝ }}.
  Proof.
    intros. epose transl_expr_meets_spec. unfold transl_if; tac2.
    - apply b.
    - iApply ret_spec_complete. iIntros "%". iPureIntro.
      destruct a; auto. econstructor. apply H.
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
      ⊢ {{ emp }} transl_stmt s {{ res, RET res; ⌜ tr_stmt s res ⌝}}
  with transl_lblstmt_meets_spec:
         forall s,
           ⊢ {{ emp }} transl_lblstmt s {{ res, RET res; ⌜ tr_lblstmts s res ⌝ }}. 
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
