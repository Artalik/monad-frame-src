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

  Definition dest_below (dst: destination) : iProp :=
    match dst with
    | For_set sd => \s (sd_temp sd)
    | _ => emp
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
      dest_below dst ∗ ∃ sl2 a2 sl3 a3 sl4 a4 t,
       tr_expr le For_val e1 sl2 a2  ∗
               tr_expr le For_val e2 sl3 a3  ∗
               tr_rvalof (Csyntax.typeof e1) a2 sl4 a4  ∗
               \s t ∗
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
      dest_below dst ∗ ∃ t, \s t  ∗
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
      dest_below dst ∗ ∃ sl2 a2 sl3 al3 t,
       \s t ∗ 
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
      dest_below dst ∗ ∃ sl2 al2 t,
       tr_exprlist le el sl2 al2  ∗
                   \s t  ∗ 
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

  
  Ltac tac :=
    match goal with
    | |- bi_emp_valid ({{ _ }} bind2 _ (fun _ _ => _) {{ _, RET _; _ }}) =>
      eapply bind_spec; intros; tac
    | |- bi_emp_valid ({{ _ }} bind _ (fun _ => _) {{ _, RET _; _ }}) =>
      eapply bind_spec; [> tac | intro; tac]
    | |- bi_emp_valid ({{ _ }} ret _ {{ _, RET _; ∃ _, _ }}) => eapply exists_spec; tac
    | |- bi_emp_valid ({{ _ }} error _ {{ _, RET _; _ }}) => apply error_spec
    | |- bi_emp_valid ({{ emp }} gensym _ {{ _, RET _; _ }}) => apply gensym_spec
    | |- bi_emp_valid ({{ _ }} gensym _ {{ _, RET _; _ }}) => frameR; apply gensym_spec 
    | H : (forall _ _, bi_emp_valid ({{ emp }} transl_valof _ _ {{ _, RET _; _}}))
      |- bi_emp_valid ({{ emp }} transl_valof _ _ {{ _, RET _; _ }}) =>
      apply H; tac
    | H : (forall _ _, bi_emp_valid ({{ emp }} transl_valof _ _ {{ _, RET _; _}}))
      |- bi_emp_valid ({{ _ }} transl_valof _ _ {{ _, RET _; _ }}) =>
      frameR; apply H; tac
    | H : (forall _ _, bi_emp_valid ({{ emp }} transl_expr _ _ {{ _, RET _; _}}))
      |- bi_emp_valid ({{ emp }} transl_expr _ _ {{ _, RET _; _ }}) =>
      apply H; tac
    | H : (forall _ _, bi_emp_valid ({{ emp }} transl_expr _ _ {{ _, RET _; _}}))
      |- bi_emp_valid ({{ _ }} transl_expr _ _ {{ _, RET _; _ }}) =>
      frameR; apply H; tac
    | H : (forall _, bi_emp_valid ({{ emp }} transl_expr _ ?l {{ _, RET _; _}}))
      |- bi_emp_valid ({{ emp }} transl_expr _ ?l {{ _, RET _; _ }}) =>
      apply H; tac
    | H : (forall _, bi_emp_valid ({{ emp }} transl_expr _ ?l {{ _, RET _; _}}))
      |- bi_emp_valid ({{ _ }} transl_expr _ ?l {{ _, RET _; _ }}) =>
      frameR; apply H; tac
    | H :(forall _, bi_emp_valid ({{ emp }} transl_exprlist _ {{ _, RET _; _}}))
      |- bi_emp_valid ({{ emp }} transl_exprlist _ {{ _, RET _; _ }}) =>
      apply H; tac
    | H :(forall _, bi_emp_valid ({{ emp }} transl_exprlist _ {{ _, RET _; _}}))
      |- bi_emp_valid ({{ _ }} transl_exprlist _ {{ _, RET _; _ }}) =>
      frameR; apply H; tac
    | H : bi_emp_valid ({{ emp }} transl_exprlist ?l {{ _, RET _; _}})
      |- bi_emp_valid ({{ emp }} transl_exprlist ?l {{ _, RET _; _ }}) =>
      apply H; tac
    | H : bi_emp_valid ({{ emp }} transl_exprlist ?l {{ _, RET _; _}})
      |- bi_emp_valid ({{ _ }} transl_exprlist ?l {{ _, RET _; _ }}) =>
      frameR; apply H; tac
    | |- bi_emp_valid ({{ _ }} match ?a with
                              | _ => _
                              end  {{ _, RET _; _ }}) =>
      destruct a eqn:?; tac
    | _ => idtac
    end.
  
  Ltac tac2 :=
    match goal with
    | |- bi_emp_valid ({{ emp }} ret ?v {{ v', RET v'; ⌜ v' = ?v ⌝ }}) => apply ret_spec
    | |- bi_emp_valid ({{ emp }} ret ?v {{ v', RET v'; \⌜ v' = ?v ⌝ }}) => apply ret_spec_pure   
    | |- bi_emp_valid ({{ emp }} ret _  {{ _, RET _; _ }}) => iApply ret_spec_bis; auto
    | |- bi_emp_valid ({{ _ }} ret _  {{ _, RET _; _ }}) => iApply ret_spec_complete; auto
    | _ => (progress tac); tac2
    | _ => idtac
    end.
  
  Lemma transl_valof_meets_spec ty a :
    ⊢{{ emp }} transl_valof ty a {{ r, RET r; tr_rvalof ty a r.1 r.2 }}.
  Proof.
    unfold transl_valof. unfold tr_rvalof. 
    destruct (type_is_volatile ty); tac2.
  Qed.

  
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
      fold transl_exprlist; fold transl_expr; tac2; simpl; iIntros; norm_all; try iModIntro.
    Ltac EvalTac dst :=
      destruct dst; auto; iSplit; auto; repeat iExists _; repeat iSplit; auto; iIntros; eauto;
      iApply locally_simpl; iIntros; iPureIntro;econstructor.
    
    1-5 : EvalTac dst.
    - iFrame; repeat iExists _; destruct dst; simpl; simpl_list; eauto.
    - iFrame. repeat iExists _. destruct dst; simpl; iFrame; simpl_list; eauto.
      rewrite <- app_assoc. eauto.
    - iFrame; repeat iExists _; destruct dst; simpl; simpl_list; eauto.
    - iFrame; repeat iExists _; destruct dst; simpl; simpl_list; eauto.
    - iFrame; repeat iExists _; destruct dst; simpl; simpl_list; eauto.
    - iFrame. repeat iExists _. iSplitL "HD"; eauto. iSplitL "HC"; eauto.
      destruct dst; simpl; simpl_list; auto. rewrite <- app_assoc. eauto. 
    - iFrame; repeat iExists _; destruct dst; simpl; simpl_list; eauto.
    - repeat iExists _. iSplitL "HF"; auto. iDestruct ("HC" with "[HE]") as "HA"; auto.
    - repeat iExists _. iSplitL "HD"; eauto.
    - repeat iExists _. iSplitL "HD"; eauto. iSplitL; eauto. iApply ("HC" with "[HF]"); auto.
    - repeat iExists _. iSplitL "HF"; auto. iSplitL; eauto. iApply ("HC" with "[HE]"); auto.
    - repeat iExists _. iSplitL "HD"; eauto. 
    - repeat iExists _. iSplitL "HD"; eauto. iSplitL; eauto. iApply ("HC" with "[HF]"); auto.
    - repeat iExists _. iSplitL "HH"; auto. iSplitL; eauto. iSplit; iApply tr_expr_abs.
      iApply ("HE" with "[HG]"); auto. iApply ("HC" with "[HG]"); auto.
    - repeat iExists _. iSplitL "HG"; eauto. iSplitL "HF"; auto.
    - iSplitL "HJ"; auto. repeat iExists _. iSplitL "HH"; auto. iSplitL; eauto.
      iSplit; iApply tr_expr_abs.
      iApply ("HE" with "[HG]"); auto. iApply ("HC" with "[HG]"); auto.
    - iFrame; repeat iExists _; destruct dst; simpl; simpl_list; eauto.
    - iFrame; repeat iExists _; destruct dst; simpl; simpl_list; eauto.
    - repeat iExists _. iSplitL "HF"; eauto. iSplitL "HE"; auto.
    - repeat iExists _. iSplitL "HD"; eauto.
    - repeat iExists _. iSplitL "HF"; eauto. iSplitL "HE"; auto. iSplitL "HC"; eauto. iSplitL; eauto.
      iPureIntro. split; auto. do 2 (rewrite <- app_assoc; f_equal).
    - iSplitR; auto. repeat iExists _. iFrame. iSplitL "HH"; eauto. iSplitL "HG"; eauto. 
    - repeat iExists _. iFrame. iSplitL "HF"; eauto. 
    - iSplitL "HK"; auto. repeat iExists _. iSplitL "HH"; auto. iSplitL "HG"; eauto. 
      iSplitL "HE"; auto.
      iSplitL "HC"; eauto. iSplitL; auto.
      iPureIntro. do 3 (rewrite <- app_assoc; f_equal).
    - repeat iExists _. iSplitL "HD"; eauto. 
    - repeat iExists _. iSplitL "HD"; eauto.
    - repeat iExists _. iSplitL "HD"; eauto. iSplitL "HF"; auto. iExists v0.
      iSplitL "HC"; auto. iSplitL; auto.
      iPureIntro. rewrite <- app_assoc; f_equal.
    - repeat iExists _. iSplitL "HD"; eauto. iSplitL; auto. iApply ("HC" with "HF").
    - iSplitR; auto. repeat iExists _. iSplitL "HC"; auto. iSplitL "HF"; auto. 
    - repeat iExists _. iSplitL "HD"; eauto.
    - iSplitL "HH"; auto. repeat iExists _. iSplitL "HC"; auto. iSplitL "HF"; auto.
      iSplitL "HE"; eauto. iPureIntro. split; auto. do 2 (rewrite <- app_assoc; f_equal).
    - iSplitR; auto. repeat iExists _. iSplitL "HD"; auto. 
    - iSplitL "HE"; auto. repeat iExists _. iSplitL "HD"; auto. iSplitL "HC"; auto. iSplitL; eauto.
      iPureIntro. rewrite <- app_assoc; f_equal.
    - repeat iExists _. iSplitL "HC"; auto.
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
  Lemma start_proof (P Q : iProp) tmps : P () tmps -> (⊢ P -∗ Q) -> Q () tmps.
  Proof.
    intros. apply soundness3 in H. apply soundness2. iIntros. iApply H0. iApply H. auto.
  Qed.
  
  Lemma transl_expr_meets_spec:
    forall r dst,
      ⊢ {{ emp }} transl_expr dst r {{ res, RET res;  dest_below dst -∗ ⌜ exists tmp, ∀ ge e le m, tr_top ge e le m dst r res.1 res.2 tmp ⌝ }}.
  Proof.
    intros. iApply (post_weaker _ _ _ _ (proj1 transl_meets_spec _ _)).
    iIntros "* HA HB". iDestruct ("HA" with "HB") as "HA". iStopProof. apply instance_heap.
    intros. exists tmps. intros. constructor. apply (start_proof _ _ _ H). auto.
  Qed.  
  
  Inductive tr_expression: Csyntax.expr -> statement -> expr -> Prop :=
  | tr_expression_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_expression r (makeseq sl) a.
  
  
  Lemma transl_expression_meets_spec: forall r,
      ⊢ {{ emp }} transl_expression r {{ res, RET res; ⌜ tr_expression r res.1 res.2 ⌝ }}.
  Proof.
    intro. unfold transl_expression. epose transl_expr_meets_spec. tac2.
    iIntros "%". iPureIntro. destruct a; eauto. econstructor; eauto.
  Qed.

  
  Inductive tr_expr_stmt: Csyntax.expr -> statement -> Prop :=
  | tr_expr_stmt_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_effects r sl a tmps) ->
      tr_expr_stmt r (makeseq sl).
  
  Lemma transl_expr_stmt_meets_spec: forall r,
      ⊢ {{ emp }} transl_expr_stmt r {{ res, RET res; ⌜ tr_expr_stmt r res ⌝}}.
  Proof.
    intro. unfold transl_expr_stmt. epose transl_expr_meets_spec. tac2. 
    iIntros "%". iPureIntro. destruct a; auto. econstructor. eapply H.
  Qed.

  Inductive tr_if: Csyntax.expr -> statement -> statement -> statement -> Prop :=
  | tr_if_intro: forall r s1 s2 sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_if r s1 s2 (makeseq (sl ++ makeif a s1 s2 :: nil)).
  
  Lemma transl_if_meets_spec: forall r s1 s2,
      ⊢ {{ emp }} transl_if r s1 s2 {{ res, RET res; ⌜ tr_if r s1 s2 res ⌝ }}.
  Proof.
    intros. epose transl_expr_meets_spec. unfold transl_if; tac2.
    iIntros "%". iPureIntro. destruct a; auto. econstructor. apply H.
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

  Ltac tac3 :=
    match goal with
    | H : forall _, bi_emp_valid ({{ emp }} transl_expression _ {{ _, RET _; _ }})
      |- bi_emp_valid ({{ emp }} transl_expression _ {{ _, RET _; _ }}) =>
      apply H; tac3
    | H : forall _, bi_emp_valid ({{ emp }} transl_expression _ {{ _, RET _; _ }})
      |- bi_emp_valid ({{ _ }} transl_expression _ {{ _, RET _; _ }}) =>
      frameR; apply H; tac3

    | H : forall _, bi_emp_valid ({{ emp }} transl_expr_stmt _ {{ _, RET _; _}})
      |- bi_emp_valid ({{ emp }} transl_expr_stmt _ {{ _, RET _; _}}) =>
      apply H; tac3 
    | H : forall _, bi_emp_valid ({{ emp }} transl_expr_stmt _ {{ _, RET _; _}})
      |- bi_emp_valid ({{ _ }} transl_expr_stmt _ {{ _, RET _; _}}) =>
      frameR; apply H; tac3

    | H: forall _ _ _, bi_emp_valid ({{ emp }} transl_if _ _ _ {{ _, RET _; _ }})
      |- bi_emp_valid ({{ emp }} transl_if _ _ _ {{ _, RET _; _ }}) =>
      apply H; tac3
    | H: forall _ _ _, bi_emp_valid ({{ emp }} transl_if _ _ _ {{ _, RET _; _ }})
      |- bi_emp_valid ({{ _ }} transl_if _ _ _ {{ _, RET _; _ }}) =>
      frameR; apply H; tac3

    | H: bi_emp_valid ({{ emp }} transl_stmt ?s {{ _, RET _; _ }})
      |- bi_emp_valid ({{ emp }} transl_stmt ?s {{ _, RET _; _ }}) =>
      apply H; tac3
    | H: bi_emp_valid ({{ emp }} transl_stmt ?s {{ _, RET _; _ }})
      |- bi_emp_valid ({{ _ }} transl_stmt ?s {{ _, RET _; _ }}) =>
      frameR; apply H; tac3

    | H: (forall _, bi_emp_valid ({{ emp }} transl_stmt _ {{ _, RET _; _ }}))
      |- bi_emp_valid ({{ emp }} transl_stmt _ {{ _, RET _; _ }}) =>
      apply H; tac3
    | H:(forall _, bi_emp_valid ({{ emp }} transl_stmt _ {{ _, RET _; _ }}))
      |- bi_emp_valid ({{ _ }} transl_stmt ?s {{ _, RET _; _ }}) =>
      frameR; apply H; tac3


    | H: (⊢ {{ emp }} transl_lblstmt ?l {{ _, RET _; _ }})
      |- (⊢ {{ emp }} transl_lblstmt ?l {{ _, RET _; _ }}) =>
      apply H; tac3
    | H: (⊢ {{ emp }} transl_lblstmt ?l {{ _, RET _; _ }})
      |- (⊢ {{ _ }} transl_lblstmt ?l {{ _, RET _; _ }}) =>
      frameR; apply H; tac3
    
    | H: (forall _, ⊢ {{ emp }} transl_lblstmt _ {{ _, RET _; _ }})
      |- (⊢ {{ emp }} transl_lblstmt _ {{ _, RET _; _ }}) =>
      apply H; tac3
    | H: (forall _, ⊢ {{ emp }} transl_lblstmt _ {{ _, RET _; _ }})
      |- (⊢ {{ _ }} transl_lblstmt _ {{ _, RET _; _ }}) =>
      frameR; apply H; tac3
                         
    | _ => (progress tac); tac3
    | _ => (progress tac2); tac3
    | _ => idtac
    end.
                       
  
  Lemma transl_stmt_meets_spec : forall s,
      ⊢ {{ emp }} transl_stmt s {{ res, RET res; ⌜ tr_stmt s res ⌝}}
  with transl_lblstmt_meets_spec:
         forall s,
           ⊢ {{ emp }} transl_lblstmt s {{ res, RET res; ⌜ tr_lblstmts s res ⌝ }}. 
  Proof.
    pose transl_expression_meets_spec. pose transl_if_meets_spec. pose transl_expr_stmt_meets_spec.
    clear transl_stmt_meets_spec. intro.
    induction s; rewrite /transl_stmt; fold transl_stmt; fold transl_lblstmt; tac3.
    
    - iPureIntro. constructor.
    - apply (post_weaker _ _ _ _ (b1 e)). iIntros. iPureIntro. apply (tr_do _ _ a).
    - iIntros "[% %]". iPureIntro. constructor; auto.
    - iIntros"[% [% %]]". iPureIntro. pose Heqb2. apply Is_true_eq_left in e0.
      apply andb_prop_elim in e0 as (P0&P1). 
      destruct (is_Sskip s1); destruct (is_Sskip s2) eqn:?; try contradiction. subst.
      eapply tr_ifthenelse_empty; eauto. 
    - iIntros"[% [% %]]". iPureIntro. apply (tr_ifthenelse _ _ _ _ _ _ _ H H1 H0).
    - iIntros "[% %]". iPureIntro. apply (tr_while _ _ _ _ H0 H).
    - iIntros "[% %]". iPureIntro. apply (tr_dowhile _ _ _ _ H0 H).
    - iIntros "[% [% [% %]]]"; iPureIntro; subst. apply (tr_for_1 _ _ _ _ _ _ H1 H0 H).
    - iIntros "[% [% [% %]]]"; iPureIntro; subst. apply (tr_for_2 _ _ _ _ _ _ _ _ H1 n H2 H0 H).
    - iPureIntro. constructor.
    - iPureIntro. constructor.
    - iIntros. iPureIntro. apply (tr_return_some _ _ _ a).
    - iPureIntro. constructor. 
    - iIntros "[% %]". iPureIntro. constructor; auto.
    - iIntros "%". iPureIntro. constructor; auto.
    - iPureIntro. constructor.
    - induction s; rewrite /transl_lblstmt; fold transl_lblstmt; fold transl_stmt; tac3.
      + iPureIntro. constructor.
      + iIntros "[% %]". iPureIntro. constructor; auto.
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
    destruct (run (transl_stmt (Csyntax.fn_body f)) initial_state) eqn:?; inversion H.
    destruct p. simpl in *. 
    apply tr_function_intro; auto; simpl.
    eapply (adequacy_pure (transl_stmt (Csyntax.fn_body f)) _ initial_state s0 s emp); auto.
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
