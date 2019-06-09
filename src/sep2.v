From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.heap_lang Require Export locations.
Require Import iris.algebra.gset.
From stdpp Require Export binders strings.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import tactics.
Set Implicit Arguments.
From iris.algebra Require Import auth frac agree gmap.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.

Set Default Proof Using "Type".
Import uPred.

Module gen_heap.

  Definition gen_heapUR (L : Type) `{Countable L} : ucmraT :=
    gsetUR L.
  Print gsetUR.
  Print UcmraT'.
  Print ofeT.
  Print gen_heapUR.
  Print mapset.
  Definition to_gen_heap {L} `{Countable L} : gset L → gen_heapUR := id.

  (** The CMRA we need. *)
  Class gen_heapG (L : Type) (Σ : gFunctors) `{Countable L} :=
    GenHeapG {
        gen_heap_inG :> inG Σ (authR (gen_heapUR));
        gen_heap_name : gname
      }.
  Arguments gen_heap_name {_ _ _ _} _ : assert.

  Class gen_heapPreG (L : Type) (Σ : gFunctors) `{Countable L} :=
    { gen_heap_preG_inG :> inG Σ (authR (gen_heapUR)) }.

  Definition gen_heapΣ (L : Type) `{Countable L} : gFunctors :=
    #[GFunctor (authR (gen_heapUR))].

  Instance subG_gen_heapPreG {Σ L} `{Countable L} :
    subG (gen_heapΣ) Σ → gen_heapPreG Σ.
  Proof. solve_inG. Qed.

  Section definitions.
    Context `{Countable L, hG : !gen_heapG Σ}.

    Definition gen_heap_ctx (σ : gset L) : iProp Σ :=
      own (gen_heap_name hG) (● (to_gen_heap σ)).

    Print own.

    Locate "{[ _ ]}".

    Definition mapsto_def (l : L) : iProp Σ :=
      own (gen_heap_name hG) (◯ {[ l ]}).
    Definition mapsto_aux : seal (@mapsto_def). by eexists. Qed.
    Definition mapsto := mapsto_aux.(unseal).
    Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
  End definitions.

  Local Notation "\s l" := (mapsto l)
                             (at level 20, format "\s l") : bi_scope.
  Local Notation "\s l" := (mapsto l) (at level 20) : bi_scope.

  Section to_gen_heap.
    Context L `{Countable L}.
    Implicit Types σ : gset L.
    (** Conversion to heaps and back *)
    Lemma to_gen_heap_valid σ : ✓ to_gen_heap σ.
    Proof. repeat red. trivial. Qed.
    Lemma lookup_to_gen_heap_None σ l : l ∈ σ <-> l ∈ to_gen_heap σ.
    Proof. auto. Qed.
    Lemma gen_heap_singleton_included σ l :
      {[ l ]} ≼ to_gen_heap σ <-> l ∈ σ.
    Proof.
      split.
      * intro. apply gset_included in H0. apply elem_of_subseteq_singleton. assumption.
      * intro. apply gset_included. apply elem_of_subseteq_singleton. assumption.
    Qed.

    Lemma to_gen_heap_insert l σ :
      to_gen_heap ( ({[ l ]} ∪ σ)) =  {[ l ]} ∪ (to_gen_heap σ).
    Proof. auto. Qed.
    Lemma to_gen_heap_delete l σ :
      to_gen_heap (σ ∖ l) = (to_gen_heap σ) ∖ l.
    Proof. auto. Qed.
  End to_gen_heap.

  Lemma gen_heap_init `{Countable L, !gen_heapPreG Σ} σ :
    (|==> ∃ _ : gen_heapG Σ, gen_heap_ctx σ)%I.
  Proof.
    iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh".
    { rewrite auth_auth_valid. exact: to_gen_heap_valid. }
    iModIntro. by iExists (GenHeapG _ γ).
  Qed.

  Section gen_heap.
    Context {L} `{Countable L, !gen_heapG Σ}.
    Implicit Types P Q : iProp Σ.
    Implicit Types σ : gset L.
    (* Implicit Types h g : gen_heapUR. *)
    Implicit Types l : L.

    Lemma gen_heap_gensym σ l :
      l ∉ σ → gen_heap_ctx σ ==∗ gen_heap_ctx ({[ l ]} ∪ σ) ∗ \s l.
    Proof.
      iIntros (?) "Hσ". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
      iMod (own_update with "Hσ") as "[Hσ Hl]".

      { eapply auth_update_alloc.
        eapply op_local_update_discrete. trivial.
      }
      iModIntro. rewrite to_gen_heap_insert.
      unfold to_gen_heap in *. simpl in *. iDestruct "Hl" as "[A B]".
      iFrame.
    Qed.

    Lemma test (A B : gset L) : A ## B -> A ∪ B = A ⋅ B.
    Proof. auto. Qed.

    Lemma gen_heap_gensym_gen σ σ' :
      σ' ## σ → gen_heap_ctx σ ==∗ gen_heap_ctx (σ' ∪ σ) ∗ [∗ set] l ∈ σ', (\s l).
    Proof.
      (* revert σ. elim σ' using set_ind. *)
      (* * epose set_finite_proper. repeat red. intros. split; pose (gset_leibniz x); apply e in H0; subst; iIntros (? ? ?); apply H0 in H1; assumption. *)
      (* * iIntros (? ?) "Hf". epose union_empty_l.  pose (elem_of_equiv_L (∅ ∪ σ) σ). apply i in l. rewrite /gen_heap_ctx mapsto_eq /mapsto_def. iModIntro. iSplit. *)
      (*   ** unfold to_gen_heap. unfold id. rewrite l. iApply "Hf". *)
      (*   ** rewrite /big_opS. rewrite /big_opL. induction (elements ∅) eqn:?. trivial. inversion Heql0. *)

      (* * intros. pose (P := H2). apply disjoint_union_l in P. destruct P. apply H1 in H4. iIntros "Hf". *)
      (*   rewrite /gen_heap_ctx mapsto_eq /mapsto_def. *)
      (*   iMod (own_update with "Hf") as "[Hf Hl]". *)
      (*   ** eapply auth_update_alloc. eapply op_local_update_discrete. trivial. *)
      (*   ** unfold to_gen_heap. unfold id. iModIntro. apply test in H2. rewrite H2. apply disjoint_singleton_l in H0. apply test in H0. rewrite H0. *)
      (*      iFrame. rewrite /big_opS. rewrite /big_opL. *)
    Admitted.

    Lemma gen_heap_valid σ l : gen_heap_ctx σ -∗ \s l -∗ ⌜l ∈ σ⌝.
    Proof.
      iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
      iDestruct (own_valid_2 with "Hσ Hl")
        as %[Hl%gen_heap_singleton_included _]%auth_both_valid; auto.
    Qed.

    Lemma test2 σ l : l ∈ σ -> equiv ({[l]} ∪ σ) σ.
    Proof.
      intro. repeat red. intros. split; intros.
      * pose (subseteq_union_1_L {[l]} σ). apply elem_of_subseteq_singleton in H0.
        apply e in H0. now rewrite H0 in H1.
      * now apply elem_of_union_r.
    Qed.

    Lemma gen_heap_update σ l :
      gen_heap_ctx σ -∗ \s l ==∗ gen_heap_ctx ({[ l ]} ∪ σ) ∗ \s l.
    Proof.
      iIntros "Hσ Hl". rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
      iDestruct (own_valid_2 with "Hσ Hl")
        as %[Hl%gen_heap_singleton_included _]%auth_both_valid.
      iModIntro. apply test2 in Hl. rewrite Hl. unfold to_gen_heap. unfold id.
      iFrame.
    Qed.
  End gen_heap.
End gen_heap.

From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From stdpp Require Import fin_maps.
Module lifting.

  (* From iris.algebra Require Import auth gmap. *)
  Export gen_heap.
  (* From iris.program_logic Require Export weakestpre. *)
  (* From iris.program_logic Require Import ectx_lifting total_ectx_lifting. *)
  Import tactics.
  (* From iris.proofmode Require Import tactics. *)
  (* From stdpp Require Import fin_maps. *)
  (* Set Default Proof Using "Type". *)
  Print gen_heapG.
  Class heapG Σ :=
    HeapG {
        heapG_invG : invG Σ;
        heapG_gen_heapG :> @gen_heapG loc Σ _ _;
      }.
  Locate irisG.
  Print irisG.
  (* Instance heapG_irisG `{!heapG Σ} : irisG heap_lang Σ := { *)
  (*                                                          iris_invG := heapG_invG; *)
  (*                                                          state_interp σ _ _ := gen_heap_ctx σ%I; *)
  (*                                                          fork_post _ := True%I; *)
  (*                                                        }. *)

  (** Override the notations so that scopes and coercions work out *)
  Notation "\s l" := (mapsto (L:=loc) l)
                       (at level 20, format "\s l") : bi_scope.
  Notation "\s l" :=
    (mapsto (L:=loc) l) (at level 20) : bi_scope.

  (** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
  Ltac inv_head_step :=
    repeat match goal with
           | _ => progress simplify_map_eq/= (* simplify memory stuff *)
           | H : to_val _ = Some _ |- _ => apply of_to_val in H
           | H : head_step ?e _ _ _ _ _ |- _ =>
             try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
             inversion H; subst; clear H
           end.

  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
  Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

  (* [simpl apply] is too stupid, so we need extern hints here. *)
  Local Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : core.
  (* Local Hint Extern 0 (head_step Gensym _ _ _ _ _) => apply gensym_fresh : core. *)
  Local Hint Resolve to_of_val : core.

  (* Instance into_val_val v : IntoVal (Val v) v. *)
  (* Proof. done. Qed. *)
  (* Instance as_val_val v : AsVal (Val v). *)
  (* Proof. by eexists. Qed. *)

  Local Ltac solve_atomic :=
    apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

  (* Instance gensym_atomic s : Atomic s Gensym. *)
  (* Proof. solve_atomic. Qed. *)
  (* Instance skip_atomic s  : Atomic s Skip. *)
  (* Proof. solve_atomic. Qed. *)

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

  (** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
  Print PureExec.
  
  
  Class AsRecV (v : val) (f x : binder) (erec : expr) :=
    as_recv : v = RecV f x erec.
  Hint Mode AsRecV ! - - - : typeclass_instances.
  Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
  Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

  Instance pure_recc f x (erec : expr) :
    PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
  Proof. solve_pure_exec. Qed.
  Instance pure_pairc (v1 v2 : val) :
    PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Instance pure_injlc (v : val) :
    PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Instance pure_injrc (v : val) :
    PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
    PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
  Proof. unfold AsRecV in *. solve_pure_exec. Qed.

  Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v').
  Proof. solve_pure_exec. Qed.

  Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.

  Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Instance pure_fst v1 v2 :
    PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.

  Instance pure_snd v1 v2 :
    PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Instance pure_case_inl v e1 e2 :
    PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
  Proof. solve_pure_exec. Qed.

  Instance pure_case_inr v e1 e2 :
    PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
  Proof. solve_pure_exec. Qed.

  Section lifting.
    Context `{!heapG Σ}.
    Implicit Types P Q : iProp Σ.
    Implicit Types Φ : val → iProp Σ.
    Implicit Types efs : list expr.
    Implicit Types σ : heap.

    (** Heap *)

    Lemma wp_gensym s E :
      {{{ True }}} Gensym @ s; E {{{ l, RET LitV (LitLoc l); \s l }}}.
    Proof.
      iIntros (Φ) "_ C". iApply wp_lift_atomic_head_step_no_fork; eauto.
      iIntros (σ1 κ κs k) "A !>". iSplit.
      - iPureIntro. red. exists []. exists (Val $ LitV $ LitLoc (fresh_locs σ1)).
        repeat econstructor. apply fresh_locs_fresh.
      - iNext. iIntros (e2 h efs A). inv_head_step.
        iMod (gen_heap_gensym with "A") as "B"; eauto.
        iModIntro. iSplit.
        * iPureIntro. reflexivity.
        * iDestruct "B" as "[A B]". iFrame. iApply "C".
          iApply "B".
    Qed.

    Lemma twp_gensym s E :
      [[{ True }]] Gensym @ s; E [[{ l, RET LitV (LitLoc l); \s l }]].
    Proof.
      iIntros (Φ) "_ A".
      iApply twp_lift_atomic_head_step_no_fork; auto.
      iIntros (σ1 κs k) "B !>"; iSplit; auto with lia.
      iIntros (κ v2 σ2 efs Hstep); inv_head_step.
      iMod (@gen_heap_gensym with "B") as "[B C]"; eauto.
      iModIntro. iSplit; eauto. iSplit; eauto. iFrame. iApply "A". iApply "C".
    Qed.
  End lifting.
End lifting.

From iris.program_logic Require Export total_weakestpre.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.

Module proofmode.
  Export tactics lifting.
  Import notation.
  Set Default Proof Using "Type".
  Import uPred.

  Lemma tac_wp_expr_eval `{!heapG Σ} Δ s E Φ e e' :
    (∀ (e'':=e'), e = e'') →
    envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
  Proof. by intros ->. Qed.
  Lemma tac_twp_expr_eval `{!heapG Σ} Δ s E Φ e e' :
    (∀ (e'':=e'), e = e'') →
    envs_entails Δ (WP e' @ s; E [{ Φ }]) → envs_entails Δ (WP e @ s; E [{ Φ }]).
  Proof. by intros ->. Qed.

  Tactic Notation "wp_expr_eval" tactic(t) :=
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      eapply tac_wp_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      eapply tac_twp_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
    | _ => fail "wp_expr_eval: not a 'wp'"
    end.

  Lemma tac_wp_pure `{!heapG Σ} Δ Δ' s E e1 e2 φ n Φ :
    PureExec φ n e1 e2 →
    φ →
    MaybeIntoLaterNEnvs n Δ Δ' →
    envs_entails Δ' (WP e2 @ s; E {{ Φ }}) →
    envs_entails Δ (WP e1 @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_eq=> ??? HΔ'. rewrite into_laterN_env_sound /=.
    rewrite HΔ' -lifting.wp_pure_step_later //.
  Qed.
  Lemma tac_twp_pure `{!heapG Σ} Δ s E e1 e2 φ n Φ :
    PureExec φ n e1 e2 →
    φ →
    envs_entails Δ (WP e2 @ s; E [{ Φ }]) →
    envs_entails Δ (WP e1 @ s; E [{ Φ }]).
  Proof.
    rewrite envs_entails_eq=> ?? ->. rewrite -total_lifting.twp_pure_step //.
  Qed.

  Lemma tac_wp_value `{!heapG Σ} Δ s E Φ v :
    envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
  Proof. rewrite envs_entails_eq=> ->. by apply wp_value. Qed.
  Lemma tac_twp_value `{!heapG Σ} Δ s E Φ v :
    envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
  Proof. rewrite envs_entails_eq=> ->. by apply twp_value. Qed.

  Ltac wp_expr_simpl := wp_expr_eval simpl.

  Ltac wp_value_head :=
    first [eapply tac_wp_value || eapply tac_twp_value].

  Ltac wp_finish :=
    wp_expr_simpl;      (* simplify occurences of subst/fill *)
    try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
    pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

  (** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
  Tactic Notation "wp_pure" open_constr(efoc) :=
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      let e := eval simpl in e in
          reshape_expr e ltac:(fun K e' =>
                                 unify e' efoc;
                                 eapply (tac_wp_pure _ _ _ _ (fill K e'));
                                 [iSolveTC                       (* PureExec *)
                                 |try fast_done                  (* The pure condition for PureExec *)
                                 |iSolveTC                       (* IntoLaters *)
                                 |wp_finish                      (* new goal *)
                              ])
          || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      let e := eval simpl in e in
          reshape_expr e ltac:(fun K e' =>
                                 unify e' efoc;
                                 eapply (tac_twp_pure _ _ _ (fill K e'));
                                 [iSolveTC                       (* PureExec *)
                                 |try fast_done                  (* The pure condition for PureExec *)
                                 |wp_finish                      (* new goal *)
                              ])
          || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
    | _ => fail "wp_pure: not a 'wp'"
    end.

  (* TODO: do this in one go, without [repeat]. *)
  Ltac wp_pures :=
    iStartProof;
    repeat (wp_pure _; []). (* The `;[]` makes sure that no side-condition
                             magically spawns. *)

  (** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
  Tactic Notation "wp_rec" :=
    let H := fresh in
    assert (H := AsRecV_recv);
    wp_pure (App _ _);
    clear H.

  Tactic Notation "wp_if" := wp_pure (If _ _ _).
  Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _).
  Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _).
  Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
  Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
  Tactic Notation "wp_op" := wp_unop || wp_binop.
  Tactic Notation "wp_lam" := wp_rec.
  Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
  Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
  Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
  Tactic Notation "wp_case" := wp_pure (Case _ _ _).
  Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam.
  Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _).
  Tactic Notation "wp_pair" := wp_pure (Pair _ _).
  Tactic Notation "wp_closure" := wp_pure (Rec _ _ _).

  Lemma tac_wp_bind `{!heapG Σ} K Δ s E Φ e f :
    f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
    envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
    envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
  Proof. rewrite envs_entails_eq=> -> ->. by apply: wp_bind. Qed.
  Lemma tac_twp_bind `{!heapG Σ} K Δ s E Φ e f :
    f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
    envs_entails Δ (WP e @ s; E [{ v, WP f (Val v) @ s; E [{ Φ }] }])%I →
    envs_entails Δ (WP fill K e @ s; E [{ Φ }]).
  Proof. rewrite envs_entails_eq=> -> ->. by apply: twp_bind. Qed.

  Ltac wp_bind_core K :=
    lazymatch eval hnf in K with
    | [] => idtac
    | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
    end.
  Ltac twp_bind_core K :=
    lazymatch eval hnf in K with
    | [] => idtac
    | _ => eapply (tac_twp_bind K); [simpl; reflexivity|reduction.pm_prettify]
    end.

  Tactic Notation "wp_bind" open_constr(efoc) :=
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
      || fail "wp_bind: cannot find" efoc "in" e
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' => unify e' efoc; twp_bind_core K)
      || fail "wp_bind: cannot find" efoc "in" e
    | _ => fail "wp_bind: not a 'wp'"
    end.

  (** Heap tactics *)
  Section heap.
    Context `{!heapG Σ}.
    Implicit Types P Q : iProp Σ.
    Implicit Types Φ : val → iProp Σ.
    Implicit Types Δ : envs (uPredI (iResUR Σ)).
    Implicit Types v : val.
    Implicit Types z : Z.

    Lemma tac_wp_gensym Δ Δ' s E j K v Φ :
      MaybeIntoLaterNEnvs 1 Δ Δ' →
      (∀ l, ∃ Δ'',
            envs_app false (Esnoc Enil j (\s l)) Δ' = Some Δ'' ∧
            envs_entails Δ'' (WP fill K (Val $ LitV l) @ s; E {{ Φ }})) →
      envs_entails Δ (WP fill K Gensym @ s; E {{ Φ }}).
    Proof.
      rewrite envs_entails_eq=> ? HΔ.
      rewrite -wp_bind. eapply wand_apply; first exact: wp_gensym.
      rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
      destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
        by rewrite right_id HΔ'.
    Qed.
    Lemma tac_twp_gensym Δ s E j K v Φ :
      (∀ l, ∃ Δ',
            envs_app false (Esnoc Enil j (\s l)) Δ = Some Δ' ∧
            envs_entails Δ' (WP fill K (Val $ LitV l) @ s; E [{ Φ }])) →
      envs_entails Δ (WP fill K Gensym @ s; E [{ Φ }]).
    Proof.
      rewrite envs_entails_eq=> HΔ.
      rewrite -twp_bind. eapply wand_apply; first exact: twp_gensym.
      rewrite left_id. apply forall_intro=> l.
      destruct (HΔ l) as (Δ'&?&HΔ'). rewrite envs_app_sound //; simpl.
        by rewrite right_id HΔ'.
    Qed.
  End heap.

  (** Evaluate [lem] to a hypothesis [H] that can be applied, and then run
[wp_bind K; tac H] for every possible evaluation context.  [tac] can do
[iApplyHyp H] to actually apply the hypothesis.  TC resolution of [lem] premises
happens *after* [tac H] got executed. *)
  Tactic Notation "wp_apply_core" open_constr(lem) tactic(tac) :=
    wp_pures;
    iPoseProofCore lem as false true (fun H =>
                                        lazymatch goal with
                                        | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
                                          reshape_expr e ltac:(fun K e' =>
                                                                 wp_bind_core K; tac H) ||
                                          lazymatch iTypeOf H with
                                          | Some (_,?P) => fail "wp_apply: cannot apply" P
                                          end
                                        | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
                                          reshape_expr e ltac:(fun K e' =>
                                                                 twp_bind_core K; tac H) ||
                                          lazymatch iTypeOf H with
                                          | Some (_,?P) => fail "wp_apply: cannot apply" P
                                          end
                                        | _ => fail "wp_apply: not a 'wp'"
                                        end).
  Tactic Notation "wp_apply" open_constr(lem) :=
    wp_apply_core lem (fun H => iApplyHyp H; try iNext; try wp_expr_simpl).
  (** Tactic tailored for atomic triples: the first, simple one just runs
[iAuIntro] on the goal, as atomic triples always have an atomic update as their
premise.  The second one additionaly does some framing: it gets rid of [Hs] from
the context, which is intended to be the non-laterable assertions that iAuIntro
would choke on.  You get them all back in the continuation of the atomic
operation. *)
  Tactic Notation "awp_apply" open_constr(lem) :=
    wp_apply_core lem (fun H => iApplyHyp H; last iAuIntro).
  Tactic Notation "awp_apply" open_constr(lem) "without" constr(Hs) :=
    wp_apply_core lem (fun H => iApply wp_frame_wand_l; iSplitL Hs; [iAccu|iApplyHyp H; last iAuIntro]).

  Tactic Notation "wp_gensym" ident(l) "as" constr(H) :=
    let Htmp := iFresh in
    let finish _ :=
        first [intros l | fail 1 "wp_gensym:" l "not fresh"];
        eexists; split;
        [pm_reflexivity || fail "wp_gensym:" H "not fresh"
        |iDestructHyp Htmp as H; wp_finish] in
    wp_pures;
    (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]).
     If that fails, it tries to use the lemma [tac_wp_allocN]
     (respectively, [tac_twp_allocN]) for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      let process_single _ :=
          first
            [reshape_expr e ltac:(fun K e' => eapply (tac_wp_gensym _ _ _ _ Htmp K))
            |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
          [iSolveTC
          |finish ()]
      in process_single ()
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      let process_single _ :=
          first
            [reshape_expr e ltac:(fun K e' => eapply (tac_twp_gensym _ _ _ Htmp K))
            |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
          finish ()
      in
      process_single ()
    | _ => fail "wp_alloc: not a 'wp'"
    end.

  Tactic Notation "wp_alloc" ident(l) :=
    wp_gensym l as "?".
End proofmode.


Import proofmode notation.
Open Scope expr_scope.
Definition label : val :=
  (rec: "label" "l" :=
    match: "l" with
      NONE => #()
    | SOME "p" =>
      #()
    end)%V.


Definition label : val :=
  rec : "label" "t" :=
    match: "t" with
      LEAF => Leaf
    | NODE "x" "t1" "t2" =>
      let "l" := Gensym in
      let "t1'" := "label" "t1" in
      let "t2'" := "label" "t2" in
      Val (Node Gensym "t1'" "t2'")
    end.



Inductive tree (X : Type) : Type :=
| leaf : tree X
| node : X -> tree X -> tree X -> tree X.




(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)


Set Implicit Arguments.
From iris.heap_lang Require Import proofmode notation.



Section proof.
  Context `{!heapG Σ}.

  Fixpoint is_tree (t : tree _) (v : val) : iProp Σ :=
    match t with
    | leaf _ => ⌜ v = NONEV ⌝
    | node x t1 t2 => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                                               ∃ v1 v2 : val, p ↦ (#x, (v1,v2)) ∗ is_tree t1 v1 ∗ is_tree t2 v2
  end%I.


  Fixpoint Tree_Spec X (t : tree X) (v : val) : iProp Σ :=
    match t with
    | leaf _ => ⌜ v = NONEV ⌝
    | node x t1 t2 => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                                               ∃ v1 v2 : val, ∃ x : loc, p ↦ (#x, (v1,v2)) ∗
                                                                           x ↦ (LitV LitUnit) ∗ Tree_Spec t1 v1 ∗ Tree_Spec t2 v2
  end%I.

  Fixpoint List_Spec X (l : list X) (v : val) : iProp Σ :=
    match l with
    | [] => ⌜ v = NONEV ⌝
    | _ :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                                          ∃ v' : val, ∃ x : loc, p ↦ (#x, v') ∗ x ↦ (LitV LitUnit) ∗ List_Spec l' v'
  end%I.

  Fixpoint is_list (l : list _) (v : val) : iProp Σ :=
    match l with
    | [] => ⌜ v = NONEV ⌝
    | x :: l' => ∃ (p : loc), ⌜ v = SOMEV #p ⌝ ∗
                                          ∃ v' : val, p ↦ (#x, v') ∗ is_list l' v'
  end%I.

  Locate "{{{ _ }}} _ {{{ _ }}}".

  SearchAbout "WP".
  Locate twp.
  Lemma label_spec (t : tree _) v :
    {{{ is_tree t v }}} label v {{{ RET #(); Tree_Spec t v }}}.
  Proof.
    iIntros (a) "Hf Post".
    iInduction t as [|x l] "IH" forall (v a).
                                       - iDestruct "Hf" as %->. wp_rec.
                                         wp_match. iApply "Post"; eauto.
                                       - iDestruct "Hf" as (p) "[-> Hf]".
                                         wp_rec. wp_match. iDestruct "Hf" as (v1 v2) "[Hf Hp]".
                                         wp_load. wp_pures. wp_alloc l' as "H'". wp_store.
                                         iDestruct "Hp" as "[Hv1 Hv2]".
                                         wp_apply ("IH" with "[Hv1]"); eauto.
                                         + iIntros. wp_seq. iApply ("IH1" with "Hv2").
                                           iNext. iIntros. iApply ("Post").
                                           unfold Tree_Spec. iExists p.
                                           iSplit; eauto.
                                           * iExists v1. iExists v2. iExists l'. iFrame.
  Qed.
End proof.
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)



Definition Symb := loc.

Inductive FreshMonad (X : Type) : Type :=
| ret: X -> FreshMonad X
| Gensym: (Symb -> FreshMonad X) -> FreshMonad X.

Arguments ret {_} x.

Fixpoint bind {X Y} (m: FreshMonad X) (k: X -> FreshMonad Y) : FreshMonad Y :=
  match m with
  | ret x => k x
  | Gensym f => Gensym (fun x => bind (f x) k)
  end.

Definition gensym := Gensym ret.

Definition triple {X} (m : FreshMonad X) (H : iProp Σ) (Q : X -> iProp Σ) :=
  forall h, H h

              Fixpoint run {X} (m: FreshMonad X) : state -> state * X :=
    match m with
    | ret x => fun s => (s,x)
    | Gensym f =>
      fun s =>
        let l := fresh (dom (gset loc) s.(heap)) in
        run (f l) (state_upd_heap <[l:=#()]> s)
    end.

Print leibnizC.
Print discreteC.
Print discrete_ofe_mixin.

Print gFunctors.
Print gFunctor.
Print rFunctor.


Axiom H : iProp stateC.


Definition triple_test {X} (m : FreshMonad X) (H: iProp Σ) (Q : X -> iProp Σ) :=
  ∀ v : X, run
             ∀ Φ : val → iPropI Σ, H -∗ ▷ (Tree_Spec t v -∗ Φ #()) -∗ WP label v {{ v, Φ v }}

                                     Definition triple {X} (m: FreshMonad X) (H: iProp Σ)(Q: X -> iProp Σ): Prop :=
    (* define in terms of 'run' *)
    forall h, H -> exists h' v, run m h = (h',v) -> Q v .


Lemma rule_gensym : forall l',
    triple (ref #())%E (l' ↦ #())%I (fun l => l' ↦ #() ∗ l ↦ #())%I.


Fixpoint run {X} (m: FreshMonad X) : gFunctors -> gFunctors * X :=
  match m with
  | ret x => fun s => (s,x)
  | Gensym f =>
    fun s =>
      let l := fresh (dom (gset loc) s.(heap)) in
      run (f l) (state_upd_heap <[l:=#()]> s)
  end.

Definition testFunctors := { n : nat & fin n → testFunctor }.



Lemma rule_gensym : forall l',
    triple gensym (l' ↦ #())%I (fun l => l' ↦ #() ∗ l ↦ #())%I.
Proof.
  intros. intro. intro.
  repeat intro. simpl. pose ( h' := (state_upd_heap <[fresh (dom (gset loc) (heap h)):=#()]> h)).
  exists h'. exists (fresh (dom (gset loc) (heap h))). intros. iFrame. iSplit.
  iIntros (a) "_ Hf". unfold gensym. wp_lam. wp_alloc l' as "?". iApply "Hf".
  pose (alloc_fresh #()).





  Require Import LibCore Omega.


  Definition var := nat.
  Definition eq_var_dec := Nat.eq_dec.


  Definition sym := nat.
  Definition null := 0%nat.

  Inductive prim : Type :=
  | val_gensym : prim      (* make a fresh name *)
  | val_eq : prim       (* comparison *)
  | val_add : prim      (* addition *)
  | val_sub : prim      (* substraction *)
  | val_mul : prim      (* multiplication *)
  | val_div : prim.      (* division *)

  Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_sym : sym -> val
  | val_prim : prim -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_leaf : val
  | val_node : val
  | val_node1 : val -> val
  | val_node2 : val -> val -> val
  | val_node3 : val -> val -> val -> val

  with trm : Type :=
       | trm_val : val -> trm
       | trm_var : var -> trm
       | trm_fun : var -> trm -> trm
       | trm_fix : var -> var -> trm -> trm
       | trm_if : trm -> trm -> trm -> trm
       | trm_match : trm -> trm -> var -> var -> var -> trm -> trm
       | trm_seq : trm -> trm -> trm
       | trm_let : var -> trm -> trm -> trm
       | trm_app : trm -> trm -> trm
       | trm_while : trm -> trm -> trm
       | trm_for : var -> trm -> trm -> trm -> trm.

  Definition trm_node (n l r: trm): trm :=
    trm_app
      (trm_app
         (trm_app
            (trm_val (val_node))
            n)
         l)
      r.

  Coercion val_prim : prim >-> val.
  Coercion val_bool : bool >-> val.
  Coercion val_int : Z >-> val.
  Coercion trm_val : val >-> trm.
  Coercion trm_var : var >-> trm.
  Coercion trm_app : trm >-> Funclass.

  Require Import MSets.

  Module Import MSet := MSetAVL.Make Nat_as_OT.
  Module Import MSetProps := MSetProperties.WPropertiesOn Nat_as_OT MSet.
  Module Import MSetInterface := MSetProperties.OrdProperties MSet.

  Definition structure := MSet.t.
  Definition empty := MSet.empty.
  Definition add := MSet.add.
  Definition remove := MSet.remove.
  Definition singleton := MSet.singleton.
  Definition union := MSet.union.
  Definition disjoint (l l': structure) :=
    forall x,
      ~(MSet.In x l /\ MSet.In x l').


  Definition state := structure.

  (* Parameter red : state -> trm -> state -> val -> Prop. *)

  Definition assertion := state -> Prop.

  Definition heap : Type := state. (* intended to represent a piece of state *)

  (** In practice, we use type [state] when defining the evaluation rules,
    and we use the type [heap] to denote the argument of an assertion.
    In the rare cases where an entity is used at the same time in an
    evaluation rule and as argument of an assertion, we use type [heap]. *)

  (** A Separation Logic assertion is a predicate over a piece of state.
    Thus, it has type [heap -> Prop]. The type of such _heap predicates_
    is written [hprop]. *)

  Definition hprop := heap -> Prop.

  Definition hempty := fun (h : heap) => Equal h empty.

  Definition hsingle loc : hprop :=
    fun h =>  Equal h (singleton loc).

  Definition hpure (P:Prop) : hprop :=
    fun h =>  Equal h empty /\ P.

  Definition hexists (A:Type) (J:A->hprop) : hprop :=
    fun h => exists x, J x h.

  Definition hstar (H1 H2:hprop) : hprop :=
    fun h => exists (h1 h2:heap),
        H1 h1
        /\ H2 h2
        /\ disjoint h1 h2
        /\ Equal h (union h1 h2).

  Definition htop : hprop :=
    fun (h:heap) => True.

  Definition hbot : hprop :=
    fun (h:heap) => False.

  Notation "\[ P ]" := (hpure P)
                         (at level 0, P at level 99, format "\[ P ]").

  Notation "\s l" := (hsingle l)
                       (at level 32, no associativity).

  Notation "'Hexists' x1 , H" := (hexists (fun x1 => H))
                                   (at level 39, x1 ident, H at level 50).

  Notation "'Hexists' ( x1 : T1 ) , H" := (hexists (fun x1:T1 => H))
                                            (at level 39, x1 ident, H at level 50, only parsing).
  Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
                                      (at level 39, x1 ident, x2 ident, H at level 50) : heap_scope.
  Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
                                         (at level 39, x1 ident, x2 ident, x3 ident, H at level 50) : heap_scope.
  Notation "'Hexists' x1 x2 x3 x4 , H" :=
    (Hexists x1, Hexists x2, Hexists x3, Hexists x4, H)
      (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, H at level 50) : heap_scope.
  Notation "'Hexists' x1 x2 x3 x4 x5 , H" :=
    (Hexists x1, Hexists x2, Hexists x3, Hexists x4, Hexists x5, H)
      (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, x5 ident, H at level 50) : heap_scope.


  Notation "H1 '\*' H2" := (hstar H1 H2)
                             (at level 41,right associativity).

  Notation "Q \*+ H" := (fun x => (Q x) \* H)
                          (at level 40).

  Notation "\[]" := (hempty)
                      (at level 0).

  Notation "\# h1 h2" := (disjoint h1 h2)
                           (at level 40, h1 at level 0, h2 at level 0, no associativity).

  Notation "h1 \+ h2" := (union h1 h2)
                           (at level 51, right associativity).

  Notation "\Top" := htop.

  Notation "\Bot" := hbot.

  Lemma disjoint_sym : forall (h1 h2:heap),
      disjoint h1 h2 -> disjoint h2 h1.
  Proof.
    unfold disjoint. intros. rewrite (Logic.and_comm). apply H.
  Qed.

  Lemma hstar_comm : forall (H1 H2:hprop) (h:heap),
      ((H1 \* H2) h) ->
      ((H2 \* H1) h).
  Proof.
    intros.
    repeat (destruct H). destruct H0. destruct H3.
    exists x0. exists x.
    apply disjoint_sym in H3. rewrite union_sym in H4.
    repeat(split); try(assumption); try(rewrite H4; trivial).
  Qed.

  Lemma not_in : forall (x1 x2 : structure) x, In x x1 -> ~ (In x x1 /\ In x x2) -> ~ (In x x2).
  Proof.
    intros. intro. destruct H0. split; assumption.
  Qed.

  Lemma elem_in_union_left : forall x1 x2 x, In x x1 -> In x (union x1 x2).
  Proof.
    intros. apply union_spec. left. assumption.
  Qed.

  Lemma elem_in_union_right : forall x1 x2 x, In x x2 -> In x (union x1 x2).
  Proof.
    intros. apply union_spec. right. assumption.
  Qed.

  Lemma disjoint_eq_1 : forall x x1 x2,
      disjoint x (union x1 x2) -> disjoint x x1.
  Proof.
    intros. unfold disjoint in *. intro. intro. destruct H0.
    apply (not_in H0) in H. destruct H. apply elem_in_union_left. assumption.
  Qed.

  Lemma disjoint_eq_2 : forall x x1 x2, disjoint x (union x1 x2) -> disjoint x x2.
  Proof.
    intros. unfold disjoint in *. intro. intro. destruct H0.
    apply (not_in H0) in H. destruct H. apply elem_in_union_right. assumption.
  Qed.

  Lemma equal_disjoint_left : forall x x0 x1 x2,
      Equal x0 (union x1 x2) -> disjoint x x0 -> disjoint x x1.
  Proof.
    intros. unfold Equal in H. unfold disjoint in *. intro. intro.
    destruct H1. apply (not_in H1) in H0. destruct H0. rewrite H.
    apply elem_in_union_left. assumption.
  Qed.

  Lemma equal_disjoint_right : forall x x0 x1 x2,
      Equal x0 (union x1 x2) -> disjoint x0 x -> disjoint x x2.
  Proof.
    intros. unfold Equal in H. apply disjoint_sym in H0. unfold disjoint in *. intro. intro.
    destruct H1. apply (not_in H1) in H0. destruct H0. rewrite H.
    apply (elem_in_union_right). assumption.
  Qed.

  Lemma union_in_not : forall x0 x1 x2, ~In x0 x2 -> In x0 (union x1 x2) -> In x0 x1.
  Proof.
    intros. apply union_spec in H0. destruct H0; intuition.
  Qed.

  Lemma disjoint_equal : forall x1 x2 x3, Equal x2 x3 -> \# x1 x2 -> \# x1 x3.
  Proof.
    intros.
    intro. intro. destruct H1. destruct (H0 x). split~. now rewrite H.
  Qed.


  Lemma union_disjoint : forall x x1 x2,
      disjoint x x1 -> disjoint x x2 -> disjoint x (union x1 x2).
  Proof.
    intros. unfold disjoint in *. intro. intro. destruct H1.
    apply (not_in H1) in H. destruct H. apply (not_in H1) in H0.
    apply (union_in_not H0 H2).
  Qed.

  Lemma hstar_assoc : forall (H1 H2 H3:hprop) (h:heap),
      ((H1 \* (H2 \* H3)) h) <-> (((H1 \* H2) \* H3) h).
  Proof.
    split; intros; repeat (destruct H).
    * destruct H0. repeat (destruct H0).
      destruct H5. destruct H6. destruct H4.
      exists (union x x1) x2. repeat (split); try(assumption).
      ** exists x x1. repeat split; try(assumption); try(trivial).
         apply (equal_disjoint_left H7) in H4. assumption.
      ** apply disjoint_sym. apply disjoint_sym in H4.
         apply (equal_disjoint_right H7) in H4. apply disjoint_sym in H6.
         apply disjoint_sym in H4. apply (union_disjoint H4 H6).
      ** intro. rewrite union_assoc. rewrite <- H7. rewrite <- H8. assumption.
      ** intro. rewrite H8. rewrite H7. rewrite <- union_assoc. assumption.
    * destruct H0. destruct H5. destruct H4. destruct H7.
      exists x1 (union x2 x0). repeat (split); try(assumption).
      ** exists x2 x0. repeat split; try(assumption); try(trivial).
         apply (equal_disjoint_right H8) in H5.
         apply disjoint_sym. assumption.
      ** apply disjoint_sym in H5. apply (equal_disjoint_left H8) in H5.
         apply disjoint_sym in H5. apply (union_disjoint H7 H5).
      ** intro. rewrite <- union_assoc. rewrite <- H8. rewrite <- H6. assumption.
      ** intro. rewrite H6. rewrite H8. rewrite union_assoc. assumption.
  Qed.

  Parameter same_heap : forall (H : hprop) h h', Equal h h' -> H h' -> H h.

  Lemma neutral_elem : forall h H, H h <-> (H \* \[]) h.
  Proof.
    split;intros.
    * exists h empty. repeat (split); intuition.
      ** unfold disjoint. intro. intro. destruct H1. inversion H2.
      ** assert (~In a empty) by (intro P; inversion P).
         *** apply (union_in_not H2 H1).
    * destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
      apply empty_is_empty_2 in H1. apply (empty_union_2 x) in H1.
      rewrite H1 in H3. apply (same_heap H H3 H0).
  Qed.

  Lemma single_fresh : forall h,
      exists l, \# (singleton l) h.
  Proof.
    intros. unfold disjoint.
    pose (max_elt h). pose (i := o). assert (o = i) by auto.
    induction i.
    * exists (S a). intros.
      ** intro. destruct H0.
         pose (P := H1). apply (max_elt_spec2 H) in P.
         apply singleton_spec in H0. rewrite H0 in P. auto.
    * exists (S 0). intros.
      ** intro. destruct H0. apply max_elt_spec3 in H.
         unfold Empty in H. apply H in H1. assumption.
  Qed.

  Implicit Types t : trm.
  Implicit Types v : val.
  Implicit Types s : sym.
  Implicit Types b : bool.
  Implicit Types n : int.
  Import ListNotations.

  Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
    let aux t := subst y w t in
    let aux_no_capture x t := if eq_var_dec x y then t else aux t in
    let aux_no_captures xs t := (fix AUX xs := match xs with
                                               | [] => aux t
                                               | x :: xs => if eq_var_dec x y then t
                                                            else AUX xs
                                               end) xs
    in
    match t with
    | trm_val v => trm_val v
    | trm_var x => if eq_var_dec x y then trm_val w else t
    | trm_fun x t1 => trm_fun x (aux_no_capture x t1)
    | trm_fix f x t1 => trm_fix f x (if eq_var_dec f y then t1 else
                                       aux_no_capture x t1)
    | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
    | trm_match t0 t1 x y z t2 => trm_match (aux t0) (aux t1) x y z (aux_no_captures [x;y;z] t2)
    | trm_seq t1 t2 => trm_seq (aux t1) (aux t2)
    | trm_let x t1 t2 => trm_let x (aux t1) (aux_no_capture x t2)
    | trm_app t1 t2 => trm_app (aux t1) (aux t2)
    | trm_while t1 t2 => trm_while (aux t1) (aux t2)
    | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (aux_no_capture x t3)
    end.


  Inductive red : state -> trm -> state -> val -> Prop :=
  | red_val : forall m v,
      red m v m v
  | red_fun : forall m x t1,
      red m (trm_fun x t1) m (val_fun x t1)
  | red_fix : forall m f x t1,
      red m (trm_fix f x t1) m (val_fix f x t1)
  | red_if : forall m1 m2 m3 b r t0 t1 t2,
      red m1 t0 m2 (val_bool b) ->
      red m2 (if b then t1 else t2) m3 r ->
      red m1 (trm_if t0 t1 t2) m3 r
  | red_match_leaf : forall x y z v t1 t2 t3 m1 m2 m3,
      red m1 t1 m2 val_leaf ->
      red m2 t2 m3 v ->
      red m1 (trm_match t1 t2 x y z t3) m3 v
  | red_match_node :
      forall m0 m1 m2 m3 t1 t2 t3 x y z v v1 v2 v3,
        red m0 t1 m1 (val_node3 v1 v2 v3) ->
        red m2 (subst x v1 (subst y v2 (subst z v3 t3))) m3 v ->
        red m0 (trm_match t1 t2 x y z t3) m3 v
  | red_node : forall m0 m1 m2 m3 t1 t2 t3 v1 v2 v3,
      red m0 t1 m1 v1 ->
      red m1 t2 m2 v2 ->
      red m2 t3 m3 v3 ->
      red m0 (trm_node t1 t2 t3) m3 (val_node3 v1 v2 v3)
  | red_seq : forall m1 m2 m3 t1 t2 r,
      red m1 t1 m2 val_unit ->
      red m2 t2 m3 r ->
      red m1 (trm_seq t1 t2) m3 r
  | red_let : forall m1 m2 m3 x t1 t2 v1 r,
      red m1 t1 m2 v1 ->
      red m2 (subst x v1 t2) m3 r ->
      red m1 (trm_let x t1 t2) m3 r
  | red_app_arg : forall m1 m2 m3 m4 t1 t2 v1 v2 r,
      (* TODO: add [not_is_val t1 \/ not_is_val t2] *)
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      red m3 (trm_app v1 v2) m4 r ->
      red m1 (trm_app t1 t2) m4 r
  | red_app_node: forall m0 m1 v v1,
      v = val_node ->
      red m0 (trm_app v v1) m1 (val_node1 v1)
  | red_app_node1: forall m0 m1 v v1 v2,
      v = val_node1 v1 ->
      red m0 (trm_app v v2) m1 (val_node2 v1 v2)
  | red_app_node2: forall m0 m1 v v1 v2 v3,
      v = val_node2 v1 v2 ->
      red m0 (trm_app v v3) m1 (val_node3 v1 v2 v3)
  | red_app_fun : forall m1 m2 v1 v2 x t r,
      v1 = val_fun x t ->
      red m1 (subst x v2 t) m2 r ->
      red m1 (trm_app v1 v2) m2 r
  | red_app_fix : forall m1 m2 v1 v2 f x t r,
      v1 = val_fix f x t ->
      red m1 (subst f v1 (subst x v2 t)) m2 r ->
      red m1 (trm_app v1 v2) m2 r
  | red_gensym : forall ma mb l,
      mb = (singleton l) ->
      \# ma mb ->
      red ma (val_gensym) (mb \+ ma) (val_sym l)
  | red_add : forall m n1 n2 n',
      n' = n1 + n2 ->
      red m (val_add (val_int n1) (val_int n2)) m (val_int n')
  | red_sub : forall m n1 n2 n',
      n' = n1 - n2 ->
      red m (val_sub (val_int n1) (val_int n2)) m (val_int n')
  | red_eq : forall m v1 v2,
      red m (val_eq v1 v2) m (val_bool (isTrue (v1 = v2)))
  | red_while : forall m1 m2 t1 t2 r,
      red m1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) m2 r ->
      red m1 (trm_while t1 t2) m2 r
  | red_for_arg : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
      (* TODO: add [not_is_val t1 \/ not_is_val t2] *)
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      red m3 (trm_for x v1 v2 t3) m4 r ->
      red m1 (trm_for x t1 t2 t3) m4 r
  | red_for : forall m1 m2 x n1 n2 t3 r,
      red m1 (
            If (n1 <= n2)
            then (trm_seq (subst x n1 t3) (trm_for x (n1+1) n2 t3))
            else val_unit) m2 r ->
      red m1 (trm_for x n1 n2 t3) m2 r.


  Definition triple (t:trm) (H:hprop) (Q:val->hprop) :=
    forall H' h,
      (H \* H') h ->
      exists v h',
        red h t h' v
        /\ (Q v \* H') h'.

  Definition pred_incl (A : Type) (P Q : A -> Prop) :=
    forall x, P x -> Q x.

  Notation "P ==> Q" := (pred_incl P Q).

  Lemma himpl_refl : forall A (Q : A -> Prop), Q ==> Q.
  Proof.
    now intros.
  Qed.

  Lemma disjoint_empty : forall (s : structure), \# empty s.
  Proof.
    intro. red. intro. intro. destruct H. apply empty_spec in H. assumption.
  Qed.

  Lemma rule_frame : forall t H Q H',
      triple t H Q ->
      triple t (H \* H') (Q \*+ H').
  Proof using.
    introv M. intros HF h N. apply hstar_assoc in N.
    forwards (h'&v&R&K): (rm M) (H' \* HF) h.
    { assumption. }
    exists h' v. splits~. now apply hstar_assoc.
  Qed.

  Lemma rule_gensym :
    triple val_gensym \[] (fun r => Hexists l, \[r = val_sym l] \* (\s l)).
  Proof.
    intros. intros HF h N.
    pose (e := single_fresh h). destruct e.
    exists (val_sym x) ((singleton x) \+ h). split.
    * apply disjoint_sym in H. apply red_gensym; try(auto).
    * exists (singleton x) h. repeat split; auto.
      ** exists x empty (singleton x). repeat split; auto. apply disjoint_empty.
      ** apply hstar_comm in N.  apply (neutral_elem h HF). assumption.
  Qed.


  (* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

  Definition LABEL := 4.
  Definition X := 3.
  Definition N := 2.
  Definition L := 1.
  Definition R := 0.
  Definition LL := 5.
  Definition RR := 6.
  Definition FF := 7.

  Definition label (t : trm) :=
    trm_app
      (val_fix LABEL X
               (trm_match (trm_var X)
                          val_leaf
                          N L R
                          (trm_let FF (trm_val val_gensym)
                                   (trm_let LL (trm_app (trm_var LABEL) (trm_var L))
                                            (trm_let RR (trm_app (trm_var LABEL) (trm_var R))
                                                     (trm_node
                                                        (trm_var FF)
                                                        (trm_var LL)
                                                        (trm_var RR)))))))
      t.

  Fixpoint TreeSpec (v : val) :=
    match v with
    | val_leaf => \[]
    | val_node3 (val_sym l) t1 t2 => \s l \* (TreeSpec t1) \* (TreeSpec t2)
    | _ => fun h => False
    end.

  Inductive IsTree : val -> Prop :=
  | isLeaf: IsTree val_leaf
  | isNode: forall n l r, IsTree l -> IsTree r -> IsTree (val_node3 n l r).


  Lemma rule_app_fix : forall f x F V t1 H Q,
      F = (val_fix f x t1) ->
      triple (subst f F (subst x V t1)) H Q ->
      triple (trm_app F V) H Q.
  Proof.
    introv EF M. subst F. intros HF h N.
    lets~ (h'&v&R&K): (rm M) HF h.
    exists h' v. splits~. { applys~ red_app_fix. }
  Qed.

  Lemma rule_match_tree : forall v t t1 t2 x y z H Q,
      t = trm_val v -> IsTree v ->
      (t = val_leaf -> triple t1 H Q) ->
      (forall n l r, t = val_node3 n l r -> triple (subst x n (subst y l (subst z r t2))) H Q) ->
      triple (trm_match t t1 x y z t2) H Q.
  Proof.
    destruct v; intros; inversion H1; subst; intros H' h I.
    * lets~ (v&h'&P&D) : (rm H2) H' h. exists v h'. splits~.
      apply (red_match_leaf _ _ _ _ (red_val h val_leaf) P).
    * lets~ (v&h'&P&D) : (rm H3) H' h. exists v h'.
      splits~. apply (red_match_node _ _ _ _ _ (red_val h (val_node3 n v2 v3)) P).
  Qed.

  Lemma himpl_frame_l : forall H1 H2 H3,
      H1 ==> H2 ->
      (H1 \* H3) ==> (H2 \* H3).
  Proof.
    introv I. intros h H. repeat (destruct H). exists x x0. auto.
  Qed.


  Lemma rule_val : forall v H Q,
      H ==> Q v ->
      triple (trm_val v) H Q.
  Proof.
    introv M. intros HF h N. exists v h. splits~.
    * apply red_val.
    * apply (himpl_frame_l M N).
  Qed.


  Lemma rule_app_node3 : forall F V1 V2 V3 H Q,
      F = val_node ->
      triple (val_node3 V1 V2 V3) H Q ->
      triple (F V1 V2 V3) H Q.
  Proof.
    introv P M. subst F. intros HF h P. lets~ (v&h'&X&D) : (rm M) HF h.
    exists (val_node3 V1 V2 V3) h. split.
    * apply (red_node (m1 :=h) (m2 := h)); apply red_val.
    * inversion X. now subst.
  Qed.


  Lemma rule_let : forall x t1 t2 H Q Q1,
      triple t1 H Q1 ->
      (forall (X:val), triple (subst x X t2) (Q1 X) Q) ->
      triple (trm_let x t1 t2) H Q.
  Proof.
    introv M Hyp. intros HF h P. lets~ (v&h'&X&D) : (rm M) HF h.
    lets~ (v'&h''&X'&D') : (rm (Hyp v)) HF h'.
    exists v' h''. split~. apply (red_let _ _ X X').
  Qed.


  Lemma rule_extract_hexists : forall t (A:Type) (J:A->hprop) Q,
      (forall x, triple t (J x) Q) ->
      triple t (hexists J) Q.
  Proof.
    introv M. intros HF h H. repeat (destruct H). lets~ (v&h'&X&D) : (rm (M x1)) HF h.
    * now exists x x0.
                 * now exists v h'.
  Qed.

  Lemma rule_consequence : forall t H' Q' H Q,
      H ==> H' ->
      triple t H' Q' ->
      (forall v, Q' v ==> Q v) ->
      triple t H Q.
  Proof.
    introv X M T. intros HF h N. lets~ (v&h'&P&D) : (rm M) HF h.
    * apply (himpl_frame_l X N).
    * exists v h'. split~. apply (himpl_frame_l (T v) D).
  Qed.

  Lemma himpl_empty_left : forall H, H ==> \[] \* H.
  Proof using.
    introv M. apply hstar_comm. now rewrite <- neutral_elem.
  Qed.

  Lemma finish_him : forall r l fresh f h,
      ((TreeSpec r \* TreeSpec l \* \[f = val_sym fresh] \* \s fresh) h) ->
      f = val_sym fresh /\ (\s fresh \* TreeSpec l \* TreeSpec r) h.
  Proof.
    intros. apply hstar_comm in H. repeat (destruct H). repeat (destruct H1). destruct H0. split~.
    - exists x4 (x0 \+ x1). destruct H3. destruct H6. destruct H2. destruct H5.
      rewrite H1 in H7. rewrite~ empty_union_1 in H7. repeat split~.
      + exists x1 x0. repeat split~.
        * apply disjoint_sym. apply disjoint_sym in H5. apply (equal_disjoint_left H8 H5).
        * now rewrite union_sym.
        * now rewrite union_sym.
      + rewrite H7 in H8. apply union_disjoint.
        * apply disjoint_sym. apply (equal_disjoint_right H8 H5).
        * apply disjoint_sym. apply (disjoint_equal H7 H2).
      + intro. rewrite H9 in H10. rewrite H7 in H8. rewrite H8 in H10. rewrite union_sym.
        rewrite union_sym in H10. now rewrite union_assoc.
      + intro. rewrite H9. rewrite H7 in H8. rewrite H8. rewrite union_sym.
        rewrite union_sym in H10. now rewrite union_assoc in H10.
  Qed.

  Lemma rule_frame_consequence : forall H2 H1 Q1 t H Q,
      H ==> H1 \* H2 ->
      triple t H1 Q1 ->
      (forall H, (Q1 \*+ H2) H ==> Q H) ->
      triple t H Q.
  Proof.
    introv WH M WQ. applys rule_consequence WH WQ. applys rule_frame M.
  Qed.



  Theorem label_correct: forall v, IsTree v ->
                                   triple (label (trm_val v)) \[] TreeSpec.
  Proof.
    intros.
    unfold label.
    induction H.
    - (* Case: v ~ val_leaf *)
      applys~ rule_app_fix; simpl.
      applys~ rule_match_tree; try constructor; try discriminate 1; intro.
      applys~ rule_val; simpl.
      apply himpl_refl.
    - (* Case: v ~ val_node *)
      applys~ rule_app_fix; simpl.
      applys~ rule_match_tree; try discriminate 1; intros.
      now constructor. inversion H1; subst.
      applys~ rule_let; [| intros f; simpl].
      + applys~ rule_gensym.
      + applys~ rule_extract_hexists; intro fresh.
        applys~ rule_let; [| intros l'; simpl].
        * apply~ (rule_frame_consequence (H2 :=  \[f = val_sym fresh] \* \s fresh)
                                         (H1 := \[])
                                         (Q1 := TreeSpec)).
          -- apply himpl_empty_left.
          -- intros x h q.
             exact q.
        * simpl. applys~ rule_let; [| intros r; simpl].
          -- apply~ (rule_frame_consequence (H2 :=  TreeSpec l' \* \[f = val_sym fresh] \* \s fresh)
                                            (H1 := \[])
                                            (Q1 := TreeSpec)).

             ++ apply himpl_empty_left.
             ++ intros x h q.
                exact q.
          -- applys~ rule_app_node3.
             applys~ rule_val.
             simpl. intros x H2.
             apply finish_him in H2.
             destruct H2. now subst f.
  Qed.

  (* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

  Inductive tree (X : Type) : Type :=
  | node : X -> tree X -> tree X -> tree X
  | leaf : tree X.

  Arguments leaf {_}.
  Arguments node {_} n l r.

  Definition Symb := nat.

  Inductive FreshMonad (X: Type): Type :=
  | ret: X -> FreshMonad X
  | Gensym: (Symb -> FreshMonad X) -> FreshMonad X.

  Arguments ret {_} x.

  Definition gensym := Gensym ret.

  Fixpoint bind {X Y} (m: FreshMonad X)(k: X -> FreshMonad Y): FreshMonad Y :=
    match m with
    | ret x => k x
    | Gensym f => Gensym (fun x => bind (f x) k)
    end.

  Parameter next' : Symb -> Symb.

  Definition next (h : heap) :=
    match max_elt h with
    | Some s' => (singleton (s' + 1)%nat) \+ h
    | None => singleton 0
    end.

  Fixpoint run' {X} (m: FreshMonad X) : Symb -> Symb * X :=
    match m with
    | ret x => fun s => (s,x)
    | Gensym f => fun s => run' (f s) (next' s)
    end.

  Fixpoint run {X} (m: FreshMonad X) : heap -> heap * X :=
    match m with
    | ret x => fun (s : heap) => (s,x)
    | Gensym f => fun (s : heap) => let s' := match max_elt s with
                                              | Some s' => (s' + 1)%nat
                                              | None => 0
                                              end in run (f s') (next s)
    end.

  Notation "'let!' x ':=' e1 'in' e2" := (bind e1 (fun x => e2))
                                           (x ident, at level 90).


  Fixpoint labelM (t: tree unit): FreshMonad (tree Symb) :=
    match t with
    | leaf => ret leaf
    | node _ l r =>
      let! f := gensym in
      let! l' := labelM l in
      let! r' := labelM r in
      ret (node f l' r')
    end.

  Definition tripleM {X} (m: FreshMonad X)(P: hprop)(Q: X -> hprop): Prop :=
    (* define in terms of 'run' *)
    forall H' h, (P \* H') h -> exists v h', run m h = (h',v)
                                             /\ (Q \*+ H') v h'.

  Ltac inversion_star H h P :=
    match goal with
    | H : (_ \* _) _ |- _ =>
      let W := fresh h in
      let w := fresh P in
      inversion H as (W&w);
      let W := fresh h in
      destruct w as (W&w);
      do 3 (let w0 := fresh P in
            destruct w as (w0&w))
    end.

  Lemma heap_max_disjoint : forall a h, max_elt h = Some a -> \# (singleton (a+1)%nat) h.
  Proof.
    intros. red. intros. intro. destruct H0. apply (max_elt_spec2 H) in H1. destruct H1.
    apply singleton_spec in H0. omega.
  Qed.

  Lemma empty_disjoint : forall h h', Empty h -> \# h' h.
  Proof.
    intros. red in H. intro. intro. destruct H0. now apply H in H1.
  Qed.

  Lemma ruleM_gensym :
    tripleM gensym \[] (fun l => \s l).
  Proof.
    intros H' h P. inversion_star P h P. red in P1. rewrite P1 in P0.
    rewrite~ empty_union_1 in P0. simpl.
    induction (max_elt h) eqn:?.
    - exists (a+1)%nat (next h).
      split~.
      exists (singleton (a+1)%nat) h.
      split.
      + red. reflexivity.
      + split.
        * apply (same_heap H' P0 P2).
        * split.
          -- apply (heap_max_disjoint Heqo).
          -- unfold next. rewrite Heqo. reflexivity.
    - exists 0 (next h).
      split~.
      exists (singleton 0) h.
      split.
      + red. reflexivity.
      + split.
        * apply (same_heap H' P0 P2).
        * split.
          -- apply max_elt_spec3 in Heqo. apply (empty_disjoint Heqo).
          -- unfold next. rewrite Heqo. apply max_elt_spec3 in Heqo.
             intro. split; intro.
             ++ apply union_spec. left~.
             ++ apply union_spec in H. destruct~ H.
                red in Heqo. now apply Heqo in H.
  Qed.

  Lemma test : forall X Y (t1 : FreshMonad X) (t2 : X -> FreshMonad Y) h,
      run (let! x := t1 in t2 x) h =
      let (h',s) := run t1 h in run (t2 s) h'.
  Proof.
    induction t1; intros; simpl in *.
    * reflexivity.
    * induction (max_elt h); now rewrite H.
  Qed.

  Lemma ruleM_let : forall X Y (t1 : FreshMonad X) (t2 : X -> FreshMonad Y) H Q Q1,
      tripleM t1 H Q1 ->
      (forall (X:X), tripleM (t2 X) (Q1 X) Q) ->
      tripleM (let! x := t1 in t2 x) H Q.
  Proof.
    introv M X. intros H' h P. rewrite test.
    apply M in P; simpl in P; destruct P as (s&h'&Eq&P);
      apply X in P; destruct P as (s0&h0&eq0&P).
    exists s0 h0. split~.
    rewrite~ Eq.
  Qed.


  Lemma ruleM_frame : forall {X} (FMX : FreshMonad X) H Q H',
      tripleM FMX H Q ->
      tripleM FMX (H \* H') (Q \*+ H').
  Proof.
    introv M. intros HF h X.
    rewrite <- hstar_assoc in X.
    edestruct (M _ _ X). destruct H0.
    exists x x0. rewrite <- hstar_assoc. exact H0.
  Qed.

  Lemma ruleM_val : forall {X} (v : X) H Q,
      H ==> Q v ->
      tripleM (ret v) H Q.
  Proof.
    introv M. intros HF h X.
    inversion_star X h P. exists v h. split~.
    exists h0 h1. split~.
  Qed.

  Lemma ruleM_consequence : forall {X} (t : FreshMonad X) H' Q' H Q,
      H ==> H' ->
      tripleM t H' Q' ->
      (forall (v : X), Q' v ==> Q v) ->
      tripleM t H Q.
  Proof.
    introv M X F. intros HF h P. inversion_star s h P. apply M in P1. edestruct (X HF h).
    * exists h0 h1. split; auto.
    * destruct H0. exists x x0. destruct H0 as (W&H0). split~. inversion_star H0 h P.
      exists h2 h3. split~. apply (F _ _ P5).
  Qed.

  Lemma ruleM_frame_consequence : forall {X} H2 H1 Q1 (t : FreshMonad X) H Q,
      H ==> H1 \* H2 ->
      tripleM t H1 Q1 ->
      (forall H, (Q1 \*+ H2) H ==> Q H) ->
      tripleM t H Q.
  Proof.
    introv WH M WQ. eapply (ruleM_consequence _ WH). apply ruleM_frame. exact M. exact WQ.
  Qed.

  Fixpoint TreeSpecM (t: tree Symb) :=
    match t with
    | leaf => \[]
    | node s l r => (\s s) \* TreeSpecM l \* TreeSpecM r
    end.

  Lemma finishM_him : forall r l fresh h,
      ((TreeSpecM r \* TreeSpecM l \* \s fresh) h) ->
      (\s fresh \* TreeSpecM l \* TreeSpecM r) h.
  Proof.
    intros. apply hstar_comm. rewrite hstar_assoc in H. red in H. destruct H. destruct H. destruct H.
    destruct H0. exists x x0. repeat split~. apply~ hstar_comm.
  Qed.

  Theorem labelM_correct: forall tree0, tripleM (labelM tree0) \[] TreeSpecM.
  Proof.
    intros.
    unfold labelM.
    induction tree0.
    - (* case node *)
      apply (ruleM_let _ ruleM_gensym).
      intros.
      eapply ruleM_let.
      + apply~ (ruleM_frame_consequence (H1 := \[])
                                        (H2 := \s X0)
                                        (Q1 := TreeSpecM)).
        * apply himpl_empty_left.
        * intros l h q.
          exact q.
      + intros.
        eapply ruleM_let.
        * apply~ (ruleM_frame_consequence (H1 := \[])
                                          (H2 := (TreeSpecM X1 \* \s X0))
                                          (Q1 := TreeSpecM)).
          -- apply himpl_empty_left.
          -- intros l h q.
             exact q.
        * intros.
          apply ruleM_val.
          simpl. intros l H. apply~ finishM_him.
    - (* case leaf *)
      apply ruleM_val.
      apply himpl_refl.
  Qed.
