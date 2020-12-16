From iris.proofmode Require Export base intro_patterns spec_patterns
     sel_patterns coq_tactics reduction
     coq_tactics ltac_tactics.
Require Import FunctionalExtensionality.
From iris Require Export bi.bi proofmode.tactics proofmode.monpred proofmode.reduction.
Global Set Warnings "-convert_concl_no_check -notation-overridden".
Require Import SepMin SepList.

(* Monade libre *)
Module FreeMonad.

  Inductive mon (E : Type -> Type) (X : Type) : Type :=
  | ret : X -> mon E X
  | op : forall Y, E Y -> (Y -> mon E X) -> mon E X.

  Arguments ret {_ _} x.
  Arguments op {_ _ _}.

  Fixpoint bind {E X Y} (m : mon E X) (f : X -> mon E Y)
    : mon E Y :=
    match m with
    | ret x => f x
    | op e c => op e (fun x => bind (c x) f)
    end.

  Definition syntax_effect {E X} (e : E X) := op e ret.

  Notation "'let!' x ':=' e1 'in' e2" :=
    (bind e1 (fun x => e2)) (x ident, at level 50).

  Notation "'ret!' v" := (ret v) (v ident, at level 50).

  Lemma lid : forall E X Y (a : X) (f : X -> mon E Y), let! v := ret! a in f v = f a.
  Proof. auto. Qed.

  Lemma rid : forall E X (m : mon E X), let! v := m in ret v = m.
  Proof.
    fix m 3.
    destruct m0.
    * reflexivity.
    * simpl. do 2 f_equal. apply functional_extensionality. intro. apply m.
  Qed.

  Lemma ass_bind : forall E X Y Z (m : mon E X) f (g : Y -> mon E Z),
      let! v :=
         let! v' := m in
         f v'
      in
      g v =
      let! v := m in
      let! v' := f v in
      g v'.
  Proof.
    fix m 5.
    destruct m0; intros.
    * reflexivity.
    * simpl. do 2 f_equal. apply functional_extensionality. intro. apply m.
  Qed.

End FreeMonad.

(* Pour le moment, juste une tactique fait maison *)
Module SepBasicCore.

  Local Ltac Fresh :=
    let x := iFresh in
    match x with
    | IAnon ?x =>
      let x := eval compute in (ascii_of_pos (x + 64)) in
          let x := eval compute in (append "H" (string_of_list_ascii [x])) in
              let env := iGetCtx in
              let P := reduction.pm_eval (envs_lookup x env) in
              match P with
              | None => x
              | Some _ => Fresh
              end
    | _ => fail "iFresh returns " x " sometimes."
    end.

  (*h should be in the environment *)
  Local Ltac norm h :=
    let env := iGetCtx in
    let P := reduction.pm_eval (envs_lookup h env) in
    match P with
    | None => fail "assert false"
    | Some (false, ?P) =>
      match P with
      | bi_exist ?Q => let x := fresh "x" in (iDestruct h as (x) h; norm h)
      | bi_sep ?Q ?W =>
        let x := Fresh in
        let y := Fresh in
        eapply tac_and_destruct with h _ x y _ _ _;
        [ pm_reflexivity | pm_reduce; iSolveTC | pm_reduce; norm x; norm y]
      | bi_pure (and ?P ?Q) =>
        let x := Fresh in
        eapply tac_and_destruct with h _ h x _ _ _;
        [pm_reflexivity
        |pm_reduce; iSolveTC
        |pm_reduce; norm h; norm x]
      | bi_pure _ => iPure h as ?
      | bi_wand _ _ => iDestruct (h with "[]") as h; [progress auto | norm h]
      | bi_absorbingly _ =>
        let name := Fresh in
        let name_mod := eval compute in (append ">" name) in
            iPoseProof h as name; iDestruct name as name_mod; norm name
      | _ =>
        match h with
        | IAnon _ =>
          let x := Fresh in
          iPoseProof h as x
        | _ => idtac
        end
      end
    | Some (true,?P) => idtac
    end.

    (* (List.fold norm) in Ltac *)
  Local Ltac norm_list l :=
    match l with
    | [] => idtac
    | ?h :: ?t => norm h ; norm_list t
    end.

  Ltac norm_all :=
    iStartProof;
    let env := iGetCtx in
    let list_ident := eval compute in (rev (envs_dom env)) in
        norm_list list_ident; auto.

  Tactic Notation "iNorm" := norm_all.

End SepBasicCore.

(* Règles structurelles commune aux logiques de ressources et effets *)
Module weakestpre.
  Export SepBasicCore.
  Import FreeMonad.

  Section structural_rules.
    Context {PROP : bi}.
    Context {biInd : biIndex}.

    Definition iPropGen  := monPred biInd PROP.

    Context {E : Type -> Type}.
    Context {E_SPEC : forall {X}, E X -> iPropGen * (X -> iPropGen)}.

    Fixpoint wp_gen {X} (e1 : mon E X) (Q : X -> iPropGen) : iPropGen :=
      match e1 with
      | ret v => Q v
      | op e f =>
        let (pre,post) := E_SPEC _ e in
        pre ∗ (∀ l, post l -∗ (wp_gen (f l) Q))
      end.

    Lemma wp_bind {X Y} (e : mon E X) (f :  X → mon E Y) (Q : Y -> iPropGen) (Q' : X -> iPropGen) :
      wp_gen e Q' ⊢
      (∀ v,  Q' v -∗ wp_gen (f v) Q ) -∗
      wp_gen (let! v := e in f v) Q %I.
    Proof.
      iIntros "HA HB". revert e. fix e 1.
      destruct e0.
      - iApply "HB". iApply "HA".
      - simpl. destruct (E_SPEC Y0 e0). iNorm. iFrame. iIntros (l) "HC".
        iDestruct ("HD" with "HC") as "HA".
        iPoseProof "HB" as "HB". apply e.
    Qed.

    Lemma wp_consequence {X} (P Q : X -> iPropGen) (f : mon E X) :
      ⊢ wp_gen f P -∗
        (∀ x, P x -∗ Q x) -∗
        wp_gen f Q.
    Proof.
      induction f; simpl; intros; auto.
      - iIntros "HA HB". iApply ("HB" with "HA").
      - iIntros. iNorm. destruct (E_SPEC Y e). iNorm. iFrame. iIntros (l) "HA".
        iApply (H with "[HA HH] HE"). iApply ("HH" with "HA").
    Qed.

    Definition triple {X} P (e : mon E X) Q : iPropGen :=
      P -∗ (wp_gen e Q).

    Notation "'{{' P } } e {{ v ; Q } } " := (triple P e (fun v => Q))
                                               (at level 20, format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").

    Lemma ret_spec {X} (v : X) H (Q : X -> iPropGen) :
      (H ⊢ Q v) -> ⊢{{ H }} (ret! v : mon E X) {{ v'; Q v' }}.
    Proof. simpl; iIntros. iApply H0; auto. Qed.

    Lemma bind_spec {X Y} (e : mon E X) (f : X -> mon E Y) Q Q' (H : iPropGen) :
      (⊢{{ H }} e {{ v; Q' v }}) ->
      (∀ v, ⊢{{ Q' v }} f v {{ v'; Q v' }}) ->
      ⊢ {{ H }} let! v := e in f v {{ v; Q v}}.
    Proof.
      intros. iIntros "HA".
      iApply (wp_bind e f _ Q' with "[HA]").
      - iApply (H0 with "[HA]"); auto.
      - iIntros (v) "HC". iApply (H1 with "[HC]"); auto.
    Qed.

    Lemma consequence {X} H H' (Q : X -> iPropGen) (Q' : X -> iPropGen) (e : mon E X) :
      (⊢{{ H' }} e {{ v; Q' v }}) ->
      (forall v, Q' v ⊢ Q v) ->
      (H ⊢ H') ->
      ⊢{{ H }} e {{ v; Q v }}.
    Proof.
      intros. iIntros "HA". iDestruct (H2 with "HA") as "HA".
      iDestruct (H0 with "HA") as "HA". iApply (wp_consequence with "HA").
      iIntros "*". iApply H1.
    Qed.

    Lemma frame_bind : forall (P : iPropGen), ⊢ P -∗ emp ∗ P.
    Proof. iIntros "* $". Qed.

    Lemma frame {X} (H : iPropGen) R Q (e : mon E X) :
      (⊢{{ H }} e {{ v; Q v }}) ->
      ⊢{{ H ∗ R }} e {{ v; Q v ∗ R }}.
    Proof.
      intro P. iIntros "[HA HC]". iApply (wp_consequence with "[HA]").
      iApply P; auto. iIntros; iFrame.
    Qed.

    Lemma intro_true_r {X} (H : iPropGen) Q (e : mon E X) :
      (⊢{{ emp ∗ H }} e {{ v; Q v }}) ->
      ⊢{{ H }} e {{ v; Q v }}.
    Proof.
      intro P. iIntros "HA". iApply (P with "[HA]"). iFrame.
    Qed.

    Lemma effect_spec {X} (e : E X) :
      ⊢({{ fst (E_SPEC _ e) }} syntax_effect e {{ l; snd (E_SPEC _ e) l }}: iPropGen).
    Proof. unfold triple. simpl. destruct (E_SPEC _ e). iIntros "$ * $". Qed.

  End structural_rules.

  Ltac Frame := eapply intro_true_r; eapply frame.
  Ltac iRet := eapply ret_spec; auto.
  Ltac iBind := eapply bind_spec; [idtac | intro; idtac].

End weakestpre.

(* Gensym avec la monade libre *)
Module gensym.
  Export FreeMonad.

  Inductive Fresh {ident} : Type -> Type :=
  | Gensym : Fresh ident.

  Definition gensym {ident} : mon Fresh ident := syntax_effect Gensym.

End gensym.

Module gensym_run.
  Export gensym.

  Definition ident := positive.

  Definition Fresh := @Fresh ident.

  Record state := mk_state { state_heap : Pmap unit;
                             next : ident }.

  Definition initial_state : state := mk_state ∅ 1%positive.

  Definition fresh (s: state) : ident * state :=
    let h := state_heap s in
    let n := next s in
    (n, mk_state (<[n:=tt]>h) (Pos.succ n)).

  Fixpoint run {X} (m : mon Fresh X) : state -> state * X :=
    match m with
    | ret v => fun n => (n, v)
    | op Gensym f =>
      fun s =>
        let (i,s') := fresh s in
        run (f i) s'
    end.

End gensym_run.

Module gensym_run2.
  Export gensym.

  Definition ident := nat.

  Definition Fresh := @Fresh ident.

  Definition initial_state := 0.

  Fixpoint run {X} (m : mon Fresh X) : ident -> ident * X :=
    match m with
    | ret v => fun n => (n, v)
    | op Gensym f =>
      fun n => run (f n) (S n)
    end.

End gensym_run2.

(* Raisonnement pour gensym avec la SL minimaliste *)
Module weakestpre_gensym_SLMin.
  Export weakestpre.
  Export SepMin.
  Export gensym_run.

  Definition iProp := @iPropGen (@hpropI unit) biInd.

  Definition op_spec X (m : Fresh X) : iProp * (X -> iProp) :=
    match m with
    | Gensym => (emp,IsFresh)
    end.

  Definition wp {X} (m : mon Fresh X) (Q : X -> iProp) : iProp :=
    @wp_gen _ _ _ op_spec _ m Q.

  Notation "'{{' P } } e {{ v ; Q } }" := (@triple _ _ _ op_spec _ P e (fun v => Q))
      (at level 20, format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").
  (** triple rules *)

  Lemma gensym_spec :
  ⊢{{ emp }} gensym {{ l; IsFresh l }}.
  Proof. unfold triple. simpl. auto. Qed.

End weakestpre_gensym_SLMin.


(* Raisonnement pour gensym avec la SL sur liste minimaliste *)
Module weakestpre_gensym_SLList.
  Export SepList.
  Export weakestpre.
  Export gensym_run2.

  Definition iProp := @iPropGen (@hpropList ident) biInd.

  Definition op_spec X (m : Fresh X) : iProp * (X -> iProp) :=
    match m with
    | Gensym => (emp, IsFresh)
    end.

  Definition wp {X} (m : mon Fresh X) (Q : X -> iProp) : iProp :=
    @wp_gen _ _ _ op_spec _ m Q.

  Notation "'{{' P } } e {{ v ; Q } }" := (@triple _ _ _ op_spec _ P e (fun v => Q))
      (at level 20, format "'[hv' {{  P  } }  '/  ' e  '/'  {{  v ;  Q  } } ']'").
  (** triple rules *)

  Lemma gensym_spec :
  ⊢{{ emp }} gensym {{ l; IsFresh l }}.
  Proof. unfold triple. simpl. auto. Qed.

End weakestpre_gensym_SLList.


(* Adequacy pour gensym avec la SL minimaliste *)
Module adequacy_gensym_SLMin.
  Export weakestpre_gensym_SLMin.

  Definition wf_state s := forall p, (∃ v, state_heap s !! p = Some v) -> Pos.lt p (next s).

  Lemma wf_init : wf_state initial_state.
  Proof.
    unfold wf_state. intros. destruct H. rewrite lookup_empty in H. inversion H.
  Qed.

  Lemma fresh_is_fresh : forall (s : state), wf_state s -> (state_heap s) !! (next s) = None.
  Proof.
    unfold wf_state.
    intros. destruct ((state_heap s) !! (next s)) eqn:?; auto.
    assert (Pos.lt (next s) (next s)). apply H. eauto. lia.
  Qed.

  Lemma adequacy {X} : forall (e : mon Fresh X) (Q : X -> iProp) (s s' : state) v,
      wf_state s ->
      (heap_ctx (state_heap s) ⊢ wp e Q ) ->
      run e s = (s', v) ->
      (Q v) () (state_heap s').
  Proof.
    fix e 1.
    destruct e0; intros.
    - inversion H1; subst. apply soundness2. iApply H0.
    - simpl in *. destruct f. eapply e.
      3 : apply H1.
      + unfold wf_state in *. simpl. intros. destruct H2.
        destruct (Pos.eq_dec p (next s)). lia. rewrite lookup_insert_ne in H2; auto.
        assert (Pos.lt p (next s)). apply H. eauto. lia.
      + iIntros "HA". simpl. apply fresh_is_fresh in H.
        apply (map_disjoint_singleton_r _ _ tt) in H.
        iDestruct (heap_ctx_split_sing _ _ _ H with "HA") as "[HA HB]".
        unfold wp in H0. simpl in *. iDestruct (H0 with "HA") as "[_ HA]".
        iApply "HA". iExists (). auto.
  Qed.

  Lemma adequacy_init {X} : forall (e : mon Fresh X) (Q : X -> iProp) (s' : state) v ,
      (⊢ wp e Q) ->
      run e initial_state = (s', v) ->
      (Q v) () (state_heap s').
  Proof. intros. eapply adequacy; eauto. apply wf_init. auto. Qed.

  Lemma adequacy_triple {X} : forall (e : mon Fresh X) (Q : X -> iProp) s v s' H,
      wf_state s ->
      (heap_ctx (state_heap s) ⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e s = (s', v) ->
      (Q v) () (state_heap s').
  Proof.
    intros. eapply adequacy; eauto. iIntros "HA". iDestruct (H1 with "HA") as "HA".
    iApply (H2 with "HA"); auto.
  Qed.

  Lemma adequacy_triple_init {X} : forall (e : mon Fresh X) (Q : X -> iProp) v s' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e initial_state = (s', v) ->
      (Q v) () (state_heap s').
  Proof.
    intros. eapply adequacy_init; eauto. iApply H1; eauto.
  Qed.

  Lemma adequacy_wp_pure {X} : forall (e : mon Fresh X) (Q : X -> Prop) s v s',
      wf_state s ->
      (heap_ctx (state_heap s) ⊢ wp e (fun v =>  ⌜Q v⌝)) ->
      run e s = (s', v) ->
      Q v.
  Proof.
    intros. apply (soundness1 (state_heap s')). iApply soundness3.
    eapply (adequacy _ _ _ _ _ H H0 H1).
  Qed.

  Lemma adequacy_pure {X} : forall (e : mon Fresh X) (Q : X -> Prop) s v s' H,
      wf_state s ->
      (heap_ctx (state_heap s) ⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e s = (s', v) ->
      Q v.
  Proof.
    intros. eapply adequacy_wp_pure; eauto. iIntros "HA". iDestruct (H1 with "HA") as "HA".
    iDestruct (H2 with "HA") as "$".
  Qed.

  Lemma adequacy_pure_init {X} : forall (e : mon Fresh X) (Q : X -> Prop) v s' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e initial_state = (s', v) ->
      Q v.
  Proof.
    intros. eapply adequacy_pure; eauto. apply wf_init.
    iIntros "_". iApply H1; auto.
  Qed.

End adequacy_gensym_SLMin.

(* Adequacy pour gensym avec la SL minimaliste *)
Module adequacy_gensym_SLList.
  Export weakestpre_gensym_SLList.

  Definition inject n := seq 0 n.

  Lemma inject_last : forall n, inject (S n) = inject n ++ [n].
  Proof. apply seq_S_end_app. Qed.

  Lemma next_disjoint : forall n, list_disjoint (inject n) [n].
  Proof.
    intros n x y P0 P1 eq. subst. inversion P1. subst. apply in_seq in P0.
    destruct P0. lia. inversion H.
  Qed.

  Lemma nodup_inject : forall n, NoDup (inject n).
  Proof.
    induction n.
    - apply NoDup_nil. trivial.
    - rewrite inject_last. apply NoDup_app. repeat split; auto.
      + intros. intro. pose (next_disjoint n).
        unfold list_disjoint in l.
        apply elem_of_list_In in H0.
        apply elem_of_list_In in H.
          by apply (l _ _ H H0).
      + apply NoDup_singleton.
  Qed.

  Lemma adequacy {X} : forall (e : mon Fresh X) (Q : X -> iProp) n n' v,
      (heap_ctx (inject n) ⊢ wp e Q ) ->
      run e n = (n', v) ->
      (Q v) () (inject n').
  Proof.
    fix e 1.
    destruct e0; intros.
    - inversion H0; subst. apply soundness2. iApply H.
    - simpl in *. destruct f. eapply e.
      2 : apply H0.
      + iIntros "HA". rewrite inject_last.
        iDestruct (heap_ctx_split with "HA") as "[HA HB]". apply next_disjoint.
        iDestruct (H with "HA") as "[_ HA]".
        iApply ("HA" with "HB").
  Qed.

  Lemma adequacy_init {X} : forall (e : mon Fresh X) (Q : X -> iProp) (s' : nat) v ,
      (⊢ wp e Q) ->
      run e initial_state = (s', v) ->
      (Q v) () (inject s').
  Proof. intros. eapply adequacy; eauto. iIntros "_". auto. Qed.

  Lemma adequacy_triple {X} : forall (e : mon Fresh X) (Q : X -> iProp) n v n' H,
      (heap_ctx (inject n) ⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e n = (n', v) ->
      (Q v) () (inject n').
  Proof.
    intros. eapply adequacy; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iApply (H1 with "HA").
  Qed.

  Lemma adequacy_triple_init {X} : forall (e : mon Fresh X) (Q : X -> iProp) v n' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e initial_state = (n', v) ->
      (Q v) () (inject n').
  Proof.
    intros. eapply adequacy_init; eauto. iApply H1; eauto.
  Qed.

  Lemma use_adequacy {X} : forall (e : mon Fresh X) (Q : X -> iProp) v n' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; Q v }}) ->
      run e initial_state = (n', v) ->
      exists s, NoDup s /\ (Q v) () s.
  Proof.
    intros. epose (adequacy_triple_init _ _ _ _ _ H0 H1 H2).
    exists (inject n'). split; auto. apply nodup_inject.
  Qed.

  Lemma adequacy_wp_pure {X} : forall (e : mon Fresh X) (Q : X -> Prop) n v n',
      (heap_ctx (inject n) ⊢ wp e (fun v =>  ⌜Q v⌝)) ->
      run e n = (n', v) ->
      Q v.
  Proof.
    intros. apply (soundness1 (inject n')). iApply soundness3.
    eapply (adequacy _ _ _ _ _ H H0).
  Qed.

  Lemma adequacy_pure {X} : forall (e : mon Fresh X) (Q : X -> Prop) n v n' H,
      (heap_ctx (inject n) ⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e n = (n', v) ->
      Q v.
  Proof.
    intros. eapply adequacy_wp_pure; eauto. iIntros "HA". iDestruct (H0 with "HA") as "HA".
    iApply (H1 with "HA").
  Qed.

  Lemma adequacy_pure_init {X} : forall (e : mon Fresh X) (Q : X -> Prop) v s' H,
      (⊢ H) -> (⊢ {{ H }} e {{ v; ⌜ Q v ⌝}}) ->
      run e initial_state = (s', v) ->
      Q v.
  Proof.
    intros. eapply adequacy_pure; eauto.
    iIntros "_". iApply H1; auto.
  Qed.

End adequacy_gensym_SLList.
