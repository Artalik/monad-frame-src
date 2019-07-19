From iris.program_logic Require Import weakestpre.
Require Import FunctionalExtensionality.
From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import tactics.
Require Import Ctypes.

Module monad.

  Section monad_rules.
    Context {state  : Type}.
    Context ( M : Type -> Type).
    Context ( ret : forall X, X -> M X).
    Context ( bind : forall X Y, M X -> (X -> M Y) -> M Y ).
    Arguments ret {_} x.
    Arguments bind {_ _} x f.
    Inductive err (X: Type) : Type :=
    | Erro : Errors.errmsg -> err X
    | Res : X -> err X.

    Class MonadProp :=
      {
        left_id (X Y : Type) (a : X) (f : X -> M Y) : bind (ret a) f = f a;
        right_id (X : Type) (m : M X) : bind m ret = m;
        assoc_bind (X Y Z : Type) (m : M X) f (g : Y -> M Z) :
          bind (bind m f) g = bind m (fun x => bind (f x) g)
      }.

  End monad_rules.

  Structure monad :=
    Monad {
        M : Type -> Type;
        state : Type;
        ret : forall (X : Type), X -> M X;
        bind : forall X Y, M X -> (X -> M Y) -> M Y;
        run : forall X, M X -> state -> err (state * X);
        prop : MonadProp M ret bind
      }.
  
End monad.

Module gensym.
  Import monad.
  Local Open Scope positive_scope.
  
  Definition ident := positive.
  Definition state := gmap ident type.
  Definition empty_state : state := gmap_empty.
  Definition state_to_list (s : state) := gmap_to_list s.
  
  (* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%ùùùùù*)
  Inductive sig (X : Type) : Type :=
  | Err : Errors.errmsg -> sig X
  | Gensym : type -> (ident -> X) -> sig X.

  Arguments Err [X].
  Arguments Gensym [X].
  
  Inductive mon (X : Type) : Type :=
  | ret : X -> mon X
  | op : sig (mon X) -> mon X.

  Arguments ret {_} x.
  Arguments op {_} s.
  
  Fixpoint bind {X Y} (m : mon X) (f : X -> mon Y) : mon Y :=
    match m with
    | ret x => f x
    | op (Err e) => op (Err e)
    | op (Gensym t g) => op (Gensym t (fun x => bind (g x) f))
    end.

  Definition error {X} (e : Errors.errmsg) : mon X := op (Err e).
  Definition gensym (t : type) : mon ident := op (Gensym t ret).  

  Lemma lid : forall X Y (a : X) (f : X -> mon Y), bind (ret a) f = f a.
  Proof. auto. Qed.

  Lemma rid : forall X (m : mon X), bind m ret = m.
  Proof.
    fix m 2.
    destruct m0.
    * reflexivity.
    * destruct s.
      ** reflexivity.
      ** simpl. do 2 f_equal. apply functional_extensionality. intro. apply m.
  Qed.

  Lemma ass_bind : forall X Y Z (m : mon X) f (g : Y -> mon Z),
      bind (bind m f) g = bind m (fun x => bind (f x) g).
  Proof.
    fix m 4.
    destruct m0; intros.
    * reflexivity.
    * destruct s.
      ** reflexivity.
      ** simpl. do 2 f_equal. apply functional_extensionality. intro. apply m.
  Qed.

  Hint Resolve lid rid ass_bind.

  Instance mP : @MonadProp mon (@ret) (@bind).
  Proof. split; eauto. Qed.

  Arguments Erro [X].
  Arguments Res [X].
  Local Open Scope positive_scope.

  Definition fresh (s : state) :=
    map_fold (fun x _ res => Pos.max res (x+1)) 1 s.
  
  Fixpoint run {X} (m : mon X) : state -> err (state * X) :=
    match m with
    | ret v => fun s => Res (s, v)
    | op (Err e) => fun s => Erro e
    | op (Gensym t f) =>
      fun s =>
        let l := fresh s in
        run (f l) (<[l := t]>s)
    end.
  

  Canonical Structure gensym_monad := @Monad mon state (@ret) (@bind) (@run) mP.

End gensym.

Module weakestpre_gensym.
  Import monad.
  Export gensym.
  Export gen_heap.
  
  (** Override the notations so that scopes and coercions work out *)
  Notation "l ↦ t" :=
    (mapsto (L:=ident) (V:=type) l 1 t) (at level 20) : bi_scope.

  Notation "\s l" :=
    (∃ t, l ↦ t)%I (at level 20) : bi_scope.

  Notation "P ⨈ Q" := (((P -∗ False) ∗ (Q -∗ False)) -∗ False)%I (at level 19) : bi_scope.
  Class heapG Σ :=
    HeapG {
        heap_preG_iris :> invG Σ;
        heapG_gen_heapG :> gen_heapG ident type Σ;
      }.
  Section mwp.
    Context `{!heapG Σ}.
    
    Fixpoint mwp {X} `{!heapG Σ} (e1 : mon X) (Q : X -> iProp Σ) : iProp Σ :=
      match e1 with
      | ret v => Q v
      | op (Err e) => True
      | op (Gensym t f) =>
        ∀ σ, gen_heap_ctx σ ==∗ mwp (f (fresh σ)) Q ∗ gen_heap_ctx (<[ fresh σ := t ]>σ)
      end%I.
  End mwp.

  Notation "'WP' e |{ Φ } |" := (mwp e Φ)
                                  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  
  Notation "'WP' e |{ v , Q } |" := (mwp e (λ v, Q))
                                      (at level 20, e, Q at level 200,
                                       format "'[' 'WP'  e  '[ ' |{  v ,  Q  } | ']' ']'") : bi_scope.
  
  Notation "'|{{' P } } | e |{{ x .. y , 'RET' pat ; Q } } |" :=
    (∀ Φ,
        P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e |{ Φ }|)%I
        (at level 20, x closed binder, y closed binder,
        format "'[hv' |{{  P  } } |  '/  ' e  '/'  |{{  x  ..  y ,  RET  pat ;  Q  } } | ']'") : bi_scope.

  Lemma fresh_is_fresh : forall σ, σ !! (fresh σ) = None.
  Admitted.

  Section mwp_proof.
    Context `{!heapG Σ}.
    Lemma mwp_value' {X} Φ (v : X) : Φ v ⊢ WP ret v |{ Φ }|.
    Proof. auto. Qed.
    Lemma mwp_value_inv' {X} Φ (v : X) : WP ret v |{ Φ }| -∗ Φ v.
    Proof. auto. Qed.

    Lemma mwp_mono {X} e Φ Ψ :
      WP e |{ Φ }| -∗ (∀ (v : X), Φ v -∗ Ψ v) -∗ WP e |{ Ψ }|.
    Proof.
      iIntros "HA HB". revert e. fix e 1.
      destruct e0.
      { iApply "HB". iApply "HA". }
      { destruct s.
        { simpl. trivial. }
        { simpl. iIntros (σ) "HC".
          iDestruct ("HA" with "HC") as "HA".
          iMod "HA" as "[HA HC]". 
          iFrame "HC". iModIntro.
          iPoseProof "HB" as "HB". apply e. }}
    Qed.

    Lemma mwp_bind {X Y} (e : mon X) (f :  X → mon Y) (Φ : Y -> iProp Σ)  (Φ' : X -> iProp Σ) :
      WP e |{ Φ' }| -∗ (∀ v,  Φ' v -∗ WP (f v) |{ Φ }|) -∗ WP bind e f |{ Φ }|%I.
    Proof.
      iIntros "HA HB". revert e. fix e 1.
      destruct e0.
      { iApply "HB". iApply "HA". }
      { destruct s.
        { simpl. auto. }
        { simpl. iIntros (σ) "HC". iDestruct ("HA" with "HC") as "HA".
          iMod "HA" as "[HA HC]". iFrame "HC".
          iPoseProof "HB" as "HB". iModIntro. apply e. }}
    Qed.
    
    Open Scope bi_scope.
    Lemma mwp_gensym t : WP gensym t |{ l, l ↦ t }|.
    Proof.
      simpl. iIntros (σ) "HA". iDestruct (gen_heap_alloc with "HA") as "HA".
      apply fresh_is_fresh. iMod "HA" as "[HA [HB _]]". iFrame. iModIntro. trivial. Qed.

    Lemma mwp_frame_l {X} (e : mon X) Φ (R : iProp Σ) : R ∗ WP e |{ Φ }| ⊢ WP e |{ v, R ∗ Φ v }|.
    Proof. iIntros "[? H]". iApply (mwp_mono with "H"). auto with iFrame. Qed.
    Lemma mwp_frame_r {X} (e : mon X) Φ R : WP e |{ Φ }| ∗ R ⊢ WP e |{ v, Φ v ∗ R }|.
    Proof. iIntros "[H ?]". iApply (mwp_mono with "H"); auto with iFrame. Qed.

  End mwp_proof.
  Open Scope bi_scope.

  Section adequacy.
    Inductive step {X} : mon X -> state -> mon X -> state -> Prop :=
    | gensym_step : forall σ t m,
        step (op (Gensym t m)) σ (m (fresh σ)) (<[ fresh σ := t ]>σ).


    Inductive nsteps {X} : nat ->  mon X -> state -> mon X -> state -> Prop :=
    | step_0 : forall e σ, nsteps 0 e σ e σ
    | step_l : forall e1 σ1 e2 σ2 e3 σ3 n,
        step e1 σ1 e2 σ2 ->
        nsteps n e2 σ2 e3 σ3 ->
        nsteps (S n) e1 σ1 e3 σ3.

    Section step.
      Context `{!heapG Σ}.

      Lemma wp_step {X} (e1 : mon X) σ1 e2 σ2 (Φ : X -> iProp Σ) :
        step e1 σ1 e2 σ2 →
        gen_heap_ctx σ1 -∗ WP e1 |{ Φ }| ==∗
        gen_heap_ctx σ2 ∗ WP e2 |{ Φ }|.
      Proof.
        iIntros (Hstep) "HA HB".
        inversion Hstep. subst.
        simpl.
        iDestruct ("HB" with "HA") as "HA".
        iMod "HA" as "[HA HB]". iModIntro. iFrame.
      Qed.

      Lemma wp_steps {X} n (e1 e2 : mon X) σ1 σ2 Φ :
        nsteps n e1 σ1 e2 σ2 →
        gen_heap_ctx σ1 -∗ WP e1 |{ Φ }| ==∗ gen_heap_ctx σ2 ∗ WP e2 |{ Φ }|.
      Proof.
        revert e1 e2 σ1 σ2 Φ.
        induction n as [| n IH]=> e1 e2 σ1 σ2 Φ /=.
        * inversion_clear 1. iIntros "HA HB". iFrame.  trivial.
        * iIntros (Hsteps) "HA HB". inversion_clear Hsteps.
          eapply (wp_step _ _ _ _ Φ)in H. iDestruct (H with "HA") as "HA".
          iMod ("HA" with "HB") as "HC".
          apply (IH _ _ _ _ Φ) in H0. iDestruct "HC" as "[HA HB]".
          iDestruct (H0 with "HA") as "HC". iMod ("HC" with "HB") as "HC".
          iFrame. trivial.
      Qed.
    End step.
    
    Class heapPreG Σ :=
    HeapPreG {
        heappre_preG_iris :> invPreG Σ;
        heap_preG_heap :> gen_heapPreG ident type Σ;
      }.
    
    Theorem wp_strong_adequacy {X} `{!heapPreG Σ} n (e1 : mon X) σ1 e2 σ2 φ :
      (∀ `{Hinv : !invG Σ},
          (|==> ∃ (heap : gen_heapG ident type Σ)
                  (Φ : X → iProp Σ),
                let _ : heapG Σ := HeapG Σ _ heap in
                gen_heap_ctx σ1 ∗
                WP e1 |{ Φ }| ∗
                (gen_heap_ctx σ2 ==∗ ⌜ φ ⌝))%I) →
      nsteps n e1 σ1 e2 σ2 →
      φ.
    Proof.
      intros Hwp ?.
      epose (step_fupdN_soundness' φ 2).
      simpl in φ0. apply φ0. intro.
      iMod Hwp as (heap Φ) "(HA & HB & HC)".
      iApply step_fupd_intro; eauto. iNext.
      epose step_fupdN_S_fupd.
      iApply (e 0%nat).
      iApply (step_fupdN_wand _ _ _ (gen_heap_ctx σ2)with "[-HC]").
      - simpl in Hwp. iDestruct (@wp_steps _ (HeapG _ Hinv heap) _ _ _ _ _ _ Φ) as "HC".
        + apply H.
        + iDestruct ("HC" with "HA") as "HA".
          iDestruct ("HA" with "HB") as "HD". iMod "HD" as "[HD HE]". iFrame "HD".
          iApply step_fupd_mask_mono; eauto.
      - iIntros "HA". iDestruct ("HC" with "HA") as "HB". iMod "HB" as "HB".
        iModIntro. iApply "HB".
    Qed.

    Definition adequate {X} (e : mon X) σ (Q : X -> state -> Prop) : Prop :=
      match run e σ with
      | Erro e => True
      | Res (σ', v) => Q v σ'
      end.

    Corollary wp_adequacy Σ {X} `{!heapPreG Σ} (e : mon X) σ φ :
      (∀ `{Hinv : !invG Σ}, |==> ∃ (heap : gen_heapG ident type Σ),
              let _ : heapG Σ := HeapG Σ _ heap in
              gen_heap_ctx σ ∗ WP e |{ v, ⌜φ v⌝ }|)%I →
      adequate e σ (λ v _, φ v).
    Proof.
      revert e σ φ. fix e 1; intros.
      unfold adequate.
      destruct e0; simpl.
      - eapply (wp_strong_adequacy 0 (ret x)). iIntros.
        iMod (H $! Hinv) as (heap) "[HA #HB]".
        iModIntro. iExists heap. iExists (fun x => ⌜ φ x ⌝).
        iFrame. iSplitL. iFrame "HB". iFrame "HB". eauto. constructor.
      - destruct s; simpl; auto.
        eapply (wp_strong_adequacy 1 (op (Gensym t m))).
        + iIntros. iMod (H $! Hinv) as (heap) "[HA HB]".
          iIntros. iModIntro. iExists heap. iExists (fun x => ⌜ φ x ⌝).
          iFrame. iIntros.
          iModIntro. iPureIntro. apply e.
          simpl in H. iIntros. iMod (H $! Hinv0) as (heap0) "[HA HB]".
          iMod ("HB" with "HA") as "[HA HB]".
          iModIntro. iExists heap0. iFrame.
        + do 3 econstructor.
    Qed.

    Lemma step_to_run {X} : forall n (e : mon X) σ v σ',
        nsteps n e σ (ret v) σ' -> run e σ = Res (σ',v).
    Proof.
      induction n; intros.
      - inversion H. subst. simpl. reflexivity.
      - inversion H. subst.
        inversion H1. subst. simpl in *. apply IHn.
        apply H2.
    Qed.

    Lemma run_to_step {X} : forall (e : mon X) σ v σ',
        run e σ = Res (σ',v) -> exists n, nsteps n e σ (ret v) σ' .
    Proof.
      fix e 1. destruct e0; intros.
      - exists (0)%nat. inversion H. subst. constructor.
      - destruct s.
        + inversion H.
        + simpl in *. apply e in H. destruct H. exists (S x). econstructor.
          * constructor.
          * apply H.
    Qed.

    Definition heap_adequacy Σ {X} `{!heapPreG Σ} (e : mon X) σ Q :
      (∀ `{!heapG Σ}, WP e |{ v, ⌜Q v⌝ }|%I) →
      adequate e σ (λ v _, Q v).
    Proof.
      intros Hwp. eapply (wp_adequacy Σ).
      iMod (gen_heap_init σ) as (?) "Hh".
      iIntros. iModIntro. iExists H. iFrame. iApply Hwp.
    Qed.
  End adequacy.

End weakestpre_gensym.

Module proofmode.
  Export weakestpre_gensym.
  Open Scope bi_scope.
  Ltac early S := iIntros (Φ) S.
  Section proofmode_intro.
    Context `{!heapG Σ}.    
    
    Lemma gensym_spec t :
    |{{ True }}| gensym t |{{ l, RET l; l ↦ t }}|.
    Proof.
      iIntros (Φ) "HA HB". simpl.
      iIntros (σ) "HC". pose mwp_gensym.
      simpl in u. iMod (u $! σ with "HC") as "[HC HD]".
      iModIntro. iFrame. iApply "HB". iApply "HC".
    Qed.
    
    Lemma ret_spec {X} (v : X) :
    |{{ True }}| ret v |{{ v', RET v'; ⌜ v' = v ⌝  }}|.
    Proof. early "HA HB". iApply "HB". auto. Qed.
    
    Lemma ret_spec_bis {X} (v : X) (Q : X -> iProp Σ) :
      Q v
      <->
    |{{ True }}| ret v |{{ v', RET v'; Q v' }}|.
    Proof.
      split.
      - intro. early "HA HB". iApply "HB". iApply H.
      - intro. iApply H; eauto.
    Qed. 
    
    Lemma error_spec {X} (Q : X -> iProp Σ) e :
    |{{ True }}| error e |{{ v, RET v; Q v }}|.
    Proof. early "HA HB". iApply "HA". Qed.
    
    Lemma bind_spec {X Y} (e : mon X) (f : X -> mon Y) Φ' Φ'' H :
    |{{ H }}| e |{{ v, RET v; Φ'' v }}| ->
                                        (∀ v, |{{ Φ'' v }}| (f v) |{{ v', RET v'; Φ' v' }}|) ->
    |{{ H }}| (bind e f) |{{ v, RET v; Φ' v}}|.
    Proof.
      intros. early "HA HB".
      iApply (mwp_bind e f _ Φ'' with "[HA]").
      - iApply (H0 with "[HA]"); auto. 
      - iIntros (v) "HC". iApply (H1 with "[HC]"); auto.
    Qed.
    
    Lemma frame_r {X} H R Φ' (e : mon X) :
    |{{ H }}| e |{{ v, RET v; Φ' v }}| ->
    |{{ H ∗ R }}| e |{{ v, RET v; Φ' v ∗ R }}|.
    Proof.
      intro P. early "HA HB". iDestruct "HA" as "[HA HC]".
      iApply (P with "[HA]"); auto.
      iIntros (v) "HA". iApply "HB". iFrame.
    Qed.

    Lemma frame_l {X} H R Φ' (e : mon X) :
    |{{ H }}| e |{{ v, RET v; Φ' v }}| ->
    |{{ R ∗ H }}| e |{{ v, RET v; R ∗ Φ' v }}|.
    Proof. intro P. early "HA HB". iDestruct "HA" as "[HA HC]".
           iApply (P with "[HC]"); auto.
           iIntros (v) "HC". iApply "HB". iFrame.
    Qed.

    Lemma consequence_post {X} Φ'' H Φ'  (e : mon X) :
      (forall v, Φ'' v -∗ Φ' v) ->
    |{{ H }}| e |{{ v, RET v; Φ'' v }}| ->
    |{{ H }}| e |{{ v, RET v; Φ' v }}|.
    Proof.
      intros P P'. early "HA HB".
      iApply (P' with "[HA]"); auto.
      iIntros (v) "HA". iApply "HB". iApply P. iApply "HA".
    Qed.

    Lemma consequence_pre {X} H' Φ' (H : iProp Σ)  (e : mon X) :
      (H -∗ H') ->
    |{{ H' }}| e |{{ v, RET v; Φ' v }}| ->
    |{{ H }}| e |{{ v, RET v; Φ' v }}|.
    Proof.
      intros P P'. early "HA HB".
      iApply (P' with "[HA]"); auto.
      iApply P. iApply "HA".
    Qed.
    
    Lemma tLeft {X} (Q : X -> iProp Σ) (R : X -> iProp Σ) S (e : mon X) :
    |{{ S }}| e |{{ v, RET v; R v }}| ->
    |{{ S }}| e |{{ v, RET v; R v ⨈ Q v }}|.
    Proof.
      intro H. early "HA HB".
      iApply (H with "[HA]"); auto.
      iIntros (v) "HA". iApply "HB". iIntros "HB". iDestruct "HB" as "[HB HC]".
      iApply "HB". iApply "HA".
    Qed.

    Lemma tRight {X} (Q : X -> iProp Σ) (R : X -> iProp Σ) S (e : mon X) :
    |{{ S }}| e |{{ v, RET v; Q v }}| ->
    |{{ S }}| e |{{ v, RET v; R v ⨈ Q v }}|.
    Proof.
      intro H. early "HA HB".
      iApply (H with "[HA]"); auto.
      iIntros (v) "HA". iApply "HB". iIntros "HB". iDestruct "HB" as "[HB HC]".
      iApply "HC". iApply "HA".
    Qed.

    Lemma ret_spec_complete {X} (Q : X -> iProp Σ) S (v : X) :
      (S -∗ Q v) ->
    |{{ S }}| ret v |{{ v', RET v'; Q v' }}|.
    Proof.
      intro. early "HA HB". iApply "HB". iDestruct (H with "HA") as "HA". iApply "HA".
    Qed.

    
    Lemma True_pre_l {X} H Φ' (e : mon X) :
    |{{ True ∗ H}}| e |{{ v, RET v; Φ' v }}| ->
    |{{ H }}| e |{{ v, RET v; Φ' v }}|.
    Proof.
      intro P. early "HA HB". 
      iApply (P with "[HA]"); auto.
    Qed.

    Lemma True_pre_r {X} H Φ' (e : mon X) :
    |{{ H ∗ True}}| e |{{ v, RET v; Φ' v }}| ->
    |{{ H }}| e |{{ v, RET v; Φ' v }}|.
    Proof.
      intro P. early "HA HB". 
      iApply (P with "[HA]"); auto.
    Qed.

  End proofmode_intro.

  Ltac tFrame_l := apply True_pre_r; apply frame_l; eauto.
  Ltac tFrame_r := apply True_pre_l; apply frame_r; eauto.
  
  Section proofmode_divers.
    Context `{!heapG Σ}.
    
    Lemma comm_post {X} R Φ' (e : mon X) H :
    |{{ H }}| e |{{ v, RET v; Φ' v ∗ R v }}| ->
    |{{ H }}| e |{{ v, RET v; R v ∗ Φ' v}}|.
    Proof.
      intro P. early "HA HB".
      iApply (P with "[HA]"); auto.
      iIntros (v) "HA". iApply "HB". iDestruct "HA" as "[HA HC]". iFrame.
    Qed.

    Lemma comm_pre {X} R Φ' (e : mon X) H :
    |{{ R ∗ H}}| e |{{ v, RET v; Φ' v }}| ->
    |{{ H ∗ R}}| e |{{ v, RET v; Φ' v}}|.
    Proof.
      intro P. early "HA HB".
      iApply (P with "[HA]"); auto.
      iDestruct "HA" as "[HA HC]". iFrame.
    Qed.

    Lemma impl_post_id {X} R P Φ' (e : mon X) :
    |{{ R }}| e |{{ v, RET v; Φ' v }}| ->
    |{{ R }}| e |{{ v, RET v; P -∗ P ∗ Φ' v}}|.
    Proof.
      intro H. early "HA HB".
      iApply (H with "[HA]"); auto.
      iIntros (v) "HA". iApply "HB". iIntros "HB". iFrame.
    Qed.

    Lemma impl_post {X} R P Φ' (e : mon X) :
    |{{ R }}| e |{{ v, RET v; Φ' v }}| ->
    |{{ R }}| e |{{ v, RET v; P -∗ Φ' v}}|.
    Proof.
      intro H. early "HA HB".
      iApply (H with "[HA]"); auto.
      iIntros (v) "HA". iApply "HB". eauto.
    Qed.

    Lemma star_assoc_post {X} R Q S T (e : mon X) :
    |{{ T }}| e |{{ v, RET v; R v ∗ (Q v ∗ S v)}}| <->
    |{{ T }}| e |{{ v, RET v; (R v ∗ Q v) ∗ S v }}|.
    Proof.
      split; intro H; early "HA HB";
        iApply (H with "[HA]"); try (iApply "HA");
          iIntros (v) "HA"; iApply "HB".
      - iDestruct "HA" as "[HA [HB HC]]". iFrame.
      - iDestruct "HA" as "[[HA HB] HC]". iFrame.
    Qed.

    Lemma star_assoc_pre {X} R Q S T (e : mon X) :
    |{{ (T ∗ R) ∗ S }}| e |{{ v, RET v; Q v }}| <->
    |{{ T ∗ (R ∗ S) }}| e |{{ v, RET v; Q v }}|.
    Proof.
      split; intro H; early "HA HB"; iApply (H with "[HA]"); eauto.
      - iDestruct "HA" as "[HA [HB HC]]". iFrame.
      - iDestruct "HA" as "[[HA HB] HC]". iFrame.
    Qed.

    Lemma impl_true_pre {X} (R : X -> iProp Σ) Q (e : mon X) :
    |{{ Q }}| e |{{ v', RET v'; R v'}}| ->
    |{{ True -∗ Q }}| e |{{ v', RET v'; R v'}}|.
    Proof.
      intro H. early "HA HB". iApply (H with "[HA]"); eauto. iApply "HA"; auto.
    Qed.

    Lemma impl_true_post {X} (R : X -> iProp Σ) Q (e : mon X) :
    |{{ Q }}| e |{{ v', RET v'; R v'}}| ->
    |{{ Q }}| e |{{ v', RET v'; True -∗ R v'}}|.
    Proof.
      intro H. early "HA HB". iApply (H with "[HA]"); eauto.
      iIntros (v') "HA". iApply "HB". auto.
    Qed.

    Lemma exist {X Y} v (R : Y -> X -> iProp Σ) Q (e : mon X) :
    |{{ Q }}| e |{{ v', RET v'; R v v'}}| ->
    |{{ Q }}| e |{{ v', RET v'; ∃ t, R t v'}}|.
    Proof.
      intro H. early "HA HB".
      iApply (H with "[HA]"); auto.
      iIntros (v0) "HC". iApply "HB". iExists v. iFrame.
    Qed.

    Lemma exists_frame_r {X Y} v (Q : Y -> iProp Σ) R (e : mon X) :
    |{{ True }}| e |{{ v', RET v'; R v v' }}| ->
    |{{ Q v }}| e |{{ v', RET v'; ∃ t, R t v' ∗ Q t}}|.
    Proof.
      intro.
      iApply (exist v). tFrame_r.
    Qed.

    Lemma exists_frame_l {X Y} v (Q : Y -> iProp Σ) R (e : mon X) :
    |{{ True }}| e |{{ v', RET v'; R v v'}}| ->
    |{{ Q v }}| e |{{ v', RET v'; ∃ t, Q t ∗ R t v'}}|.
    Proof.
      intro.
      iApply (exist v).
      tFrame_l.
    Qed.

    Lemma exists_out_l {X Y} (Q : iProp Σ) (R : Y -> X -> iProp Σ) S (e : mon X) :
    |{{ S }}| e |{{ v', RET v'; Q ∗ ∃ t, R t v' }}| ->
    |{{ S }}| e |{{ v', RET v'; ∃ t, Q ∗ R t v'}}|.
    Proof.
      intro H. early "HA HB".
      iApply (H with "[HA]"); auto.
      iIntros (v) "HA". iApply "HB". iDestruct "HA" as "[HA HB]". iDestruct "HB" as (t) "HB".
      iExists t. iFrame.
    Qed.

    Lemma exists_out_r {X Y} (Q : iProp Σ) (R : Y -> X -> iProp Σ) S (e : mon X) :
    |{{ S }}| e |{{ v', RET v'; (∃ t, R t v') ∗ Q }}| ->
    |{{ S }}| e |{{ v', RET v'; ∃ t, R t v' ∗ Q }}|.
    Proof.
      intro H. early "HA HB".
      iApply (H with "[HA]"); auto.
      iIntros (v) "HA". iApply "HB". iDestruct "HA" as "[HA HB]". iDestruct "HA" as (t) "HA".
      iExists t. iFrame.
    Qed.

    Lemma ret_frame_l {X Y} (R : Y -> iProp Σ) (R' Φ' : X -> iProp Σ) (v' : X) (v'': Y) : 
      Φ' v' -> R v'' = R' v' ->
    |{{ R v'' }}| ret v' |{{ v, RET v; R' v ∗ Φ' v }}|.
    Proof.
      intros H H'. early "HA HB".
      iApply mwp_value'. iApply "HB". rewrite H'. iFrame. iApply H.
    Qed.

    Lemma ret_frame_r {X Y} (R : Y -> iProp Σ) (R' Φ' : X -> iProp Σ) (v' : X) (v'' : Y): 
      Φ' v' -> R v'' = R' v' ->
    |{{ R v'' }}| ret v' |{{ v, RET v; Φ' v ∗ R' v }}|.
    Proof.
      intros H H'. early "HA HB".
      iApply mwp_value'. iApply "HB". rewrite H'. iFrame. iApply H.
    Qed.

  End proofmode_divers.
  
End proofmode.

