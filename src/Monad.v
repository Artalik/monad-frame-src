From iris.algebra Require Import gmap.
Require Import FunctionalExtensionality.
From stdpp Require Import binders strings.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import wsat.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Export  adequacy.

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

(* Module weakestpre. *)
(*   Export monad. *)


(*   Class Mwp {X} (Λ : monad) (PROP : Type) := *)
(*     mwp : ((M Λ) X) → (X → PROP) → PROP. *)
(*   Instance: Params (@Mwp) 7 := {}. *)

(*   Notation "'WP' e |{ Φ } |" := (mwp e Φ) *)
(*                                       (at level 20, e, Φ at level 200, only parsing) : bi_scope. *)
(*   Notation "'WP' e |{ v , Q } |" := (mwp e (λ v, Q)) *)
(*   (at level 20, e, Q at level 200, *)
(*    format "'[' 'WP'  e  '[ ' |{  v ,  Q  } | ']' ']'") : bi_scope. *)

(*   Notation "'|{{' P } } | e |{{ x .. y , 'RET' pat ; Q } } |" := *)
(*     ( □ ∀ Φ, *)
(*        P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e |{ Φ }|)%I *)
(*          (at level 20, x closed binder, y closed binder, *)
(*           format "'[hv' |{{  P  } } |  '/  ' e  '/'  |{{  x  ..  y ,  RET  pat ;  Q  } } | ']'") : bi_scope. *)

(* End weakestpre. *)

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

  (* err permet la transition vers transl_function 
     
  Definition transl_function (f: Csyntax.function) : res function :=
    let (s, e) := run (transl_stmt f.(Csyntax.fn_body)) empty in
    match e with
    | Erro msg =>
      Error msg
    | Res v  =>
      OK (mkfunction
          f.(Csyntax.fn_return)
          f.(Csyntax.fn_callconv)
          f.(Csyntax.fn_params)
          f.(Csyntax.fn_vars)
          (elements s)
          v)
     end. 

  Voila, l'idée
   *)
  

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
  Open Scope positive_scope.

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
        heapG_gen_heapG :> gen_heapG ident type Σ;
      }.
  
  Class irisG (Σ : gFunctors) :=
    IrisG {
        state_interp : state → iProp Σ;
      }.
  Global Opaque iris_invG.
  
  Instance heapG_irisG `{!heapG Σ} : irisG Σ := {
                                                 state_interp σ := gen_heap_ctx σ%I;
                                               }.
  
  Section mwp.
    Context `{!heapG Σ}.
    Fixpoint mwp {X} (e1 : mon X) (Q : X -> iProp Σ) : iProp Σ :=
      match e1 with
      | ret v => Q v
      | op (Err e) => True
      | op (Gensym t f) =>
        ∀ l, l ↦ t -∗ mwp (f l) Q
      end%I.    
  End mwp.

  Notation "'WP' e |{ Φ } |" := (mwp e Φ)
                                  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  
  Notation "'WP' e |{ v , Q } |" := (mwp e (λ v, Q))
                                      (at level 20, e, Q at level 200,
                                       format "'[' 'WP'  e  '[ ' |{  v ,  Q  } | ']' ']'") : bi_scope.
  
  Notation "'|{{' P } } | e |{{ x .. y , 'RET' pat ; Q } } |" :=
    ( ∀ Φ,
        P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e |{ Φ }|)%I
                                                             (at level 20, x closed binder, y closed binder,
                                                              format "'[hv' |{{  P  } } |  '/  ' e  '/'  |{{  x  ..  y ,  RET  pat ;  Q  } } | ']'") : bi_scope.

    
    Class heapPreG Σ :=
      HeapPreG {
          heap_preG_heap :> gen_heapPreG ident type Σ
        }.

    Definition heapΣ : gFunctors := #[gen_heapΣ ident type].
    Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
    Proof. solve_inG. Qed.

    Definition adequate `{heapG Σ} {X} (e : mon X) (σ1 : state) (φ : X → state → iProp Σ) :=
      (match run e σ1 with
       | Res (σ2,v) => φ v σ2
       | Erro e => True
      end)%I.

    
    
    Open Scope bi_scope.

    Lemma adequate_step {X} `{heapG Σ} σ φ t m :
      adequate (op (Gensym t m)) σ (λ (v : X) (_ : state), φ v) ∗-∗
               adequate (m (fresh σ)) (<[ fresh σ := t ]>σ) (λ (v : X) (_ : state), φ v).
    Proof. iSplit; eauto. Qed.

    Print gmap.alloc_updateP'.

    Lemma disjointeness_fresh `{heapG Σ} : forall (σ : gmap ident type), σ !! (fresh σ) = None.
    Proof.
      epose fupd_mask_weaken.
    Admitted.

    (* Lemma soundness `{!heapPreG heapΣ} {X} P Q : forall (e : mon X) σ, *)
    (*   (state_interp σ -∗ *)
    (*   |{{ P }}| e |{{ v, RET v; Q v }}|) -> *)
    (*   adequate e σ (fun v _ => Q v). *)
    (* Proof. *)
    (*   fix e 1. *)
    (*   destruct e0; simpl; intros. *)
    (*   * unfold adequate. simpl. *)
    (*     iMod (gen_heap_init σ) as (?) "Hh". *)
    
    (* Lemma gen_heap_alloc σ l v : *)
    (*   σ !! l = None → *)
    (*   gen_heap_ctx σ -∗ gen_heap_ctx (<[l:=v]>σ) ∗ l ↦ v ∗ meta_token l ⊤. *)
    (* Proof. *)
    (*   iIntros (P) "HA". *)
    (*   rewrite /gen_heap_ctx mapsto_eq /mapsto_def meta_token_eq /meta_token_def /=. *)
    (*   iDestruct "HA" as  (m) "HA". *)
    (*   iDestruct "HA" as "[HA [HB HC]]". *)
    (*   iSplitL "HA HB". *)
    (*   * iExists (<[l:=v]>m). *)
    (*     rewrite to_gen_heap_insert. *)
    (*     iSplit. *)
    (*     ** *)
    (*       epose (not_elem_of_dom (D:=gset ident)). *)
    (*       admit. *)
    (*     **  *)

    Lemma wp_adequacy {X} `{heapG Σ} (e : mon X) σ (φ : X -> iProp Σ) :
      ((|==> state_interp σ ∗ WP e |{ v, φ v }|) ->
                                          |==> adequate e σ (λ v _, φ v) )%I.
    Proof.
      revert e σ. fix e 1.
      destruct e0.
      iStartProof.
      - iIntros (x0 HA).
        iPoseProof HA as "HA". iMod "HA" as "HA". iDestruct "HA" as "[HA HB]". iApply "HB".
      - iIntros (σ HA).
        destruct s.
        + unfold adequate. simpl. iStartProof. trivial.
        + iApply adequate_step. iApply e.
          iPoseProof HA as "HA".
          iMod "HA" as "HA".
          iDestruct "HA" as "[HA HB]".
          simpl. pose disjointeness_fresh. apply (gen_heap_alloc σ _ t)  in e0.
          iPoseProof e0 as "HC".
          iDestruct ("HC" with "HA") as "HE".
          iMod "HE" as "HE".
          iModIntro.
          iDestruct "HE" as "[HA [HD HE]]".
          iFrame. iApply "HB". iFrame.
    Qed.

    Import uPred.    

    Lemma test `{!heapG Σ} t t' : forall σ l,
        σ !! l = None ->
            state_interp σ -∗  state_interp (<[l:=t]> σ) ∗ l ↦ t'.
    Proof.
      iIntros (σ l P) "HA". unfold state_interp. simpl.
      rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
      epose own_valid_2.
      epose gen_heap_singleton_included.
      epose auth.auth_both_valid.
      epose to_gen_heap_insert.
      epose sep_assoc'.
      iSplitL. 
      - iExists m.
        + iSplitL "HA".
          * iDestruct "HA" as "%". iPureIntro. apply dom_insert_subseteq_compat_l. apply H.
          * iSplitL "HB".
            -- 
                
      
    Lemma next_step `{!heapG Σ} {X} P Q t : forall m σ,
    state_interp σ ∗ |{{ P }}| op (Gensym t m)  |{{ (v : X), RET v; Q v }}|
    ∗-∗  state_interp (<[fresh σ:=t]> σ) ∗ |{{ P }}| m (fresh σ)  |{{ (v : X), RET v; Q v }}|.
    Proof.
      iIntros (m σ).
      iSplit.
      * iIntros "HA". iDestruct "HA" as "[HA HB]".

        
                         
        

    
    Lemma soundness `{!heapG Σ} {X} P Q (e : mon X) σ:
      (state_interp σ ∗
      |{{ P }}| e |{{ v, RET v; Q v }}|) ->
      match run e σ with
      | Erro _ => True
      | Res (σ',x) => P -> Q x
      end.
    Proof.
      revert e σ. fix e 1.
      destruct e0; intros.
      - intro. iPoseProof H as "HA". iDestruct "HA" as "[HA HB]".
        iApply "HB".        
        + iApply H0.
        + eauto.
      - destruct s.
        + simpl. trivial.
        + simpl. apply e.

          


          epose (gen_heap_init σ).
      
    
    Section mwp.
      Context `{!heapG heapΣ}.
      Fixpoint mwp {X} (e1 : mon X) (Q : X -> iProp heapΣ) : iProp heapΣ :=
        match e1 with
        | ret v => Q v
        | op (Err e) => True
        | op (Gensym t f) =>
          ∀ l, l ↦ t -∗ mwp (f l) Q
        end%I.

    End mwp.

    Notation "'WP' e |{ Φ } |" := (mwp e Φ)
                                    (at level 20, e, Φ at level 200, only parsing) : bi_scope.

    Notation "'WP' e |{ v , Q } |" := (mwp e (λ v, Q))
                                        (at level 20, e, Q at level 200,
                                         format "'[' 'WP'  e  '[ ' |{  v ,  Q  } | ']' ']'") : bi_scope.

    Notation "'|{{' P } } | e |{{ x .. y , 'RET' pat ; Q } } |" :=
      ( ∀ Φ,
          P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e |{ Φ }|)%I
                                                               (at level 20, x closed binder, y closed binder,
                                                                format "'[hv' |{{  P  } } |  '/  ' e  '/'  |{{  x  ..  y ,  RET  pat ;  Q  } } | ']'") : bi_scope.
    Open Scope bi_scope.
    Print ucmraT. Print iResUR. Print gFunctors. Print fin. Locate Fin. Print Fin.
    Lemma test `{!heapG heapΣ} {X} P Q (e : mon X) :
      (state_interp empty_state -∗ |{{ P }}| e |{{ v, RET v; Q v }}|) ->
    |{{ P }}| e |{{ v, RET v; Q v }}|.
    Proof. Print heapG. Locate heapG.
    Admitted.

    Lemma soundness `{!heapG heapΣ} {X} P Q (e : mon X) σ:
      (state_interp σ -∗
      |{{ P }}| e |{{ v, RET v; Q v }}|) ->
      match run e σ with
      | Erro _ => True
      | Res (σ',x) => P -> Q x
      end.
    Proof.
      revert e σ. fix e 1. destruct e0.
      - intros. simpl. intro. iApply H.
        + unfold gen_heap_ctx. iExists empty. iSplit.
          * iPureIntro. Print subseteq_dom.
            epose (@subseteq_dom _ _ (gset ident) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∅ σ).
            apply s.
            apply map_subseteq_spec.
            intros. erewrite lookup_empty in H1. inversion H1.
          *  admit.
        + iApply H0.
        + iIntros (v) "HA".
          iApply "HA".
      - intros. simpl. destruct s; eauto.
        apply e. iIntros "HA".
        iIntros. Print erased_step.




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
              { simpl. iIntros (l) "HC". iDestruct ("HA" with "HC") as "HA".
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
              { simpl. iIntros (l) "HC". iDestruct ("HA" with "HC") as "HA".
                iPoseProof "HB" as "HB". apply e. }}
          Qed.

          Open Scope bi_scope.
          Lemma mwp_gensym t : WP gensym t |{ l, l ↦ t }|.
          Proof. simpl. iIntros. iFrame. Qed.

          Lemma mwp_frame_l {X} (e : mon X) Φ R : R ∗ WP e |{ Φ }| ⊢ WP e |{ v, R ∗ Φ v }|.
          Proof. iIntros "[? H]". iApply (mwp_mono with "H"). auto with iFrame. Qed.
          Lemma mwp_frame_r {X} (e : mon X) Φ R : WP e |{ Φ }| ∗ R ⊢ WP e |{ v, Φ v ∗ R }|.
          Proof. iIntros "[H ?]". iApply (mwp_mono with "H"); auto with iFrame. Qed.



        End mwp_proof.

        Open Scope bi_scope.


        Lemma soundness `{!heapG Σ} {X} P Q (e : mon X) :
        |{{ P }}| e |{{ v, RET v; Q v }}| ->
                                          (forall n (s : state), P n s -> Q (run e s)).


End weakestpre_gensym.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.

Module proofmode.
  Export weakestpre_gensym.
  Open Scope bi_scope.
  Ltac early S := iIntros (Φ) S.
  Section proofmode_intro.
    Context `{!heapG Σ}.    
    
    Lemma gensym_spec t :
    |{{ True }}| gensym t |{{ l, RET l; l ↦ t }}|.
    Proof. iIntros (l) "HA HB". iApply "HB". Qed.
    
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

    Lemma run_spec {X} : forall (e : mon X) (Φ : X -> iProp Σ) (p : state * X) (s : state),
        run e s = Res p ->
    |{{ True }}| e |{{ v, RET v; Φ v }}| -> Φ p.2.
    Proof.
      fix e 1.
      destruct e0; intros.
      - apply ret_spec_bis in H0. inversion H. apply H0.
      - destruct s.
        + inversion H.
        + simpl in H. pose (e _ Φ _ _ H). apply u. simpl in H0. pose (heapG Σ). Print heapG.
          pose (heapG_gen_heapG (heapG Σ)).
          
          Print gFunctors. Print rFunctor. Print heapG.
          
          
          applye in H.
          unfold mwp in H0. iApply H0. simpl in H0. iApply H0.
    Qed.        
  End proofmode_divers.
  
End proofmode.


(* (* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%Old%%%%%%%%%%%%%%%%%%% *) *)

(* Module gensym. *)
(*   Import monad. *)
(*   Open Scope positive_scope. *)

(*   Definition ident := positive. *)
(*   Definition state := gmap ident type. *)

(*   Inductive FreshMonad (X : Type) : Type := *)
(*   | ret : X -> FreshMonad X *)
(*   | Gensym: (ident -> FreshMonad X) -> FreshMonad X. *)

(*   Arguments ret {_} x. *)
(*   Arguments Gensym {_} f. *)

(*   Fixpoint bind {X Y} (m: FreshMonad X) (k: X -> FreshMonad Y) : FreshMonad Y := *)
(*     match m with *)
(*     | ret x => k x *)
(*     | Gensym f => Gensym (fun x => bind (f x) k) *)
(*     end. *)

(*   Definition gensym := Gensym ret. *)

(*   Definition fresh (s : state) := map_fold (fun x _ res => Pos.max res (x+1)) 1 s. *)

(*   Fixpoint run {X} (m : FreshMonad X) : state -> state * X := *)
(*     match m with *)
(*     | ret v => fun s => (s,v) *)
(*     | Gensym f => *)
(*       fun s => *)
(*         let l := fresh s in *)
(*         run (f l) ({[l := Tvoid]} ∪ s) *)
(*     end. *)

(*   Lemma lid : forall X Y (a : X) (f : X -> FreshMonad Y), bind (ret a) f = f a. *)
(*   Proof. auto. Qed. *)

(*   Lemma rid : forall X (m : FreshMonad X), bind m ret = m. *)
(*   Proof. induction m; auto. simpl. f_equal. apply functional_extensionality. auto. Qed. *)

(*   Lemma ass_bind : forall X Y Z (m : FreshMonad X) f (g : Y -> FreshMonad Z), *)
(*       bind (bind m f) g = bind m (fun x => bind (f x) g). *)
(*   Proof. induction m; auto. intros. simpl. f_equal. apply functional_extensionality. auto. Qed. *)

(*   Hint Resolve lid rid ass_bind. *)

(*   Instance mP : @MonadProp FreshMonad (@ret) (@bind). *)
(*   Proof. split; eauto. Qed. *)

(*   Canonical Structure gensym_monad := @Monad FreshMonad (gmap ident type) (@ret) (@bind) (@run) mP. *)

(* End gensym. *)


(* Module weakestpre_gensym. *)
(*   Export weakestpre. *)
(*   Export gensym. *)
(*   Export gen_heap. *)

(*   Class irisG (Σ : gFunctors) := *)
(*     IrisG { *)
(*         iris_invG :> invG.invG Σ; *)
(*         state_interp : state → iProp Σ; *)
(*       }. *)
(*   Global Opaque iris_invG. *)

(*   Class heapG Σ := *)
(*     HeapG { *)
(*         heapG_invG : invG.invG Σ; *)
(*         heapG_gen_heapG :> gen_heapG positive type Σ; *)
(*       }. *)

(*   Instance heapG_irisG `{!heapG Σ} : irisG Σ := { *)
(*                                                  iris_invG := heapG_invG; *)
(*                                                  state_interp σ := gen_heap_ctx σ%I; *)
(*                                                }. *)

(*   (** Override the notations so that scopes and coercions work out *) *)
(*   Notation "\s l" := (mapsto (L:=ident) (V:=type) l 1 Tvoid) *)
(*                        (at level 20, format "\s l") : bi_scope. *)
(*   Notation "\s l" := *)
(*     (mapsto (L:=ident) (V:=type) l 1 Tvoid) (at level 20) : bi_scope. *)

(*   Section mwp. *)
(*     Context {X : Type} `{!heapG Σ}. *)
(*     Implicit Types P : iProp Σ. *)
(*     Implicit Types Φ : X → iProp Σ. *)
(*     Implicit Types v : X. *)
(*     Implicit Types e : FreshMonad X. *)

(*     Fixpoint mwp `{!irisG Σ} (e1 : FreshMonad X) (Q : X -> iProp Σ) : iProp Σ := *)
(*       match e1 with *)
(*       | ret v => Q v *)
(*       | Gensym f => *)
(*         ∀ l, (\s l) -∗ mwp (f l) Q *)
(*       end%I. *)

(*     Global Instance mwp' `{!irisG Σ} : @Mwp X gensym_monad (iProp Σ) := mwp. *)
    
(*     Global Instance mwp_ne e n : *)
(*       Proper (pointwise_relation _ (dist n) ==> dist n) (mwp e). *)
(*     Proof. *)
(*       revert e. induction (lt_wf n) as [n _ IH]=> e P P' HP. *)
(*       induction e; simpl. *)
(*       * apply HP. *)
(*       * do 3 f_equiv. apply H. *)
(*     Qed. *)

(*     Global Instance mwp_proper e : *)
(*       Proper (pointwise_relation _ (≡) ==> (≡)) (mwp e). *)
(*     Proof. *)
(*         by intros Φ Φ' ?; apply equiv_dist=>n; apply mwp_ne=>v; apply equiv_dist. *)
(*     Qed. *)

(*     Lemma mwp_unfold e Φ : *)
(*       WP e |{ Φ }| ⊣⊢ mwp e Φ. *)
(*     Proof. auto. Qed. *)

(*     Lemma mwp_value' Φ v : Φ v ⊢ WP ret v |{ Φ }|. *)
(*     Proof. eauto. Qed. *)
(*     Lemma mwp_value_inv' Φ v : WP ret v |{ Φ }| -∗ Φ v. *)
(*     Proof. eauto. Qed. *)
  
(*     Lemma mwp_mono e Φ Ψ : *)
(*       WP e |{ Φ }| -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e |{ Ψ }|. *)
(*     Proof. *)
(*       iIntros "HA HB". rewrite !mwp_unfold. iInduction e as [|e] "IH". *)
(*       { iApply "HB". iApply "HA". } *)
(*       { simpl. iIntros (l) "HC". iDestruct ("HA" with "HC") as "HA". *)
(*         iApply ("IH" with "[HA] [HB]"); eauto. } *)
(*       Qed. *)
      
(*     Lemma mwp_bind e f Φ Φ' : *)
(*       WP e |{ Φ' }| -∗ (∀ v,  Φ' v -∗ WP (f v) |{ Φ }|) -∗ WP bind e f |{ Φ }|%I. *)
(*     Proof. *)
(*       iIntros "HA HB". rewrite !mwp_unfold. iInduction e as [|e] "IH". *)
(*       { iApply "HB". iApply "HA". } *)
(*       { simpl. iIntros (l) "HC". iDestruct ("HA" with "HC") as "HA". *)
(*         iApply ("IH" with "[HA] [HB]"); eauto. } *)
(*     Qed. *)

(*     Lemma mwp_frame_l e Φ R : R ∗ WP e |{ Φ }| ⊢ WP e |{ v, R ∗ Φ v }|. *)
(*     Proof. iIntros "[? H]". iApply (mwp_mono with "H"); auto with iFrame. Qed. *)
(*     Lemma mwp_frame_r e Φ R : WP e |{ Φ }| ∗ R ⊢ WP e |{ v, Φ v ∗ R }|. *)
(*     Proof. iIntros "[H ?]". iApply (mwp_mono with "H"); auto with iFrame. Qed. *)

(*   End mwp. *)
  

(* End weakestpre_gensym. *)

