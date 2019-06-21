Require Import FunctionalExtensionality.
From stdpp Require Import binders strings.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import wsat.
From iris.base_logic.lib Require Import gen_heap.
Require Import Ctypes.

Module monad.

  Section monad_rules.
    Context {state  : Type}.
    Context ( M : Type -> Type).
    Context ( ret : forall X, X -> M X).
    Context ( bind : forall X Y, M X -> (X -> M Y) -> M Y ).
    Arguments ret {_} x.
    Arguments bind {_ _} x f.
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
        (* run : forall X, M X -> state -> state * X; *)
        prop : MonadProp M ret bind
      }.
  
End monad.

Module weakestpre.
  Export monad.

  Class Mwp {X} (Λ : monad) (PROP : Type) :=
    mwp : ((M Λ) X) → (X → PROP) → PROP.
  Instance: Params (@Mwp) 7 := {}.

  Notation "'WP' e |{ Φ } |" := (mwp e Φ)
                                      (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WP' e |{ v , Q } |" := (mwp e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '[ ' |{  v ,  Q  } | ']' ']'") : bi_scope.

  Notation "'|{{' P } } | e |{{ x .. y , 'RET' pat ; Q } } |" :=
    ( □ ∀ Φ,
       P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e |{ Φ }|)%I
         (at level 20, x closed binder, y closed binder,
          format "'[hv' |{{  P  } } |  '/  ' e  '/'  |{{  x  ..  y ,  RET  pat ;  Q  } } | ']'") : bi_scope.

End weakestpre.

Module gensym.
  Import monad.
  Open Scope positive_scope.
  
  Definition ident := positive.
  Definition state := gmap ident type.
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

  Inductive err (X: Type) : Type :=
  | Erro : Errors.errmsg -> err X
  | Res : X -> err X.

  Arguments Erro [X].
  Arguments Res [X].

  Definition fresh (s : state) := map_fold (fun x _ res => Pos.max res (x+1)) 1 s.
  
  Fixpoint run {X} (m : mon X) : state -> state * err X :=
    match m with
    | ret v => fun s => (s, Res v)
    | op (Err e) => fun s => (s, Erro e)
    | op (Gensym t f) =>
        fun s =>
          let l := fresh s in
          run (f l) ({[l := t]} ∪ s)
    end.
  
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

  Canonical Structure gensym_monad := @Monad mon (gmap ident type) (@ret) (@bind) mP.
End gensym.

Module weakestpre_gensym.
  Export weakestpre.
  Export gensym.
  Export gen_heap.
   
  Class irisG (Σ : gFunctors) :=
    IrisG {
        iris_invG :> invG.invG Σ;
        state_interp : state → iProp Σ;
      }.
  Global Opaque iris_invG.
  
  Class heapG Σ :=
    HeapG {
        heapG_invG : invG.invG Σ;
        heapG_gen_heapG :> gen_heapG positive type Σ;
      }.
  
  Instance heapG_irisG `{!heapG Σ} : irisG Σ := {
                                                 iris_invG := heapG_invG;
                                                 state_interp σ := gen_heap_ctx σ%I;
                                               }.

  (** Override the notations so that scopes and coercions work out *)
  Notation "l ↦ t" :=
    (mapsto (L:=ident) (V:=type) l 1 t) (at level 20) : bi_scope.

  Notation "\s l" :=
    (∃ t, l ↦ t)%I (at level 20) : bi_scope.
  
  Section mwp.
    Context {X : Type} `{!heapG Σ}.
    Implicit Types P : iProp Σ.
    Implicit Types Φ : X → iProp Σ.
    Implicit Types v : X.
    Implicit Types e : mon X.
    
    Fixpoint mwp `{!irisG Σ} (e1 : mon X) (Q : X -> iProp Σ) : iProp Σ :=
      match e1 with
      | ret v => Q v
      | op (Err e) => False
      | op (Gensym t f) =>
        ∀ l, l ↦ t -∗ mwp (f l) Q
      end%I.

    Global Instance mwp' `{!irisG Σ} : @Mwp X gensym_monad (iProp Σ) := mwp.
    
    Global Instance mwp_ne e n :
      Proper (pointwise_relation _ (dist n) ==> dist n) (mwp e).
    Proof.
      revert e. induction (lt_wf n) as [n _ IH]=> e P P' HP.
      revert e. fix e 1.
      destruct e0.
      * apply HP.
      * destruct s.
        ** simpl. auto.
        ** simpl. do 3 f_equiv. apply e. 
    Qed.

    Global Instance mwp_proper e :
      Proper (pointwise_relation _ (≡) ==> (≡)) (mwp e).
    Proof.
        by intros Φ Φ' ?; apply equiv_dist=>n; apply mwp_ne=>v; apply equiv_dist.
    Qed.

    Lemma mwp_unfold e Φ :
      WP e |{ Φ }| ⊣⊢ mwp e Φ.
    Proof. auto. Qed.

    Lemma mwp_value' Φ v : Φ v ⊢ WP ret v |{ Φ }|.
    Proof. eauto. Qed.
    Lemma mwp_value_inv' Φ v : WP ret v |{ Φ }| -∗ Φ v.
    Proof. eauto. Qed.
  
    Lemma mwp_mono e Φ Ψ :
      WP e |{ Φ }| -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e |{ Ψ }|.
    Proof.
      iIntros "HA HB". rewrite !mwp_unfold. revert e. fix e 1.
      destruct e0.
      { iApply "HB". iApply "HA". }
      { destruct s.
        { simpl. auto. }
        { simpl. iIntros (l) "HC". iDestruct ("HA" with "HC") as "HA".
          iPoseProof "HB" as "HB". apply e. }}
    Qed.
      
    Lemma mwp_bind e f Φ Φ' :
      WP e |{ Φ' }| -∗ (∀ v,  Φ' v -∗ WP (f v) |{ Φ }|) -∗ WP bind e f |{ Φ }|%I.
    Proof.
      iIntros "HA HB". rewrite !mwp_unfold. revert e. fix e 1.
      destruct e0.
      { iApply "HB". iApply "HA". }
      { destruct s.
        { simpl. auto. }
        { simpl. iIntros (l) "HC". iDestruct ("HA" with "HC") as "HA".
          iPoseProof "HB" as "HB". apply e. }}
    Qed.

    Lemma mwp_frame_l e Φ R : R ∗ WP e |{ Φ }| ⊢ WP e |{ v, R ∗ Φ v }|.
    Proof. iIntros "[? H]". iApply (mwp_mono with "H"); auto with iFrame. Qed.
    Lemma mwp_frame_r e Φ R : WP e |{ Φ }| ∗ R ⊢ WP e |{ v, Φ v ∗ R }|.
    Proof. iIntros "[H ?]". iApply (mwp_mono with "H"); auto with iFrame. Qed.

  End mwp.
  
End weakestpre_gensym.




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
