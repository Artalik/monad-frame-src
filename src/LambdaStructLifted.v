(**

This file formalizes basic examples from standard Separation Logic, 
as described in Arthur Charguéraud's lecture notes.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
Require Export LambdaStruct LambdaCFLifted.
Open Scope trm_scope.
Open Scope charac.
Generalizable Variables A.

Ltac auto_star ::= jauto.



(* ********************************************************************** *)
(* ################################################################# *)
(* * Derived basic functions, useful for metaprogramming *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Rewriting lemmas for [Subst] *)

Lemma Subst_seq : forall x V t1 t2,
  Subst x V (trm_seq t1 t2) = trm_seq (Subst x V t1) (Subst x V t2).
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Rewriting lemmas for [Substs] *)

Lemma Substs_cons : forall x xs V Vs t,
  Substs (x::xs) (V::Vs) t = Substs xs Vs (Subst x V t).
Proof using. auto. Qed.

Lemma Substs_val : forall xs Vs (v:val),
  length Vs = length xs ->
  Substs xs Vs v = v.
Proof using.
  unfold Substs. intros xs. induction xs as [|x xs']; introv E. { auto. }
  destruct Vs as [|V Vs']; rew_list in *. { false. }
  (* todo: induction principle on two lists of the same length *)
  simpl. rewrite~ IHxs'.
Qed.

Lemma Substs_var_neq : forall xs (Vs:dyns) x,
  var_fresh x xs ->
  length Vs = length xs ->
  Substs xs Vs (trm_var x) = trm_var x.
Proof using.
  intros xs. unfold Substs. induction xs as [|x xs']. { auto. }
  introv HF EL. destruct Vs as [|V Vs']; rew_list in *. { false. }
  (* todo: induction principle on two lists of the same length *)
  simpls. case_if in HF. case_if. rewrite~ IHxs'.
Qed.

Lemma Substs_seq : forall xs Vs t1 t2,
  length xs = length Vs ->
  Substs xs Vs (trm_seq t1 t2) = trm_seq (Substs xs Vs t1) (Substs xs Vs t2).
Proof using.
  intros xs. induction xs as [|x xs']; introv E.
  { auto. }
  { destruct Vs as [|V Vs']. { rew_list in E. false. }
    do 3 rewrite Substs_cons. rewrite Subst_seq.
    rew_list in E. rewrite~ IHxs'. }
Qed.

Lemma Substs_let : forall xs (Vs:dyns) x t1 t2,
  var_fresh x xs ->
  length Vs = length xs ->
  Substs xs Vs (trm_let x t1 t2) = trm_let x (Substs xs Vs t1) (Substs xs Vs t2).
Proof using.
  intros xs. unfold Substs. induction xs as [|x xs']. { auto. }
  introv HF EL. destruct Vs as [|V Vs']; rew_list in *. { false. }
  (* todo: induction principle on two lists of the same length *)
  simpls. case_if in HF. case_if. rewrite~ IHxs'.
Qed.

Lemma Substs_app : forall xs (Vs:dyns) t1 t2,
  length Vs = length xs ->
  Substs xs Vs (trm_app t1 t2) = trm_app (Substs xs Vs t1) (Substs xs Vs t2).
Proof using.
  intros xs. unfold Substs. induction xs as [|x xs']. { auto. }
  introv EL. destruct Vs as [|V Vs']; rew_list in *. { false. }
  (* todo: induction principle on two lists of the same length *)
  simpls. rewrite~ IHxs'.
Qed.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Derived basic functions *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Increment *)

Lemma Rule_incr : forall (p:loc) (n:int), 
  Triple (val_incr `p)
    PRE (p ~~> n) 
    POST (fun (r:unit) => p ~~> (n+1)).
Proof using.
  xcf. xapps. xapps. xapps. hsimpl~.
Qed. 

Hint Extern 1 (Register_Spec val_incr) => Provide Rule_incr.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Negation *)

Lemma Rule_not : forall (b:bool), 
  Triple (val_not b)
    PRE \[] 
    POST (fun b' => \[b' = !b]).
Proof using.
  intros. unfold Triple, Post. xapply rule_not. (*todo: xapplys bug *)
  hsimpl. hpull. intros. subst. hsimpl~ (!b).
Qed.

Hint Extern 1 (Register_Spec val_not) => Provide Rule_not.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Disequality *)

Lemma Rule_neq : forall `{EA:Enc A} (v1 v2:A), 
  Enc_injective EA ->
  Triple (val_neq `v1 `v2)
    PRE \[] 
    POST (fun (b:bool) => \[b = isTrue (v1 <> v2)]).
Proof using. 
  intros. xcf.
  xapps~. (* Details: xlet. xapp~.xpull ;=> X E. subst. *)
  xapps. isubst. hsimpl. rew_isTrue~.
Qed.

Hint Extern 1 (Register_Spec val_neq) => Provide Rule_neq.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Lifted records *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Record representation *)

(** Representation predicate [r ~> Record L], where [L]
    is an association list from fields to values. *)

Definition Record_field : Type := field * dyn.
Definition Record_fields : Type := list Record_field.

Fixpoint Record (L:Record_fields) (r:loc) : hprop :=
  match L with
  | nil => \[]
  | (f, Dyn V)::L' => (r `.` f ~~> V) \* (r ~> Record L')
  end. 

(* TODO: currently restricted due to [r `.` f ~> V] not ensuring [r<>null] *)
Lemma hRecord_not_null : forall (r:loc) (L:Record_fields),
  (* L <> nil -> *)
  mem (0%nat:field) (List.map fst L) ->
  (r ~> Record L) ==> (r ~> Record L) \* \[r <> null].
Proof using.
  introv M. induction L as [|(f,[A EA v]) L'].
  { inverts M. }
  { xunfold Record. inverts M.
    { hchange~ (Hfield_not_null r). hsimpl~. }
    { hchange~ IHL'. hsimpl~. } }
Qed.

(** Lemmas for unfolding the definition *)

Lemma Record_nil : forall p,
  p ~> Record nil = \[].
Proof using. auto. Qed.

Lemma Record_cons : forall p x (V:dyn) L,
  (p ~> Record ((x, V)::L)) =
  (p`.`x ~~> (`V) \* p ~> Record L).
Proof using. intros. destruct~ V. Qed.

Lemma Record_not_null : forall (r:loc) (L:Record_fields),
  L <> nil ->
  (r ~> Record L) ==+> \[r <> null].
Proof using.
  intros. destruct L as [|(f,v) L']. { false. } 
  rewrite Record_cons. hchanges~ Hfield_not_null.
Qed.


(** Notation for record contents (only supported up to arity 5) *)

Notation "`{ f1 := x1 }" := 
  ((f1, Dyn x1)::nil)
  (at level 0, f1 at level 0) 
  : fields_scope.
Notation "`{ f1 := x1 ; f2 := x2 }" :=
  ((f1, Dyn x1)::(f2, Dyn x2)::nil)
  (at level 0, f1 at level 0, f2 at level 0) 
  : fields_scope.
Notation "`{ f1 := x1 ; f2 := x2 ; f3 := x3 }" :=
  ((f1, Dyn x1)::(f2, Dyn x2)::(f3, Dyn x3)::nil)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0) 
  : fields_scope.
Notation "`{ f1 := x1 ; f2 := x2 ; f3 := x3 ; f4 := x4 }" :=
  ((f1, Dyn x1)::(f2, Dyn x2)::(f3, Dyn x3)::(f4, Dyn x4)::nil)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0)
  : fields_scope.
Notation "`{ f1 := x1 ; f2 := x2 ; f3 := x3 ; f4 := x4 ; f5 := x5 }" :=
  ((f1, Dyn x1)::(f2, Dyn x2)::(f3, Dyn x3)::(f4, Dyn x4)::(f5, Dyn x5)::nil)
  (at level 0, f1 at level 0, f2 at level 0, f3 at level 0, f4 at level 0, f5 at level 0)
  : fields_scope.

Open Scope fields_scope.
Bind Scope fields_scope with Record_fields.
Delimit Scope fields_scope with fields.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Derived small-footprint lifted specifications for records *)

Section Rule_fields.
Transparent Hfield.

Lemma Rule_get_field : forall (l:loc) f `{EA:Enc A} (V:A),
  Triple ((val_get_field f) l)
    PRE (l `.` f ~~> V) 
    POST (fun r => \[r = V] \* (l `.` f ~~> V)).
Proof using. 
  intros. unfold Triple, Post. rewrite Hfield_to_hfield. xapplys~ rule_get_field.
Qed.

Lemma Rule_set_field : forall `{EA1:Enc A1} (V1:A1) (l:loc) f `{EA2:Enc A2} (V2:A2),
  Triple ((val_set_field f) l `V2)
    PRE (l `.` f ~~> V1) 
    POST (fun (r:unit) => l `.` f ~~> V2).
Proof using. 
  intros. unfold Triple, Post. rewrite Hfield_to_hfield. xapply~ rule_set_field.
  hsimpl. hsimpl~ tt.
Qed.

End Rule_fields.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Derived large-footprint lifted specifications for records *)

Definition field_eq_dec := Nat.eq_dec.

Fixpoint record_get_compute_dyn (f:field) (L:Record_fields) : option dyn :=
  match L with
  | nil => None
  | (f',d')::T' => 
     if field_eq_dec f f' 
       then Some d' 
       else record_get_compute_dyn f T'
  end.

Definition record_get_compute_spec (f:field) (L:Record_fields) : option Prop :=
  match record_get_compute_dyn f L with
  | None => None 
  | Some (Dyn V) => Some (forall r,
     Triple (val_get_field f `r) (r ~> Record L) (fun x => \[x = V] \* r ~> Record L))
  end.

Lemma record_get_compute_spec_correct : forall (f:field) L (P:Prop),
  record_get_compute_spec f L = Some P -> 
  P.
Proof using.
  introv M. unfolds record_get_compute_spec. 
  sets_eq <- vo E: (record_get_compute_dyn f L).
  destruct vo as [[T ET v]|]; inverts M. intros r.
  induction L as [|[F D] L']; [false|].
  destruct D as [A EA V]. simpl in E.
  xunfold Record at 1. xunfold Record at 2. case_if. (*--todo fix subst *)
  { subst. inverts E. xapplys~ Rule_get_field. }
  { specializes IHL' (rm E). xapplys~ IHL'. }
Qed.

Fixpoint record_set_compute_dyn (f:nat) (d:dyn) (L:Record_fields) : option Record_fields :=
  match L with
  | nil => None
  | (f',d')::T' => 
     if field_eq_dec f f' 
       then Some ((f,d)::T') 
       else match record_set_compute_dyn f d T' with
            | None => None
            | Some L' => Some ((f',d')::L')
            end
  end.

Definition record_set_compute_spec (f:field) `{EA:Enc A} (W:A) (L:Record_fields) : option Prop :=
  match record_set_compute_dyn f (Dyn W) L with
  | None => None 
  | Some L' => Some (forall r,
     Triple (val_set_field f `r `W) (r ~> Record L) (fun (_:unit) => r ~> Record L'))
  end.

Lemma record_set_compute_spec_correct : forall (f:field) `{EA:Enc A} (W:A) L (P:Prop),
  record_set_compute_spec f W L = Some P ->
  P.
Proof using.
  introv M. unfolds record_set_compute_spec. 
  sets_eq <- do E: (record_set_compute_dyn f (Dyn W) L).
  destruct do as [L'|]; inverts M. 
  gen L'. induction L as [|[f' D] T]; intros; [false|].
  destruct D as [A' EA' V]. simpl in E.
  xunfold Record at 1. simpl. case_if. (*--todo fix subst *)
  { subst. inverts E. xapply~ Rule_set_field. intros _. xunfold Record at 2. simpl. hsimpl. }
  { cases (record_set_compute_dyn f (Dyn W) T) as C'; [|false].
    inverts E. specializes~ IHT r. xapply IHT. hsimpl.
    intros. xunfold Record at 2. simpl. hsimpl~. }
Qed.

Global Opaque Record.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Tactics for generating specifications for get and set on records *)

(** Auxiliary tactic to read the record state from the pre-condition *)

Ltac xspec_record_repr_compute r H :=
  match H with context [ r ~> Record ?L ] => constr:(L) end.

(** Tactic [xget] derives a record [get] specification *)

Ltac xspec_record_get_compute_for f L :=
  let G := fresh in
  forwards G: (record_get_compute_spec_correct f L);
  [ reflexivity | revert G ].

Ltac xspec_record_get_loc v :=
  match v with
  | val_loc ?r => constr:(r)
  | @enc loc Enc_loc ?r => constr:(r)
  end.

Ltac xspec_record_get_compute tt :=
  match goal with |- Triple (trm_apps (trm_val (val_get_field ?f)) ((trm_val ?v)::nil)) ?H _ =>
    let r := xspec_record_get_loc v in
    let L := xspec_record_repr_compute r H in
    xspec_record_get_compute_for f L end.

(** Tactic [sget] derives a record [set] specification *)

Ltac xspec_record_get_arg w :=
  match w with
  | @enc _ _ ?W => constr:(W)
  | _ => constr:(w)
  end.

Ltac xspec_record_set_compute_for f W L :=
  let G := fresh in
  forwards G: (record_set_compute_spec_correct f W L);
  [ reflexivity | revert G ].

Ltac xspec_record_set_compute tt :=
  match goal with |- Triple (trm_apps (trm_val (val_set_field ?f)) ((trm_val ?v)::(trm_val ?w)::nil)) ?H _ =>
    let r := xspec_record_get_loc v in  
    let W := xspec_record_get_arg w in
    let L := xspec_record_repr_compute r H in
    xspec_record_set_compute_for f W L end.


(*--------------------------------------------------------*)
(* ================================================================= *)
(* ** [xspec] extended to get and set functions *)

Ltac xspec_base tt ::=
  match goal with
  | |- Triple (trm_apps (trm_val (val_get_field ?f)) _) _ _ =>
     xspec_record_get_compute tt
  | |- Triple (trm_apps (trm_val (val_set_field ?f)) _) _ _ =>
     xspec_record_set_compute tt
  | |- ?G => xspec_database G
  end.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Conversion between allocated segments and record representation *)

Section Alloc_to_Record.
Transparent Record repr loc.

(** Special case of arity 2 *)

Lemma Alloc2_to_Record : forall p, p <> null ->
  Alloc (abs 2) p ==> 
    Hexists (v1:val) (v2:val),
    (p ~> Record `{ (0%nat) := v1; (1%nat) := v2}).
Proof using.
  introv Np. change (abs 2) with 2%nat. rew_Alloc.
  hpull ;=> v1 v2. xunfold Record. unfold repr.
  rewrite Hfield_eq_fun_Hsingle. xunfold Hsingle.
  replace (p+0)%nat with p; [ | unfolds loc; math ].
  replace (p+1)%nat with (S p); [ | unfolds loc; math ].
  hsimpl~.
Qed.

(** General case *)

Lemma Alloc_to_Record : forall (p:loc) (start:nat) (n:nat),
  p <> null ->
  let xs := nat_seq start n in
      Alloc n (p+start)%nat 
  ==> Hexists (Vs:dyns), \[length Vs = n] \* p ~> Record (combine xs Vs).
Proof using.
  introv Np. gen start. induction n; intros; rew_Alloc.
  { subst. hsimpl (@nil dyn). rew_list~. }
  { hpull ;=> v. forwards K: (rm IHn) (S start).  
    math_rewrite ((p + S start)%nat = S (p+start)) in K.
    hchange K. hpull ;=> Vs LVs. applys (himpl_hexists_r ((Dyn v)::Vs)).
    simpl List.combine. xunfold Record.
    rewrite Hfield_to_hfield.
    rewrite hfield_eq_fun_hsingle. rew_enc.
    unfold repr. hsimpl~. rew_list; math. }
Qed.

End Alloc_to_Record.


(* ---------------------------------------------------------------------- *)
(* ** Specification for allocation of records of arity 2,
      See below for the generalization to arbitrary arities. *)

Definition val_new_record_2 := 
  Vars X1, X2, P in
  ValFun X1 X2 := 
    Let P := val_alloc 2 in
    val_set_field 0%nat P X1;;
    val_set_field 1%nat P X2;;
    P.

Lemma Rule_new_record_2 : forall `{EA1:Enc A1} `{EA2:Enc A2} (v1:A1) (v2:A2),
  Triple (val_new_record_2 `v1 `v2) 
    PRE \[]
    POST (fun p => p ~> Record`{ 0%nat := v1 ; 1%nat := v2 }).
Proof using. 
  xcf. xapp Rule_alloc as p. { math. } (* TODO: try Rule_alloc_nat *)
  intros Np. xchanges~ Alloc2_to_Record ;=> w1 w2.
  xapp. xapp. xval~. hsimpl.
Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Specification for allocation of records of arbitrary arity *)

Definition val_new_record (n:nat) :=
  let xs := nat_seq 0%nat n in
  let P : var := n%nat in
  val_funs xs (
    Let P := val_alloc n in
    LibList.fold_right (fun x t => val_set_field (x:field) P (x:var);; t) (trm_var P) xs).

Lemma Subst_new_record_aux : forall xs Vs (i n n':nat) (p:loc),
  n' = length Vs ->
  xs = nat_seq i n' ->
  (i + n' = n)%nat ->
    (Subst n (Dyn p) (Substs xs Vs (fold_right (fun x t => trm_seq (val_set_field x (trm_var n) (trm_var x)) t) (trm_var n) xs)))
  =  fold_right (fun xV t => let '(x,V) := xV in trm_seq (val_set_field x p (enc V)) t) p (LibList.combine xs Vs).
Proof using.
  intros xs. induction xs as [|x xs']; introv LVs Exs Ein. 
  { simpl combine. rew_list. unfold Subst. simpl. case_if~. } 
  { forwards Lin: length_nat_seq i n'.
    rewrite <- Exs in Lin. rew_list in Lin. 
    destruct Vs as [|V Vs']. { false. rew_list in LVs. math. }
    rew_list in LVs. asserts EL: (length xs' = length Vs'). { math. }
    destruct n' as [|n'']. { inverts Exs. } simpl in Exs. 
    invert Exs. intros Ei Exs'. subst i. rewrite <- Exs'. 
    asserts N: (x <> n). { math. } 
    rewrite Substs_cons. rewrite combine_cons. rew_listx.
    rewrite Subst_seq.
    asserts_rewrite (Subst x V (val_set_field x (trm_var n) (trm_var x)) 
                     = val_set_field x (trm_var n) (enc V)).
    { unfold Subst. simpl. case_if. case_if~.  }
    rewrite~ Substs_seq.
    asserts_rewrite (Substs xs' Vs' (val_set_field x (trm_var n) `V) 
                    = (val_set_field x (trm_var n) `V)).
    { do 2 rewrite~ Substs_app. do 2 rewrite~ Substs_val. rewrite~ Substs_var_neq.
      { rewrite Exs'. applys var_fresh_nat_seq_ge. math. } }
    rewrite~ Subst_seq.
    asserts_rewrite (Subst n (Dyn p) (val_set_field x (trm_var n) `V) = val_set_field x p `V).
    { unfold Subst; simpl. case_if~. } (* todo: lemma Subst_var *)
    fequals.
    match goal with |- context [Subst x V ?t'] => set (t:=t') end.
    asserts_rewrite (Subst x V t = t).
    { subst xs'. cuts K: (forall n' i, 
       (x < i)%nat ->
        let t := @fold_right nat trm (fun f t => trm_seq (val_set_field f (trm_var n) (trm_var f)) t) (trm_var n) (nat_seq i n') in
       Subst x V t = t).
     { applys K. math. }
     intros n'. gen N. clears_all. induction n'; introv L; intros; subst t.
     { simpl. unfold Subst. simpl. case_if~. } (*todo: Subst_var_neq.*)
     { simpl. rewrite Subst_seq. fequals.
       { unfold Subst. simpl. case_if. case_if. { false; math. } { auto. } }
       { rewrite~ IHn'. } } } 
    applys IHxs' Exs'; math. }
Qed.

Lemma Rule_new_record : forall (n:nat) (Vs:dyns),
  (n > 0)%nat ->
  n = length Vs -> 
  let xs := nat_seq 0%nat n in
  Triple (trm_apps (val_new_record n) (encs Vs))
    PRE \[]
    POST (fun p => p ~> Record (combine xs Vs)).
Proof using. 
  introv HP LVs. intros xs. applys Rule_apps_funs.
  { reflexivity. }
  { subst. applys~ var_funs_nat_seq. }
  { asserts EL: (length Vs = length xs). { unfold xs. rewrite~ length_nat_seq. }
    rewrite Substs_let; [| applys var_fresh_nat_seq_ge; math | auto ].
    asserts_rewrite (Substs (nat_seq 0 n) Vs (val_alloc n) = val_alloc n).
    { rewrite~ Substs_app. do 2 rewrite~ Substs_val. }
    eapply (@Rule_let _ _ _ _ _ _ _ loc). (* todo: cleanup *)
    { xapplys Rule_alloc_nat. }
    { intros p. xpull ;=> Np. xchange~ (@Alloc_to_Record p 0%nat).
      { math_rewrite ((p+0)%nat = p). hsimpl. } (* todo simplify *)
        xpull ;=> Ws LWs. fold xs.
        rewrite (@Subst_new_record_aux xs Vs 0%nat n n); try first [ math | auto ].
        asserts Lxs: (length xs = n). { subst xs. rewrite~ length_nat_seq. }
        clearbody xs. clear HP.
        applys local_weaken_post (fun p' => \[p' = p] \* p ~> Record (combine xs Vs));
        [ xlocal | | hsimpl; intros; subst~]. (* todo: weaken_post with swapped order *)
        gen n Vs Ws. induction xs; intros.
        { simpl. (* todo: rew_list *) applys~ Rule_val p. hsimpl~. }
        { rew_list in Lxs.
          destruct Vs as [|V Vs']; rew_list in LVs.
          { false; math. }
          destruct Ws as [|W Ws']; rew_list in LWs.
          { false; math. }
          destruct n as [|n']. { false; math. }
          { do 2 rewrite combine_cons. rew_list.
            rewrite Record_cons. applys Rule_seq.
            { xapplys @Rule_set_field. }
            { simpl. xapply (>> IHxs n' Vs' Ws'); try math.
              { hsimpl. } { intros p'. rewrite Record_cons. hsimpl~. } } } } } }
Qed.

Lemma Rule_new_record' : forall (n:nat) (Vs:dyns) (vs:vals) (Q:loc->hprop),
  vs = (encs Vs) ->
  (n = List.length Vs)%nat -> 
  (n > 0)%nat ->
  let xs := nat_seq 0%nat n in
  ((fun p => p ~> Record (List.combine xs Vs)) ===> Q) ->
  Triple (trm_apps (val_new_record n) (vals_to_trms vs)) \[] Q.
Proof using. 
  introv E HL HP HQ. rewrite List_length_eq in HL.
  rewrite List_combine_eq in HQ; [| rewrite~ length_nat_seq].
  subst. xapply~ Rule_new_record. hsimpl. hchanges~ HQ.
Qed.

(** Tactic [xrule_new_record] for proving the specification 
    triple for the allocation of a specific record.
    For an example, check out [ExampleTree.v], 
    Definition [val_new_node] and  Lemma [Rule_new_node]. *)

Ltac xrule_new_record_core tt :=
  intros; rew_nary; rew_vals_to_trms; applys Rule_new_record';
  [ xeq_encs | auto | math | hsimpl ].

Tactic Notation "xrule_new_record" :=
  xrule_new_record_core tt.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Lifted access rules for arrays *)

(* TODO *)









































