Set Implicit Arguments.
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
Program Definition union := MSet.union.
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

(*
Fixpoint trm_size (t:trm) : nat :=
  match t with
  | trm_var x => 1
  | trm_val v => 1
  | trm_fun x t1 => 1 + trm_size t1
  | trm_fix f x t1 => 1 + trm_size t1
  | trm_if t0 t1 t2 => 1 + trm_size t0 + trm_size t1 + trm_size t2
  | trm_seq t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_let x t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_app t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_while t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_for x t1 t2 t3 => 1 + trm_size t1 + trm_size t2 + trm_size t3
  | trm_match t1 t2 t3 => 1 + trm_size t1 + trm_size t2 + trm_size t3
  | trm_node t1 t2 t3 => 1 + trm_size t1 + trm_size t2 + trm_size t2
  end.

Lemma l_max_Sl : forall (n m : nat), n < S (max n m).
Proof.
  induction n; intros; intuition.
  induction m; simpl; intuition.
  pose (IHn m). induction n; intuition.
Qed.
 *)

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
Proof using.
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

Lemma rule_fix : forall f x t1 H Q,
    H ==> Q (val_fix f x t1) ->
    triple (trm_fix f x t1) H Q.
Proof using.
  introv M. intros HF h H0. exists___. splits.
  { applys red_fix. }
  { red in M. red. red in H0. repeat (destruct H0). destruct H1. destruct H2.
    exists x0 x1. repeat split; auto.
    { intro. now rewrite H3 in H4. }
    { intro. now rewrite H3. }
  }
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

Definition spec_fun (x:var) (t1:trm) (F:val) :=
  forall X H, triple (subst x X t1) H ==> triple (trm_app F X) H.

Lemma spec_fun_fun : forall x t1, spec_fun x t1 (val_fun x t1).
Proof.
  introv M. intros HF h N. lets~ (v&h'&P&D) : (rm M) HF h. exists v h'. split~.
  now eapply red_app_fun.
Qed.

Lemma rule_fun_spec : forall x t1 H Q,
    (forall (F:val), spec_fun x t1 F -> (H ==> Q F)) ->
    triple (trm_fun x t1) H Q.
Proof.
  introv M. intros HF h H0. exists (val_fun x t1) h. split.
  * apply red_fun.
  * repeat (destruct H0). exists x0 x1. split~. apply~ M. apply spec_fun_fun.
Qed.

Lemma rule_app_node : forall F V H Q,
    F = val_node ->
    triple (val_node1 V) H Q ->
    triple (trm_app F V) H Q.
Proof.
  introv P M. subst F. intros HF h P. lets~ (v&h'&X&D) : (rm M) HF h.
  exists (val_node1 V) h'. split.
  * apply~ red_app_node.
  * inversion X. now subst.
Qed.

Lemma rule_app_node1 : forall F v1 V H Q,
    F = val_node1 v1 ->
    triple (val_node2 v1 V) H Q ->
    triple (trm_app F V) H Q.
Proof.
  introv P M. subst F. intros HF h P. lets~ (v&h'&X&D) : (rm M) HF h.
  exists (val_node2 v1 V) h'. split.
  * apply~ red_app_node1.
  * inversion X. now subst.
Qed.


Lemma rule_app_node2 : forall F v1 v2 V H Q,
    F = val_node2 v1 v2 ->
    triple (val_node3 v1 v2 V) H Q ->
    triple (trm_app F V) H Q.
Proof.
  introv P M. subst F. intros HF h P. lets~ (v&h'&X&D) : (rm M) HF h.
  exists (val_node3 v1 v2 V) h'. split.
  * apply~ red_app_node2.
  * inversion X. now subst.
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

Lemma rule_extract_hprop : forall t (P:Prop) H Q,
    (P -> triple t H Q) ->
    triple t (\[P] \* H) Q.
Proof.
  introv M. intros HF h H0. repeat (destruct H0). apply M in H3. destruct H2. destruct H1.
  destruct H4. destruct H5.
  lets~ (v&h'&X&D) : (rm H3) HF h.
  - exists x2 x0. repeat split~; intro.
    + apply disjoint_sym. apply (equal_disjoint_right H6 H5).
    + rewrite H0 in H6. rewrite~ empty_union_1 in H6. rewrite H6 in H7. now rewrite H7 in H3.
    + rewrite H0 in H6. rewrite~ empty_union_1 in H6. rewrite H6 in H7. now rewrite H7.
  - exists~ v h'.
Qed.

Lemma himpl_empty_left : forall H, H ==> \[] \* H.
Proof.
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
      * apply (rule_consequence (H' := \[] \* \[f = val_sym fresh] \* \s fresh)
                                (Q' := fun l' => TreeSpec l' \* \[f = val_sym fresh] \* \s fresh)).
        -- apply himpl_empty_left.
        -- applys~ rule_frame.
        -- intros x h q.
           exact q.
      * simpl. applys~ rule_let; [| intros r; simpl].
        -- apply (rule_consequence (H' := \[] \* TreeSpec l' \* \[f = val_sym fresh] \* \s fresh)
                                   (Q' := fun r' => TreeSpec r' \* TreeSpec l' \* \[f = val_sym fresh] \* \s fresh)).
           ++ apply himpl_empty_left.
           ++ applys~ rule_frame.
           ++ intros x h q.
              exact q.
        -- applys~ rule_app_node3.
           applys~ rule_val.
           simpl. intro. intro.
           apply finish_him in H2.
           destruct H2. now subst f.
Qed.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Inductive tree (X : Type) : Type :=
| node : X -> tree X -> tree X -> tree X
| leaf : tree X.

Arguments leaf {_}.
Arguments node {_} n l r.

Axiom FreshMonad : Type -> Type.

Axiom Sym : Type.
Axiom gensym : FreshMonad Sym.

Axiom ret : forall {X}, X -> FreshMonad X.
Axiom bind: forall {X Y}, FreshMonad X -> (X -> FreshMonad Y) -> FreshMonad Y.

Notation "'let!' x ':=' e1 'in' e2" := (bind e1 (fun x => e2))
                                         (x ident, at level 90).

Fixpoint label' (t: tree unit): FreshMonad (tree Sym) :=
  match t with
  | leaf => ret leaf
  | node _ l r =>
    let! f := gensym in
    let! l' := label' l in
    let! r' := label' r in
    ret (node f l' r')
  end.
