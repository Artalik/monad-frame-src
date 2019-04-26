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
| val_node : trm -> trm -> trm -> val

with trm : Type :=
     | trm_val : val -> trm
     | trm_var : var -> trm
     | trm_fun : var -> trm -> trm
     | trm_fix : var -> var -> trm -> trm
     | trm_node : trm -> trm -> trm -> trm
     | trm_if : trm -> trm -> trm -> trm
     | trm_match : trm -> trm -> trm -> trm
     | trm_seq : trm -> trm -> trm
     | trm_let : var -> trm -> trm -> trm
     | trm_app : trm -> trm -> trm
     | trm_while : trm -> trm -> trm
     | trm_for : var -> trm -> trm -> trm -> trm.


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
  fun h =>  Equal h (singleton loc) /\ loc <> null.

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
    exists l, \# (singleton l) h /\ l <> null.
Proof.
  intros. unfold disjoint.
  pose (max_elt h). pose (i := o). assert (o = i) by auto.
  induction i.
  * exists (S a). split; intros.
    ** intro. destruct H0.
       pose (P := H1). apply (max_elt_spec2 H) in P.
       apply singleton_spec in H0. rewrite H0 in P. auto.
    ** auto.
  * exists (S 0). split; intros.
    ** intro. destruct H0. apply max_elt_spec3 in H.
       unfold Empty in H. apply H in H1. assumption.
    ** auto.
Qed.

Implicit Types t : trm.
Implicit Types v : val.
Implicit Types s : sym.
Implicit Types b : bool.
Implicit Types n : int.

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let aux_no_capture x t := if eq_var_dec x y then t else aux t in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if eq_var_dec x y then trm_val w else t
  | trm_fun x t1 => trm_fun x (aux_no_capture x t1)
  | trm_fix f x t1 => trm_fix f x (if eq_var_dec f y then t1 else
                                     aux_no_capture x t1)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_match t0 t1 t2 => trm_match (aux t0) (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (aux_no_capture x t2)
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (aux_no_capture x t3)
  | trm_node t1 t2 t3 => trm_node (aux t1) (aux t2) (aux t3)
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
| red_match_leaf : forall v t1 t2 t3 m1 m2 m3,
    red m1 t1 m2 val_leaf ->
    red m2 t2 m3 v ->
    red m1 (trm_match t1 t2 t3) m3 v
| red_match_node :
    forall m0 m1 m2 m3 trm1 trm2 trm3 t1 t2 t3 v,
      red m0 t1 m1 (val_node trm1 trm2 trm3) ->
      red m2 (trm_app (trm_app (trm_app t3 trm1) trm2) trm3) m3 v ->
      red m0 (trm_match t1 t2 t3) m3 v
| red_node : forall m0 m1 m2 m3 t1 t2 t3 v1 v2 v3,
    red m0 t1 m1 v1 ->
    red m1 t2 m2 v2 ->
    red m2 t3 m3 v3 ->
    red m0 (trm_node t1 t2 t3) m3 (val_node v1 v2 v3)
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
    l <> null ->
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


Definition triple (t:trm) (H:hprop) (Q:val->hprop) :=
  forall H' h,
    (H \* H') h ->
    exists v h',
      red h t h' v
      /\ (Q v \* H') h'.

Definition pred_incl (A : Type) (P Q : A -> Prop) :=
  forall x, P x -> Q x.

Notation "P ==> Q" := (pred_incl P Q).


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

Lemma rule_ref :
  triple val_gensym \[] (fun r => Hexists l, \[r = val_sym l] \* (\s l)).
Proof.
  intros. intros HF h N.
  pose (e := single_fresh h). destruct e. destruct H.
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
















Definition rec_res :=
  (trm_node (trm_val val_gensym) (trm_app (trm_var 4) (trm_var 1)) (trm_app (trm_var 4) (trm_var 0))).

Definition branche_node := trm_fun 2 (trm_fun 1 (trm_fun 0 rec_res)).

Definition fix_label :=
  val_fix 4 3
          (trm_match (trm_var 3) val_leaf branche_node).

Definition label (t : trm) := trm_app fix_label t.

Inductive tree (A : Type) :=
| Leaf : tree A
| Node : A -> tree A -> tree A -> tree A.



Fixpoint tree_equiv (T : tree trm) (t : trm) :=
  match T, t with
  | Node x t1 t2, val_node x' t1' t2' => tree_equiv t1 t1' /\ tree_equiv t2 t2' /\ x = x'
  | Leaf _, val_leaf => True
  | _,_ => False
  end.

Fixpoint MTree (t : tree trm) :=
  match t with
  | Leaf _ => \[]
  | Node (trm_val (val_sym l)) t1 t2 => \s l \* (MTree t1) \* (MTree t2)
  | _ => fun h => False
  end.


Fixpoint TreeSpec (t : trm) :=
  match t with
  | val_leaf => \[]
  | val_node (val_sym l) t1 t2 => \s l \* (TreeSpec t1) \* (TreeSpec t2)
  | _ => fun h => False
  end.


Fixpoint is_tree_unit (t : val) :=
  match t with
  | val_node val_unit (trm_val t1) (trm_val t2) => is_tree_unit t1 /\ is_tree_unit t2
  | val_leaf => True
  | _ => False
  end.

Definition id :=
  trm_fix 4 3 (trm_match 3 val_leaf
                                  (trm_fun 2 (trm_fun 1 (trm_fun 0
                                                                 (trm_node 2 (trm_app (trm_var 4) (trm_var 1)) (trm_app (trm_var 4) (trm_var 0))))))).


Lemma test : forall (t : trm) v,
    triple (id v)
           (\[ t = trm_val v /\ is_tree_unit v] \* TreeSpec t)
           (fun v => \[ t = trm_val v /\ is_tree_unit v] \* TreeSpec t).
Proof.
  induction t0.
  * induction v0.
    { apply rule_frame. red. intros. red in H. simpl in *. repeat (destruct H). now destruct H1. }
    {  apply rule_frame. red. intros. red in H. simpl in *. repeat (destruct H). now destruct H1. }
    { apply rule_frame. red. intros. red in H. simpl in *. repeat (destruct H). now destruct H1. }
    {  apply rule_frame. red. intros. red in H. simpl in *. repeat (destruct H). now destruct H1. }
    {  apply rule_frame. red. intros. red in H. simpl in *. repeat (destruct H). now destruct H1. }
    {  apply rule_frame. red. intros. red in H. simpl in *. repeat (destruct H). now destruct H1. }
    {  apply rule_frame. red. intros. red in H. simpl in *. repeat (destruct H). now destruct H1. }
    { intros H N P.

















Lemma Equiv_Tree : forall (T : tree trm) (t : trm) (h : heap),
    tree_equiv T t -> TreeSpec t h -> MTree T h.
Proof.
  induction T; intros.
  * simpl in *. induction t0; simpl in *; try(contradiction).
    ** induction v; try(contradiction). assumption.
  * simpl in *. induction t0; simpl in *; try(contradiction).
    ** induction v; try(contradiction). destruct H. destruct H1.
       subst. induction t0; try(contradiction).
       induction v; try(contradiction). red. red in H0. destruct H0.
       destruct H0. destruct H0. destruct H2. destruct H3.
       exists x x0. repeat split; auto.
       *** intro. red in H0. destruct H0. now rewrite <- H0.
       *** intro. red in H0. destruct H0. now rewrite H0.
       *** now destruct H0.
       *** red. destruct H2. destruct H2. destruct H2. destruct H5. destruct H6.
           exists x1 x2. repeat split; auto.
           **** now apply (IHT1 t1).
           **** now apply (IHT2 t2).
           ****  intro. now rewrite H7 in H8.
           **** intro. now rewrite H7.
       *** intro. now rewrite H4 in H5.
       *** intro. now rewrite H4.
Qed.

Lemma Equiv_Tree2 : forall (T : tree trm) (t : trm) (h : heap),
    tree_equiv T t -> MTree T h -> TreeSpec t h.
Proof.
  induction T; intros.
  * simpl in *. induction t0; simpl in *; try(contradiction).
    ** induction v; try(contradiction). assumption.
  * simpl in *. induction t0; simpl in *; try(contradiction).
    ** induction v; try(contradiction). destruct H. destruct H1.
       subst. induction t0; try(contradiction).
       induction v; try(contradiction). red. red in H0. destruct H0.
       destruct H0. destruct H0. destruct H2. destruct H3.
       exists x x0. repeat split; auto.
       *** intro. red in H0. destruct H0. now rewrite <- H0.
       *** intro. red in H0. destruct H0. now rewrite H0.
       *** now destruct H0.
       *** red. destruct H2. destruct H2. destruct H2. destruct H5. destruct H6.
           exists x1 x2. repeat split; auto.
           **** intro. now rewrite H7 in H8.
           **** intro. now rewrite H7.
       *** intro. now rewrite H4 in H5.
       *** intro. now rewrite H4.
Qed.

Lemma trm_pos : forall t, 1 <= trm_size t.
Proof.
  induction t0; simpl; math.
Qed.

Lemma red_size : forall t m0 m1 r, red m0 t m1 r -> trm_size r <= trm_size t.
Proof.
  induction t0; intros; simpl; try(reflexivity); try(math).
Qed.





      rule_frame : forall t H Q H',
          triple t H Q ->
          triple t (H \* H') (Q \*+ H').

      (* Lemma val_label : forall x t1 t2 v1 v2 m1 m2, *)
      (*     t1 = trm_val v1 -> *)
      (*     t2 = trm_val v2 -> *)
      (*     is_tree v1 -> *)
      (*     is_tree v2 -> *)
      (*     red m1 (label (val_node x t1 t2)) m2 (val_node val_gensym (fix_label t1) (fix_label t2)). *)
      (* Proof. *)
      (*   induction x; intros. *)
      (*   * eapply red_app_arg. *)
      (*     ** apply red_fix. *)
      (*     ** apply red_val. *)
      (*     ** eapply red_app_arg. *)
      (*        *** apply red_val. *)
      (*        *** apply red_val. *)
      (*        *** eapply red_app_fix. *)
      (*            **** f_equal. *)
      (*            **** eapply red_match_node. *)
      (*                 { apply red_val. } *)
      (*                 eapply red_app_arg. *)
      (*                 { eapply red_app_arg. *)
      (*                   { eapply red_app_arg. *)
      (*                     { eapply red_fun. } *)
      (*                     { apply red_val. } *)
      (*                     { eapply red_app_fun. *)
      (*                       { f_equal. } *)
      (*                       { apply red_fun. } *)
      (*                     } *)
      (*                   } *)
      (*                   { induction v1; simpl in *; try contradiction; subst. *)
      (*                     { instantiate (3:=m1). eapply red_val. } *)
      (*                     { apply red_val. } *)

      (*                   } *)
      (*                   { eapply red_app_fun. *)
      (*                     { f_equal. } *)
      (*                     { apply red_fun. } *)
      (*                   } *)
      (*                 } *)
      (*                 { *)
      (*                   { induction v2; simpl in *; try contradiction; subst. *)
      (*                     { eapply red_val. } *)
      (*                     { apply red_val. } *)
      (*                   } *)
      (*                 } *)
      (*                 { eapply red_app_fun. *)
      (*                   { f_equal. } *)
      (*                   { simpl. unfold rec_res. *)



      Lemma spec_tree : forall t0 v1, triple (label t0)
                                             \[(t0 = trm_val v1 /\ is_tree_unit v1)]

                                             (fun r => TreeSpec r).
      Proof.
        induction t0; red; intros. destruct H; destruct H;
                                     destruct H; destruct H0; destruct H1; destruct H; destruct H3.
        * rewrite H3.
          pose rule_ref.
          unfold triple in t0. pose (t0 htop h). destruct e.
          { red. exists empty x0. repeat split; auto.
            { apply disjoint_empty. }
            { intro. rewrite H in H2. now rewrite H2 in H5. }
            { intro. rewrite H in H2. now rewrite H2. }
          }
          destruct H5. destruct H5.
          induction v1; simpl in *; try contradiction.
          ** exists val_leaf __.
             split.
             *** eapply red_app_arg.
                 **** apply red_val.
                 **** apply red_val.
                 **** eapply red_app_fix.
                      ***** unfold fix_label. f_equal.
                      ***** simpl. eapply red_match_leaf; apply red_val.
             *** red. exists empty x0. repeat split; try (now intro).
                 **** assumption.
                 **** intro. rewrite H in H2. now rewrite H2 in H7.
                 **** intro. rewrite H in H2. now rewrite H2.
          ** induction t1; try contradiction. induction v0; try contradiction.
             exists (val_node
                       x1
                       (val_fix 4 3
                                (trm_match (trm_var 3) val_leaf branche_node) t2)
                       (val_fix 4 3
                                (trm_match (trm_var 3) val_leaf branche_node) t3)
                    ) __.
             split.
             *** eapply red_app_arg.
                 **** apply red_val.
                 **** apply red_val.
                 **** eapply red_app_fix.
                      ***** unfold fix_label. f_equal.
                      ***** simpl. eapply red_match_node.
                      { apply red_val. }
                      { instantiate (2 := h). induction t2; induction t3; try contradiction.
                        subst.
                        eapply red_app_arg.
                        { eapply red_app_arg.
                          { eapply red_app_arg.
                            { eapply red_fun. }
                            { apply red_val. }
                            { eapply red_app_fun.
                              { f_equal. }
                              { simpl. apply red_fun. }
                            }
                          }
                          { instantiate (1 := v0). apply red_val. }
                          { eapply red_app_fun.
                            { f_equal. }
                            { simpl. apply red_fun. }
                          }
                        }
                        { apply red_val. }
                        { eapply red_app_fun.
                          { f_equal. }
                          { simpl. unfold fix_label. apply red_node. eassumption. }
                        }
                      }
             *** destruct H6. destruct H6. destruct H6. destruct H6. destruct H6. destruct H6. destruct H6.
                 destruct H6. subst. red. destruct H8. destruct H9.
                 destruct H7. destruct H11.
                 exists x2 x0. repeat split.
                 { red. exists x7 empty. repeat split; destruct H8.
                   { intro. now rewrite H8 in H14. }
                   { intro. now rewrite H8. }
                   { assumption. }
                   { red.









                     *** simpl in *. red in H6. destruct H6. destruct H6. destruct H6. destruct H6. destruct H6.
                         destruct H6. destruct H6. destruct H6. rewrite H9. red. destruct H8. destruct H9.
                         exists x7 x4. repeat split.
                         **** red. exists x7 empty. destruct H8. repeat split; auto.
                              { intro. now rewrite H8 in H11. }
                              { intro. now rewrite H8. }
                              { red.





                                exists ___.
                                *** eapply red_app_arg.
                                    **** apply red_fix.
                                    **** apply red_val.
                                    **** eapply red_app_fix.
                                         ***** f_equal.
                                         ***** simpl. eapply red_match_node.
                                         { apply red_val. }
                                         { instantiate (3 := h). eapply red_app_arg.
                                           { eapply red_app_arg.
                                             { eapply red_app_arg.
                                               { apply red_fun. }
                                               { induction t3; try contradiction. induction v0; try contradiction.
                                                 apply red_val. }
                                               { eapply red_app_fun.
                                                 { f_equal. }
                                                 { simpl. apply red_fun. }
                                               }
                                             }
                                             { induction t4 eqn:?.
                                               {




                                                 induction v1; simpl in *; try contradiction.
                                                 { eapply red_match_leaf.
                                                   { apply red_val. }
                                                   { apply red_val. }
                                                 }
                                                 { induction t3; try contradiction. induction v0; try contradiction.
                                                   eapply red_match_node.
                                                   { apply red_val. }
                                                   { eapply red_app_arg.
                                                     { eapply red_app_arg.
                                                       { eapply red_app_arg.
                                                         { eapply red_fun. }
                                                         { instantiate (3 := h). apply red_val. }
                                                         { eapply red_app_fun.
                                                           { f_equal. }
                                                           { simpl. apply red_fun. }
                                                         }
                                                       }
                                                       { induction t4; induction t5; simpl in *; try contradiction.
                                                         destruct H4. induction v0; simpl in *; try contradiction.
                                                         { apply red_val. }
                                                         {



                                                           ***** instantiate (2:=h). instantiate (1 := v).



                                                           t1 = val_node trm1 trm2 trm3 ->
                                                           red m2 trm1 m3 v1 ->
                                                           red m3 trm2 m4 v2 ->
                                                           red m4 trm3 m5 v3 ->
                                                           red m5 v m6 (val_fun x (val_fun y (val_fun z term))) ->
                                                           red m6 (subst x v1 (subst y v2 (subst z v3 term))) m7 vres ->
                                                           red m1 (trm_match t1 t2 v) m7 vres



                                                               induction t0; red; intros; destruct H; destruct H; destruct H; destruct H0; destruct H1.
                                                           * induction v; simpl in *.
                                                             ** unfold label. unfold fix_label.
                                                                exists val_leaf empty. split; auto.
                                                                *** eapply (red_app_fix val_unit).
                                                                    **** f_equal.
                                                                    **** eapply red_match_wrong. unfold branche_node. red.

                                                                         (subst 4 fix_label (subst 3 val_unit (trm_match 3 val_leaf branche_node))).

                                                                         apply (red_app_fix).

                                                                         | red_app_fix : forall m1 m2 v1 v2 f x t r,
                                                                             v1 = val_fix f x t ->
                                                                             red m1 (subst f v1 (subst x v2 t)) m2 r ->
                                                                             red m1 (trm_app v1 v2) m2 r
