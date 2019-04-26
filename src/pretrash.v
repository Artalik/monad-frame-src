Inductive tree (A : Type) :=
| Leaf : tree A
| Node : A -> tree A -> tree A -> tree A.

Fixpoint flatten_tree {A : Type} (t : tree A) :=
  match t with
  | Leaf _ => nil
  | Node e t1 t2 => e :: (flatten_tree t1) ++ (flatten_tree t2)
  end.

Fixpoint TreeSpec (t : tree _) :=
  match t with
  | Leaf _ => \[]
  | Node v t1 t2 =>
    (Hexists l, (fun h => red h v (singleton l \+ h) (val_loc l))) \* (TreeSpec t1) \* (TreeSpec t2)
  end.

Fixpoint ListSpec (l : list _) :=
  match l with
  | nil => \[]
  | v :: t =>
    (Hexists l, (fun h => red h v (singleton l \+ h) (val_loc l))) \* (ListSpec t)
  end.


Fixpoint label (t : tree unit) :=
  match t with
  | Leaf _ => Leaf _
  | Node _ t1 t2 =>
    Node (val_ref val_unit) (label t1) (label t2)
  end.

Fixpoint label_list (l : list unit) :=
  match l with
  | nil => nil
  | h :: l =>
    (val_ref val_unit) :: (label_list l)
  end.


Lemma equal_disjoint : forall (x x0 x1 : structure),
    Equal x0 x1 -> disjoint x x1 -> disjoint x x0.
Proof.
  intros. red in *. intro. intro. destruct H1. apply H in H2.
  apply (not_in H1) in H2. assumption. apply H0.
Qed.

Lemma union_empty : forall x1 x2, Equal x1 empty -> Equal (x1 \+ x2) x2.
Proof.
  intuition.
Qed.

Lemma equal_sym : forall x1 x2, Equal x1 x2 -> Equal x2 x1.
Proof.
  intros. unfold Equal in *. intro. apply iff_sym. apply H.
Qed.

Lemma ListSpec_equal : forall l x1 x2, Equal x1 x2 -> ListSpec l x1 -> ListSpec l x2.
Proof.
  induction l; intros.
  * simpl in *. red in H0. red. rewrite <- H0. apply equal_sym. assumption.
  * simpl in *. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    destruct H0. red. exists x x0. repeat(split); auto.
    ** red. exists x3. assumption.
    ** intro. rewrite <- H in H4. rewrite H3 in H4. assumption.
    ** intro. rewrite H in H3. rewrite <- H3 in H4. assumption.
Qed.

Lemma fold_app : forall (A : Type) (l l' : list A),
    LibList.fold_right (fun x4 acc => (x4 :: acc)) l' l = l ++ l'.
Proof.
  induction l; intros.
  * reflexivity.
  * simpl. rewrite <- IHl. reflexivity.
Qed.

Lemma cons_wtf : forall (A : Type) (l : list A) a, (a :: l) = (a :: l)%list.
Proof.
  induction l; intros; reflexivity.
Qed.

Lemma app_wtf : forall (A : Type) (l l' : list A), (l ++ l') = (l ++ l')%list.
Proof.
  induction l; intros.
  * now setoid_rewrite app_nil_l.
  * simpl. rewrite IHl. reflexivity.
Qed.

Lemma label_nil : forall l, label_list (nil ++ l) = label_list l.
Proof.
  induction l.
  * reflexivity.
  * simpl. f_equal.
Qed.

Lemma app_label_list : forall l l', label_list l ++ label_list l' = label_list (l++l').
Proof.
  induction l; intros.
  * simpl. now rewrite label_nil.
  * simpl. f_equal. rewrite IHl. rewrite (fold_app l l'). rewrite app_wtf. reflexivity.
Qed.

Lemma flatten_label : forall t0, flatten_tree (label t0) = label_list (flatten_tree t0).
Proof.
  induction t0.
  * reflexivity.
  * simpl. f_equal. rewrite IHt0_1. rewrite IHt0_2. rewrite app_label_list.
    rewrite app_wtf. reflexivity.
Qed.


Lemma app_spec : forall (l l' : list trm) x1 x2,
    ListSpec l x1 -> ListSpec l' x2 -> \# x1 x2 -> ListSpec (l ++ l') (x1 \+ x2).
Proof.
  induction l; intros.
  * simpl in H.  red in H. apply (union_empty x2) in H. apply equal_sym in H.
    apply (ListSpec_equal l' H) in H0. rewrite <- (app_nil_l l') in H0. assumption.
  * simpl in H. destruct H. destruct H. destruct H. destruct H. destruct H2. destruct H3.
    exists x (x0 \+ x2). repeat split.
    ** exists x3. assumption.
    ** rewrite fold_app. setoid_rewrite (app_wtf l l'). apply (IHl l' x0) in H0; auto.
       apply (equal_disjoint_right H4) in H1.
       apply disjoint_sym. assumption.
    ** apply disjoint_sym in H1. apply (equal_disjoint_left H4) in H1.
       apply disjoint_sym in H1. apply (union_disjoint H3 H1).
    ** rewrite H4. apply union_assoc.
    ** rewrite H4. apply union_assoc.
Qed.


Lemma treespec_to_listspec : forall t h, TreeSpec (label t) h -> ListSpec (flatten_tree (label t)) h.
Proof.
  induction t0; intros; simpl in *; auto.
  destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0. destruct H0.
  destruct H2. destruct H3. destruct H1. red. destruct H. exists x (x1 \+ x2).
  repeat(split); auto.
  * red. pose (P := (single_fresh x)). destruct P. exists x4. apply red_ref; intuition.
    apply (disjoint_sym H7).
  * apply IHt0_1 in H0. apply IHt0_2 in H2. rewrite app_wtf.
    apply (app_spec (flatten_tree (label t0_1)) (flatten_tree (label t0_2)) H0 H2 H3).
  * apply equal_sym in H4. apply (equal_disjoint H4 H1).
  * intro. rewrite H4 in H5. now rewrite H5 in H6.
  * intro. rewrite H4 in H5. now rewrite H5.
Qed.

Lemma cut_spec : forall (l l' : list trm) x,
    ListSpec (l ++ l') x ->
    exists x1 x2, ListSpec l x1 /\ ListSpec l' x2 /\ \# x1 x2 /\ Equal x (x1 \+ x2).
Proof.
  induction l; intros.
  * exists empty x. repeat split; auto. apply disjoint_empty.
  * destruct H. destruct H. destruct H. destruct H0. destruct H1.
    simpl. rewrite fold_app in H0. rewrite app_wtf in H0. apply IHl in H0. destruct H0.
    destruct H0. destruct H0. destruct H3. destruct H4. exists (x0 \+ x2) x3.
    repeat split; auto.
    ** red. exists x0 x2.
       repeat (split);auto. apply (equal_disjoint_left H5 H1).
    ** apply disjoint_sym in H1. apply (equal_disjoint_right H5) in H1.
       apply disjoint_sym in H1. apply disjoint_sym in H4. apply disjoint_sym.
       apply (union_disjoint H1 H4).
    ** intro. rewrite H5 in H2. rewrite H2 in H6. now apply union_assoc.
    ** intro. rewrite H5 in H2. rewrite H2. now apply union_assoc.
Qed.


Lemma listspec_to_treespec : forall t h, ListSpec (flatten_tree (label t)) h -> TreeSpec (label t) h.
Proof.
  induction t0; intros; simpl in *; auto.
  destruct H. destruct H. destruct H. destruct H0. destruct H1.
  red. exists x x0.
  repeat split; auto; try( rewrite H2; now intro).
  * red. rewrite app_wtf in H0. apply cut_spec in H0. destruct H0. destruct H0.
    destruct H0. destruct H3. destruct H4. exists x1 x2.
    repeat split; auto; try(rewrite H5; now intro).
Qed.


Lemma open_tree : forall (tt : unit) (t t1 t2: tree unit) h h',
    t = (Node tt t1 t2) -> TreeSpec (label t1) h -> TreeSpec (label t2) h' ->
    \# h h' -> TreeSpec (label t) (h \+ h').
Proof.
  intros. subst. simpl. red. exists empty (h \+ h'). intuition.
  * red. pose (P := (single_fresh (h \+ h'))). destruct P.
    exists x. apply red_ref; intuition. apply disjoint_empty.
  * exists h h'. intuition.
  * apply disjoint_empty.
Qed.

Lemma list_from_tree_prop : forall t0 e, List.In e (flatten_tree (label t0)) -> e = (val_ref val_unit).
Proof.
  induction t0; intros; simpl in *; try(contradiction).
  destruct H; auto. apply (in_app_or (flatten_tree (label t0_1))) in H.
  destruct H.
  * apply IHt0_1 in H; auto.
  * apply IHt0_2 in H; auto.
Qed.

Lemma tree_equiv : forall (A : Type) (l : list A), exists t0, l = flatten_tree t0.
Proof.
  induction l; intros.
  * exists (Leaf A). reflexivity.
  * destruct IHl. exists (Node a x (Leaf A)).
    rewrite H. unfold flatten_tree. rewrite app_nil_r. reflexivity.
Qed.

(* Lemma tree_equiv2 : forall (l : list trm), exists t0, l = flatten_tree (label t0). *)
(* Proof. *)
(*   intro. *)
(*   pose (tree_equiv l). destruct e. *)
(*   induction l; intros. *)
(*   * exists (Leaf unit). reflexivity. *)
(*   * destruct IHl. exists (Node tt x (Leaf unit)). *)
(*     rewrite H. unfold flatten_tree. rewrite app_nil_r. reflexivity. *)
(* Qed. *)

Lemma label_list_weak : forall l, exists t0 h, l = (flatten_tree (label t0)) -> ListSpec l h.
Proof.
  induction l; intros.
  * exists (Leaf unit) empty. simpl. now trivial.
  * destruct IHl. destruct H. pose (P := (single_fresh x0)). destruct P.
    destruct H0. exists (Node tt x (Leaf unit)) (x0).
    intro. simpl. red. exists empty x0. repeat split; auto.
    ** assert (List.In a (a :: l)) by (apply in_eq). rewrite H2 in H3.
       apply list_from_tree_prop in H3. subst.
       red. exists x1. apply red_ref; auto. apply disjoint_empty.
    ** simpl in H2. inversion H2. rewrite app_nil_r in H5. rewrite app_nil_r in H2.
       rewrite app_nil_r. subst. now apply H.
    ** apply disjoint_empty.
Qed.

Fixpoint list_to_tree (A : Type) (l : list A) : tree A :=
  match l with
  | nil => Leaf _
  | h :: t =>
    Node h (list_to_tree t) (Leaf _)
  end.

Lemma app_flatten_list_flatten : forall (A : Type) (l l' : list A),
    flatten_tree (list_to_tree (l ++ l')) =
    flatten_tree (list_to_tree l) ++
                 (flatten_tree (list_to_tree l')).
Proof.
  induction l; intros.
  * simpl. now setoid_rewrite (app_nil_l l').
  * simpl. f_equal. rewrite fold_app. repeat (rewrite app_nil_r). rewrite <- IHl.
    now rewrite app_wtf.
Qed.

Fixpoint concat_tree (A : Type) (t1 t2 : tree A) : tree A :=
  list_to_tree (flatten_tree t1 ++ flatten_tree t2).

Lemma flatten_list_flatten : forall (A : Type) (t0 : tree A),
    flatten_tree (list_to_tree (flatten_tree t0)) = flatten_tree t0.
Proof.
  induction t0.
  * reflexivity.
  * simpl. f_equal. rewrite app_nil_r. rewrite app_wtf.
    rewrite (app_flatten_list_flatten (flatten_tree t0_1) (flatten_tree t0_2)).
    rewrite IHt0_1. rewrite IHt0_2. now rewrite app_wtf.
Qed.


Lemma concat_tree_spec: forall (A : Type) (t1 t2 : tree A),
    flatten_tree t1 ++ flatten_tree t2 = flatten_tree (concat_tree t1 t2).
Proof.
  induction t1; intros.
  * simpl. setoid_rewrite (app_nil_l (flatten_tree t2)). now rewrite flatten_list_flatten.
  * simpl. f_equal. rewrite fold_app. rewrite <- app_assoc.
    rewrite IHt1_2. rewrite IHt1_1. rewrite app_nil_r. now rewrite flatten_list_flatten.
Qed.

Lemma label_flatten_app : forall t1 t2,
    label_list (flatten_tree t1 ++ flatten_tree t2) = label_list (flatten_tree (concat_tree t1 t2)).
Proof.
  intros. rewrite <- app_wtf.
  now rewrite (concat_tree_spec t1 t2).
Qed.

(* Lemma concat_label : forall t1 t2, *)
(*     concat_tree (label t1) (label t2) = label (concat_tree t1 t2). *)
(* Proof. *)
(*   intros.  *)
(*   induction t1; intros. *)
(*   * simpl. setoid_rewrite (app_nil_l (flatten_tree (label t2))). *)
(*     setoid_rewrite (app_nil_l (flatten_tree t2)).  *)


Lemma label_list_strong : forall l t0, exists h, l = (flatten_tree (label t0)) -> ListSpec l h.
Proof.
  induction l; intros.
  * exists empty. simpl. now trivial.
  * induction t0.
    ** exists empty. intro. inversion H.
    ** destruct IHt0_1. destruct IHt0_2. exists (x \+ x0). intro.
       inversion H1. simpl. red. rewrite flatten_label in H4. rewrite flatten_label in H4.
       rewrite app_label_list in H4. rewrite label_flatten_app in H4.
       rewrite <- flatten_label in H4. pose (H40 := H4).
       pose (IHl (concat_tree t0_1 t0_2)). destruct e. apply H2 in H40.
       exists empty x1. repeat split; auto.
       *** red. pose (P := (single_fresh (x \+ x0))). destruct P. destruct H5.
           exists x2. apply red_ref; auto. apply disjoint_empty.
       *** rewrite concat_tree_spec.


           rewrite <- H6.
           induction t0_1.
           **** simpl in *. pose (IHl t0_2).
                destruct e. apply H2 in H6.



                case (t0_1).
       *** simpl. pose (IHl t0_2). destruct e. exists x.
           intro. inversion H0.
           red. exists empty x. repeat split; auto.
           **** pose (P := (single_fresh x)). destruct P. destruct H1.
                exists x0. apply red_ref; auto. apply disjoint_empty.
           **** rewrite <- H3. now apply H in H3.
           **** apply disjoint_empty.
       *** intros. destruct IHt0_1. exists x. intro. inversion H0.
           apply IHl in H3.







           Lemma aux_final : forall (t0 : tree unit), exists (l : list trm), l = (flatten_tree (label t0)).
           Proof.
             induction t0; intros.
             * exists (nil: list trm). reflexivity.
             * destruct IHt0_1. destruct IHt0_2. exists ((val_ref val_unit) :: x ++ x0).
               simpl. f_equal. now subst.
           Qed.

           Lemma test : forall t0, exists h, TreeSpec (label t0) h.
           Proof.
             intro. pose (aux_final t0). destruct e. pose (label_list_strong x t0).
             destruct e. exists x0. apply listspec_to_treespec. subst. intuition.
           Qed.


           Lemma listspec_to_treespec : forall t h, ListSpec (flatten_tree (label t)) h -> TreeSpec (label t) h.

             Lemma label_list : forall t0, exists h, ListSpec (flatten_tree (label t0)) h.
             Proof.
               induction t0; intros.
               * exists empty. repeat red. now trivial.
               * destruct IHt0_1. destruct IHt0_2.
                 pose (P := (single_fresh (x \+ x0))). destruct P.
                 exists (singleton x1 \+ x \+ x0). simpl. red.
                 exists empty (x \+ x0).
                 repeat split; auto.
                 ** red. exists x1. destruct H1. apply red_ref; auto. apply disjoint_empty.
                 **


                   induction l; intros.
               * exists empty. intro. rewrite <- H. red. red. reflexivity.
               * pose (IHl t0). destruct e. pose (P := (single_fresh x)). destruct P.
                 exists (empty \+ x). intro. rewrite <- H1.
                 simpl. red. exists empty x. repeat split; auto.
                 ** assert (List.In a (a :: l)) by (apply in_eq). rewrite H1 in H2.
                    apply list_from_tree_prop in H2. red. rewrite H2. exists x0. destruct H0.
                    apply red_ref; auto. apply disjoint_empty.
                 ** pose (tree_equiv l). destruct e.



                    intro.
                    induction (flatten_tree (label t0)).

                    induction t0; intros.
               * exists empty. repeat red. now trivial.
               * destruct IHt0_1. destruct IHt0_2.
                 pose (P := (single_fresh (x \+ x0))). destruct P.
                 exists (singleton x1 \+ x \+ x0). simpl. red.
                 exists empty (x \+ x0).
                 repeat split; auto.
                 ** red. exists x1. destruct H1. apply red_ref; auto. apply disjoint_empty.
                 **

                   ListSpec l x1 -> ListSpec l' x2 -> \# x1 x2 -> ListSpec (l ++ l') (x1 \+ x2).


                   induction l; intros.
               * exists empty. repeat red. now trivial.
               * destruct IHl. pose (P := (single_fresh x)). destruct P.
                 exists (singleton x0 \+ x). simpl. red. exists empty x.
                 repeat split; auto.





                 Lemma label_disjoint : forall (t1 t2 : tree unit),
                     exists h h1 h2, h = h1 \+ h2 ->
                                     TreeSpec (label t1) h1 -> TreeSpec (label t2) h2 ->
                                     \# h1 h2.
                 Proof.
                   induction t1.
                   * intros. exists (empty \=


                                           induction t0; intros.
                                     * inversion H.
                                     * inversion H. red. exists h h'. split; intuition.


                                       Lemma test : triple (val_ref val_unit) \[] (fun r => Hexists l, \[r = val_loc l] \* (\s l)) ->
                                                    forall t, exists h, TreeSpec(label t) h.
                                       Proof.
                                         intros. induction t0.
                                         * simpl. exists empty. red. reflexivity.
                                         *





                                           intro. induction t0; intros; red in H.
                                         * simpl. exists empty. red. reflexivity.
                                         * destruct IHt0_1. destruct IHt0_2.
                                           pose (P := (single_fresh (x \+ x0))). destruct P.
                                           exists (x \+ x0). simpl.


                                           (* Lemma tree_spec : forall t t' h h', (TreeSpec (label t) \* TreeSpec (label t')) (h \+ h') -> TreeSpec (label t) h -> TreeSpec (label t') h' ->\# h h'. *)
                                           (* Proof. *)
                                           (*   intros. repeat (destruct H). destruct H2. destruct H3. *)




                                           (*   induction t0; simpl; intros; red in H. *)
                                           (*   * red in H. red. intro. intro. destruct H1. apply H in H1. inversion H1. *)
                                           (*   * destruct H. destruct H. destruct H. destruct H. destruct H. repeat(destruct H1). *)
                                           (*     destruct H5. destruct H6. destruct H4. apply (IHt0_1 t' x h') in H1. apply (IHt0_2 t' x2 h') in H5. *)
                                           (*     apply disjoint_sym in H1. apply disjoint_sym in H5. apply (union_disjoint H1) in H5. *)
                                           (*     apply (equal_disjoint H7) in H5. clear H1. *)

                                           Lemma test : forall t0, exists h, TreeSpec (label t0) h.
                                           Proof.
                                             induction t0.
                                             * exists empty. simpl. red. reflexivity.
                                             * destruct IHt0_1. destruct IHt0_2. simpl.
                                               pose (P := (single_fresh (x \+ x0))). destruct P.
                                               exists (x \+ x0). red.
                                               exists empty (x \+ x0).
                                               split.
                                               ** exists x1. apply red_ref; intuition. apply disjoint_empty.
                                               ** split.
                                                  *** exists x x0. split; intuition. unfold label in *.





                                                      exists empty ( x \+ x0).
                                                      split.
                                               ** apply red_ref; intuition. apply disjoint_empty.
                                               ** split.
                                                  *** exists x x0. split; intuition.



                                                      exists ((singleton x1) \+ x \+ x0). exists x1.
                                                      exists empty ((singleton x1) \+ x \+ x0).
                                                      split.
                                               ** apply red_ref; intuition. apply disjoint_empty.
                                               ** split.
                                                  ***
