Require Import Byte List Lia Wf.

Definition bytes := list byte.

Inductive consumed_length (b : bytes) : Type :=
| Consume : forall (n : nat), n <= length b -> consumed_length b.

Arguments Consume [b].


Definition consume_0 {b} : consumed_length b.
  apply (Consume 0 (le_0_n (length b))).
Defined.

Definition get_nat {b : bytes} (c : consumed_length b) :=
  match c with
  | Consume n _ => n
  end.

Lemma getnat_consume_0 : forall b n, @get_nat b consume_0 <= n.
Proof.
  intros. simpl. lia.
Qed.

Definition bare_parser (X : Type) := forall (b : bytes), option (X * consumed_length b).

Definition parse {X} (p : bare_parser X) (input : bytes) : option (X * consumed_length input) :=
  p input.

Definition ret {X} (x : X) : bare_parser X := fun b => Some (x, consume_0).

Definition parse_empty := ret tt.

Definition hd {X} (l : list X) (_ : l <> nil) : X.
  destruct l. contradiction.
  apply x.
Defined.

Definition tl {X} (l : list X) (_ : l <> nil) : list X.
  destruct l. contradiction.
  apply l.
Defined.

Lemma tl_next : forall X (b : list X) n (pr : b <> nil), S n <= length b -> n <= length (tl b pr).
Proof.
  intros. destruct b. contradiction. simpl in *. lia.
Qed.

Lemma succ_length : forall X (b : list X) n, S n <= length b -> b <> nil.
Proof.
  intros. intro. subst. simpl in H. lia.
Qed.


Fixpoint slice (b : bytes) (i : nat) (j : nat) (_ : i <= j) (_ :j <= length b) : bytes.
  destruct i.
  (* n = 0 *)
  - destruct j eqn:?.
    (*j = 0*)
    + apply nil.
    (* j = S n*)
    + pose H0. apply succ_length in l. eapply tl_next in H0.
      apply (cons (hd b l) (slice (tl b l) 0 n (le_0_n n) H0)).
  (* n := S i*)
  - pose (PeanoNat.Nat.le_trans (S i) j (length b) H H0). apply succ_length in l.
    apply (slice (tl b l) i (pred j)).
    destruct j. inversion H. simpl. apply le_S_n. apply H.
    destruct j. inversion H. simpl. apply tl_next. apply H0.
Defined.

Lemma slice_side : forall b n pr1 pr2,
    length (slice b n (length b) pr1 pr2) = (length b) - n.
Proof.
  induction b.
  - intros. inversion pr1.  simpl in H. subst. simpl. reflexivity.
  - intros. simpl in *. destruct n.
    + simpl in *. f_equal. etransitivity. apply IHb. rewrite Minus.minus_n_O. reflexivity.
    + rewrite IHb. reflexivity.
Qed.

Program Definition and_then {X} (p : bare_parser X) {Y} (p' : X -> bare_parser Y): bare_parser Y :=
  fun (b : bytes) =>
    match p b with
    | Some (v, Consume n pr_n) =>
      let p'v := p' v in
      let s' := slice b n (length b) pr_n (PeanoNat.Nat.le_refl _) in
      match parse p'v s' with
      | Some (v', Consume n' pr_n') =>
        let res : consumed_length b := Consume (n+n') _ in
        Some (v', res)
      | None => None
      end
    | None => None
    end.
Next Obligation.
  pose pr_n'.
  rewrite slice_side in l. lia.
Defined.

Definition fail {X} : bare_parser X := fun _ => None.

Program Definition read_byte : bare_parser byte :=
  fun l => match l with
        | nil => None
        | h :: t => Some (h, Consume 1 _)
        end.
Next Obligation.
  lia.
Defined.

Definition synth {X Y} (p : bare_parser X) (f : X -> Y) : bare_parser Y :=
  fun b => match parse p b with
        | None => None
        | Some (x1, consumed) => Some (f x1, consumed)
        end.

Definition filter {X} (p : bare_parser X) (f : X -> bool) : bare_parser X :=
  fun b => match parse p b with
        | None => None
        | Some (x, consumed) => if f x
                               then Some (x, consumed)
                               else None
        end.

Program Fixpoint plist {X} (p : bare_parser X) (b : bytes) {measure (length b)}: option (list X * consumed_length b) :=
  match b with
  | nil => Some (nil, consume_0)
  | b =>
    match parse p b with
    | None => None
    | Some (v, Consume n pr_n) =>
      match n with
      | 0 => None
      | n =>
        match plist p (slice b n (length b) _ _) with
        | Some (l, Consume n' pr_n') => Some (v :: l, Consume (n + n') _)
        | None => None
        end
      end
    end
  end.
Next Obligation.
  rewrite slice_side. lia.
Qed.
Next Obligation.
  simpl in *. pose pr_n'. rewrite slice_side in l0. lia.
Qed.

Inductive parser_subkind :=
| ParserStrong
| ParserConsumesAll.

Inductive parser_kind_metadata_some :=
| ParserKindMetadataTotal
| ParserKindMetadataFail.

Definition parser_kind_metadata_t := option parser_kind_metadata_some.

Record parser_kind' := {
  parser_kind_low : nat;
  parser_kind_high : option nat;
  parser_kind_subkind : option parser_subkind;
  parser_kind_metadata : parser_kind_metadata_t
                      }.

Definition is_Some {X} (x : option X) :=
  match x with
  | None => False
  | Some _ => True
  end.

Definition parser_kind_wf (p : parser_kind') :=
  match parser_kind_high p with
  | None => True
  | Some v => parser_kind_low p <= v
  end.

(* Injectivité *)

Definition injective_precond {X} (p : bare_parser X) (b1 b2 : bytes) : Type :=
  match parse p b1 with
  | None => False
  | Some (v1, Consume n1 pr_n1) =>
    match parse p b2 with
    | None => False
    | Some (v2, Consume n2 pr_n2) =>
      v1 = v2
    end
  end.


Definition injective_postcond {X} (p : bare_parser X) (b1 b2 : bytes) : Type :=
  match parse p b1 with
  | None => False
  | Some (v1, Consume n1 pr_n1) =>
    match parse p b2 with
    | None => False
    | Some (v2, Consume n2 pr_n2) =>
      n1 = n2 /\ forall v1 v2 v3 v4, slice b1 0 n1 v1 v2 = slice b2 0 n2 v3 v4
    end
  end.

Definition injective {X} (p : bare_parser X) : Type :=
  forall (b1 b2 : bytes), injective_precond p b1 b2 -> injective_postcond p b1 b2.

Inductive parser_kind :=
| Meta : forall (k : parser_kind'), parser_kind_wf k -> parser_kind.

Definition parser_kind_prop {X} (k : parser_kind) (f : bare_parser X) : Type :=
  injective f /\
  (match parser_kind_subkind k with
   | None => True
   |)



Definition Parser (k : parser_kind) (X : Type) : Type :=
Definition Serializer (X : Type) := fun (x : X) => bytes.

Def
Definition serialize {X} (s : Serializer X) :
