Require Import Coqlib Maps Integers Floats Errors Globalenvs.
Require Import AST Linking Values Memory Events.

Record attr : Type := mk_attr {
                          attr_volatile: bool;
                          attr_alignas: option N         (**r log2 of required alignment *)
                        }.

Inductive signedness : Type :=
| Signed: signedness
| Unsigned: signedness.

Inductive intsize : Type :=
| I8: intsize
| I16: intsize
| I32: intsize
| IBool: intsize.

Inductive floatsize : Type :=
| F32: floatsize
| F64: floatsize.

Inductive type : Type :=
| Tvoid: type                                    (**r the [void] type *)
| Tint: intsize -> signedness -> attr -> type    (**r integer types *)
| Tlong: signedness -> attr -> type              (**r 64-bit integer types *)
| Tfloat: floatsize -> attr -> type              (**r floating-point types *)
| Tpointer: type -> attr -> type                 (**r pointer types ([*ty]) *)
| Tarray: type -> Z -> attr -> type              (**r array types ([ty[len]]) *)
| Tfunction: typelist -> type -> calling_convention -> type    (**r function types *)
| Tstruct: ident -> attr -> type                 (**r struct types *)
| Tunion: ident -> attr -> type                  (**r union types *)
with typelist : Type :=
     | Tnil: typelist
     | Tcons: type -> typelist -> typelist.


Inductive expr : Type :=
| Eval (v: val) (ty: type)
| Evar (x: ident) (ty: type)
| Eseqand (r1 r2: expr) (ty: type)
| Econdition (r1 r2 r3: expr) (ty: type)
| Eparen (r: expr) (tycast: type) (ty: type).

Inductive kind : Type := LV | RV.

Inductive context: kind -> kind -> (expr -> expr) -> Prop :=
| ctx_top: forall k,
    context k k (fun x => x)
| ctx_seqand: forall k C r2 ty,
    context k RV C -> context k RV (fun x => Eseqand (C x) r2 ty)
| ctx_condition: forall k C r2 r3 ty,
    context k RV C -> context k RV (fun x => Econdition (C x) r2 r3 ty)
| ctx_paren: forall k C ty tycast,
    context k RV C -> context k RV (fun x => Eparen (C x) tycast ty).

(** Strategy for reducing expressions. We reduce the leftmost innermost
  non-simple subexpression, evaluating its arguments (which are necessarily
  simple expressions) with the big-step semantics.
  If there are none, the whole expression is simple and is evaluated in
  one big step. *)
Definition env := PTree.t block.
Definition empty_env: env := (PTree.empty block).

Section SIMPLE_EXPRS.

  Variable e: env.


  Inductive eval_simple_lvalue: expr -> block -> ptrofs -> Prop :=
  | esl_var_local: forall x b ty,
      e!x = Some b ->
      eval_simple_lvalue (Evar x ty) b Ptrofs.zero.

  Inductive eval_simple_rvalue: expr -> val -> Prop :=
  | esr_val: forall v ty, eval_simple_rvalue (Eval v ty) v.

End SIMPLE_EXPRS.


Inductive state: Type :=
| ExprState                           (**r reduction of an expression *)
    (r: expr)
    (e: env)
    (m: mem) : state.


Inductive classify_bool_cases : Type :=
| bool_case_i                           (**r integer *)
| bool_case_l                           (**r long *)
| bool_case_f                           (**r double float *)
| bool_case_s                           (**r single float *)
| bool_default.

Definition noattr := {| attr_volatile := false; attr_alignas := None |}.

Definition change_attributes (f: attr -> attr) (ty: type) : type :=
  match ty with
  | Tvoid => ty
  | Tint sz si a => Tint sz si (f a)
  | Tlong si a => Tlong si (f a)
  | Tfloat sz a => Tfloat sz (f a)
  | Tpointer elt a => Tpointer elt (f a)
  | Tarray elt sz a => Tarray elt sz (f a)
  | Tfunction args res cc => ty
  | Tstruct id a => Tstruct id (f a)
  | Tunion id a => Tunion id (f a)
  end.

Definition remove_attributes (ty: type) : type :=
  change_attributes (fun _ => noattr) ty.

Definition typeconv (ty: type) : type :=
  match ty with
  | Tint (I8 | I16 | IBool) _ _ => Tint I32 Signed noattr
  | Tarray t sz a       => Tpointer t noattr
  | Tfunction _ _ _     => Tpointer ty noattr
  | _                   => remove_attributes ty
  end.


Definition classify_bool (ty: type) : classify_bool_cases :=
  match typeconv ty with
  | Tint _ _ _ => bool_case_i
  | Tpointer _ _ => if Archi.ptr64 then bool_case_l else bool_case_i
  | Tfloat F64 _ => bool_case_f
  | Tfloat F32 _ => bool_case_s
  | Tlong _ _ => bool_case_l
  | _ => bool_default
  end.


Definition bool_val (v: val) (t: type) (m: mem) : option bool :=
  match classify_bool t with
  | bool_case_i =>
    match v with
    | Vint n => Some (negb (Int.eq n Int.zero))
    | Vptr b ofs =>
      if Archi.ptr64 then None else
        if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None
    | _ => None
    end
  | bool_case_l =>
    match v with
    | Vlong n => Some (negb (Int64.eq n Int64.zero))
    | Vptr b ofs =>
      if negb Archi.ptr64 then None else
        if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None
    | _ => None
    end
  | bool_case_f =>
    match v with
    | Vfloat f => Some (negb (Float.cmp Ceq f Float.zero))
    | _ => None
    end
  | bool_case_s =>
    match v with
    | Vsingle f => Some (negb (Float32.cmp Ceq f Float32.zero))
    | _ => None
    end
  | bool_default => None
  end.

Definition typeof (a: expr) : type :=
  match a with
  | Evar _ ty => ty
  | Eval _ ty => ty
  | Econdition _ _ _ ty => ty
  | Eseqand _ _ ty => ty
  | Eparen _ _ ty => ty
  end.


Inductive classify_cast_cases : Type :=
  | cast_case_pointer                              (**r between pointer types or intptr_t types *)
  | cast_case_i2i (sz2:intsize) (si2:signedness)   (**r int -> int *)
  | cast_case_f2f                                  (**r double -> double *)
  | cast_case_s2s                                  (**r single -> single *)
  | cast_case_f2s                                  (**r double -> single *)
  | cast_case_s2f                                  (**r single -> double *)
  | cast_case_i2f (si1: signedness)                (**r int -> double *)
  | cast_case_i2s (si1: signedness)                (**r int -> single *)
  | cast_case_f2i (sz2:intsize) (si2:signedness)   (**r double -> int *)
  | cast_case_s2i (sz2:intsize) (si2:signedness)   (**r single -> int *)
  | cast_case_l2l                       (**r long -> long *)
  | cast_case_i2l (si1: signedness)     (**r int -> long *)
  | cast_case_l2i (sz2: intsize) (si2: signedness) (**r long -> int *)
  | cast_case_l2f (si1: signedness)                (**r long -> double *)
  | cast_case_l2s (si1: signedness)                (**r long -> single *)
  | cast_case_f2l (si2:signedness)                 (**r double -> long *)
  | cast_case_s2l (si2:signedness)                 (**r single -> long *)
  | cast_case_i2bool                               (**r int -> bool *)
  | cast_case_l2bool                               (**r long -> bool *)
  | cast_case_f2bool                               (**r double -> bool *)
  | cast_case_s2bool                               (**r single -> bool *)
  | cast_case_struct (id1 id2: ident)              (**r struct -> struct *)
  | cast_case_union  (id1 id2: ident)              (**r union -> union *)
  | cast_case_void                                 (**r any -> void *)
  | cast_case_default.

Lemma intsize_eq: forall (s1 s2: intsize), {s1=s2} + {s1<>s2}.
Proof.
  decide equality.
Defined.

Definition classify_cast (tfrom tto: type) : classify_cast_cases :=
  match tto, tfrom with
  (* To [void] *)
  | Tvoid, _ => cast_case_void
  (* To [_Bool] *)
  | Tint IBool _ _, Tint _ _ _ => cast_case_i2bool
  | Tint IBool _ _, Tlong _ _ => cast_case_l2bool
  | Tint IBool _ _, Tfloat F64 _ => cast_case_f2bool
  | Tint IBool _ _, Tfloat F32 _ => cast_case_s2bool
  | Tint IBool _ _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => 
      if Archi.ptr64 then cast_case_l2bool else cast_case_i2bool
  (* To [int] other than [_Bool] *)
  | Tint sz2 si2 _, Tint _ _ _ =>
      if Archi.ptr64 then cast_case_i2i sz2 si2
      else if intsize_eq sz2 I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
  | Tint sz2 si2 _, Tlong _ _ => cast_case_l2i sz2 si2
  | Tint sz2 si2 _, Tfloat F64 _ => cast_case_f2i sz2 si2
  | Tint sz2 si2 _, Tfloat F32 _ => cast_case_s2i sz2 si2
  | Tint sz2 si2 _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
      if Archi.ptr64 then cast_case_l2i sz2 si2
      else if intsize_eq sz2 I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
  (* To [long] *)
  | Tlong _ _, Tlong _ _ =>
      if Archi.ptr64 then cast_case_pointer else cast_case_l2l
  | Tlong _ _, Tint sz1 si1 _ => cast_case_i2l si1
  | Tlong si2 _, Tfloat F64 _ => cast_case_f2l si2
  | Tlong si2 _, Tfloat F32 _ => cast_case_s2l si2
  | Tlong si2 _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
      if Archi.ptr64 then cast_case_pointer else cast_case_i2l si2
  (* To [float] *)
  | Tfloat F64 _, Tint sz1 si1 _ => cast_case_i2f si1
  | Tfloat F32 _, Tint sz1 si1 _ => cast_case_i2s si1
  | Tfloat F64 _, Tlong si1 _ => cast_case_l2f si1
  | Tfloat F32 _, Tlong si1 _ => cast_case_l2s si1
  | Tfloat F64 _, Tfloat F64 _ => cast_case_f2f
  | Tfloat F32 _, Tfloat F32 _ => cast_case_s2s
  | Tfloat F64 _, Tfloat F32 _ => cast_case_s2f
  | Tfloat F32 _, Tfloat F64 _ => cast_case_f2s
  (* To pointer types *)
  | Tpointer _ _, Tint _ _ _ =>
      if Archi.ptr64 then cast_case_i2l Unsigned else cast_case_pointer
  | Tpointer _ _, Tlong _ _ =>
      if Archi.ptr64 then cast_case_pointer else cast_case_l2i I32 Unsigned
  | Tpointer _ _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => cast_case_pointer
  (* To struct or union types *)
  | Tstruct id2 _, Tstruct id1 _ => cast_case_struct id1 id2
  | Tunion id2 _, Tunion id1 _ => cast_case_union id1 id2
  (* Catch-all *)
  | _, _ => cast_case_default
  end.

Definition cast_int_int (sz: intsize) (sg: signedness) (i: int) : int :=
  match sz, sg with
  | I8, Signed => Int.sign_ext 8 i
  | I8, Unsigned => Int.zero_ext 8 i
  | I16, Signed => Int.sign_ext 16 i
  | I16, Unsigned => Int.zero_ext 16 i
  | I32, _ => i
  | IBool, _ => if Int.eq i Int.zero then Int.zero else Int.one
  end.

Definition cast_int_float (si: signedness) (i: int) : float :=
  match si with
  | Signed => Float.of_int i
  | Unsigned => Float.of_intu i
  end.

Definition cast_float_int (si : signedness) (f: float) : option int :=
  match si with
  | Signed => Float.to_int f
  | Unsigned => Float.to_intu f
  end.

Definition cast_int_single (si: signedness) (i: int) : float32 :=
  match si with
  | Signed => Float32.of_int i
  | Unsigned => Float32.of_intu i
  end.

Definition cast_single_int (si : signedness) (f: float32) : option int :=
  match si with
  | Signed => Float32.to_int f
  | Unsigned => Float32.to_intu f
  end.

Definition cast_int_long (si: signedness) (i: int) : int64 :=
  match si with
  | Signed => Int64.repr (Int.signed i)
  | Unsigned => Int64.repr (Int.unsigned i)
  end.

Definition cast_long_float (si: signedness) (i: int64) : float :=
  match si with
  | Signed => Float.of_long i
  | Unsigned => Float.of_longu i
  end.

Definition cast_long_single (si: signedness) (i: int64) : float32 :=
  match si with
  | Signed => Float32.of_long i
  | Unsigned => Float32.of_longu i
  end.

Definition cast_float_long (si : signedness) (f: float) : option int64 :=
  match si with
  | Signed => Float.to_long f
  | Unsigned => Float.to_longu f
  end.

Definition cast_single_long (si : signedness) (f: float32) : option int64 :=
  match si with
  | Signed => Float32.to_long f
  | Unsigned => Float32.to_longu f
  end.

Definition sem_cast (v: val) (t1 t2: type) (m: mem): option val :=
  match classify_cast t1 t2 with
  | cast_case_pointer =>
      match v with
      | Vptr _ _ => Some v
      | Vint _ => if Archi.ptr64 then None else Some v
      | Vlong _ => if Archi.ptr64 then Some v else None
      | _ => None
      end
  | cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Some (Vint (cast_int_int sz2 si2 i))
      | _ => None
      end
  | cast_case_f2f =>
      match v with
      | Vfloat f => Some (Vfloat f)
      | _ => None
      end
  | cast_case_s2s =>
      match v with
      | Vsingle f => Some (Vsingle f)
      | _ => None
      end
  | cast_case_s2f =>
      match v with
      | Vsingle f => Some (Vfloat (Float.of_single f))
      | _ => None
      end
  | cast_case_f2s =>
      match v with
      | Vfloat f => Some (Vsingle (Float.to_single f))
      | _ => None
      end
  | cast_case_i2f si1 =>
      match v with
      | Vint i => Some (Vfloat (cast_int_float si1 i))
      | _ => None
      end
  | cast_case_i2s si1 =>
      match v with
      | Vint i => Some (Vsingle (cast_int_single si1 i))
      | _ => None
      end
  | cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
          match cast_float_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_s2i sz2 si2 =>
      match v with
      | Vsingle f =>
          match cast_single_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_i2bool =>
      match v with
      | Vint n =>
          Some(Vint(if Int.eq n Int.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some Vone else None
      | _ => None
      end
  | cast_case_l2bool =>
      match v with
      | Vlong n =>
          Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if negb Archi.ptr64 then None else
          if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some Vone else None

      | _ => None
      end
  | cast_case_f2bool =>
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_s2bool =>
      match v with
      | Vsingle f =>
          Some(Vint(if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_l2l =>
      match v with
      | Vlong n => Some (Vlong n)
      | _ => None
      end
  | cast_case_i2l si =>
      match v with
      | Vint n => Some(Vlong (cast_int_long si n))
      | _ => None
      end
  | cast_case_l2i sz si =>
      match v with
      | Vlong n => Some(Vint (cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => None
      end
  | cast_case_l2f si1 =>
      match v with
      | Vlong i => Some (Vfloat (cast_long_float si1 i))
      | _ => None
      end
  | cast_case_l2s si1 =>
      match v with
      | Vlong i => Some (Vsingle (cast_long_single si1 i))
      | _ => None
      end
  | cast_case_f2l si2 =>
      match v with
      | Vfloat f =>
          match cast_float_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_s2l si2 =>
      match v with
      | Vsingle f =>
          match cast_single_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_struct id1 id2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end
  | cast_case_union id1 id2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end
  | cast_case_void =>
      Some v
  | cast_case_default =>
      None
  end.

Definition type_int32s := Tint I32 Signed noattr.

Definition type_bool := Tint IBool Signed noattr.

Inductive estep: state -> trace -> state -> Prop :=
| step_expr: forall r e m v ty,
    eval_simple_rvalue r v ->
    match r with Eval _ _ => False | _ => True end ->
    ty = typeof r ->
    estep (ExprState r e m)
          E0 (ExprState (Eval v ty) e m)
| step_seqand_true: forall C r1 r2 ty e m v,
    context RV RV C ->
    eval_simple_rvalue r1 v ->
    bool_val v (typeof r1) m = Some true ->
    estep (ExprState (C (Eseqand r1 r2 ty)) e m)
          E0 (ExprState (C (Eparen r2 type_bool ty)) e m)
| step_seqand_false: forall C r1 r2 ty e m v,
    context RV RV C ->
    eval_simple_rvalue r1 v ->
    bool_val v (typeof r1) m = Some false ->
    estep (ExprState (C (Eseqand r1 r2 ty)) e m)
          E0 (ExprState (C (Eval (Vint Int.zero) ty)) e m)
| step_condition: forall C r1 r2 r3 ty e m v b,
    context RV RV C ->
    eval_simple_rvalue r1 v ->
    bool_val v (typeof r1) m = Some b ->
    estep (ExprState (C (Econdition r1 r2 r3 ty)) e m)
          E0 (ExprState (C (Eparen (if b then r2 else r3) ty ty)) e m)
| step_paren: forall C r tycast ty e m v1 v,
    context RV RV C ->
    eval_simple_rvalue r v1 ->
    sem_cast v1 (typeof r) tycast m = Some v ->
    estep (ExprState (C (Eparen r tycast ty)) e m)
          E0 (ExprState (C (Eval v ty)) e m).

