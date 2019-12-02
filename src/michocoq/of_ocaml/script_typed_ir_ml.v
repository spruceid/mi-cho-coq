Require Import Coq.Strings.String.
Require Import ZArith.

Local Open Scope type_scope.

Module Tezos_protocol_environment_alpha.
  Module Environment.
    Module Chain_id.
      Parameter t : Type.
    End Chain_id.

    Module MBytes.
      Parameter t : Type.
    End MBytes.

    Module Z.
      Parameter t : Type.
    End Z.
  End Environment.
End Tezos_protocol_environment_alpha.

Module Tezos_raw_protocol_alpha.
  Module Alpha_context.
    Module Contract.
      Parameter big_map_diff : Type.
      Parameter t : Type.
    End Contract.

    Module Script.
      Parameter location : Type.
      Parameter node : Type.
    End Script.

    Module Script_int.
      Parameter n : Type.
      Parameter num : Type -> Type.
      Parameter z : Type.
    End Script_int.

    Module Script_timestamp.
      Parameter t : Type.
    End Script_timestamp.

    Module Tez.
      Parameter t : Type.
    End Tez.

    Parameter packed_internal_operation : Type.
    Parameter public_key : Type.
    Parameter public_key_hash : Type.
    Parameter signature : Type.
  End Alpha_context.
End Tezos_raw_protocol_alpha.

Parameter var_annot : Type.

Parameter type_annot : Type.

Parameter field_annot : Type.

Definition address :=
  Tezos_raw_protocol_alpha.Alpha_context.Contract.t * string.

Definition pair (a b : Type) := a * b.

Inductive union (a b : Type) : Type :=
| L : a -> union a b
| R : b -> union a b.

Arguments L {_ _}.
Arguments R {_ _}.

Inductive comb : Type :=
| Comb : comb.

Inductive leaf : Type :=
| Leaf : leaf.

Inductive comparable_struct : forall (_ _ : Type), Type :=
| Int_key : forall {A : Type}, (option type_annot) ->
  comparable_struct
    (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) A
| Nat_key : forall {A : Type}, (option type_annot) ->
  comparable_struct
    (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) A
| String_key : forall {A : Type}, (option type_annot) ->
  comparable_struct string A
| Bytes_key : forall {A : Type}, (option type_annot) ->
  comparable_struct Tezos_protocol_environment_alpha.Environment.MBytes.t A
| Mutez_key : forall {A : Type}, (option type_annot) ->
  comparable_struct Tezos_raw_protocol_alpha.Alpha_context.Tez.t A
| Bool_key : forall {A : Type}, (option type_annot) -> comparable_struct bool A
| Key_hash_key : forall {A : Type}, (option type_annot) ->
  comparable_struct Tezos_raw_protocol_alpha.Alpha_context.public_key_hash A
| Timestamp_key : forall {A : Type}, (option type_annot) ->
  comparable_struct Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t A
| Address_key : forall {A : Type}, (option type_annot) ->
  comparable_struct address A
| Pair_key : forall {C a b : Type},
  ((comparable_struct a leaf) * (option field_annot)) ->
  ((comparable_struct b C) * (option field_annot)) -> (option type_annot) ->
  comparable_struct (pair a b) comb.

Definition comparable_ty (a : Type) := comparable_struct a comb.

(*Module Boxed_set.
  Record signature {elt OPS_t : Type} := {
    elt := elt;
    elt_ty : comparable_ty elt;
    OPS : S.SET.signature elt OPS_t;
    boxed : OPS.(Tezos_protocol_environment_alpha.Environment.SET.S.t);
    size : Z;
  }.
  Arguments signature : clear implicits.
End Boxed_set.

Definition set (elt : Type) := {OPS_t : _ & Boxed_set.signature elt OPS_t}.*)

Parameter set : Type -> Type.

(*Module Boxed_map.
  Record signature {key value OPS_t : Type} := {
    key := key;
    value := value;
    key_ty : comparable_ty key;
    OPS : S.MAP.signature key OPS_t;
    boxed : (OPS.(Tezos_protocol_environment_alpha.Environment.MAP.S.t) value)
      * Z;
  }.
  Arguments signature : clear implicits.
End Boxed_map.

Definition map (key value : Type) :=
  {OPS_t : _ & Boxed_map.signature key value OPS_t}.*)

Parameter map : Type -> Type -> Type.

Definition operation :=
  Tezos_raw_protocol_alpha.Alpha_context.packed_internal_operation *
    (option Tezos_raw_protocol_alpha.Alpha_context.Contract.big_map_diff).

Reserved Notation "'script".
Reserved Notation "'end_of_stack".
Reserved Notation "'typed_contract".
Reserved Notation "'big_map".
Reserved Notation "'descr".

Record descr_skeleton {loc bef aft instr : Type} := {
  loc : loc;
  bef : bef;
  aft : aft;
  instr_ : instr }.
Arguments descr_skeleton : clear implicits.

Record big_map_skeleton {id diff key_type value_type : Type} := {
  id : id;
  diff : diff;
  key_type : key_type;
  value_type : value_type }.
Arguments big_map_skeleton : clear implicits.

Record script_skeleton {code arg_type storage storage_type root_name : Type} :=
  {
  code : code;
  arg_type : arg_type;
  storage : storage;
  storage_type : storage_type;
  root_name : root_name }.
Arguments script_skeleton : clear implicits.

(*Inductive lambda : forall (arg ret : Type), Type :=
| Lam : forall (arg ret : Type), ('descr (arg * 'end_of_stack) (ret * 'end_of_stack)) ->
Tezos_raw_protocol_alpha.Alpha_context.Script.node -> lambda arg ret*)

Parameter lambda : forall (arg ret : Type), Type.

Polymorphic Inductive Ty : forall (ty : Type), Type :=
| Unit_t : (option type_annot) -> Ty unit
| Int_t : (option type_annot) ->
  Ty
    (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z)
| Nat_t : (option type_annot) ->
  Ty
    (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n)
| Signature_t : (option type_annot) ->
  Ty Tezos_raw_protocol_alpha.Alpha_context.signature
| String_t : (option type_annot) -> Ty string
| Bytes_t : (option type_annot) ->
  Ty Tezos_protocol_environment_alpha.Environment.MBytes.t
| Mutez_t : (option type_annot) ->
  Ty Tezos_raw_protocol_alpha.Alpha_context.Tez.t
| Key_hash_t : (option type_annot) ->
  Ty Tezos_raw_protocol_alpha.Alpha_context.public_key_hash
| Key_t : (option type_annot) ->
  Ty Tezos_raw_protocol_alpha.Alpha_context.public_key
| Timestamp_t : (option type_annot) ->
  Ty Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t
| Address_t : (option type_annot) -> Ty address
| Bool_t : (option type_annot) -> Ty bool
| Pair_t : forall {a b : Type},
  ((Ty a) * (option field_annot) * (option var_annot)) ->
  ((Ty b) * (option field_annot) * (option var_annot)) -> (option type_annot) ->
  bool -> Ty (pair a b)
| Union_t : forall {a b : Type}, ((Ty a) * (option field_annot)) ->
  ((Ty b) * (option field_annot)) -> (option type_annot) -> bool ->
  Ty (union a b)
| Lambda_t : forall {arg ret : Type}, (Ty arg) -> (Ty ret) ->
  (option type_annot) -> Ty (lambda arg ret)
| Option_t : forall {v : Type}, (Ty v) -> (option type_annot) -> bool ->
  Ty (option v)
| List_t : forall {v : Type}, (Ty v) -> (option type_annot) -> bool ->
  Ty (list v)
| Set_t : forall {v : Type}, (comparable_ty v) -> (option type_annot) ->
  Ty (set v)
| Map_t : forall {k v : Type}, (comparable_ty k) -> (Ty v) ->
  (option type_annot) -> bool -> Ty (map k v)
(*| Big_map_t : forall {k v : Type}, (comparable_ty k) -> (Ty v) ->
  (option type_annot) -> Ty ('big_map k v)*)
(*| Contract_t : forall {arg : Type}, (Ty arg) -> (option type_annot) ->
  Ty ('typed_contract arg)*)
| Operation_t : (option type_annot) -> Ty operation
| Chain_id_t : (option type_annot) ->
  Ty Tezos_protocol_environment_alpha.Environment.Chain_id.t

with stack_ty : forall (ty : Type), Type :=
| Item_t : forall {rest ty : Type}, (Ty ty) -> (stack_ty rest) ->
  (option var_annot) -> stack_ty (ty * rest)
| Empty_t : stack_ty 'end_of_stack

with instr : forall (bef aft : Type), Type :=
| Drop : forall {A rest : Type}, instr (A * rest) rest
| Dup : forall {rest top : Type}, instr (top * rest) (top * (top * rest))
| Swap : forall {rest tip top : Type},
  instr (tip * (top * rest)) (top * (tip * rest))
| Const : forall {rest ty : Type}, ty -> instr rest (ty * rest)
| Cons_pair : forall {car cdr rest : Type},
  instr (car * (cdr * rest)) ((pair car cdr) * rest)
| Car : forall {B car rest : Type}, instr ((pair car B) * rest) (car * rest)
| Cdr : forall {A cdr rest : Type}, instr ((pair A cdr) * rest) (cdr * rest)
| Cons_some : forall {rest v : Type}, instr (v * rest) ((option v) * rest)
| Cons_none : forall {a rest : Type}, (Ty a) -> instr rest ((option a) * rest)
| If_none : forall {a aft bef : Type}, ('descr bef aft) ->
  ('descr (a * bef) aft) -> instr ((option a) * bef) aft
| Left : forall {l r rest : Type}, instr (l * rest) ((union l r) * rest)
| Right : forall {l r rest : Type}, instr (r * rest) ((union l r) * rest)
| If_left : forall {aft bef l r : Type}, ('descr (l * bef) aft) ->
  ('descr (r * bef) aft) -> instr ((union l r) * bef) aft
| Cons_list : forall {a rest : Type},
  instr (a * ((list a) * rest)) ((list a) * rest)
| Nil : forall {a rest : Type}, instr rest ((list a) * rest)
| If_cons : forall {a aft bef : Type}, ('descr (a * ((list a) * bef)) aft) ->
  ('descr bef aft) -> instr ((list a) * bef) aft
| List_map : forall {a b rest : Type}, ('descr (a * rest) (b * rest)) ->
  instr ((list a) * rest) ((list b) * rest)
| List_iter : forall {a rest : Type}, ('descr (a * rest) rest) ->
  instr ((list a) * rest) rest
| List_size : forall {a rest : Type},
  instr ((list a) * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Empty_set : forall {a rest : Type}, (comparable_ty a) ->
  instr rest ((set a) * rest)
| Set_iter : forall {a rest : Type}, ('descr (a * rest) rest) ->
  instr ((set a) * rest) rest
| Set_mem : forall {elt rest : Type},
  instr (elt * ((set elt) * rest)) (bool * rest)
| Set_update : forall {elt rest : Type},
  instr (elt * (bool * ((set elt) * rest))) ((set elt) * rest)
| Set_size : forall {a rest : Type},
  instr ((set a) * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Empty_map : forall {a rest v : Type}, (comparable_ty a) -> (Ty v) ->
  instr rest ((map a v) * rest)
| Map_map : forall {a r rest v : Type}, ('descr ((a * v) * rest) (r * rest)) ->
  instr ((map a v) * rest) ((map a r) * rest)
| Map_iter : forall {a rest v : Type}, ('descr ((a * v) * rest) rest) ->
  instr ((map a v) * rest) rest
| Map_mem : forall {a rest v : Type},
  instr (a * ((map a v) * rest)) (bool * rest)
| Map_get : forall {a rest v : Type},
  instr (a * ((map a v) * rest)) ((option v) * rest)
| Map_update : forall {a rest v : Type},
  instr (a * ((option v) * ((map a v) * rest))) ((map a v) * rest)
| Map_size : forall {a b rest : Type},
  instr ((map a b) * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
(*| Empty_big_map : forall {a rest v : Type}, (comparable_ty a) -> (Ty v) ->
  instr rest (('big_map a v) * rest)
| Big_map_mem : forall {a rest v : Type},
  instr (a * (('big_map a v) * rest)) (bool * rest)
| Big_map_get : forall {a rest v : Type},
  instr (a * (('big_map a v) * rest)) ((option v) * rest)
| Big_map_update : forall {key rest value : Type},
  instr (key * ((option value) * (('big_map key value) * rest)))
    (('big_map key value) * rest)*)
| Concat_string : forall {rest : Type},
  instr ((list string) * rest) (string * rest)
| Concat_string_pair : forall {rest : Type},
  instr (string * (string * rest)) (string * rest)
| Slice_string : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * (string * rest)))
    ((option string) * rest)
| String_size : forall {rest : Type},
  instr (string * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Concat_bytes : forall {rest : Type},
  instr ((list Tezos_protocol_environment_alpha.Environment.MBytes.t) * rest)
    (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
| Concat_bytes_pair : forall {rest : Type},
  instr
    (Tezos_protocol_environment_alpha.Environment.MBytes.t *
      (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest))
    (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
| Slice_bytes : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
        (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)))
    ((option Tezos_protocol_environment_alpha.Environment.MBytes.t) * rest)
| Bytes_size : forall {rest : Type},
  instr (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Add_seconds_to_timestamp : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) *
      (Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t * rest))
    (Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t * rest)
| Add_timestamp_to_seconds : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest))
    (Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t * rest)
| Sub_timestamp_seconds : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest))
    (Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t * rest)
| Diff_timestamps : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t *
      (Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Add_tez : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.Tez.t *
      (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest))
    (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest)
| Sub_tez : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.Tez.t *
      (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest))
    (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest)
| Mul_teznat : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.Tez.t *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest)
| Mul_nattez : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest))
    (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest)
| Ediv_teznat : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.Tez.t *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((option
      (pair Tezos_raw_protocol_alpha.Alpha_context.Tez.t
        Tezos_raw_protocol_alpha.Alpha_context.Tez.t)) * rest)
| Ediv_tez : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.Tez.t *
      (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest))
    ((option
      (pair
        (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
          Tezos_raw_protocol_alpha.Alpha_context.Script_int.n)
        Tezos_raw_protocol_alpha.Alpha_context.Tez.t)) * rest)
| Or : forall {rest : Type}, instr (bool * (bool * rest)) (bool * rest)
| And : forall {rest : Type}, instr (bool * (bool * rest)) (bool * rest)
| Xor : forall {rest : Type}, instr (bool * (bool * rest)) (bool * rest)
| Not : forall {rest : Type}, instr (bool * rest) (bool * rest)
| Is_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
    ((option
      (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n)) * rest)
| Neg_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Neg_int : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Abs_int : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Int_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Add_intint : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Add_intnat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Add_natint : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Add_natnat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Sub_int : forall {rest s t : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num s) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num t) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Mul_intint : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Mul_intnat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Mul_natint : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Mul_natnat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Ediv_intint : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest))
    ((option
      (pair
        (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
          Tezos_raw_protocol_alpha.Alpha_context.Script_int.z)
        (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
          Tezos_raw_protocol_alpha.Alpha_context.Script_int.n))) * rest)
| Ediv_intnat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((option
      (pair
        (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
          Tezos_raw_protocol_alpha.Alpha_context.Script_int.z)
        (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
          Tezos_raw_protocol_alpha.Alpha_context.Script_int.n))) * rest)
| Ediv_natint : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest))
    ((option
      (pair
        (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
          Tezos_raw_protocol_alpha.Alpha_context.Script_int.z)
        (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
          Tezos_raw_protocol_alpha.Alpha_context.Script_int.n))) * rest)
| Ediv_natnat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((option
      (pair
        (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
          Tezos_raw_protocol_alpha.Alpha_context.Script_int.n)
        (Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
          Tezos_raw_protocol_alpha.Alpha_context.Script_int.n))) * rest)
| Lsl_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Lsr_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Or_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| And_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| And_int_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Xor_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) *
      ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Not_nat : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Not_int : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Seq : forall {aft bef trans : Type}, ('descr bef trans) -> ('descr trans aft)
  -> instr bef aft
| If : forall {aft bef : Type}, ('descr bef aft) -> ('descr bef aft) ->
  instr (bool * bef) aft
| Loop : forall {rest : Type}, ('descr rest (bool * rest)) ->
  instr (bool * rest) rest
| Loop_left : forall {a b rest : Type}, ('descr (a * rest) ((union a b) * rest))
  -> instr ((union a b) * rest) (b * rest)
| Dip : forall {aft bef top : Type}, ('descr bef aft) ->
  instr (top * bef) (top * aft)
| Exec : forall {arg rest ret : Type},
  instr (arg * ((lambda arg ret) * rest)) (ret * rest)
| Apply : forall {arg remaining rest ret : Type}, (Ty arg) ->
  instr (arg * ((lambda (arg * remaining) ret) * rest))
    ((lambda remaining ret) * rest)
| Lambda : forall {arg rest ret : Type}, (lambda arg ret) ->
  instr rest ((lambda arg ret) * rest)
| Failwith : forall {a aft rest : Type}, (Ty a) -> instr (a * rest) aft
| Nop : forall {rest : Type}, instr rest rest
| Compare : forall {a rest : Type}, (comparable_ty a) ->
  instr (a * (a * rest))
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest)
| Eq : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest) (bool * rest)
| Neq : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest) (bool * rest)
| Lt : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest) (bool * rest)
| Gt : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest) (bool * rest)
| Le : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest) (bool * rest)
| Ge : forall {rest : Type},
  instr
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.z) * rest) (bool * rest)
(*| Address : forall {A rest : Type},
  instr (('typed_contract A) * rest) (address * rest)*)
(*| Contract : forall {p rest : Type}, (Ty p) -> string ->
  instr (address * rest) ((option ('typed_contract p)) * rest)*)
(*| Transfer_tokens : forall {arg rest : Type},
  instr
    (arg *
      (Tezos_raw_protocol_alpha.Alpha_context.Tez.t *
        (('typed_contract arg) * rest))) (operation * rest)*)
| Create_account : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.public_key_hash *
      ((option Tezos_raw_protocol_alpha.Alpha_context.public_key_hash) *
        (bool * (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest))))
    (operation * (address * rest))
(*| Implicit_account : forall {rest : Type},
  instr (Tezos_raw_protocol_alpha.Alpha_context.public_key_hash * rest)
    (('typed_contract unit) * rest)*)
| Create_contract : forall {g p rest : Type}, (Ty g) -> (Ty p) ->
  (lambda (p * g) ((list operation) * g)) -> (option string) ->
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.public_key_hash *
      ((option Tezos_raw_protocol_alpha.Alpha_context.public_key_hash) *
        (bool *
          (bool * (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * (g * rest))))))
    (operation * (address * rest))
| Create_contract_2 : forall {g p rest : Type}, (Ty g) -> (Ty p) ->
  (lambda (p * g) ((list operation) * g)) -> (option string) ->
  instr
    ((option Tezos_raw_protocol_alpha.Alpha_context.public_key_hash) *
      (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * (g * rest)))
    (operation * (address * rest))
| Set_delegate : forall {rest : Type},
  instr ((option Tezos_raw_protocol_alpha.Alpha_context.public_key_hash) * rest)
    (operation * rest)
| Now : forall {rest : Type},
  instr rest (Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t * rest)
| Balance : forall {rest : Type},
  instr rest (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest)
| Check_signature : forall {rest : Type},
  instr
    (Tezos_raw_protocol_alpha.Alpha_context.public_key *
      (Tezos_raw_protocol_alpha.Alpha_context.signature *
        (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)))
    (bool * rest)
| Hash_key : forall {rest : Type},
  instr (Tezos_raw_protocol_alpha.Alpha_context.public_key * rest)
    (Tezos_raw_protocol_alpha.Alpha_context.public_key_hash * rest)
| Pack : forall {a rest : Type}, (Ty a) ->
  instr (a * rest)
    (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
| Unpack : forall {a rest : Type}, (Ty a) ->
  instr (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
    ((option a) * rest)
| Blake2b : forall {rest : Type},
  instr (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
    (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
| Sha256 : forall {rest : Type},
  instr (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
    (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
| Sha512 : forall {rest : Type},
  instr (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
    (Tezos_protocol_environment_alpha.Environment.MBytes.t * rest)
| Steps_to_quota : forall {rest : Type},
  instr rest
    ((Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.n) * rest)
| Source : forall {rest : Type}, instr rest (address * rest)
| Sender : forall {rest : Type}, instr rest (address * rest)
(*| Self : forall {p rest : Type}, (Ty p) -> string ->
  instr rest (('typed_contract p) * rest)*)
| Amount : forall {rest : Type},
  instr rest (Tezos_raw_protocol_alpha.Alpha_context.Tez.t * rest)
| Dig : forall {aft bef rest x : Type}, Z ->
  (stack_prefix_preservation_witness (x * rest) rest bef aft) ->
  instr bef (x * aft)
| Dug : forall {aft bef rest x : Type}, Z ->
  (stack_prefix_preservation_witness rest (x * rest) bef aft) ->
  instr (x * bef) aft
| Dipn : forall {aft bef faft fbef : Type}, Z ->
  (stack_prefix_preservation_witness fbef faft bef aft) -> ('descr fbef faft) ->
  instr bef aft
| Dropn : forall {C bef rest : Type}, Z ->
  (stack_prefix_preservation_witness rest rest bef C) -> instr bef rest
| ChainId : forall {rest : Type},
  instr rest
    (Tezos_protocol_environment_alpha.Environment.Chain_id.t * rest)

with stack_prefix_preservation_witness : forall
  (bef aft bef_suffix aft_suffix : Type), Type :=
| Prefix : forall {aft bef faft fbef x : Type},
  (stack_prefix_preservation_witness fbef faft bef aft) ->
  stack_prefix_preservation_witness fbef faft (x * bef) (x * aft)
| Rest : forall {aft bef : Type},
  stack_prefix_preservation_witness bef aft bef aft

where "'script" := (fun (arg storage : Type) =>
  script_skeleton (lambda (pair arg storage) (pair (list operation) storage))
    (Ty arg) storage (Ty storage) (option string))
and "'end_of_stack" := (unit)
and "'typed_contract" := (fun (arg : Type) => (Ty arg) * address)
and "'big_map" := (fun (key value : Type) =>
  big_map_skeleton (option Tezos_protocol_environment_alpha.Environment.Z.t)
    (map key (option value)) (Ty key) (Ty value))
and "'descr" := (fun (bef aft : Type) =>
  descr_skeleton Tezos_raw_protocol_alpha.Alpha_context.Script.location
    (stack_ty bef) (stack_ty aft) (instr bef aft)).

Definition script := 'script.
Definition end_of_stack := 'end_of_stack.
Definition typed_contract := 'typed_contract.
Definition big_map := 'big_map.
Definition descr := 'descr.

Inductive ex_big_map : Type :=
| Ex_bm : forall {key value : Type}, (big_map key value) -> ex_big_map.
