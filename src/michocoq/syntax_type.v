Require String.

Definition annotation := String.string.
Definition annot_o := Datatypes.option annotation.

Module default_entrypoint.
  Import String.

  Definition default : annotation := "%default"%string.

End default_entrypoint.

Inductive simple_comparable_type : Set :=
| string
| nat
| int
| bytes
| bool
| mutez
| address
| key_hash
| timestamp.

Inductive comparable_type : Set :=
| Comparable_type_simple : simple_comparable_type -> comparable_type
| Cpair : simple_comparable_type -> comparable_type -> comparable_type.

Lemma comparable_type_dec (a b : comparable_type) : {a = b} + {a <> b}.
Proof.
  repeat decide equality.
Defined.

Inductive type : Set :=
| Comparable_type (_ : simple_comparable_type)
| key
| unit
| signature
| option (a : type)
| list (a : type)
| set (a : comparable_type)
| contract (a : type)
| operation
| pair (a : type) (b : type)
| or (a : type) (b : type)
| lambda (a b : type)
| map (k : comparable_type) (v : type)
| big_map (k : comparable_type) (v : type)
| chain_id.

Fixpoint comparable_type_to_type (c : comparable_type) : type :=
  match c with
  | Comparable_type_simple a => Comparable_type a
  | Cpair a b => pair (Comparable_type a) (comparable_type_to_type b)
  end.


Coercion comparable_type_to_type : comparable_type >-> type.
Coercion Comparable_type_simple : simple_comparable_type >-> comparable_type.
(* Coercion Comparable_type : simple_comparable_type >-> type. *)

Fixpoint is_pushable (a : type) : Datatypes.bool :=
  match a with
  | operation | big_map _ _ | contract _ => false
  | Comparable_type _ | unit | signature | key | lambda _ _ | set _
  | chain_id => true
  | option ty
  | list ty
  | map _ ty => is_pushable ty
  | pair a b | or a b => is_pushable a && is_pushable b
  end.

Fixpoint is_passable (a : type) : Datatypes.bool :=
  match a with
  | operation => false
  | Comparable_type _ | unit | signature | key | lambda _ _ | set _
  | chain_id | contract _ => true
  | option ty
  | list ty
  | map _ ty
  | big_map _ ty => is_passable ty
  | pair a b | or a b => is_passable a && is_passable b
  end.

Fixpoint is_storable (a : type) : Datatypes.bool :=
  match a with
  | operation | contract _ => false
  | Comparable_type _ | unit | signature | key | lambda _ _ | set _
  | chain_id => true
  | option ty
  | list ty
  | map _ ty
  | big_map _ ty => is_storable ty
  | pair a b | or a b => is_storable a && is_storable b
  end.

Fixpoint is_packable (a : type) : Datatypes.bool :=
  match a with
  | operation | big_map _ _=> false
  | Comparable_type _ | unit | signature | key | lambda _ _ | set _
  | contract _
  | chain_id => true
  | option ty
  | list ty
  | map _ ty => is_packable ty
  | pair a b | or a b => is_packable a && is_packable b
  end.

Fixpoint is_big_map_value (a : type) : Datatypes.bool :=
  match a with
  | operation | big_map _ _=> false
  | Comparable_type _ | unit | signature | key | lambda _ _ | set _
  | contract _
  | chain_id => true
  | option ty
  | list ty
  | map _ ty => is_big_map_value ty
  | pair a b | or a b => is_big_map_value a && is_big_map_value b
  end.

Lemma type_dec (a b : type) : {a = b} + {a <> b}.
Proof.
  repeat decide equality.
Defined.

Lemma stype_dec (A B : Datatypes.list type) : {A = B} + {A <> B}.
Proof.
  decide equality; apply type_dec.
Defined.

Infix ":::" := (@cons type) (at level 60, right associativity).
Infix "+++" := (@app type) (at level 60, right associativity).
