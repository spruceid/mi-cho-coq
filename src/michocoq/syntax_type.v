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
| Comparable_type : simple_comparable_type -> type
| key : type
| unit : type
| signature : type
| option : type -> type
| list : type -> type
| set : comparable_type -> type
| contract : type -> type
| operation : type
| pair : type -> type -> type
| or : type -> type -> type
| lambda : type -> type -> type
| map : comparable_type -> type -> type
| big_map : comparable_type -> type -> type
| chain_id : type.

Fixpoint comparable_type_to_type (c : comparable_type) : type :=
  match c with
  | Comparable_type_simple a => Comparable_type a
  | Cpair a b => pair (Comparable_type a) (comparable_type_to_type b)
  end.


Coercion comparable_type_to_type : comparable_type >-> type.
Coercion Comparable_type_simple : simple_comparable_type >-> comparable_type.
(* Coercion Comparable_type : simple_comparable_type >-> type. *)

Fixpoint is_packable (a : type) : Datatypes.bool :=
  match a with
  | operation | big_map _ _ | contract _ => false
  | Comparable_type _ | unit | signature | key | lambda _ _ | set _ | chain_id => true
  | option ty
  | list ty
  | map _ ty => is_packable ty
  | pair a b | or a b => is_packable a && is_packable b
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
