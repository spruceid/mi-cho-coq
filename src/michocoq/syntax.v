(* Open Source License *)
(* Copyright (c) 2019 Nomadic Labs. <contact@nomadic-labs.com> *)

(* Permission is hereby granted, free of charge, to any person obtaining a *)
(* copy of this software and associated documentation files (the "Software"), *)
(* to deal in the Software without restriction, including without limitation *)
(* the rights to use, copy, modify, merge, publish, distribute, sublicense, *)
(* and/or sell copies of the Software, and to permit persons to whom the *)
(* Software is furnished to do so, subject to the following conditions: *)

(* The above copyright notice and this permission notice shall be included *)
(* in all copies or substantial portions of the Software. *)

(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *)
(* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, *)
(* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL *)
(* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *)
(* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING *)
(* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER *)
(* DEALINGS IN THE SOFTWARE. *)


(* Syntax and typing of the Michelson language *)

Require Import ZArith.
Require String.
Require Import ListSet.
Require set map.
Require Import error.
Require tez.

(* source: http://doc.tzalpha.net/whitedoc/michelson.html#xii-full-grammar *)

Inductive comparable_type : Set :=
| string
| nat
| int
| bytes
| bool
| mutez
| address
| key_hash
| timestamp.

Inductive type : Set :=
| Comparable_type : comparable_type -> type
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
| big_map : comparable_type -> type -> type.

Coercion Comparable_type : comparable_type >-> type.

Infix ":::" := (@cons type) (at level 60, right associativity).


Section Overloading.

(* Boolean binary opertations (OR, XOR, AND) are overloaded as bitwise operations for nat. *)
Inductive bitwise_variant : type -> Set :=
| Bitwise_variant_bool : bitwise_variant bool
| Bitwise_variant_nat : bitwise_variant nat.
Structure bitwise_struct (a : type) :=
  Mk_bitwise { bitwise_variant_field : bitwise_variant a }.
Canonical Structure bitwise_bool : bitwise_struct bool := {| bitwise_variant_field := Bitwise_variant_bool |}.
Canonical Structure bitwise_nat : bitwise_struct nat := {| bitwise_variant_field := Bitwise_variant_nat |}.

(* Logical negation is also overloaded for int *)
Inductive not_variant : type -> type -> Set :=
| Not_variant_bool : not_variant bool bool
| Not_variant_nat : not_variant nat int
| Not_variant_int : not_variant int int.
Structure not_struct (a : type) :=
  Mk_not { not_ret_type : type; not_variant_field : not_variant a not_ret_type }.
Canonical Structure not_bool : not_struct bool :=
  {| not_variant_field := Not_variant_bool |}.
Canonical Structure not_nat : not_struct nat :=
  {| not_variant_field := Not_variant_nat |}.
Canonical Structure not_int : not_struct int :=
  {| not_variant_field := Not_variant_int |}.

(* NEG takes either a nat or an int as argument *)
Inductive neg_variant : type -> Set :=
| Neg_variant_nat : neg_variant nat
| Neg_variant_int : neg_variant int.
Structure neg_struct (a : type) := Mk_neg { neg_variant_field : neg_variant a }.
Canonical Structure neg_nat : neg_struct nat :=
  {| neg_variant_field := Neg_variant_nat |}.
Canonical Structure neg_int : neg_struct int :=
  {| neg_variant_field := Neg_variant_int |}.

(* ADD *)
Inductive add_variant : type -> type -> type -> Set :=
| Add_variant_nat_nat : add_variant nat nat nat
| Add_variant_nat_int : add_variant nat int int
| Add_variant_int_nat : add_variant int nat int
| Add_variant_int_int : add_variant int int int
| Add_variant_timestamp_int : add_variant timestamp int timestamp
| Add_variant_int_timestamp : add_variant int timestamp timestamp
| Add_variant_tez_tez : add_variant mutez mutez mutez.
Structure add_struct (a b : type) :=
  Mk_add { add_ret_type : type; add_variant_field : add_variant a b add_ret_type }.
Canonical Structure add_nat_nat : add_struct nat nat :=
  {| add_variant_field := Add_variant_nat_nat |}.
Canonical Structure add_nat_int : add_struct nat int :=
  {| add_variant_field := Add_variant_nat_int |}.
Canonical Structure add_int_nat : add_struct int nat :=
  {| add_variant_field := Add_variant_int_nat |}.
Canonical Structure add_int_int : add_struct int int :=
  {| add_variant_field := Add_variant_int_int |}.
Canonical Structure add_timestamp_int : add_struct timestamp int :=
  {| add_variant_field := Add_variant_timestamp_int |}.
Canonical Structure add_int_timestamp : add_struct int timestamp :=
  {| add_variant_field := Add_variant_int_timestamp |}.
Canonical Structure add_tez_tez : add_struct mutez mutez :=
  {| add_variant_field := Add_variant_tez_tez |}.

(* SUB *)
Inductive sub_variant : type -> type -> type -> Set :=
| Sub_variant_nat_nat : sub_variant nat nat int
| Sub_variant_nat_int : sub_variant nat int int
| Sub_variant_int_nat : sub_variant int nat int
| Sub_variant_int_int : sub_variant int int int
| Sub_variant_timestamp_int : sub_variant timestamp int timestamp
| Sub_variant_timestamp_timestamp : sub_variant timestamp timestamp int
| Sub_variant_tez_tez : sub_variant mutez mutez mutez.
Structure sub_struct (a b : type) :=
  Mk_sub { sub_ret_type : type; sub_variant_field : sub_variant a b sub_ret_type }.
Canonical Structure sub_nat_nat : sub_struct nat nat :=
  {| sub_variant_field := Sub_variant_nat_nat |}.
Canonical Structure sub_nat_int : sub_struct nat int :=
  {| sub_variant_field := Sub_variant_nat_int |}.
Canonical Structure sub_int_nat : sub_struct int nat :=
  {| sub_variant_field := Sub_variant_int_nat |}.
Canonical Structure sub_int_int : sub_struct int int :=
  {| sub_variant_field := Sub_variant_int_int |}.
Canonical Structure sub_timestamp_int : sub_struct timestamp int :=
  {| sub_variant_field := Sub_variant_timestamp_int |}.
Canonical Structure sub_timestamp_timestamp : sub_struct timestamp timestamp :=
  {| sub_variant_field := Sub_variant_timestamp_timestamp |}.
Canonical Structure sub_tez_tez : sub_struct mutez mutez :=
  {| sub_variant_field := Sub_variant_tez_tez |}.

(* MUL *)
Inductive mul_variant : type -> type -> type -> Set :=
| Mul_variant_nat_nat : mul_variant nat nat nat
| Mul_variant_nat_int : mul_variant nat int int
| Mul_variant_int_nat : mul_variant int nat int
| Mul_variant_int_int : mul_variant int int int
| Mul_variant_tez_nat : mul_variant mutez nat mutez
| Mul_variant_nat_tez : mul_variant nat mutez mutez.
Structure mul_struct (a b : type) :=
  Mk_mul { mul_ret_type : type; mul_variant_field : mul_variant a b mul_ret_type }.
Canonical Structure mul_nat_nat : mul_struct nat nat :=
  {| mul_variant_field := Mul_variant_nat_nat |}.
Canonical Structure mul_nat_int : mul_struct nat int :=
  {| mul_variant_field := Mul_variant_nat_int |}.
Canonical Structure mul_int_nat : mul_struct int nat :=
  {| mul_variant_field := Mul_variant_int_nat |}.
Canonical Structure mul_int_int : mul_struct int int :=
  {| mul_variant_field := Mul_variant_int_int |}.
Canonical Structure mul_tez_nat : mul_struct mutez nat :=
  {| mul_variant_field := Mul_variant_tez_nat |}.
Canonical Structure mul_nat_tez : mul_struct nat mutez :=
  {| mul_variant_field := Mul_variant_nat_tez |}.

(* EDIV *)
Inductive ediv_variant : type -> type -> type -> type -> Set :=
| Ediv_variant_nat_nat : ediv_variant nat nat nat nat
| Ediv_variant_nat_int : ediv_variant nat int int nat
| Ediv_variant_int_nat : ediv_variant int nat int nat
| Ediv_variant_int_int : ediv_variant int int int nat
| Ediv_variant_tez_nat : ediv_variant mutez nat mutez mutez
| Ediv_variant_tez_tez : ediv_variant mutez mutez nat mutez.
Structure ediv_struct (a b : type) :=
  Mk_ediv { ediv_quo_type : type; ediv_rem_type : type;
            ediv_variant_field : ediv_variant a b ediv_quo_type ediv_rem_type }.
Canonical Structure ediv_nat_nat : ediv_struct nat nat :=
  {| ediv_variant_field := Ediv_variant_nat_nat |}.
Canonical Structure ediv_nat_int : ediv_struct nat int :=
  {| ediv_variant_field := Ediv_variant_nat_int |}.
Canonical Structure ediv_int_nat : ediv_struct int nat :=
  {| ediv_variant_field := Ediv_variant_int_nat |}.
Canonical Structure ediv_int_int : ediv_struct int int :=
  {| ediv_variant_field := Ediv_variant_int_int |}.
Canonical Structure ediv_tez_nat : ediv_struct mutez nat :=
  {| ediv_variant_field := Ediv_variant_tez_nat |}.
Canonical Structure ediv_tez_tez : ediv_struct mutez mutez :=
  {| ediv_variant_field := Ediv_variant_tez_tez |}.

(* SLICE and CONCAT *)
Inductive stringlike_variant : type -> Set :=
| Stringlike_variant_string : stringlike_variant string
| Stringlike_variant_bytes : stringlike_variant bytes.
Structure stringlike_struct (a : type) :=
  Mk_stringlike { stringlike_variant_field : stringlike_variant a }.
Canonical Structure stringlike_string : stringlike_struct string :=
  {| stringlike_variant_field := Stringlike_variant_string |}.
Canonical Structure stringlike_bytes : stringlike_struct bytes :=
  {| stringlike_variant_field := Stringlike_variant_bytes |}.

(* SIZE *)
Inductive size_variant : type -> Set :=
| Size_variant_set a : size_variant (set a)
| Size_variant_map key val : size_variant (map key val)
| Size_variant_list a : size_variant (list a)
| Size_variant_string : size_variant string
| Size_variant_bytes : size_variant bytes.
Structure size_struct (a : type) :=
  Mk_size { size_variant_field : size_variant a }.
Canonical Structure size_set a : size_struct (set a) :=
  {| size_variant_field := Size_variant_set a |}.
Canonical Structure size_map key val : size_struct (map key val) :=
  {| size_variant_field := Size_variant_map key val |}.
Canonical Structure size_list a : size_struct (list a) :=
  {| size_variant_field := Size_variant_list a |}.
Canonical Structure size_string : size_struct string :=
  {| size_variant_field := Size_variant_string |}.
Canonical Structure size_bytes : size_struct bytes :=
  {| size_variant_field := Size_variant_bytes |}.

(* MEM *)
Inductive mem_variant : comparable_type -> type -> Set :=
| Mem_variant_set a : mem_variant a (set a)
| Mem_variant_map key val : mem_variant key (map key val)
| Mem_variant_bigmap key val : mem_variant key (big_map key val).
Structure mem_struct (key : comparable_type) (a : type) :=
  Mk_mem { mem_variant_field : mem_variant key a }.
Canonical Structure mem_set a : mem_struct a (set a) :=
  {| mem_variant_field := Mem_variant_set a |}.
Canonical Structure mem_map key val : mem_struct key (map key val) :=
  {| mem_variant_field := Mem_variant_map key val |}.
Canonical Structure mem_bigmap key val : mem_struct key (big_map key val) :=
  {| mem_variant_field := Mem_variant_bigmap key val |}.

(* UPDATE *)
Inductive update_variant : comparable_type -> type -> type -> Set :=
| Update_variant_set a : update_variant a bool (set a)
| Update_variant_map key val : update_variant key (option val) (map key val)
| Update_variant_bigmap key val : update_variant key (option val) (big_map key val).
Structure update_struct key val collection :=
  Mk_update { update_variant_field : update_variant key val collection }.
Canonical Structure update_set a : update_struct a bool (set a) :=
  {| update_variant_field := Update_variant_set a |}.
Canonical Structure update_mao key val :=
  {| update_variant_field := Update_variant_map key val |}.
Canonical Structure update_bigmap key val :=
  {| update_variant_field := Update_variant_bigmap key val |}.

(* ITER *)
Inductive iter_variant : type -> type -> Set :=
| Iter_variant_set (a : comparable_type) : iter_variant a (set a)
| Iter_variant_map (key : comparable_type) val : iter_variant (pair key val) (map key val)
| Iter_variant_list a : iter_variant a (list a).
Structure iter_struct collection :=
  Mk_iter { iter_elt_type : type;
            iter_variant_field : iter_variant iter_elt_type collection }.
Canonical Structure iter_set a : iter_struct (set a) :=
  {| iter_variant_field := Iter_variant_set a |}.
Canonical Structure iter_map key val : iter_struct (map key val) :=
  {| iter_variant_field := Iter_variant_map key val |}.
Canonical Structure iter_list a : iter_struct (list a) :=
  {| iter_variant_field := Iter_variant_list a |}.

(* GET *)
Inductive get_variant : comparable_type -> type -> type -> Set :=
| Get_variant_map key val : get_variant key val (map key val)
| Get_variant_bigmap key val : get_variant key val (big_map key val).
Structure get_struct key collection :=
  Mk_get { get_val_type : type;
           get_variant_field : get_variant key get_val_type collection }.
Canonical Structure get_map key val : get_struct key (map key val) :=
  {| get_variant_field := Get_variant_map key val |}.
Canonical Structure get_bigmap key val : get_struct key (big_map key val) :=
  {| get_variant_field := Get_variant_bigmap key val |}.

(* MAP *)
Inductive map_variant : type -> type -> type -> type -> Set :=
| Map_variant_map (key : comparable_type) val b :
    map_variant (pair key val) b (map key val) (map key b)
| Map_variant_list a b :
    map_variant a b (list a) (list b).
Structure map_struct collection b :=
  Mk_map { map_in_type : type; map_out_collection_type : type;
           map_variant_field :
             map_variant map_in_type b collection map_out_collection_type }.
Canonical Structure map_map key val b : map_struct (map key val) b :=
  {| map_variant_field := Map_variant_map key val b |}.
Canonical Structure map_list a b : map_struct (list a) b :=
  {| map_variant_field := Map_variant_list a b |}.

End Overloading.

Definition str := String.string.
Inductive timestamp_constant : Set := Mk_timestamp : str -> timestamp_constant.
Inductive signature_constant : Set := Mk_sig : str -> signature_constant.
Inductive key_constant : Set := Mk_key : str -> key_constant.
Inductive key_hash_constant : Set := Mk_key_hash : str -> key_hash_constant.
Inductive tez_constant : Set := Mk_tez : str -> tez_constant.
Inductive contract_constant : Set := Mk_contract : str -> contract_constant.
Inductive address_constant : Set := Mk_address : str -> address_constant.
Inductive operation_constant : Set := Mk_operation : str -> operation_constant.
Inductive mutez_constant : Set := Mk_mutez : tez.mutez -> mutez_constant.

Section syntax.

Context {get_contract_type : contract_constant -> M type}.


Inductive elt_pair (a b : Set) : Set :=
| Elt : a -> b -> elt_pair a b.

(* The type of the parameter of the current contract *)
Context {self_type : type}.

Inductive instruction : Datatypes.list type -> Datatypes.list type -> Set :=
| NOOP {A} : instruction A A    (* Undocumented *)
| FAILWITH {A B a} : instruction (a ::: A) B
| SEQ {A B C} : instruction A B -> instruction B C -> instruction A C
(* The instruction SEQ I C is written "{ I ; C }" in Michelson *)
| IF_ {A B} : instruction A B -> instruction A B -> instruction (bool ::: A) B
(* "IF" is a reserved keyword in file Coq.Init.Logic because it is
part of the notation "'IF' c1 'then' c2 'else' c3" so we cannot call
this constructor "IF" but we can make a notation for it. *)
| LOOP {A} : instruction A (bool ::: A) -> instruction (bool ::: A) A
| LOOP_LEFT {a b A} : instruction (a :: A) (or a b :: A) ->
                      instruction (or a b :: A) (b :: A)
| DIP {b A C} : instruction A C -> instruction (b :: A) (b :: C)
| EXEC {a b C} : instruction (a ::: lambda a b ::: C) (b :: C)
| DROP {a A} : instruction (a :: A) A
| DUP {a A} : instruction (a ::: A) (a ::: a ::: A)
| SWAP {a b A} : instruction (a ::: b ::: A) (b ::: a ::: A)
| PUSH (a : type) (x : concrete_data a) {A} : instruction A (a :: A)
| UNIT {A} : instruction A (unit :: A)
| LAMBDA (a b : type) {A} : instruction (a :: nil) (b :: nil) ->
                     instruction A (lambda a b :: A)
| EQ {S} : instruction (int ::: S) (bool ::: S)
| NEQ {S} : instruction (int ::: S) (bool ::: S)
| LT {S} : instruction (int ::: S) (bool ::: S)
| GT {S} : instruction (int ::: S) (bool ::: S)
| LE {S} : instruction (int ::: S) (bool ::: S)
| GE {S} : instruction (int ::: S) (bool ::: S)
| OR {b} {s : bitwise_struct b} {S} : instruction (b ::: b ::: S) (b ::: S)
| AND {b} {s : bitwise_struct b} {S} : instruction (b ::: b ::: S) (b ::: S)
| XOR {b} {s : bitwise_struct b} {S} : instruction (b ::: b ::: S) (b ::: S)
| NOT {b} {s : not_struct b} {S} : instruction (b ::: S) (not_ret_type _ s ::: S)
| NEG {n} {s : neg_struct n} {S} : instruction (n ::: S) (int ::: S)
| ABS {S} : instruction (int ::: S) (nat ::: S)
| ADD {a b} {s : add_struct a b} {S} :
    instruction (a ::: b ::: S) (add_ret_type _ _ s ::: S)
| SUB {a b} {s : sub_struct a b} {S} :
    instruction (a ::: b ::: S) (sub_ret_type _ _ s ::: S)
| MUL {a b} {s : mul_struct a b} {S} :
    instruction (a ::: b ::: S) (mul_ret_type _ _ s ::: S)
| EDIV {a b} {s : ediv_struct a b} {S} : instruction (a ::: b ::: S) (option (pair (ediv_quo_type _ _ s) (ediv_rem_type _ _ s)) :: S)
| LSL {S} : instruction (nat ::: nat ::: S) (nat ::: S)
| LSR {S} : instruction (nat ::: nat ::: S) (nat ::: S)
| COMPARE {a : comparable_type} {S} : instruction (a ::: a ::: S) (int ::: S)
| CONCAT {a} {i : stringlike_struct a} {S} : instruction (a ::: a ::: S) (a ::: S)
| SIZE {a} {i : size_struct a} {S} :
    instruction (a ::: S) (nat ::: S)
| SLICE {a} {i : stringlike_struct a} {S} :
    instruction (nat ::: nat ::: a ::: S) (option a ::: S)
| PAIR {a b S} : instruction (a ::: b ::: S) (pair a b :: S)
| CAR {a b S} : instruction (pair a b :: S) (a :: S)
| CDR {a b S} : instruction (pair a b :: S) (b :: S)
| EMPTY_SET elt {S} : instruction S (set elt ::: S)
| MEM {elt a} {i : mem_struct elt a} {S} :
    instruction (elt ::: a ::: S) (bool ::: S)
| UPDATE {elt val collection} {i : update_struct elt val collection} {S} :
    instruction (elt ::: val ::: collection ::: S) (collection ::: S)
| ITER {collection} {i : iter_struct collection} {A} :
    instruction (iter_elt_type _ i ::: A) A -> instruction (collection :: A) A
| EMPTY_MAP (key : comparable_type) (val : type) {S} :
    instruction S (map key val :: S)
| GET {key collection} {i : get_struct key collection} {S} :
    instruction (key ::: collection ::: S) (option (get_val_type _ _ i) :: S)
| MAP {collection b} {i : map_struct collection b} {A} :
    instruction (map_in_type _ _ i :: A) (b :: A) ->
    instruction (collection :: A) (map_out_collection_type _ _ i :: A)
| SOME {a S} : instruction (a :: S) (option a :: S)
| NONE (a : type) {S} : instruction S (option a :: S)
(* Not the one documented, see https://gitlab.com/tezos/tezos/issues/471 *)
| IF_NONE {a A B} :
    instruction A B -> instruction (a :: A) B ->
    instruction (option a :: A) B
| LEFT {a} (b : type) {S} : instruction (a :: S) (or a b :: S)
| RIGHT (a : type) {b S} : instruction (b :: S) (or a b :: S)
| IF_LEFT {a b A B} :
    instruction (a :: A) B ->
    instruction (b :: A) B ->
    instruction (or a b :: A) B
| IF_RIGHT {a b A B} :
    instruction (b :: A) B ->
    instruction (a :: A) B ->
    instruction (or a b :: A) B
| CONS {a S} : instruction (a ::: list a ::: S) (list a :: S)
| NIL (a : type) {S} : instruction S (list a :: S)
| IF_CONS {a A B} :
    instruction (a ::: list a ::: A) B ->
    instruction A B ->
    instruction (list a :: A) B
| CREATE_CONTRACT {p g S} :
    instruction
      (key_hash ::: option key_hash ::: bool ::: bool ::: mutez :::
       lambda (pair p g) (pair (list operation) g) ::: g ::: S)
      (operation ::: address ::: S)
| CREATE_CONTRACT_literal {S} (g p : type) :
    instruction (pair p g :: nil) (pair (list operation) g :: nil) ->
    instruction (key_hash ::: option key_hash ::: bool ::: bool ::: mutez ::: g ::: S)
                (operation ::: address ::: S)
| CREATE_ACCOUNT {S} :
    instruction (key_hash ::: option key_hash ::: bool ::: mutez ::: S)
                (operation ::: contract unit ::: S)
| TRANSFER_TOKENS {p S} :
    instruction (p ::: mutez ::: contract p ::: S) (operation ::: S)
| SET_DELEGATE {S} :
    instruction (option key_hash ::: S) (operation ::: S)
| BALANCE {S} : instruction S (mutez ::: S)
| ADDRESS {p S} : instruction (contract p ::: S) (address ::: S)
| CONTRACT {S} p : instruction (address ::: S) (option (contract p) ::: S)
(* Mistake in the doc: the return type must be an option *)
| SOURCE {S} : instruction S (address ::: S)
| SENDER {S} : instruction S (address ::: S)
| SELF {S} : instruction S (contract self_type :: S)
(* p should be the current parameter type *)
| AMOUNT {S} : instruction S (mutez ::: S)
| IMPLICIT_ACCOUNT {S} : instruction (key_hash ::: S) (contract unit :: S)
| STEPS_TO_QUOTA {S} : instruction S (nat ::: S)
| NOW {S} : instruction S (timestamp ::: S)
| PACK {a S} : instruction (a ::: S) (bytes ::: S)
| UNPACK {a S} : instruction (bytes ::: S) (option a ::: S)
| HASH_KEY {S} : instruction (key ::: S) (key_hash ::: S)
| BLAKE2B {S} : instruction (bytes ::: S) (bytes ::: S)
| SHA256 {S} : instruction (bytes ::: S) (bytes ::: S)
| SHA512 {S} : instruction (bytes ::: S) (bytes ::: S)
| CHECK_SIGNATURE {S} : instruction (key ::: signature ::: bytes ::: S) (bool ::: S)

with
concrete_data : type -> Set :=
| Int_constant : Z -> concrete_data int
| Nat_constant : N -> concrete_data nat
| String_constant : String.string -> concrete_data string
| Timestamp_constant : Z -> concrete_data timestamp
| Signature_constant : String.string -> concrete_data signature
| Key_constant : String.string -> concrete_data key
| Key_hash_constant : String.string -> concrete_data key_hash
| Mutez_constant : mutez_constant -> concrete_data mutez
| Contract_constant {a} : forall cst : contract_constant,
    get_contract_type cst = Return _ a -> concrete_data (contract a)
| Unit : concrete_data unit
| True_ : concrete_data bool
| False_ : concrete_data bool
| Pair {a b : type} : concrete_data a -> concrete_data b -> concrete_data (pair a b)
| Left {a b : type} : concrete_data a -> concrete_data (or a b)
| Right {a b : type} : concrete_data b -> concrete_data (or a b)
| Some_ {a : type} : concrete_data a -> concrete_data (option a)
| None_ {a : type} : concrete_data (option a)
| Concrete_list {a} : Datatypes.list (concrete_data a) -> concrete_data (list a)
| Concrete_set {a : comparable_type} :
    Datatypes.list (concrete_data a) -> concrete_data (set a)
| Concrete_map {a : comparable_type} {b} :
    Datatypes.list (elt_pair (concrete_data a) (concrete_data b)) ->
    concrete_data (map a b)
| Instruction {a b} : instruction (a ::: nil) (b ::: nil) ->
                      concrete_data (lambda a b).
(* TODO: add the no-ops CAST and RENAME *)


Coercion int_constant := Int_constant.
Coercion nat_constant := Nat_constant.
Coercion string_constant := String_constant.

End syntax.

Definition full_contract {get_contract_type} params storage :=
  @instruction
    get_contract_type
    params
    ((pair params storage) ::: nil)
    ((pair (list operation) storage) ::: nil).

Notation "'IF'" := (IF_).
Definition stack_type := Datatypes.list type.

Notation "A ;; B" := (SEQ A B) (at level 100, right associativity).

(* For debugging purpose, a version of ;; with explicit stack type *)
Notation "A ;;; S ;;;; B" := (@SEQ _ S _ A B) (at level 100, only parsing).
