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
Require tez.
Require Export syntax_type.

(* source: http://doc.tzalpha.net/whitedoc/michelson.html#xii-full-grammar *)

Section Overloading.

(* Boolean binary opertations (OR, XOR, AND) are overloaded as bitwise operations for nat. *)
Inductive bitwise_variant : type -> Set :=
| Bitwise_variant_bool : bitwise_variant bool
| Bitwise_variant_nat : bitwise_variant nat.
Structure bitwise_struct (a : type) :=
  Mk_bitwise { bitwise_variant_field : bitwise_variant a }.
Canonical Structure bitwise_bool : bitwise_struct bool := {| bitwise_variant_field := Bitwise_variant_bool |}.
Canonical Structure bitwise_nat : bitwise_struct nat := {| bitwise_variant_field := Bitwise_variant_nat |}.

Set Warnings "-redundant-canonical-projection".

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
Canonical Structure update_map key val :=
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
Inductive chain_id_constant : Set := Mk_chain_id : str -> chain_id_constant.

Module Type ContractContext.
  Parameter get_contract_type : contract_constant -> Datatypes.option type.
End ContractContext.

Module Syntax(C:ContractContext).

Inductive elt_pair (a b : Set) : Set :=
| Elt : a -> b -> elt_pair a b.


Inductive instruction :
  forall (self_type : Datatypes.option type) (tail_fail_flag : Datatypes.bool) (A B : Datatypes.list type), Set :=
| NOOP {self_type A} : instruction self_type Datatypes.false A A    (* Undocumented *)
| FAILWITH {self_type A B a} : instruction self_type Datatypes.true (a ::: A) B
| SEQ {self_type A B C tff} : instruction self_type Datatypes.false A B -> instruction self_type tff B C -> instruction self_type tff A C
(* The instruction self_type SEQ I C is written "{self_type  I ; C }" in Michelson *)
| IF_ {self_type A B tffa tffb} :
    instruction self_type tffa A B -> instruction self_type tffb A B ->
    instruction self_type (tffa && tffb) (bool ::: A) B
(* "IF" is a reserved keyword in file Coq.Init.Logic because it is
part of the notation "'IF' c1 'then' c2 'else' c3" so we cannot call
this constructor "IF" but we can make a notation for it. *)
| LOOP {self_type A} : instruction self_type Datatypes.false A (bool ::: A) -> instruction self_type Datatypes.false (bool ::: A) A
| LOOP_LEFT {self_type a b A} : instruction self_type Datatypes.false (a :: A) (or a b :: A) ->
                      instruction self_type Datatypes.false (or a b :: A) (b :: A)
| EXEC {self_type a b C} : instruction self_type Datatypes.false (a ::: lambda a b ::: C) (b :: C)
| APPLY {self_type a b c D} {_ : Bool.Is_true (is_packable a)} :
    instruction self_type Datatypes.false (a ::: lambda (pair a b) c ::: D) (lambda b c ::: D)
| DUP {self_type a A} : instruction self_type Datatypes.false (a ::: A) (a ::: a ::: A)
| SWAP {self_type a b A} : instruction self_type Datatypes.false (a ::: b ::: A) (b ::: a ::: A)
| PUSH (a : type) (x : concrete_data a) {self_type A} : instruction self_type Datatypes.false A (a :: A)
| UNIT {self_type A} : instruction self_type Datatypes.false A (unit :: A)
| LAMBDA (a b : type) {self_type A tff} :
    instruction None tff (a :: nil) (b :: nil) ->
    instruction self_type Datatypes.false A (lambda a b :: A)
| EQ {self_type S} : instruction self_type Datatypes.false (int ::: S) (bool ::: S)
| NEQ {self_type S} : instruction self_type Datatypes.false (int ::: S) (bool ::: S)
| LT {self_type S} : instruction self_type Datatypes.false (int ::: S) (bool ::: S)
| GT {self_type S} : instruction self_type Datatypes.false (int ::: S) (bool ::: S)
| LE {self_type S} : instruction self_type Datatypes.false (int ::: S) (bool ::: S)
| GE {self_type S} : instruction self_type Datatypes.false (int ::: S) (bool ::: S)
| OR {self_type b} {s : bitwise_struct b} {S} : instruction self_type Datatypes.false (b ::: b ::: S) (b ::: S)
| AND {self_type b} {s : bitwise_struct b} {S} : instruction self_type Datatypes.false (b ::: b ::: S) (b ::: S)
| XOR {self_type b} {s : bitwise_struct b} {S} : instruction self_type Datatypes.false (b ::: b ::: S) (b ::: S)
| NOT {self_type b} {s : not_struct b} {S} : instruction self_type Datatypes.false (b ::: S) (not_ret_type _ s ::: S)
| NEG {self_type n} {s : neg_struct n} {S} : instruction self_type Datatypes.false (n ::: S) (int ::: S)
| ABS {self_type S} : instruction self_type Datatypes.false (int ::: S) (nat ::: S)
| ISNAT {self_type S} : instruction self_type Datatypes.false (int ::: S) (option nat ::: S)
| INT {self_type S} : instruction self_type Datatypes.false (nat ::: S) (int ::: S)
| ADD {self_type a b} {s : add_struct a b} {S} :
    instruction self_type Datatypes.false (a ::: b ::: S) (add_ret_type _ _ s ::: S)
| SUB {self_type a b} {s : sub_struct a b} {S} :
    instruction self_type Datatypes.false (a ::: b ::: S) (sub_ret_type _ _ s ::: S)
| MUL {self_type a b} {s : mul_struct a b} {S} :
    instruction self_type Datatypes.false (a ::: b ::: S) (mul_ret_type _ _ s ::: S)
| EDIV {self_type a b} {s : ediv_struct a b} {S} : instruction self_type Datatypes.false (a ::: b ::: S) (option (pair (ediv_quo_type _ _ s) (ediv_rem_type _ _ s)) :: S)
| LSL {self_type S} : instruction self_type Datatypes.false (nat ::: nat ::: S) (nat ::: S)
| LSR {self_type S} : instruction self_type Datatypes.false (nat ::: nat ::: S) (nat ::: S)
| COMPARE {self_type} {a : comparable_type} {S} : instruction self_type Datatypes.false (a ::: a ::: S) (int ::: S)
| CONCAT {self_type a} {i : stringlike_struct a} {S} : instruction self_type Datatypes.false (a ::: a ::: S) (a ::: S)
| SIZE {self_type a} {i : size_struct a} {S} :
    instruction self_type Datatypes.false (a ::: S) (nat ::: S)
| SLICE {self_type a} {i : stringlike_struct a} {S} :
    instruction self_type Datatypes.false (nat ::: nat ::: a ::: S) (option a ::: S)
| PAIR {self_type a b S} : instruction self_type Datatypes.false (a ::: b ::: S) (pair a b :: S)
| CAR {self_type a b S} : instruction self_type Datatypes.false (pair a b :: S) (a :: S)
| CDR {self_type a b S} : instruction self_type Datatypes.false (pair a b :: S) (b :: S)
| EMPTY_SET elt {self_type S} : instruction self_type Datatypes.false S (set elt ::: S)
| MEM {self_type elt a} {i : mem_struct elt a} {S} :
    instruction self_type Datatypes.false (elt ::: a ::: S) (bool ::: S)
| UPDATE {self_type elt val collection} {i : update_struct elt val collection} {S} :
    instruction self_type Datatypes.false (elt ::: val ::: collection ::: S) (collection ::: S)
| ITER {self_type collection} {i : iter_struct collection} {A} :
    instruction self_type Datatypes.false (iter_elt_type _ i ::: A) A -> instruction self_type Datatypes.false (collection :: A) A
| EMPTY_MAP (key : comparable_type) (val : type) {self_type S} :
    instruction self_type Datatypes.false S (map key val :: S)
| GET {self_type key collection} {i : get_struct key collection} {S} :
    instruction self_type Datatypes.false (key ::: collection ::: S) (option (get_val_type _ _ i) :: S)
| MAP {self_type collection b} {i : map_struct collection b} {A} :
    instruction self_type Datatypes.false (map_in_type _ _ i :: A) (b :: A) ->
    instruction self_type Datatypes.false (collection :: A) (map_out_collection_type _ _ i :: A)
| SOME {self_type a S} : instruction self_type Datatypes.false (a :: S) (option a :: S)
| NONE (a : type) {self_type S} : instruction self_type Datatypes.false S (option a :: S)
(* Not the one documented, see https://gitlab.com/tezos/tezos/issues/471 *)
| IF_NONE {self_type a A B tffa tffb} :
    instruction self_type tffa A B -> instruction self_type tffb (a :: A) B ->
    instruction self_type (tffa && tffb) (option a :: A) B
| LEFT {self_type a} (b : type) {S} : instruction self_type Datatypes.false (a :: S) (or a b :: S)
| RIGHT (a : type) {self_type b S} : instruction self_type Datatypes.false (b :: S) (or a b :: S)
| IF_LEFT {self_type a b A B tffa tffb} :
    instruction self_type tffa (a :: A) B ->
    instruction self_type tffb (b :: A) B ->
    instruction self_type (tffa && tffb) (or a b :: A) B
| IF_RIGHT {self_type a b A B tffa tffb} :
    instruction self_type tffa (b :: A) B ->
    instruction self_type tffb (a :: A) B ->
    instruction self_type (tffa && tffb) (or a b :: A) B
| CONS {self_type a S} : instruction self_type Datatypes.false (a ::: list a ::: S) (list a :: S)
| NIL (a : type) {self_type S} : instruction self_type Datatypes.false S (list a :: S)
| IF_CONS {self_type a A B tffa tffb} :
    instruction self_type tffa (a ::: list a ::: A) B ->
    instruction self_type tffb A B ->
    instruction self_type (tffa && tffb) (list a :: A) B
| CREATE_CONTRACT {self_type S tff} (g p : type) :
    instruction (Some p) tff (pair p g :: nil) (pair (list operation) g :: nil) ->
    instruction self_type Datatypes.false
                (option key_hash ::: mutez ::: g ::: S)
                (operation ::: address ::: S)
| TRANSFER_TOKENS {self_type p S} :
    instruction self_type Datatypes.false (p ::: mutez ::: contract p ::: S) (operation ::: S)
| SET_DELEGATE {self_type S} :
    instruction self_type Datatypes.false (option key_hash ::: S) (operation ::: S)
| BALANCE {self_type S} : instruction self_type Datatypes.false S (mutez ::: S)
| ADDRESS {self_type p S} : instruction self_type Datatypes.false (contract p ::: S) (address ::: S)
| CONTRACT {self_type S} p : instruction self_type Datatypes.false (address ::: S) (option (contract p) ::: S)
(* Mistake in the doc: the return type must be an option *)
| SOURCE {self_type S} : instruction self_type Datatypes.false S (address ::: S)
| SENDER {self_type S} : instruction self_type Datatypes.false S (address ::: S)
| SELF {self_type S} : instruction (Some self_type) Datatypes.false S (contract self_type :: S)
(* p should be the current parameter type *)
| AMOUNT {self_type S} : instruction self_type Datatypes.false S (mutez ::: S)
| IMPLICIT_ACCOUNT {self_type S} : instruction self_type Datatypes.false (key_hash ::: S) (contract unit :: S)
| NOW {self_type S} : instruction self_type Datatypes.false S (timestamp ::: S)
| PACK {self_type a S} : instruction self_type Datatypes.false (a ::: S) (bytes ::: S)
| UNPACK a {self_type S} : instruction self_type Datatypes.false (bytes ::: S) (option a ::: S)
| HASH_KEY {self_type S} : instruction self_type Datatypes.false (key ::: S) (key_hash ::: S)
| BLAKE2B {self_type S} : instruction self_type Datatypes.false (bytes ::: S) (bytes ::: S)
| SHA256 {self_type S} : instruction self_type Datatypes.false (bytes ::: S) (bytes ::: S)
| SHA512 {self_type S} : instruction self_type Datatypes.false (bytes ::: S) (bytes ::: S)
| CHECK_SIGNATURE {self_type S} : instruction self_type Datatypes.false (key ::: signature ::: bytes ::: S) (bool ::: S)
| DIG (n : Datatypes.nat) {self_type S1 S2 t} :
    length S1 = n ->
    instruction self_type Datatypes.false (S1 +++ (t ::: S2)) (t ::: S1 +++ S2)
| DUG (n : Datatypes.nat) {self_type S1 S2 t} :
    length S1 = n ->
    instruction self_type Datatypes.false (t ::: S1 +++ S2) (S1 +++ (t ::: S2))
| DIP (n : Datatypes.nat) {self_type A B C} :
    length A = n ->
    instruction self_type Datatypes.false B C ->
    instruction self_type Datatypes.false (A +++ B) (A +++ C)
| DROP (n : Datatypes.nat) {self_type A B} :
    length A = n ->
    instruction self_type Datatypes.false (A +++ B) B
| CHAIN_ID {self_type S} : instruction self_type Datatypes.false S (chain_id ::: S)

with
concrete_data : type -> Set :=
| Int_constant : Z -> concrete_data int
| Nat_constant : N -> concrete_data nat
| String_constant : String.string -> concrete_data string
| Bytes_constant : String.string -> concrete_data bytes
| Timestamp_constant : Z -> concrete_data timestamp
| Signature_constant : String.string -> concrete_data signature
| Key_constant : String.string -> concrete_data key
| Key_hash_constant : String.string -> concrete_data key_hash
| Mutez_constant : mutez_constant -> concrete_data mutez
| Address_constant : address_constant -> concrete_data address
| Contract_constant {a} : forall cst : contract_constant,
    C.get_contract_type cst = Some a -> concrete_data (contract a)
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
| Instruction {a b} tff : instruction None tff (a ::: nil) (b ::: nil) ->
                          concrete_data (lambda a b)
| Chain_id_constant : chain_id_constant -> concrete_data chain_id.
(* TODO: add the no-ops CAST and RENAME *)

Coercion int_constant := Int_constant.
Coercion nat_constant := Nat_constant.
Coercion string_constant := String_constant.

Definition full_contract param storage :=
  instruction (Some param) Datatypes.false
    ((pair param storage) ::: nil)
    ((pair (list operation) storage) ::: nil).

Notation "'IF'" := (IF_).
Definition stack_type := Datatypes.list type.

Notation "A ;; B" := (SEQ A B) (at level 100, right associativity).

(* For debugging purpose, a version of ;; with explicit stack type *)
Notation "A ;;; S ;;;; B" := (@SEQ _ _ S _ A B) (at level 100, only parsing).

Notation "n ~Mutez" := (exist _ (int64.of_Z n) eq_refl) (at level 100).

Notation "n ~mutez" := (Mutez_constant (Mk_mutez (n ~Mutez))) (at level 100).

(* Dig stuff *)

Lemma nltz : forall n: Datatypes.nat, (n ?= 0) = Lt -> False.
Proof. intros. rewrite Nat.compare_lt_iff in H. omega. Qed.

Lemma lt_S_n : forall n m, (S n ?= S m) = Lt -> (n ?= m) = Lt.
Proof. intros. rewrite Nat.compare_lt_iff in *. omega. Qed.

Fixpoint stacktype_split_dig (l : stack_type) (n : Datatypes.nat) : (n ?= List.length l) = Lt -> (stack_type * type * stack_type) :=
    match l, n with
    | List.nil, _ => (fun pf => match nltz n pf with end)
    | List.cons x tl, 0 => (fun _ => (nil, x, tl))
    | List.cons x xs', S n' => (fun pf => let '(l1, a, l2) := stacktype_split_dig xs' n' (lt_S_n n' (Datatypes.length xs') pf) in (List.cons x l1, a, l2))
    end.

Lemma stacktype_split_dig_size : forall l n H,
    let stack := stacktype_split_dig l n H in
    (l = (List.app (fst (fst stack)) (List.cons (snd (fst stack)) (snd stack))) /\ List.length (fst (fst stack)) = n).
Proof.
  induction l; intros n H; simpl in *.
  - destruct nltz.
  - destruct n.
    + simpl. auto.
    + specialize (IHl _ (lt_S_n _ _ H)).
      destruct (stacktype_split_dig l n (lt_S_n n (length l) H)) as [[l1 t] l2]. simpl in *.
      destruct IHl as [IHl1 IHlen]. subst. auto.
Qed.

Lemma length_app_cons_dig : forall n l1 l2 t,
    n = Datatypes.length l1 ->
    n ?= Datatypes.length (l1 +++ t ::: l2) = Lt.
Proof.
  intros n l1 l2 t Hlen.
  rewrite List.app_length. rewrite <- Hlen.
  simpl. rewrite Nat.compare_lt_iff in *. omega.
Qed.

Lemma stacktype_dig_proof_irrelevant : forall l n Hlen1 Hlen2,
    stacktype_split_dig l n Hlen1 = stacktype_split_dig l n Hlen2.
Proof.
  induction l; intros n Hlen1 Hlen2.
  - simpl. specialize (nltz _ Hlen1) as Hfalse. inversion Hfalse.
  - simpl. destruct n. reflexivity.
    erewrite IHl. erewrite IHl at 2. eauto.
Qed.

Lemma stacktype_split_dig_exact : forall l1 l2 t n (Hlen : n = Datatypes.length l1),
    stacktype_split_dig (l1+++t:::l2) n (length_app_cons_dig _ l1 l2 t Hlen) = (l1, t, l2).
Proof.
  induction l1; intros l2 t n Hlen; simpl.
  - destruct n. reflexivity.
    inversion Hlen.
  - destruct n. inversion Hlen.
    simpl in Hlen; inversion Hlen.
    specialize (IHl1 l2 t n H0).
    specialize (stacktype_dig_proof_irrelevant (l1+++t:::l2) n (length_app_cons_dig n l1 l2 t H0)
                                               (lt_S_n n (Datatypes.length (l1 +++ t ::: l2))
                                                       (length_app_cons_dig (S n) (a ::: l1) l2 t Hlen))) as Hpi.
    rewrite <- Hpi. rewrite IHl1. reflexivity.
Qed.

(* Dug stuff *)

Lemma Snltz {A} : forall n',
    S n' ?= S (@Datatypes.length A nil) = Lt -> False.
Proof.
  intros n' Hlen; simpl in *. rewrite Nat.compare_lt_iff in *. omega.
Qed.

Fixpoint stacktype_split_dug_aux (l : stack_type) (n : Datatypes.nat) : n ?= (S (List.length l)) = Lt -> (stack_type * stack_type) :=
  match l, n with
  | _, 0 => (fun _ => (nil, l))
  | List.nil, S n' => (fun pf => match (Snltz n' pf) with end)
  | List.cons x xs', S n' => (fun pf => let '(l1, l2) := stacktype_split_dug_aux xs' n' (lt_S_n n' (Datatypes.length (x::xs')) pf) in (List.cons x l1, l2))
  end.

Definition stacktype_split_dug (l : stack_type) (n : Datatypes.nat) : n ?= (List.length l) = Lt -> (type * stack_type * stack_type) :=
  match l with
  | nil => (fun pf => match (nltz n pf) with end)
  | List.cons x xs' => (fun pf => let '(l1, l2) := stacktype_split_dug_aux xs' n (lt_S_n n (Datatypes.length (x::xs')) pf) in (x, l1, l2)) 
  end.

Lemma stacktype_split_dug_aux_size : forall l n H,
    let stack := stacktype_split_dug_aux l n H in
    (l = (List.app (fst stack) (snd stack)) /\ List.length (fst stack) = n).
Proof.
  induction l; intros n H; simpl in *.
  - destruct n; simpl in *; auto. destruct Snltz.
  - destruct n.
    + simpl. auto.
    + specialize (IHl _ (lt_S_n _ _ H)).
      destruct (stacktype_split_dug_aux l n (lt_S_n n (S (length l)) H)) as [l1 l2]. simpl in *.
      destruct IHl as [IHl1 IHlen]. subst. auto.
Qed.

Lemma stacktype_dug_aux_proof_irrelevant : forall l n Hlen1 Hlen2,
    stacktype_split_dug_aux l n Hlen1 = stacktype_split_dug_aux l n Hlen2.
Proof.
  induction l; intros n Hlen1 Hlen2.
  - simpl. destruct n.
    reflexivity.
    simpl in Hlen1. destruct Snltz.
  - simpl. destruct n. reflexivity.
    erewrite IHl. erewrite IHl at 2. eauto.
Qed.

Lemma stacktype_dug_proof_irrelevant : forall l n Hlen1 Hlen2,
    stacktype_split_dug l n Hlen1 = stacktype_split_dug l n Hlen2.
Proof.
  intros l n Hlen1 Hlen2.
  destruct l; simpl.
  - destruct nltz.
  - rewrite (stacktype_dug_aux_proof_irrelevant l n (lt_S_n n (S (length l)) Hlen1) (lt_S_n n (S (length l)) Hlen2)).
    reflexivity.
Qed.

Lemma stacktype_split_dug_size : forall l n H,
    let stack := stacktype_split_dug l n H in
    (l = (List.cons (fst (fst stack)) (List.app (snd (fst stack)) (snd stack))) /\ List.length (snd (fst stack)) = n).
Proof.
  destruct l; intros n H; simpl in *.
  - destruct nltz.
  - specialize (stacktype_split_dug_aux_size l n H) as Hsize.
    assert (stacktype_split_dug_aux l n H = stacktype_split_dug_aux l n (lt_S_n n (S (length l)) H)) as Hpi by apply stacktype_dug_aux_proof_irrelevant.
    rewrite <- Hpi. destruct (stacktype_split_dug_aux l n H); simpl in *.
    destruct Hsize. split; f_equal; auto.
Qed.

Lemma length_app_cons_dug : forall n l1 l2,
    n = Datatypes.length l1 ->
    n ?= S (Datatypes.length (l1 +++ l2)) = Lt.
Proof.
  intros n l1 l2 Hlen.
  simpl. rewrite List.app_length. rewrite <- Hlen.
  rewrite Nat.compare_lt_iff.
  omega.
Qed.

Lemma stacktype_split_dug_aux_exact : forall l1 l2 n (Hlen : n = Datatypes.length l1),
    stacktype_split_dug_aux (l1+++l2) n (length_app_cons_dug _ l1 l2 Hlen) = (l1, l2).
Proof.
  induction l1; intros l2 n Hlen; simpl.
  - destruct n. induction l2; reflexivity. 
    inversion Hlen.
  - destruct n. inversion Hlen.
    simpl in Hlen; inversion Hlen.
    specialize (IHl1 l2 n H0).
    inversion Hlen.
    specialize (stacktype_dug_aux_proof_irrelevant (l1+++l2) n (length_app_cons_dug n l1 l2 H0)) as Hpi.
    rewrite <- Hpi. rewrite IHl1. reflexivity.
Qed.

End Syntax.
