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


(* Operational semantics of the Michelson language *)

Require Import ZArith.
Require Import String.
Require Import syntax macros.
Require NPeano.

Require Import comparable error.
Import error.Notations.

Module Type SelfType.
  Parameter self_type : type.
End SelfType.

Module EnvDef(C:ContractContext).
  Export C.
  Module macros := Macros(C). Export macros.
  Fixpoint data (a : type) {struct a} : Set :=
    match a with
    | Comparable_type b => comparable_data b
    | signature => signature_constant
    | operation => operation_constant
    | key => key_constant
    | unit => Datatypes.unit
    | pair a b => data a * data b
    | or a b => sum (data a) (data b)
    | option a => Datatypes.option (data a)
    | list a => Datatypes.list (data a)
    | set a => set.set (comparable_data a) (compare a)
    | map a b => map.map (comparable_data a) (data b) (compare a)
    | big_map a b => map.map (comparable_data a) (data b) (compare a)
    | lambda a b =>
      {tff : Datatypes.bool &
             instruction None tff (a ::: nil) (b ::: nil)}
    | contract a => {s : contract_constant | get_contract_type s = Some a }
    | chain_id => chain_id_constant
    end.

  Record proto_env {self_ty : Datatypes.option type} : Set :=
    mk_proto_env
      {
        create_contract : forall g p tff,
          Datatypes.option (comparable_data key_hash) ->
          tez.mutez ->
          syntax.instruction (Some p) tff
                             (pair p g ::: nil)
                             (pair (list operation) g ::: nil) ->
          data g -> data (pair operation address);
        transfer_tokens : forall p,
            data p -> tez.mutez -> data (contract p) ->
            data operation;
        set_delegate : Datatypes.option (comparable_data key_hash) ->
                       data operation;
        balance : tez.mutez;
        address_ : forall p, data (contract p) -> data address;
        contract_ : forall p, data address -> data (option (contract p));
        source : data address;
        sender : data address;
        self : match self_ty with
               | None => Datatypes.unit
               | Some self_ty => data (contract self_ty)
               end;
        amount : tez.mutez;
        implicit_account :
          comparable_data key_hash -> data (contract unit);
        now : comparable_data timestamp;
        hash_key : data key -> comparable_data key_hash;
        pack : forall a, data a -> data bytes;
        unpack : forall a, data bytes -> data (option a);
        blake2b : data bytes -> data bytes;
        sha256 : data bytes -> data bytes;
        sha512 : data bytes -> data bytes;
        check_signature :
          data key -> data signature -> data bytes -> data bool;
        chain_id_ : data chain_id
      }.

  Definition no_self {self_type} (e : proto_env (self_ty := self_type)) :
    proto_env (self_ty := None) :=
    mk_proto_env None
                 (create_contract e)
                 (transfer_tokens e)
                 (set_delegate e)
                 (balance e)
                 (address_ e)
                 (contract_ e)
                 (source e)
                 (sender e)
                 tt
                 (amount e)
                 (implicit_account e)
                 (now e)
                 (hash_key e)
                 (pack e)
                 (unpack e)
                 (blake2b e)
                 (sha256 e)
                 (sha512 e)
                 (check_signature e)
                 (chain_id_ e).

End EnvDef.

Module Type Env(ST : SelfType)(C:ContractContext).
  Include EnvDef C.
  Parameter env:(@proto_env (Some ST.self_type)).
End Env.

Module Semantics(ST : SelfType)(C:ContractContext)(E:Env ST C).

  Export E.

  Fixpoint stack (t : stack_type) : Set :=
    match t with
    | nil => Datatypes.unit
    | cons a A => data a * stack A
    end.

  (** Stack manipulation *)
  Inductive stack_ind : stack_type -> Set -> Prop :=
  | stack_nil : stack_ind nil Datatypes.unit
  | stack_cons : forall a A S,
      stack_ind A S -> stack_ind (cons a A) (data a * S).

  Lemma stack_iff_stack_ind : forall (t : stack_type) (s : Set),
      stack t = s <-> stack_ind t s.
  Proof.
    intros t.
    induction t; intros s; simpl.
    - split; intros; subst.
      + constructor.
      + inversion H; reflexivity.
    - split; intros; subst.
      + constructor. rewrite <- (IHt (stack t)); reflexivity.
      + inversion H; subst. 
        assert (stack t = S) by (rewrite (IHt S); assumption); subst; reflexivity.
  Qed.

  (* Dig stuff *)

  Definition stack_app {l1} {l2} (S1 : stack l1) (S2 : stack l2) : stack (l1+++l2).
  Proof.
    induction l1; simpl.
    - assumption.
    - inversion S1. split; auto.
  Defined.

  Definition stack_split {l1 l2} (S : stack (l1 +++ l2)) : (stack l1 * stack l2).
  Proof.
    induction l1; simpl.
    - exact (tt, S).
    - simpl in S.
      destruct S as (x, S).
      apply IHl1 in S.
      destruct S as (S1, S2).
      repeat (split; try assumption).
  Defined.

  Definition stack_dig {l1 l2 t} (SA : stack (l1+++t:::l2)) : stack (t:::l1+++l2).
  Proof.
    simpl.
    apply stack_split in SA.
    simpl in SA.
    destruct SA as (S1, (x, S2)).
    refine (x, _).
    apply stack_app; assumption.
  Defined.

  Definition stack_dug {l1 l2 t} (SA : stack (t:::l1+++l2)) : stack (l1+++t:::l2).
  Proof.
    simpl in SA.
    destruct SA as (x, S12).
    apply stack_split in S12.
    destruct S12 as (S1, S2).
    apply stack_app.
    - exact S1.
    - exact (x, S2).
  Defined.

  Fixpoint comparable_data_to_data (a : comparable_type) (x : comparable_data a) : data a :=
    match a, x with
    | Cpair a b, (x, y) => (x, comparable_data_to_data _ y)
    | Comparable_type_simple _, x => x
    end.

  Fixpoint data_to_comparable_data (a : comparable_type) (x : data a) : comparable_data a :=
    match a, x with
    | Cpair a b, (x, y) => (x, data_to_comparable_data _ y)
    | Comparable_type_simple _, x => x
    end.

  Fixpoint concrete_data_to_data (a : type) (d : concrete_data a) : data a :=
    match d with
    | Int_constant x => x
    | Nat_constant x => x
    | String_constant x => x
    | Bytes_constant x => x
    | Timestamp_constant x => x
    | Signature_constant x => Mk_sig x
    | Key_constant x => Mk_key x
    | Key_hash_constant x => Mk_key_hash x
    | Mutez_constant (Mk_mutez x) => x
    | Address_constant x => x
    | @Contract_constant a x H => exist _ x H
    | Unit => tt
    | True_ => true
    | False_ => false
    | Pair a b => (concrete_data_to_data _ a, concrete_data_to_data _ b)
    | Left a => inl (concrete_data_to_data _ a)
    | Right b => inr (concrete_data_to_data _ b)
    | Some_ a => Some (concrete_data_to_data _ a)
    | None_ => None
    | Concrete_list l => List.map (concrete_data_to_data _) l
    | @Concrete_set a l =>
      (fix concrete_data_set_to_data (l : Datatypes.list (concrete_data a)) :=
         match l with
         | nil => set.empty _ _
         | cons x l =>
           set.insert
             (comparable_data a)
             (comparable.compare a)
             (comparable.compare_eq_iff a)
             (comparable.lt_trans a)
             (comparable.gt_trans a)
             (data_to_comparable_data _ (concrete_data_to_data a x))
             (concrete_data_set_to_data l)
         end) l
    | @Concrete_map a b l =>
      (fix concrete_data_map_to_data
           (l : Datatypes.list (elt_pair (concrete_data a) (concrete_data b))) :=
         match l with
         | nil => map.empty _ _ _
         | cons (Elt _ _ x y) l =>
           map.update
             (comparable_data a)
             (data b)
             (comparable.compare a)
             (comparable.compare_eq_iff a)
             (comparable.lt_trans a)
             (comparable.gt_trans a)
             (data_to_comparable_data _ (concrete_data_to_data _ x))
             (Some (concrete_data_to_data _ y))
             (concrete_data_map_to_data l)
         end) l
    | Instruction tff i => existT _ _ i
    | Chain_id_constant x => x
    end.


  Definition simple_comparable_data_to_concrete_data (a : simple_comparable_type) (x : comparable_data a) : concrete_data a :=
    match a, x with
    | int, x => Int_constant x
    | nat, x => Nat_constant x
    | string, x => String_constant x
    | timestamp, x => Timestamp_constant x
    | key_hash, Mk_key_hash y => Key_hash_constant y
    | mutez, x => Mutez_constant (Mk_mutez x)
    | bytes, x => Bytes_constant x
    | address, x => Address_constant x
    | bool, true => True_
    | bool, false => False_
    end.

  Fixpoint comparable_data_to_concrete_data (a : comparable_type) (x : comparable_data a) : concrete_data a :=
    match a, x with
    | Cpair a b, (x, y) => Pair (simple_comparable_data_to_concrete_data a x) (comparable_data_to_concrete_data b y)
    | Comparable_type_simple a, x => simple_comparable_data_to_concrete_data a x
    end.

  Fixpoint data_to_concrete_data (a : type) (H : Is_true (is_packable a)) (x : data a) :
    concrete_data a :=
    match a, H, x with
    | Comparable_type b, _, x => comparable_data_to_concrete_data b x
    | unit, _, tt => Unit
    | signature, _ , Mk_sig y => Signature_constant y
    | key, _, Mk_key y => Key_constant y
    | option _, _, None => None_
    | option a, H, Some y => Some_ (data_to_concrete_data a H y)
    | list a, H, l =>
      Concrete_list (List.map (data_to_concrete_data a H) l)
    | set a, H, exist _ l _ =>
      Concrete_set (List.map (comparable_data_to_concrete_data a) l)
    | map a b, H, exist _ l _ =>
      Concrete_map (List.map (fun '(k, v) =>
                                Elt _
                                    _
                                    (comparable_data_to_concrete_data _ k)
                                    (data_to_concrete_data b H v))
                             l)
    | contract _, H, exist _ x Hx =>
      Contract_constant x Hx
    | operation, H, _ => match H with end
    | big_map _ _, H, _ => match H with end
    | pair a b, H, (x, y) =>
      Pair (data_to_concrete_data a (Is_true_and_left _ _ H) x)
           (data_to_concrete_data b (Is_true_and_right _ _ H) y)
    | or a b, H, inl x =>
      Left (data_to_concrete_data a (Is_true_and_left _ _ H) x)
    | or a b, H, inr x =>
      Right (data_to_concrete_data b (Is_true_and_right _ _ H) x)
    | lambda a b, _, existT _ tff f => Instruction tff f
    | chain_id, _, x => Chain_id_constant x
    end.

  Definition or_fun a (v : bitwise_variant a) : data a -> data a -> data a :=
    match v with
    | Bitwise_variant_bool => orb
    | Bitwise_variant_nat => N.lor
    end.

  Definition and a (v : bitwise_variant a) : data a -> data a -> data a :=
    match v with
    | Bitwise_variant_bool => andb
    | Bitwise_variant_nat => N.land
    end.

  Definition xor a (v : bitwise_variant a) : data a -> data a -> data a :=
    match v with
    | Bitwise_variant_bool => xorb
    | Bitwise_variant_nat => N.lxor
    end.

  Definition not a b (v : not_variant a b) : data a -> data b :=
    match v with
    | Not_variant_bool => negb
    | Not_variant_int => fun x => (- 1 - x)%Z
    | Not_variant_nat => fun x => (- 1 - Z.of_N x)%Z
    end.

  Definition neg a (v : neg_variant a) : data a -> data int :=
    match v with
    | Neg_variant_nat => fun x => (- Z.of_N x)%Z
    | Neg_variant_int => fun x => (- x)%Z
    end.

  Definition add a b c (v : add_variant a b c) : data a -> data b -> M (data c) :=
    match v with
    | Add_variant_nat_nat => fun x y => Return (x + y)%N
    | Add_variant_nat_int => fun x y => Return (Z.of_N x + y)%Z
    | Add_variant_int_nat => fun x y => Return (x + Z.of_N y)%Z
    | Add_variant_int_int => fun x y => Return (x + y)%Z
    | Add_variant_timestamp_int => fun x y => Return (x + y)%Z
    | Add_variant_int_timestamp => fun x y => Return (x + y)%Z
    | Add_variant_tez_tez =>
      fun x y => tez.of_Z (tez.to_Z x + tez.to_Z y)
    end.

  Definition sub a b c (v : sub_variant a b c) : data a -> data b -> M (data c) :=
    match v with
    | Sub_variant_nat_nat => fun x y => Return (Z.of_N x - Z.of_N y)%Z
    | Sub_variant_nat_int => fun x y => Return (Z.of_N x - y)%Z
    | Sub_variant_int_nat => fun x y => Return (x - Z.of_N y)%Z
    | Sub_variant_int_int => fun x y => Return (x - y)%Z
    | Sub_variant_timestamp_int => fun x y => Return (x - y)%Z
    | Sub_variant_timestamp_timestamp => fun x y => Return (x - y)%Z
    | Sub_variant_tez_tez => fun x y => tez.of_Z (tez.to_Z x - tez.to_Z y)
    end.

  Definition mul a b c (v : mul_variant a b c) : data a -> data b -> M (data c) :=
    match v with
    | Mul_variant_nat_nat => fun x y => Return (x * y)%N
    | Mul_variant_nat_int => fun x y => Return (Z.of_N x * y)%Z
    | Mul_variant_int_nat => fun x y => Return (x * Z.of_N y)%Z
    | Mul_variant_int_int => fun x y => Return (x * y)%Z
    | Mul_variant_tez_nat => fun x y => tez.of_Z (tez.to_Z x * Z.of_N y)
    | Mul_variant_nat_tez => fun x y => tez.of_Z (Z.of_N x * tez.to_Z y)
    end.

  Definition ediv_Z x y :=
    if (y =? 0)%Z then None else Some (x / y, Z.to_N (x mod y))%Z.
  Definition ediv_N x y :=
    if (y =? 0)%N then None else Some (x / y, x mod y)%N.

  Definition ediv a b c d (v : ediv_variant a b c d) : data a -> data b -> data (option (pair c d)) :=
    match v with
    | Ediv_variant_nat_nat => fun x y => ediv_N x y
    | Ediv_variant_nat_int => fun x y => ediv_Z (Z.of_N x) y
    | Ediv_variant_int_nat => fun x y => ediv_Z x (Z.of_N y)
    | Ediv_variant_int_int => fun x y => ediv_Z x y
    | Ediv_variant_tez_nat =>
      fun x y =>
        match ediv_Z (tez.to_Z x) (Z.of_N y) with
        | None => None
        | Some (quo, rem) =>
          match tez.of_Z quo, tez.of_Z (Z.of_N rem) with
          | Return quo, Return rem => Some (quo, rem)
          | _, _ => None
          end
        end
    | Ediv_variant_tez_tez =>
      fun x y =>
        match ediv_Z (tez.to_Z x) (tez.to_Z y) with
        | None => None
        | Some (quo, rem) =>
          match tez.of_Z (Z.of_N rem) with
          | Return rem => Some (Z.to_N quo, rem)
          | _ => None
          end
        end
    end.

  Definition concat a (v : stringlike_variant a) : data a -> data a -> data a :=
    match v with
    | Stringlike_variant_string => String.append
    | Stringlike_variant_bytes => String.append
    end.

  Definition empty_stringlike a (v : stringlike_variant a) : data a :=
    match v with
    | Stringlike_variant_string => EmptyString
    | Stringlike_variant_bytes => EmptyString
    end.

  Fixpoint concat_list a (v : stringlike_variant a) (l : data (list a)) : data a :=
    match l with
    | nil => empty_stringlike a v
    | cons x l =>
      concat a v x (concat_list a v l)
    end.

  Definition slice a (v : stringlike_variant a) : data nat -> data nat -> data a -> data (option a) :=
    match v with
    | Stringlike_variant_string =>
      fun (n1 n2 : N) (s : data string) =>
        if (n1 + n2 <=? N.of_nat (String.length s))%N then
          (Some (String.substring (N.to_nat n1) (N.to_nat n2) s)
           : data (option string))
        else None
    | Stringlike_variant_bytes =>
      fun n1 n2 s =>
        if (n1 + n2 <=? N.of_nat (String.length s))%N then
          Some (String.substring (N.to_nat n1) (N.to_nat n2) s)
        else None
    end.

  Definition mem a b (v : mem_variant a b) : comparable_data a -> data b -> data bool :=
    match v with
    | Mem_variant_set a =>
      fun (x : comparable_data a) (y : data (set a)) => set.mem _ _ x y
    | Mem_variant_map _ _ => map.mem _ _ _
    | Mem_variant_bigmap _ _ => map.mem _ _ _
    end.

  Definition update a b c (v : update_variant a b c) :
    comparable_data a -> data b -> data c -> data c :=
    match v with
    | Update_variant_set a =>
      set.update _ _ (compare_eq_iff a) (lt_trans a) (gt_trans a)
    | Update_variant_map k v =>
      map.update _ _ _ (compare_eq_iff k) (lt_trans k) (gt_trans k)
    | Update_variant_bigmap k _ =>
      map.update _ _ _ (compare_eq_iff k) (lt_trans k) (gt_trans k)
    end.

  Definition size a (v : size_variant a) : data a -> Datatypes.nat :=
    match v with
    | Size_variant_list a => fun l => List.length l
    | Size_variant_set a => set.size (comparable_data a) (compare a)
    | Size_variant_map k v => map.size (comparable_data k) (data v) (compare k)
    | Size_variant_string => String.length
    | Size_variant_bytes => String.length
    end.

  Definition iter_destruct a b (v : iter_variant a b)
    : data b -> data (option (pair a b)) :=
    match v with
    | Iter_variant_set _ =>
      fun x =>
        match set.destruct _ _ x with
        | None => None
        | Some (elt, rst) =>
          Some (comparable_data_to_data _ elt, rst)
        end
    | Iter_variant_map _ _ =>
      fun x =>
        match set.destruct _ _ x with
        | None => None
        | Some ((k, v), rst) =>
          Some ((comparable_data_to_data _ k, v), rst)
        end
    | Iter_variant_list _ =>
      fun l => match l with
               | nil => None
               | cons a l => Some (a, l)
               end
    end.

  Definition get k val c (v : get_variant k val c)
    : comparable_data k -> data c -> data (option val) :=
    match v with
    | Get_variant_map _ _ => map.get _ _ _
    | Get_variant_bigmap _ _ => map.get _ _ _
    end.

  Definition map_destruct a b ca cb (v : map_variant a b ca cb)
    : data ca -> data (option (pair a ca)) :=
    match v with
    | Map_variant_map _ _ _ =>
      fun x =>
        match set.destruct _ _ x with
        | None => None
        | Some ((k, v), rst) =>
          Some ((comparable_data_to_data _ k, v), rst)
        end
    | Map_variant_list _ _ =>
      fun l => match l with
               | nil => None
               | cons a l => Some (a, l)
               end
    end.

  Definition map_empty a b ca cb (v : map_variant a b ca cb)
    : data cb :=
    match v with
    | Map_variant_map _ _ _ => map.empty _ _ _
    | Map_variant_list _ _ => nil
    end.

  Definition map_insert a b ca cb (v : map_variant a b ca cb)
    : data a -> data b -> data cb -> data cb :=
    match v with
    | Map_variant_map k_ty _ v_ty =>
      fun '(k, _) v (m : data (map k_ty v_ty)) =>
        map.update _ _ _ (comparable.compare_eq_iff _) (comparable.lt_trans _) (comparable.gt_trans _) (data_to_comparable_data _ k) (Some v) m
    | Map_variant_list _ _ =>
      fun _ => cons
    end.

  Definition data_to_string {a} (x : data a) : String.string := "".

  (* The gas argument is used to ensure termination, it is not the
  amount of gas that is actually required to run the contract because
  in the SEQ case, both instructions are run with gas n *)

  Fixpoint eval {param_ty : Datatypes.option type} {tff0} (env : @proto_env param_ty) {A : stack_type} {B : stack_type}
           (i : instruction param_ty tff0 A B) (fuel : Datatypes.nat) (SA : stack A) {struct fuel} : M (stack B) :=
    match fuel with
    | O => Failed _ Out_of_fuel
    | S n =>
      match i, SA, env with
      | FAILWITH, (x, _), _ =>
        Failed _ (Assertion_Failure _ x)

      (* According to the documentation, FAILWITH's argument should
         not be part of the state reached by the instruction but the
         whole point of this instruction (compared to the FAIL macro)
         is to report the argument to the user. *)

      | NOOP, SA, _ => Return SA
      | SEQ B C, SA, env =>
        let! r := eval env B n SA in
        eval env C n r
      | IF_ bt bf, (b, SA), env =>
        if b then eval env bt n SA else eval env bf n SA
      | LOOP body, (b, SA), env =>
        if b then eval env (body;; (LOOP body)) n SA else Return SA
      | LOOP_LEFT body, (ab, SA), env =>
        match ab with
        | inl x => eval env (body;; LOOP_LEFT body) n (x, SA)
        | inr y => Return (y, SA)
        end
      | EXEC, (x, (existT _ tff f, SA)), env =>
        let! (y, tt) := eval (no_self env) f n (x, tt) in
        Return (y, SA)
      | @APPLY _ a b c D i, (x, (existT _ _ f, SA)), env =>
        Return (existT
                    _ _
                    (PUSH _ (data_to_concrete_data _ i x) ;; PAIR ;; f), SA)
      | DUP, (x, SA), _ => Return (x, (x, SA))
      | SWAP, (x, (y, SA)), _ => Return (y, (x, SA))
      | PUSH a x, SA, _ => Return (concrete_data_to_data _ x, SA)
      | UNIT, SA, _ => Return (tt, SA)
      | LAMBDA a b code, SA, _ => Return (existT _ _ code, SA)
      | EQ, (x, SA), _ => Return ((x =? 0)%Z, SA)
      | NEQ, (x, SA), _ => Return (negb (x =? 0)%Z, SA)
      | LT, (x, SA), _ => Return ((x <? 0)%Z, SA)
      | GT, (x, SA), _ => Return ((x >? 0)%Z, SA)
      | LE, (x, SA), _ => Return ((x <=? 0)%Z, SA)
      | GE, (x, SA), _ => Return ((x >=? 0)%Z, SA)
      | @OR _ _ s, (x, (y, SA)), _ =>
        Return (or_fun _ (bitwise_variant_field _ s) x y, SA)
      | @AND _ _ s, (x, (y, SA)), _ =>
        Return (and _ (bitwise_variant_field _ s) x y, SA)
      | @XOR _ _ s, (x, (y, SA)), _ =>
        Return (xor _ (bitwise_variant_field _ s) x y, SA)
      | @NOT _ _ s, (x, SA), _ => Return (not _ _ (not_variant_field _ s) x, SA)
      | @NEG _ _ s, (x, SA), _ => Return (neg _ (neg_variant_field _ s) x, SA)
      | ABS, (x, SA), _ => Return (Z.abs_N x, SA)
      | ISNAT, (x, SA), _ =>
        Return (if (x >=? 0)%Z then (Some (Z.to_N x), SA) else (None, SA))
      | INT, (x, SA), _ => Return (Z.of_N x, SA)
      | @ADD _ _ _ s, (x, (y, SA)), _ =>
        let! r := add _ _ _ (add_variant_field _ _ s) x y in
        Return (r, SA)
      | @SUB _ _ _ s, (x, (y, SA)), _ =>
        let! r := sub _ _ _ (sub_variant_field _ _ s) x y in
        Return (r, SA)
      | @MUL _ _ _ s, (x, (y, SA)), _ =>
        let! r := mul _ _ _ (mul_variant_field _ _ s) x y in
        Return (r, SA)
      | @EDIV _ _ _ s, (x, (y, SA)), _ =>
        Return (ediv _ _ _ _ (ediv_variant_field _ _ s) x y, SA)
      | LSL, (x, (y, SA)), _ => Return (N.shiftl x y, SA)
      | LSR, (x, (y, SA)), _ => Return (N.shiftr x y, SA)
      | COMPARE, (x, (y, SA)), _ =>
        Return (comparison_to_int
                    (compare _
                             (data_to_comparable_data _ x)
                             (data_to_comparable_data _ y)), SA)
      | @CONCAT _ _ s _, (x, (y, SA)), _ =>
        Return (concat _ (stringlike_variant_field _ s) x y, SA)
      | @CONCAT_list _ _ s _, (l, SA), _ =>
        Return (concat_list _ (stringlike_variant_field _ s) l, SA)
      | @SLICE _ _ i, (n1, (n2, (s, SA))), _ =>
        Return (slice _ (stringlike_variant_field _ i) n1 n2 s, SA)
      | PAIR, (x, (y, SA)), _ => Return ((x, y), SA)
      | CAR, ((x, y), SA), _ => Return (x, SA)
      | CDR, ((x, y), SA), _ => Return (y, SA)
      | EMPTY_SET a, SA, _ => Return (set.empty _ (compare a), SA)
      | @MEM _ _ _ s _, (x, (y, SA)), _ =>
        Return (mem _ _
                      (mem_variant_field _ _ s)
                      (data_to_comparable_data _ x)
                      y, SA)
      | @UPDATE _ _ _ _ s _, (x, (y, (z, SA))), _ =>
        Return (update _ _ _ (update_variant_field _ _ _ s) (data_to_comparable_data _ x) y z, SA)
      | @ITER _ _ s _ body, (x, SA), env =>
        match iter_destruct _ _ (iter_variant_field _ s) x with
        | None => Return SA
        | Some (a, y) =>
          let! SB := eval env body n (a, SA) in
          eval env (ITER body) n (y, SB)
        end
      | @SIZE _ _ s, (x, SA), _ =>
        Return (N.of_nat (size _ (size_variant_field _ s) x), SA)
      | EMPTY_MAP k val, SA, _ =>
        Return (map.empty (comparable_data k) (data val) _, SA)
      | EMPTY_BIG_MAP k val, SA, _ =>
        Return (map.empty (comparable_data k) (data val) _, SA)
      | @GET _ _ _ s _, (x, (y, SA)), _ =>
        Return (get _ _ _
                      (get_variant_field _ _ s)
                      (data_to_comparable_data _ x)
                      y, SA)
      | @MAP _ _ _ s _ body, (x, SA), env =>
        let v := (map_variant_field _ _ s) in
        match map_destruct _ _ _ _ v x with
        | None => Return (map_empty _ _ _ _ v, SA)
        | Some (a, y) =>
          let! (b, SB) := eval env body n (a, SA) in
          let! (c, SC) := eval env (MAP body) n (y, SB) in
          Return (map_insert _ _ _ _ v a b c, SC)
        end
      | SOME, (x, SA), _ => Return (Some x, SA)
      | NONE _, SA, _ => Return (None, SA)
      | IF_NONE bt bf, (b, SA), env =>
        match b with
        | None => eval env bt n SA
        | Some b => eval env bf n (b, SA)
        end
      | LEFT _, (x, SA), _ => Return (inl x, SA)
      | RIGHT _, (x, SA), _ => Return (inr x, SA)
      | IF_LEFT bt bf, (b, SA), env =>
        match b with
        | inl a => eval env bt n (a, SA)
        | inr b => eval env bf n (b, SA)
        end
      | IF_RIGHT bt bf, (b, SA), env =>
        match b with
        | inl a => eval env bf n (a, SA)
        | inr b => eval env bt n (b, SA)
        end
      | CONS, (x, (y, SA)), _ => Return (cons x y, SA)
      | NIL _, SA, _ => Return (nil, SA)
      | IF_CONS bt bf, (l, SA), env =>
        match l with
        | cons a b => eval env bt n (a, (b, SA))
        | nil => eval env bf n SA
        end
      | CREATE_CONTRACT _ _ f, (a, (b, (c, SA))), env =>
        let (oper, addr) := create_contract env _ _ _ a b f c in
        Return (oper, (addr, SA))
      | TRANSFER_TOKENS, (a, (b, (c, SA))), env =>
        Return (transfer_tokens env _ a b c, SA)
      | SET_DELEGATE, (x, SA), env => Return (set_delegate env x, SA)
      | BALANCE, SA, env => Return (balance env, SA)
      | ADDRESS, (x, SA), env => Return (address_ env _ x, SA)
      | CONTRACT _, (x, SA), env => Return (contract_ env _ x, SA)
      | SOURCE, SA, env => Return (source env, SA)
      | SENDER, SA, env => Return (sender env, SA)
      | SELF, SA, env => Return (self env, SA)
      | AMOUNT, SA, env => Return (amount env, SA)
      | IMPLICIT_ACCOUNT, (x, SA), env => Return (implicit_account env x, SA)
      | NOW, SA, env => Return (now env, SA)
      | PACK, (x, SA), env => Return (pack env _ x, SA)
      | UNPACK ty, (x, SA), env => Return (unpack env ty x, SA)
      | HASH_KEY, (x, SA), env => Return (hash_key env x, SA)
      | BLAKE2B, (x, SA), env => Return (blake2b env x, SA)
      | SHA256, (x, SA), env => Return (sha256 env x, SA)
      | SHA512, (x, SA), env => Return (sha512 env x, SA)
      | CHECK_SIGNATURE, (x, (y, (z, SA))), env =>
        Return (check_signature env x y z, SA)
      | DIG n Hlen, SA, _ => Return (stack_dig SA)
      | DUG n Hlen, SA, _ => Return (stack_dug SA)
      | DIP nl Hlen i, SA, env =>
        let (S1, S2) := stack_split SA in
        let! S3 := eval env i n S2 in
        Return (stack_app S1 S3)
      | DROP n Hlen, SA, _ =>
        let (S1, S2) := stack_split SA in Return S2
      | CHAIN_ID, SA, env => Return (chain_id_ env, SA)
      end
    end.

  (* The evaluator does not depend on the amount of fuel provided *)
  Lemma eval_deterministic_le :
    forall fuel1 fuel2,
      fuel1 <= fuel2 ->
      forall {self_type env tff0 A B} (i : instruction self_type tff0 A B) st,
        success (eval env i fuel1 st) ->
        eval env i fuel1 st = eval env i fuel2 st.
  Proof.
    induction fuel1; intros fuel2 Hle self_type env tff0 A B i st Hsucc.
    - contradiction.
    - destruct fuel2.
      + inversion Hle.
      + apply le_S_n in Hle.
        specialize (IHfuel1 fuel2 Hle).
        simpl.
        destruct i; try reflexivity.
        * simpl in Hsucc.
          destruct (success_bind _ _ Hsucc) as (x, (H1, H2)).
          rewrite <- IHfuel1.
          -- rewrite H1.
             simpl.
             apply IHfuel1.
             assumption.
          -- apply success_eq_return in H1.
             exact H1.
        * destruct st as ([], st); rewrite IHfuel1; try assumption; reflexivity.
        * destruct st as ([], st).
          -- rewrite IHfuel1; try assumption; reflexivity.
          -- reflexivity.
        * destruct st as ([x|y], st).
          -- rewrite IHfuel1; try assumption; reflexivity.
          -- reflexivity.
        * destruct st as (x, ((tff, f), SA)).
          f_equal.
          rewrite IHfuel1.
          -- reflexivity.
          -- simpl in Hsucc.
             apply success_bind_arg in Hsucc.
             assumption.
        * destruct st as (x, SA).
          generalize Hsucc; clear Hsucc.
          simpl.
          destruct (iter_destruct (iter_elt_type collection i) collection
                                  (iter_variant_field collection i) x).
          -- destruct d.
             fold stack.
             intro Hsucc.
             rewrite <- IHfuel1.
             ++ destruct (success_bind _ _ Hsucc) as (SB, (Ha, Hb)).
                rewrite Ha.
                simpl.
                apply IHfuel1.
                assumption.
             ++ apply success_bind_arg in Hsucc.
                assumption.
          -- reflexivity.
        * destruct st as (x, SA).
          generalize Hsucc; clear Hsucc.
          simpl.
          fold stack.
          destruct (map_destruct (map_in_type collection b i)
                                 b
                                 collection
                                 (map_out_collection_type collection b i)
                                 (map_variant_field collection b i) x).
          -- destruct d.
             intro Hsucc.
             rewrite <- IHfuel1.
             ++ destruct (success_bind _ _ Hsucc) as ((c, SC), (Ha, Hb)).
                destruct (success_bind _ _ Hb) as ((dd, SD), (Hm, _)).
                rewrite Ha.
                simpl.
                rewrite <- IHfuel1.
                ** reflexivity.
                ** rewrite Hm.
                   constructor.
             ++ apply success_bind_arg in Hsucc.
                assumption.
          -- reflexivity.
        * destruct st as ([|], SA); rewrite IHfuel1.
          -- reflexivity.
          -- exact Hsucc.
          -- reflexivity.
          -- exact Hsucc.
        * destruct st as ([|], SA); rewrite IHfuel1.
          -- reflexivity.
          -- exact Hsucc.
          -- reflexivity.
          -- exact Hsucc.
        * destruct st as ([|], SA); rewrite IHfuel1.
          -- reflexivity.
          -- exact Hsucc.
          -- reflexivity.
          -- exact Hsucc.
        * destruct st as ([|], SA); rewrite IHfuel1.
          -- reflexivity.
          -- exact Hsucc.
          -- reflexivity.
          -- exact Hsucc.
        * simpl in Hsucc.
          destruct (stack_split st); rewrite IHfuel1.
          -- reflexivity.
          -- destruct (success_bind _ _ Hsucc) as (x, (H1, H2)).
             apply success_eq_return in H1.
             exact H1.
  Qed.

  Lemma eval_deterministic_success_both {self_type env} fuel1 fuel2 {A B tff0} (i : instruction self_type tff0 A B) S :
    success (eval env i fuel1 S) ->
    success (eval env i fuel2 S) ->
    eval env i fuel1 S = eval env i fuel2 S.
  Proof.
    case (le_ge_dec fuel1 fuel2).
    - intros Hle Hsucc _.
      apply eval_deterministic_le; assumption.
    - unfold ge.
      intros Hle _ Hsucc.
      symmetry.
      apply eval_deterministic_le; assumption.
  Qed.

  Definition eval_precond_body
             (eval_precond_n : forall {self_type},
                 @proto_env self_type ->
                 forall {tff0 A B},
                   instruction self_type tff0 A B ->
                   (stack B -> Prop) -> stack A -> Prop)
             {self_type} env tff0 A B
             (i : instruction self_type tff0 A B)
             (psi : stack B -> Prop)
             (SA : stack A) : Prop :=
    match i, env, psi, SA with
    | FAILWITH, _, _, _ => false
    | NOOP, env, psi, st => psi st
    | SEQ B C, env, psi, st =>
      eval_precond_n env B (eval_precond_n env C psi) st
    | IF_ bt bf, env, psi, (b, SA) =>
      if b then eval_precond_n env bt psi SA
      else eval_precond_n env bf psi SA
    | LOOP body, env, psi, (b, SA) =>
      if b then eval_precond_n env (body;; (LOOP body)) psi SA
      else psi SA
    | LOOP_LEFT body, env, psi, (ab, SA) =>
      match ab with
      | inl x => eval_precond_n env (body;; LOOP_LEFT body) psi (x, SA)
      | inr y => psi (y, SA)
      end
    | EXEC, env, psi, (x, (existT _ _ f, SA)) =>
      eval_precond_n (no_self env) f (fun '(y, tt) => psi (y, SA)) (x, tt)
    | @APPLY _ a b c D i, env, psi, (x, (existT _ _ f, SA)) =>
      psi (existT _ _ (PUSH _ (data_to_concrete_data _ i x) ;; PAIR ;; f), SA)
    | DUP, env, psi, (x, SA) => psi (x, (x, SA))
    | SWAP, env, psi, (x, (y, SA)) => psi (y, (x, SA))
    | PUSH a x, env, psi, SA => psi (concrete_data_to_data _ x, SA)
    | UNIT, env, psi, SA => psi (tt, SA)
    | LAMBDA a b code, env, psi, SA => psi (existT _ _ code, SA)
    | EQ, env, psi, (x, SA) => psi ((x =? 0)%Z, SA)
    | NEQ, env, psi, (x, SA) => psi (negb (x =? 0)%Z, SA)
    | LT, env, psi, (x, SA) => psi ((x <? 0)%Z, SA)
    | GT, env, psi, (x, SA) => psi ((x >? 0)%Z, SA)
    | LE, env, psi, (x, SA) => psi ((x <=? 0)%Z, SA)
    | GE, env, psi, (x, SA) => psi ((x >=? 0)%Z, SA)
    | @OR _ _ s _, env, psi, (x, (y, SA)) => psi (or_fun _ (bitwise_variant_field _ s) x y, SA)
    | @AND _ _ s _, env, psi, (x, (y, SA)) => psi (and _ (bitwise_variant_field _ s) x y, SA)
    | @XOR _ _ s _, env, psi, (x, (y, SA)) => psi (xor _ (bitwise_variant_field _ s) x y, SA)
    | @NOT _ _ s _, env, psi, (x, SA) => psi (not _ _ (not_variant_field _ s) x, SA)
    | @NEG _ _ s _, env, psi, (x, SA) => psi (neg _ (neg_variant_field _ s) x, SA)
    | ABS, env, psi, (x, SA) => psi (Z.abs_N x, SA)
    | ISNAT, env, psi, (x, SA) => psi (if (x >=? 0)%Z then (Some (Z.to_N x), SA) else (None, SA))
    | INT, env, psi, (x, SA) => psi (Z.of_N x, SA)
    | @ADD _ _ _ s _, env, psi, (x, (y, SA)) =>
      precond (add _ _ _ (add_variant_field _ _ s) x y) (fun z => psi (z, SA))
    | @SUB _ _ _ s _, env, psi, (x, (y, SA)) =>
      precond (sub _ _ _ (sub_variant_field _ _ s) x y) (fun z => psi (z, SA))
    | @MUL _ _ _ s _, env, psi, (x, (y, SA)) =>
      precond (mul _ _ _ (mul_variant_field _ _ s) x y) (fun z => psi (z, SA))
    | @EDIV _ _ _ s _, env, psi, (x, (y, SA)) =>
      psi (ediv _ _ _ _ (ediv_variant_field _ _ s) x y, SA)
    | LSL, env, psi, (x, (y, SA)) => psi (N.shiftl x y, SA)
    | LSR, env, psi, (x, (y, SA)) => psi (N.shiftr x y, SA)
    | COMPARE, env, psi, (x, (y, SA)) => psi (comparison_to_int (compare _ (data_to_comparable_data _ x) (data_to_comparable_data _ y)), SA)
    | @CONCAT _ _ s _, env, psi, (x, (y, SA)) =>
      psi (concat _ (stringlike_variant_field _ s) x y, SA)
    | @CONCAT_list _ _ s _, env, psi, (l, SA) =>
      psi (concat_list _ (stringlike_variant_field _ s) l, SA)
    | @SLICE _ _ i, env, psi, (n1, (n2, (s, SA))) =>
      psi (slice _ (stringlike_variant_field _ i) n1 n2 s, SA)
    | PAIR, env, psi, (x, (y, SA)) => psi ((x, y), SA)
    | CAR, env, psi, ((x, y), SA) => psi (x, SA)
    | CDR, env, psi, ((x, y), SA) => psi (y, SA)
    | EMPTY_SET a, env, psi, SA => psi (set.empty _ (compare a), SA)
    | @MEM _ _ _ s _, env, psi, (x, (y, SA)) =>
      psi (mem _ _ (mem_variant_field _ _ s) (data_to_comparable_data _ x) y, SA)
    | @UPDATE _ _ _ _ s _, env, psi, (x, (y, (z, SA))) =>
      psi (update _ _ _ (update_variant_field _ _ _ s) (data_to_comparable_data _ x) y z, SA)
    | @ITER _ _ s _ body, env, psi, (x, SA) =>
      match iter_destruct _ _ (iter_variant_field _ s) x with
      | None => psi SA
      | Some (a, y) =>
        eval_precond_n
          env body
          (fun SB => eval_precond_n env (ITER body) psi (y, SB))
          (a, SA)
      end
    | @SIZE _ _ s, env, psi, (x, SA) => psi (N.of_nat (size _ (size_variant_field _ s) x), SA)
    | EMPTY_MAP k val, env, psi, SA => psi (map.empty (comparable_data k) (data val) _, SA)
    | EMPTY_BIG_MAP k val, env, psi, SA => psi (map.empty (comparable_data k) (data val) _, SA)
    | @GET _ _ _ s _, env, psi, (x, (y, SA)) => psi (get _ _ _ (get_variant_field _ _ s) (data_to_comparable_data _ x) y, SA)
    | @MAP _ _ _ s _ body, env, psi, (x, SA) =>
      let v := (map_variant_field _ _ s) in
      match map_destruct _ _ _ _ v x with
      | None => psi (map_empty _ _ _ _ v, SA)
      | Some (a, y) =>
        eval_precond_n
          env body
          (fun '(b, SB) =>
             eval_precond_n
               env (MAP body)
               (fun '(c, SC) => psi (map_insert _ _ _ _ v a b c, SC))
               (y, SB))
          (a, SA)
      end
    | SOME, env, psi, (x, SA) => psi (Some x, SA)
    | NONE _, env, psi, SA => psi (None, SA)
    | IF_NONE bt bf, env, psi, (b, SA) =>
      match b with
      | None => eval_precond_n env bt psi SA
      | Some b => eval_precond_n env bf psi (b, SA)
      end
    | LEFT _, env, psi, (x, SA) => psi (inl x, SA)
    | RIGHT _, env, psi, (x, SA) => psi (inr x, SA)
    | IF_LEFT bt bf, env, psi, (b, SA) =>
      match b with
      | inl a => eval_precond_n env bt psi (a, SA)
      | inr b => eval_precond_n env bf psi (b, SA)
      end
    | IF_RIGHT bt bf, env, psi, (b, SA) =>
      match b with
      | inl a => eval_precond_n env bf psi (a, SA)
      | inr b => eval_precond_n env bt psi (b, SA)
      end
    | CONS, env, psi, (x, (y, SA)) => psi (cons x y, SA)
    | NIL _, env, psi, SA => psi (nil, SA)
    | IF_CONS bt bf, env, psi, (l, SA) =>
      match l with
      | cons a b => eval_precond_n env bt psi (a, (b, SA))
      | nil => eval_precond_n env bf psi SA
      end
    | CREATE_CONTRACT _ _ f, env, psi, (a, (b, (c, SA))) =>
      let (oper, addr) := create_contract env _ _ _ a b f c in
      psi (oper, (addr, SA))
    | TRANSFER_TOKENS, env, psi, (a, (b, (c, SA))) =>
      psi (transfer_tokens env _ a b c, SA)
    | SET_DELEGATE, env, psi, (x, SA) =>
      psi (set_delegate env x, SA)
    | BALANCE, env, psi, SA => psi (balance env, SA)
    | ADDRESS, env, psi, (x, SA) => psi (address_ env _ x, SA)
    | CONTRACT _, env, psi, (x, SA) => psi (contract_ env _ x, SA)
    | SOURCE, env, psi, SA => psi (source env, SA)
    | SENDER, env, psi, SA => psi (sender env, SA)
    | SELF, env, psi, SA => psi (self env, SA)
    | AMOUNT, env, psi, SA => psi (amount env, SA)
    | IMPLICIT_ACCOUNT, env, psi, (x, SA) => psi (implicit_account env x, SA)
    | NOW, env, psi, SA => psi (now env, SA)
    | PACK, env, psi, (x, SA) => psi (pack env _ x, SA)
    | UNPACK ty, env, psi, (x, SA) => psi (unpack env ty x, SA)
    | HASH_KEY, env, psi, (x, SA) => psi (hash_key env x, SA)
    | BLAKE2B, env, psi, (x, SA) => psi (blake2b env x, SA)
    | SHA256, env, psi, (x, SA) => psi (sha256 env x, SA)
    | SHA512, env, psi, (x, SA) => psi (sha512 env x, SA)
    | CHECK_SIGNATURE, env, psi, (x, (y, (z, SA))) =>
      psi (check_signature env x y z, SA)
    | DIG n Hlen, env, psi, st => psi (stack_dig st)
    | DUG n Hlen, env, psi, st => psi (stack_dug st)
    | DIP n Hlen i, env, psi, SA =>
      let (S1, S2) := stack_split SA in
      eval_precond_n env i (fun SB => psi (stack_app S1 SB)) S2
    | DROP n Hlen, env, psi, SA =>
      let (S1, S2) := stack_split SA in psi S2
    | CHAIN_ID, env, psi, SA => psi (chain_id_ env, SA)
    end.

  Fixpoint eval_precond (fuel : Datatypes.nat) :
    forall {self_type} env {tff0 A B},
      instruction self_type tff0 A B ->
      (stack B -> Prop) -> (stack A -> Prop) :=
    match fuel with
    | O => fun _ _ _ _ _ _ _ _ => false
    | S n =>
      @eval_precond_body (@eval_precond n)
    end.

  Lemma eval_precond_correct {sty env tff0 A B} (i : instruction sty tff0 A B) n st psi :
    precond (eval env i n st) psi <-> eval_precond n env i psi st.
  Proof.
    generalize sty env tff0 A B i st psi; clear sty env tff0 A B i st psi.
    induction n; intros sty env tff0 A B i st psi; [simpl; intuition|].
    destruct i; simpl; fold data stack.
    - reflexivity.
    - destruct st; reflexivity.
    - rewrite precond_bind.
      rewrite <- IHn.
      apply precond_eqv.
      intro SB.
      apply IHn.
    - destruct st as ([|], st); auto.
    - destruct st as ([|], st).
      + apply IHn.
      + simpl. reflexivity.
    - destruct st as ([|], st); simpl.
      + apply (IHn _ _ _ _ _ (i;; LOOP_LEFT i)).
      + reflexivity.
    - destruct st as (x, ((tff, f), st)).
      rewrite precond_bind.
      rewrite <- (IHn _ _ _ _ _ f (x, tt) (fun '(y, tt) => psi (y, st))).
      apply precond_eqv.
      intros (y, []).
      simpl.
      reflexivity.
    - destruct st as (x, ((tff, y), st)); reflexivity.
    - destruct st; reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st as (x, (y, st)); rewrite precond_bind; reflexivity.
    - destruct st as (x, (y, st)); rewrite precond_bind; reflexivity.
    - destruct st as (x, (y, st)); rewrite precond_bind; reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st as (x, (y, (z, st))); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as ((x, y), st); reflexivity.
    - destruct st as ((x, y), st); reflexivity.
    - reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, (z, st))); reflexivity.
    - destruct st as (x, st).
      destruct (iter_destruct (iter_elt_type collection i) collection
                              (iter_variant_field collection i) x) as [(hd, tl)|].
      + rewrite precond_bind.
        rewrite <- IHn.
        apply precond_eqv.
        intro SA.
        apply IHn.
      + reflexivity.
    - reflexivity.
    - reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, st).
      destruct (map_destruct (map_in_type collection b i) b collection
                             (map_out_collection_type collection b i)
                             (map_variant_field collection b i) x) as [(hd, tl)|].
      + rewrite precond_bind.
        rewrite <- IHn.
        apply precond_eqv.
        intros (bb, SA).
        rewrite precond_bind.
        rewrite <- IHn.
        apply precond_eqv.
        intros (c, B).
        reflexivity.
      + reflexivity.
    - destruct st; reflexivity.
    - reflexivity.
    - destruct st as ([|], st); apply IHn.
    - destruct st; reflexivity.
    - destruct st; reflexivity.
    - destruct st as ([|], st); apply IHn.
    - destruct st as ([|], st); apply IHn.
    - destruct st as (x, (y, st)); reflexivity.
    - reflexivity.
    - destruct st as ([|], st); apply IHn.
    - destruct st as (a, (b, (c, SA))).
      destruct (create_contract env g p _ a b i c).
      reflexivity.
    - destruct st as (a, (b, (c, SA))).
      reflexivity.
    - destruct st as (a, SA).
      reflexivity.
    - reflexivity.
    - destruct st as (a, SA).
      reflexivity.
    - destruct st as (a, SA).
      reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - destruct st as (a, SA).
      reflexivity.
    - reflexivity.
    - destruct st as (x, SA).
      reflexivity.
    - destruct st as (x, SA).
      reflexivity.
    - destruct st as (x, SA).
      reflexivity.
    - destruct st as (x, SA).
      reflexivity.
    - destruct st as (x, SA).
      reflexivity.
    - destruct st as (x, SA).
      reflexivity.
    - destruct st as (a, (b, (c, SA))).
      reflexivity.
    - reflexivity.
    - reflexivity.
    - destruct (stack_split st).
      rewrite precond_bind.
      apply IHn.
    - destruct (stack_split st).
      reflexivity.
    - reflexivity.
  Qed.

End Semantics.
