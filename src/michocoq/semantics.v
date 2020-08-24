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

Require Import ZArith Lia.
Require Import String.
Require Import syntax macros.
Require NPeano.

Require Import comparable error.
Import error.Notations.

Module Type ContractContext.
  Parameter get_contract_type :
    smart_contract_address_constant -> Datatypes.option type.
End ContractContext.


Definition ediv_Z x y :=
  (if y =? 0 then None else
     let d := x / y in
     let r := x mod y in
     if y >? 0 then Some (d, Z.to_N r)
     else if r =? 0 then Some (d, 0%N)
          else Some (d + 1, Z.to_N (r - y)))%Z.

Lemma ediv_Z_correct_pos x y (Hy : (y > 0)%Z) d r :
  (Some (x / y, Z.to_N (x mod y)) = Some (d, r) <-> (y * d + Z.of_N r = x /\ 0 <= Z.of_N r < Z.abs y))%Z.
Proof.
  rewrite Z.abs_eq; [|lia].
  split.
  - intro H; injection H; clear H.
    intros; subst.
    assert (0 <= x mod y < y)%Z as Hbound by (apply Z.mod_pos_bound; lia).
    rewrite Z2N.id; [|apply Hbound].
    split; [|assumption].
    symmetry.
    apply Z_div_mod_eq.
    assumption.
  - intros (He, Hbound).
    f_equal.
    assert (d = x / y)%Z.
    + subst x.
      rewrite Z.mul_comm.
      rewrite Z_div_plus_full_l; [|lia].
      assert (Z.of_N r / y = 0)%Z as Hr by (apply Z.div_small_iff; lia).
      lia.
    + subst d.
      f_equal.
      rewrite Zmod_eq; [|lia].
      assert (x - x / y * y = Z.of_N r)%Z as Hr by lia.
      rewrite Hr.
      apply N2Z.id.
Qed.

Lemma ediv_Z_correct x y d r :
  ediv_Z x y = Some (d, r) <-> (y * d + Z.of_N r = x /\ 0 <= Z.of_N r < Z.abs y)%Z.
Proof.
  unfold ediv_Z.
  case_eq (y =? 0)%Z.
  - intro Hy.
    apply Z.eqb_eq in Hy.
    subst y.
    simpl.
    split.
    + discriminate.
    + intros (_, Habs).
      exfalso.
      lia.
  - intro Hy.
    apply Z.eqb_neq in Hy.
    case_eq (y >? 0)%Z.
    + intro Hy2.
      apply Z.gtb_lt in Hy2.
      apply ediv_Z_correct_pos; lia.
    + intro Hy2.
      rewrite Z.gtb_ltb in Hy2.
      rewrite Z.ltb_ge in Hy2.
      assert (- y > 0)%Z as Hym by lia.
      specialize (ediv_Z_correct_pos x (- y) Hym (- d) r); intro Hm.
      rewrite Z.abs_opp in Hm.
      case_eq (x mod y =? 0)%Z.
      * intro Hr.
        apply Z.eqb_eq in Hr.
        assert (x mod - y = 0)%Z as Hmodm by (apply Z_mod_zero_opp_r; assumption).
        rewrite Hmodm in Hm.
        rewrite Z2N.inj_0 in Hm.
        rewrite Z.mul_opp_opp in Hm.
        rewrite <- Hm.
        apply Z_div_zero_opp_r in Hr.
        rewrite Hr.
        split.
        -- intuition congruence.
        -- intro H; injection H; clear H.
           intros.
           f_equal.
           f_equal; lia.
      * intro Hr.
        apply Z.eqb_neq in Hr.
        assert (x mod - y = x mod y - y)%Z as Hmodm by (apply Z_mod_nz_opp_r; congruence).
        rewrite Hmodm in Hm.
        rewrite Z.mul_opp_opp in Hm.
        rewrite <- Hm.
        apply Z_div_nz_opp_r in Hr.
        rewrite Hr.
        split.
        -- intro H; injection H; clear H.
           intros.
           f_equal.
           f_equal; lia.
        -- intro H; injection H; clear H.
           intros.
           f_equal.
           f_equal; lia.
Qed.

Definition ediv_N x y :=
  if (y =? 0)%N then None else Some (x / y, x mod y)%N.

Lemma ediv_N_correct x y (Hy : (y <> 0)%N) d r :
  (Some (x / y, x mod y) = Some (d, r) <-> (y * d + r = x /\ r < y))%N.
Proof.
  split.
  - intro H; injection H; clear H.
    intros; subst.
    assert (x mod y < y)%N as Hbound by (apply N.mod_upper_bound; lia).
    split; [|assumption].
    symmetry.
    apply N.div_mod.
    assumption.
  - intros (He, Hbound).
    f_equal.
    symmetry in He.
    f_equal.
    + symmetry.
      apply N.div_unique with (r := r); assumption.
    + symmetry.
      apply N.mod_unique with (q := d); assumption.
Qed.

Module Semantics(C : ContractContext).

  (* more_fuel replaces
   *   Hfuel : S n <= fuel  with Hfuel : n <= fuel
   *   and fuel in the goal with S fuel
   *)
  Ltac more_fuel :=
  match goal with
    | Hfuel : (_ <= ?fuel) |- _ =>
      destruct fuel as [|fuel];
      [inversion Hfuel; fail
      | apply le_S_n in Hfuel]
  end.

  (* Test *)
  Goal forall fuel (Hfuel : 42 <= fuel) (F : Datatypes.nat -> Prop), F fuel.
  Proof.
    intros.
    more_fuel.
  Abort.

  (* Like more_fuel, but attempts to keep Peano numbers in
   * the decimal representation *)
  Ltac more_fuel' :=
    match goal with
    | Hfuel: (S ?x) + _ <= ?fuel |- _ =>
      change (S x) with (1 + x) in Hfuel;
      rewrite <- plus_assoc in Hfuel; more_fuel
    end.

  Lemma more_fuel_add_lemma a b fuel fuel' :
    fuel' = fuel - a ->
    a + b <= fuel ->
    (b <= fuel' /\ fuel = a + fuel').
  Proof.
    intros H Hfuel; subst fuel'.
    split.
    - apply (NPeano.Nat.sub_le_mono_r (a + b) fuel a) in Hfuel.
      rewrite minus_plus in Hfuel.
      assumption.
    - apply le_plus_minus.
      transitivity (a + b).
      + apply Nat.le_add_r.
      + assumption.
  Qed.

  (* fuel replace n replaces
   *   Hfuel : a <= fuel  with Hfuel : n <= fuel
   * if lia cannot prove n <= a, a subgoal is generated.
   *)
  Ltac fuel_replace n :=
    match goal with
    | Hfuel : ?a <= ?fuel |- _ =>
      apply (le_trans n a fuel) in Hfuel; [|try lia]
    end.

  (* Test *)
  Goal forall fuel a b (Hfuel : a + b <= fuel), b + a <= fuel.
  Proof.
    intros.
    fuel_replace (b + a).
  Abort.

  (* more_fuel_add replaces
   *   Hfuel : a + b <= fuel  with Hfuel : b <= fuel
   *   and fuel in the goal with a + fuel
   *)
  Ltac more_fuel_add :=
    match goal with
    | Hfuel : (?a + ?b <= ?fuel) |- _ =>
      remember (fuel - a) as fuel' eqn:Heqfuel';
      apply (more_fuel_add_lemma a b fuel fuel' Heqfuel') in Hfuel;
      destruct Hfuel as (Hfuel, Heqfuel);
      subst fuel; rename fuel' into fuel; clear Heqfuel'
    end.

  (* Test *)
  Goal forall a b fuel (Hfuel : a + b <= fuel) F, F fuel.
  Proof.
    intros.
    more_fuel_add.
  Abort.

  Lemma extract_fuel_lemma n fuel f (Hfuel : n <= fuel) (Hf : f <= n) :
    f + (n - f) <= fuel.
  Proof.
    rewrite <- le_plus_minus; assumption.
  Qed.

  (* extract_fuel f replaces
   *   Hfuel : n <= fuel  with Hfuel : n - f <= fuel
   *   and fuel in the goal with f + fuel
   * if lia cannot prove f <= fuel, a subgoal is generated.
   *)
  Ltac extract_fuel f :=
    match goal with
    | Hfuel : ?n <= ?fuel |- _ =>
      apply (extract_fuel_lemma n fuel f) in Hfuel; [more_fuel_add|try lia]
    end.

  (* Test *)
  Goal forall x fuel (Hfuel : x + 4 <= fuel) F, F fuel.
  Proof.
    intros.
    extract_fuel 2.
  Abort.

  Export C.

  Definition get_address_type (sao : comparable_data address * annot_o)
    : Datatypes.option type :=
    let '(addr, ao) := sao in
    opt_bind
      (match addr with
        | Implicit _ => Some unit
        | Originated addr => get_contract_type addr
       end)
      (fun ty =>
         get_entrypoint_opt ao ty None).

  Fixpoint data (a : type) {struct a} : Set :=
    match a with
    | Comparable_type b => comparable_data b
    | signature => signature_constant
    | operation => operation_constant
    | key => key_constant
    | unit => Datatypes.unit
    | pair a b => data a * data b
    | or a _ b _ => sum (data a) (data b)
    | option a => Datatypes.option (data a)
    | list a => Datatypes.list (data a)
    | set a => set.set (comparable_data a) (compare a)
    | map a b => map.map (comparable_data a) (data b) (compare a)
    | big_map a b => map.map (comparable_data a) (data b) (compare a)
    | lambda a b =>
      sigT (fun tff : Datatypes.bool =>
             instruction_seq None tff (a ::: nil) (b ::: nil))
    | contract a => sig (fun sao : (address_constant * annot_o) => get_address_type sao = Some a )
    | chain_id => chain_id_constant
    end.

  Record proto_env {self_ty : self_info} : Type :=
    mk_proto_env
      {
        create_contract : forall g p annot tff,
          Datatypes.option (comparable_data key_hash) ->
          tez.mutez ->
          syntax.instruction_seq (Some (p, annot)) tff
                             (pair p g ::: nil)
                             (pair (list operation) g ::: nil) ->
          data g -> data (pair operation address);
        transfer_tokens : forall p,
            data p -> tez.mutez -> data (contract p) ->
            data operation;
        set_delegate : Datatypes.option (comparable_data key_hash) ->
                       data operation;
        balance : tez.mutez;
        source : data address;
        sender : data address;
        self :
            match self_ty with
            | None => Datatypes.unit
            | Some (ty, self_annot) =>
              forall annot_opt H,
                data (contract (get_opt (get_entrypoint_opt annot_opt ty self_annot) H))
            end;
        amount : tez.mutez;
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

  Definition no_self
             {self_type}
             (e : proto_env (self_ty := self_type)) :
    proto_env (self_ty := None) :=
    mk_proto_env None
                 (create_contract e)
                 (transfer_tokens e)
                 (set_delegate e)
                 (balance e)
                 (source e)
                 (sender e)
                 tt
                 (amount e)
                 (now e)
                 (hash_key e)
                 (pack e)
                 (unpack e)
                 (blake2b e)
                 (sha256 e)
                 (sha512 e)
                 (check_signature e)
                 (chain_id_ e).

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
    induction t as [|a t]; intros s; simpl.
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
    induction l1 as [|a l1]; simpl.
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
    | Comparable_constant _ x => x
    | Signature_constant x => Mk_sig x
    | Key_constant x => Mk_key x
    | Unit => tt
    | Pair a b => (concrete_data_to_data _ a, concrete_data_to_data _ b)
    | Left a _ _ => inl (concrete_data_to_data _ a)
    | Right b _ _ => inr (concrete_data_to_data _ b)
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
    | @Concrete_big_map a b l =>
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

  Fixpoint comparable_data_to_concrete_data (a : comparable_type) {struct a} :
    comparable_data a -> concrete_data a :=
    match a with
    | Comparable_type_simple _ => fun x => Comparable_constant _ x
    | Cpair _ _ => fun '(x, y) => Pair x (comparable_data_to_concrete_data _ y)
    end.

  Fixpoint data_to_concrete_data (a : type) (H : Is_true (is_packable a)) (x : data a) :
    concrete_data a :=
    match a, H, x with
    | Comparable_type b, _, x => Comparable_constant b x
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
    | contract _, H, _ => match H with end
    | operation, H, _ => match H with end
    | big_map _ _, H, _ => match H with end
    | pair a b, H, (x, y) =>
      Pair (data_to_concrete_data a (Is_true_and_left _ _ H) x)
           (data_to_concrete_data b (Is_true_and_right _ _ H) y)
    | or a an b bn, H, inl x =>
      Left (data_to_concrete_data a (Is_true_and_left _ _ H) x) an bn
    | or a an b bn, H, inr x =>
      Right (data_to_concrete_data b (Is_true_and_right _ _ H) x) an bn
    | lambda a b, _, existT _ tff f => Instruction tff f
    | chain_id, _, x => Chain_id_constant x
    end.

  Definition or_fun a (v : bitwise_variant a) : data a -> data a -> data a :=
    match v with
    | Bitwise_variant_bool => orb
    | Bitwise_variant_nat => N.lor
    end.

  Definition and a b c (v : and_variant a b c) : data a -> data b -> data c :=
    match v with
    | And_variant_bool => andb
    | And_variant_nat => N.land
    | And_variant_int =>
      fun x y => Z.to_N (Z.land x (Z.of_N y))
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

  Definition add_variant_rev a b c (v : add_variant a b c) : add_variant b a c :=
    match v with
    | Add_variant_nat_int => Add_variant_int_nat
    | Add_variant_int_nat => Add_variant_nat_int
    | Add_variant_timestamp_int => Add_variant_int_timestamp
    | Add_variant_int_timestamp => Add_variant_timestamp_int
    | v => v
    end.

  Lemma add_comm a b c v x y :
    @add a b c v x y = @add b a c (add_variant_rev a b c v) y x.
  Proof.
    destruct v; simpl; f_equal.
    - apply N.add_comm.
    - apply Z.add_comm.
    - apply Z.add_comm.
    - apply Z.add_comm.
    - apply Z.add_comm.
    - apply Z.add_comm.
    - apply Z.add_comm.
  Qed.

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

  Definition contract_ (an : annot_o) (p : type) (x : data address) : data (option (contract p)).
  Proof.
    case_eq (get_address_type (x, an)).
    - intros p' H.
      simpl.
      case (type_dec p p').
      + intro; subst p'.
        apply Some.
        eexists.
        eassumption.
      + intro; apply None.
    - intro; apply None.
  Defined.

  Definition implicit_account (x : data key_hash) : data (contract unit).
  Proof.
    simpl.
    exists (Implicit x, None).
    reflexivity.
  Defined.

  Definition address_ a (x : data (contract a)) : data address :=
    match x with exist _ (addr, _) _ => addr end.

  Definition eval_opcode param_ty (env : @proto_env param_ty) {A B : stack_type}
             (o : @opcode param_ty A B) (SA : stack A) : M (stack B) :=
    match o, SA with
      | @APPLY _ a b c D i, (x, (existT _ _ f, SA)) =>
        Return (existT
                    _ _
                    (PUSH _ (data_to_concrete_data _ i x) ;; PAIR ;; f), SA)
      | DUP, (x, SA) => Return (x, (x, SA))
      | SWAP, (x, (y, SA)) => Return (y, (x, SA))
      | UNIT, SA => Return (tt, SA)
      | EQ, (x, SA) => Return ((x =? 0)%Z, SA)
      | NEQ, (x, SA) => Return (negb (x =? 0)%Z, SA)
      | LT, (x, SA) => Return ((x <? 0)%Z, SA)
      | GT, (x, SA) => Return ((x >? 0)%Z, SA)
      | LE, (x, SA) => Return ((x <=? 0)%Z, SA)
      | GE, (x, SA) => Return ((x >=? 0)%Z, SA)
      | @OR _ _ s, (x, (y, SA)) =>
        Return (or_fun _ (bitwise_variant_field _ s) x y, SA)
      | @AND _ _ _ s, (x, (y, SA)) =>
        Return (and _ _ _ (and_variant_field _ _ s) x y, SA)
      | @XOR _ _ s, (x, (y, SA)) =>
        Return (xor _ (bitwise_variant_field _ s) x y, SA)
      | @NOT _ _ s, (x, SA) => Return (not _ _ (not_variant_field _ s) x, SA)
      | @NEG _ _ s, (x, SA) => Return (neg _ (neg_variant_field _ s) x, SA)
      | ABS, (x, SA) => Return (Z.abs_N x, SA)
      | ISNAT, (x, SA) =>
        Return (if (x >=? 0)%Z then (Some (Z.to_N x), SA) else (None, SA))
      | INT, (x, SA) => Return (Z.of_N x, SA)
      | @ADD _ _ _ s, (x, (y, SA)) =>
        let! r := add _ _ _ (add_variant_field _ _ s) x y in
        Return (r, SA)
      | @SUB _ _ _ s, (x, (y, SA)) =>
        let! r := sub _ _ _ (sub_variant_field _ _ s) x y in
        Return (r, SA)
      | @MUL _ _ _ s, (x, (y, SA)) =>
        let! r := mul _ _ _ (mul_variant_field _ _ s) x y in
        Return (r, SA)
      | @EDIV _ _ _ s, (x, (y, SA)) =>
        Return (ediv _ _ _ _ (ediv_variant_field _ _ s) x y, SA)
      | LSL, (x, (y, SA)) => Return (N.shiftl x y, SA)
      | LSR, (x, (y, SA)) => Return (N.shiftr x y, SA)
      | COMPARE, (x, (y, SA)) =>
        Return (comparison_to_int
                    (compare _
                             (data_to_comparable_data _ x)
                             (data_to_comparable_data _ y)), SA)
      | @CONCAT _ _ s _, (x, (y, SA)) =>
        Return (concat _ (stringlike_variant_field _ s) x y, SA)
      | @CONCAT_list _ _ s _, (l, SA) =>
        Return (concat_list _ (stringlike_variant_field _ s) l, SA)
      | @SLICE _ _ i, (n1, (n2, (s, SA))) =>
        Return (slice _ (stringlike_variant_field _ i) n1 n2 s, SA)
      | PAIR, (x, (y, SA)) => Return ((x, y), SA)
      | CAR, ((x, y), SA) => Return (x, SA)
      | CDR, ((x, y), SA) => Return (y, SA)
      | EMPTY_SET a, SA => Return (set.empty _ (compare a), SA)
      | @MEM _ _ _ s _, (x, (y, SA)) =>
        Return (mem _ _
                      (mem_variant_field _ _ s)
                      (data_to_comparable_data _ x)
                      y, SA)
      | @UPDATE _ _ _ _ s _, (x, (y, (z, SA))) =>
        Return (update _ _ _ (update_variant_field _ _ _ s) (data_to_comparable_data _ x) y z, SA)
      | @SIZE _ _ s, (x, SA) =>
        Return (N.of_nat (size _ (size_variant_field _ s) x), SA)
      | EMPTY_MAP k val, SA =>
        Return (map.empty (comparable_data k) (data val) _, SA)
      | EMPTY_BIG_MAP k val, SA =>
        Return (map.empty (comparable_data k) (data val) _, SA)
      | @GET _ _ _ s _, (x, (y, SA)) =>
        Return (get _ _ _
                      (get_variant_field _ _ s)
                      (data_to_comparable_data _ x)
                      y, SA)
      | SOME, (x, SA) => Return (Some x, SA)
      | NONE _, SA => Return (None, SA)
      | LEFT _, (x, SA) => Return (inl x, SA)
      | RIGHT _, (x, SA) => Return (inr x, SA)
      | CONS, (x, (y, SA)) => Return (cons x y, SA)
      | NIL _, SA => Return (nil, SA)
      | TRANSFER_TOKENS, (a, (b, (c, SA))) =>
        Return (transfer_tokens env _ a b c, SA)
      | SET_DELEGATE, (x, SA) => Return (set_delegate env x, SA)
      | BALANCE, SA => Return (balance env, SA)
      | ADDRESS, (x, SA) => Return (address_ _ x, SA)
      | CONTRACT ao p, (x, SA) => Return (contract_ ao p x, SA)
      | SOURCE, SA => Return (source env, SA)
      | SENDER, SA => Return (sender env, SA)
      | AMOUNT, SA => Return (amount env, SA)
      | IMPLICIT_ACCOUNT, (x, SA) => Return (implicit_account x, SA)
      | NOW, SA => Return (now env, SA)
      | PACK, (x, SA) => Return (pack env _ x, SA)
      | UNPACK ty, (x, SA) => Return (unpack env ty x, SA)
      | HASH_KEY, (x, SA) => Return (hash_key env x, SA)
      | BLAKE2B, (x, SA) => Return (blake2b env x, SA)
      | SHA256, (x, SA) => Return (sha256 env x, SA)
      | SHA512, (x, SA) => Return (sha512 env x, SA)
      | CHECK_SIGNATURE, (x, (y, (z, SA))) =>
        Return (check_signature env x y z, SA)
      | DIG n Hlen, SA => Return (stack_dig SA)
      | DUG n Hlen, SA => Return (stack_dug SA)
      | DROP n Hlen, SA =>
        let (S1, S2) := stack_split SA in Return S2
      | CHAIN_ID, SA => Return (chain_id_ env, SA)
    end.

  Definition if_family_destruct {A B t} (i : if_family A B t) (x : data t) : stack A + stack B :=
    match i, x with
    | IF_bool, true => inl tt
    | IF_bool, false => inr tt
    | IF_or _ _ _ _, inl x => inl (x, tt)
    | IF_or _ _ _ _, inr x => inr (x, tt)
    | IF_option a, None => inl tt
    | IF_option a, Some x => inr (x, tt)
    | IF_list a, cons x l => inl (x, (l, tt))
    | IF_list a, nil => inr tt
    end.

  Definition loop_family_destruct {A B t} (i : loop_family A B t) (x : data t) : stack A + stack B :=
    match i, x with
    | LOOP_bool, true => inl tt
    | LOOP_bool, false => inr tt
    | LOOP_or _ _ _ _, inl x => inl (x, tt)
    | LOOP_or _ _ _ _, inr x => inr (x, tt)
    end.

  Fixpoint eval_seq_body
           (eval : forall param_ty tff0 (env : @proto_env param_ty) A B, instruction param_ty tff0 A B -> stack A -> M (stack B))
           {param_ty : self_info} {tff0} (env : @proto_env param_ty) {A : stack_type} {B : stack_type}
           (i : instruction_seq param_ty tff0 A B) (SA : stack A) {struct i} : M (stack B) :=
    match i, SA, env with
    | NOOP, SA, _ => Return SA
    | Tail_fail i, SA, env => eval _ _ env _ _ i SA
    | SEQ B C, SA, env =>
      let! r := eval _ _ env _ _ B SA in
      eval_seq_body eval env C r
    end.

  Fixpoint eval {param_ty : self_info} {tff0} (env : @proto_env param_ty) {A : stack_type} {B : stack_type}
           (i : instruction param_ty tff0 A B) (fuel : Datatypes.nat) (SA : stack A) {struct fuel} : M (stack B) :=
    match fuel with
    | O => Failed _ Out_of_fuel
    | S n =>
      let eval_n {param_ty : self_info} {tff0} (env : @proto_env param_ty)
                 {A : stack_type} {B : stack_type} (i : instruction param_ty tff0 A B)
                 (SA : stack A) : M (stack B) :=
          eval env i n SA in
      match i, SA, env with
      | Instruction_seq i, SA, env =>
        eval_seq_body (@eval_n) env i SA
      | FAILWITH, (x, _), _ =>
        Failed _ (Assertion_Failure _ x)

      (* According to the documentation, FAILWITH's argument should
         not be part of the state reached by the instruction but the
         whole point of this instruction (compared to the FAIL macro)
         is to report the argument to the user. *)

      | IF_ f bt bf, (x, SA), env =>
        match if_family_destruct f x with
        | inl SB => eval_seq_body (@eval_n) env bt (stack_app SB SA)
        | inr SB => eval_seq_body (@eval_n) env bf (stack_app SB SA)
        end
      | LOOP_ f body, (ab, SA), env =>
        match loop_family_destruct f ab with
        | inl SB =>
          let! SC := eval_seq_body (@eval_n) env body (stack_app SB SA) in
          eval_n env (LOOP_ f body) SC
        | inr SB => Return (stack_app SB SA)
        end
      | PUSH a x, SA, _ => Return (concrete_data_to_data _ x, SA)
      | LAMBDA a b code, SA, _ => Return (existT _ _ code, SA)
      | @ITER _ _ _ s _ body, (x, SA), env =>
        match iter_destruct _ _ (iter_variant_field _ s) x with
        | None => Return SA
        | Some (a, y) =>
          let! SB := eval_seq_body (@eval_n) env body (a, SA) in
          eval_n env (ITER body) (y, SB)
        end
      | @MAP _ _ _ s _ body, (x, SA), env =>
        let v := (map_variant_field _ _ s) in
        match map_destruct _ _ _ _ v x with
        | None => Return (map_empty _ _ _ _ v, SA)
        | Some (a, y) =>
          let! (b, SB) := eval_seq_body (@eval_n) env body (a, SA) in
          let! (c, SC) := eval_n env (MAP body) (y, SB) in
          Return (map_insert _ _ _ _ v a b c, SC)
        end
      | CREATE_CONTRACT g p an f, (a, (b, (c, SA))), env =>
        let (oper, addr) := create_contract env g p an _ a b f c in
        Return (oper, (addr, SA))
      | SELF ao H, SA, env => Return (self env ao H, SA)
      | EXEC, (x, (existT _ tff f, SA)), env =>
        let! (y, tt) := eval_seq_body (@eval_n) (no_self env) f (x, tt) in
        Return (y, SA)
      | DIP nl Hlen i, SA, env =>
        let (S1, S2) := stack_split SA in
        let! S3 := eval_seq_body (@eval_n) env i S2 in
        Return (stack_app S1 S3)
      | Instruction_opcode o, SA, env =>
        eval_opcode _ env o SA
      end
    end.

  Definition eval_seq
             {param_ty : self_info} {tff0} (env : @proto_env param_ty) {A : stack_type} {B : stack_type}
             (i : instruction_seq param_ty tff0 A B) (fuel : Datatypes.nat) (SA : stack A) : M (stack B) :=
    eval_seq_body (fun param_ty tff env A B i SA => eval env i fuel SA) env i SA.

  Lemma eval_seq_deterministic_le_aux
             (eval1 eval2 : forall param_ty tff (env : @proto_env param_ty) A B, instruction param_ty tff A B -> stack A -> M (stack B))
             (H : forall param_ty env tff A B (i : instruction param_ty tff A B) st,
                 success (eval1 param_ty tff env A B i st) ->
                 eval1 param_ty tff env A B i st = eval2 param_ty tff env A B i st) :
             forall param_ty env tff A B (i : instruction_seq param_ty tff A B) st,
                 success (eval_seq_body eval1 env i st) ->
                 eval_seq_body eval1 env i st =
                 eval_seq_body eval2 env i st.
  Proof.
    intros param_ty env tff A B i.
    induction i; simpl; auto.
    intros st Hsucc.
    destruct (success_bind _ _ Hsucc) as (x, (H1, H2)).
    rewrite <- H.
    - rewrite H1.
      simpl.
      apply IHi.
      exact H2.
    - rewrite H1.
      constructor.
  Qed.

  (* The evaluator does not depend on the amount of fuel provided *)
  Fixpoint eval_deterministic_le fuel1 :
    forall fuel2,
      fuel1 <= fuel2 ->
      forall {self_type env tff0 A B} (i : instruction self_type tff0 A B) st,
        success (eval env i fuel1 st) ->
        eval env i fuel1 st = eval env i fuel2 st.
  Proof.
    {
      destruct fuel1; intros fuel2 Hle self_type env tff0 A B i st Hsucc.
      - contradiction.
      - destruct fuel2.
        + inversion Hle.
        + apply le_S_n in Hle.
          pose (eval1 := fun param_ty tff env A B (i : instruction param_ty tff A B) st => eval env i fuel1 st).
          pose (eval2 := fun param_ty tff env A B (i : instruction param_ty tff A B) st => eval env i fuel2 st).
          assert (forall param_ty env tff A B (i : instruction param_ty tff A B) st,
                 success (eval1 param_ty tff env A B i st) ->
                 eval1 param_ty tff env A B i st = eval2 param_ty tff env A B i st) as Heval12 by (apply eval_deterministic_le; assumption).
          specialize (eval_seq_deterministic_le_aux eval1 eval2 Heval12); intro Haux.
          simpl.
          destruct i; try reflexivity.
          * apply Haux; assumption.
          * simpl in Hsucc.
            destruct st as (x, st); destruct (if_family_destruct _ x) as [SB|SB];
              rewrite Haux; try assumption; reflexivity.
          * simpl in Hsucc.
            destruct st as (x, st); destruct (loop_family_destruct _ x) as [SB|SB]; clear x.
            -- apply success_bind in Hsucc.
               destruct Hsucc as ((x, stA), (H1, H2)).
               change (fun param_ty tff0 env A B i SA => eval env i fuel1 SA) with eval1 in H1.
               change (fun param_ty tff0 env A B i SA => eval env i fuel1 SA) with eval1.
               change (fun param_ty tff0 env A B i SA => eval env i fuel2 SA) with eval2.
               rewrite <- Haux; try assumption.
               ++ rewrite H1.
                  simpl.
                  apply eval_deterministic_le; assumption.
               ++ rewrite H1.
                  constructor.
            -- reflexivity.
          * destruct st as (x, SA).
            generalize Hsucc; clear Hsucc.
            simpl.
            destruct (iter_destruct (iter_elt_type collection i) collection
                                    (iter_variant_field collection i) x).
            -- destruct d.
               change (fun param_ty tff0 env A B i SA => eval env i fuel1 SA) with eval1.
               change (fun param_ty tff0 env A B i SA => eval env i fuel2 SA) with eval2.
               intro Hsucc.
               rewrite <- Haux.
               ++ destruct (success_bind _ _ Hsucc) as (SB, (Ha, Hb)).
                  rewrite Ha.
                  simpl.
                  apply eval_deterministic_le; assumption.
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
               change (fun param_ty tff0 env A B i SA => eval env i fuel1 SA) with eval1.
               change (fun param_ty tff0 env A B i SA => eval env i fuel2 SA) with eval2.
               intro Hsucc.
               rewrite <- Haux; try assumption.
               ++ destruct (success_bind _ _ Hsucc) as ((c, SC), (Ha, Hb)).
                  destruct (success_bind _ _ Hb) as ((dd, SD), (Hm, _)).
                  rewrite Ha.
                  simpl.
                  rewrite <- (eval_deterministic_le fuel1 fuel2); try assumption.
                  ** reflexivity.
                  ** rewrite Hm.
                     constructor.
               ++ apply success_bind_arg in Hsucc.
                  assumption.
            -- reflexivity.
          * destruct st as (x, ((tff, f), SA)).
            f_equal.
            rewrite Haux; try assumption.
            -- reflexivity.
            -- simpl in Hsucc.
               apply success_bind_arg in Hsucc.
               assumption.
          * simpl in Hsucc.
            destruct (stack_split st); rewrite Haux; try assumption.
            -- reflexivity.
            -- destruct (success_bind _ _ Hsucc) as (x, (H1, H2)).
               apply success_eq_return in H1.
               exact H1.
    }
  Qed.

  Lemma eval_seq_deterministic_le fuel1 fuel2 :
      fuel1 <= fuel2 ->
      forall {self_type env tff0 A B} (i : instruction_seq self_type tff0 A B) st,
        success (eval_seq env i fuel1 st) ->
        eval_seq env i fuel1 st = eval_seq env i fuel2 st.
  Proof.
    pose (eval1 := fun param_ty tff env A B (i : instruction param_ty tff A B) st => eval env i fuel1 st).
    pose (eval2 := fun param_ty tff env A B (i : instruction param_ty tff A B) st => eval env i fuel2 st).
    intro H.
    apply (eval_seq_deterministic_le_aux eval1 eval2).
    apply eval_deterministic_le; assumption.
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

  Definition eval_precond_opcode {self_type} (env : @proto_env self_type)
             A B (o : @opcode self_type A B) (psi : stack B -> Prop) (SA : stack A) : Prop :=
    match o, env, psi, SA with
    | @APPLY _ a b c D i, env, psi, (x, (existT _ _ f, SA)) =>
      psi (existT _ _ (PUSH _ (data_to_concrete_data _ i x) ;; Instruction_opcode PAIR ;; f), SA)
    | DUP, env, psi, (x, SA) => psi (x, (x, SA))
    | SWAP, env, psi, (x, (y, SA)) => psi (y, (x, SA))
    | UNIT, env, psi, SA => psi (tt, SA)
    | EQ, env, psi, (x, SA) => psi ((x =? 0)%Z, SA)
    | NEQ, env, psi, (x, SA) => psi (negb (x =? 0)%Z, SA)
    | LT, env, psi, (x, SA) => psi ((x <? 0)%Z, SA)
    | GT, env, psi, (x, SA) => psi ((x >? 0)%Z, SA)
    | LE, env, psi, (x, SA) => psi ((x <=? 0)%Z, SA)
    | GE, env, psi, (x, SA) => psi ((x >=? 0)%Z, SA)
    | @OR _ _ s _, env, psi, (x, (y, SA)) => psi (or_fun _ (bitwise_variant_field _ s) x y, SA)
    | @AND _ _ _ s _, env, psi, (x, (y, SA)) => psi (and _ _ _ (and_variant_field _ _ s) x y, SA)
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
    | @SIZE _ _ s, env, psi, (x, SA) => psi (N.of_nat (size _ (size_variant_field _ s) x), SA)
    | EMPTY_MAP k val, env, psi, SA => psi (map.empty (comparable_data k) (data val) _, SA)
    | EMPTY_BIG_MAP k val, env, psi, SA => psi (map.empty (comparable_data k) (data val) _, SA)
    | @GET _ _ _ s _, env, psi, (x, (y, SA)) => psi (get _ _ _ (get_variant_field _ _ s) (data_to_comparable_data _ x) y, SA)
    | SOME, env, psi, (x, SA) => psi (Some x, SA)
    | NONE _, env, psi, SA => psi (None, SA)
    | LEFT _, env, psi, (x, SA) => psi (inl x, SA)
    | RIGHT _, env, psi, (x, SA) => psi (inr x, SA)
    | CONS, env, psi, (x, (y, SA)) => psi (cons x y, SA)
    | NIL _, env, psi, SA => psi (nil, SA)
    | TRANSFER_TOKENS, env, psi, (a, (b, (c, SA))) =>
      psi (transfer_tokens env _ a b c, SA)
    | SET_DELEGATE, env, psi, (x, SA) =>
      psi (set_delegate env x, SA)
    | BALANCE, env, psi, SA => psi (balance env, SA)
    | ADDRESS, env, psi, (x, SA) => psi (address_ _ x, SA)
    | CONTRACT ao p, env, psi, (x, SA) => psi (contract_ ao p x, SA)
    | SOURCE, env, psi, SA => psi (source env, SA)
    | SENDER, env, psi, SA => psi (sender env, SA)
    | AMOUNT, env, psi, SA => psi (amount env, SA)
    | IMPLICIT_ACCOUNT, env, psi, (x, SA) => psi (implicit_account x, SA)
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
    | DROP n Hlen, env, psi, SA =>
      let (S1, S2) := stack_split SA in psi S2
    | CHAIN_ID, env, psi, SA => psi (chain_id_ env, SA)
    end.

  Fixpoint eval_seq_precond_body_aux
           (eval_precond_n : forall {self_type},
               @proto_env self_type ->
               forall {tff0 A B},
                 instruction self_type tff0 A B ->
                 (stack B -> Prop) -> stack A -> Prop)
           {self_type} env tff0 A B
           (i : instruction_seq self_type tff0 A B)
           (psi : stack B -> Prop)
           (SA : stack A) : Prop :=
    match i, env, psi, SA with
    | NOOP, env, psi, st => psi st
    | SEQ B C, env, psi, st =>
      eval_precond_n env B (@eval_seq_precond_body_aux (@eval_precond_n) _ env _ _ _ C psi) st
    | Tail_fail i, env, psi, st =>
      eval_precond_n env i psi st
    end.

  Definition eval_seq_precond_body
           (eval_precond_n : forall {self_type},
               @proto_env self_type ->
               forall {tff0 A B},
                 instruction self_type tff0 A B ->
                 (stack B -> Prop) -> stack A -> Prop)
           {self_type} env tff0 : forall A B
           (i : instruction_seq self_type tff0 A B)
           (psi : stack B -> Prop)
           (SA : stack A), Prop :=
    if tff0 then fun A B i psi SA => false else @eval_seq_precond_body_aux (@eval_precond_n) self_type env tff0.

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
    | Instruction_seq i, env, psi, SA =>
      eval_seq_precond_body (@eval_precond_n) env _ _ _ i psi SA
    | FAILWITH, _, _, _ => false

    | @IF_ _ _ _ tffa tffb _ _ _ IF_bool bt bf, env, psi, (x, SA) =>
      match tffa, tffb with
      | false, true =>
        x = true /\ eval_seq_precond_body (@eval_precond_n) env _ _ _ bt psi SA
      | true, false =>
        x = false /\ eval_seq_precond_body (@eval_precond_n) env _ _ _ bf psi SA
      | true, true =>
        false
      | false, false =>
      if x then eval_seq_precond_body (@eval_precond_n) env _ _ _ bt psi SA
      else eval_seq_precond_body (@eval_precond_n) env _ _ _ bf psi SA
      end
    | @IF_ _ _ _ tffa tffb _ _ _ (IF_or a an b bn) bt bf, env, psi, (x, SA) =>
      match tffa, tffb with
      | false, true =>
        exists y,
        x = inl y /\
        eval_seq_precond_body (@eval_precond_n) env _ _ _ bt psi (y, SA)
      | true, false =>
        exists y,
        x = inr y /\ eval_seq_precond_body (@eval_precond_n) env _ _ _ bf psi (y, SA)
      | true, true =>
        false
      | false, false =>
        match x with
        | inl y => eval_seq_precond_body (@eval_precond_n) env _ _ _ bt psi (y, SA)
        | inr y => eval_seq_precond_body (@eval_precond_n) env _ _ _ bf psi (y, SA)
        end
      end
    | @IF_ _ _ _ tffa tffb _ _ _ (IF_option a) bt bf, env, psi, (x, SA) =>
      match tffa, tffb with
      | false, true =>
        x = None /\ eval_seq_precond_body (@eval_precond_n) env _ _ _ bt psi SA
      | true, false =>
        exists y,
        x = Some y /\ eval_seq_precond_body (@eval_precond_n) env _ _ _ bf psi (y, SA)
      | true, true =>
        false
      | false, false =>
        match x with
        | None => eval_seq_precond_body (@eval_precond_n) env _ _ _ bt psi SA
        | Some y => eval_seq_precond_body (@eval_precond_n) env _ _ _ bf psi (y, SA)
        end
      end
    | @IF_ _ _ _ tffa tffb _ _ _ (IF_list a) bt bf, env, psi, (x, SA) =>
      match tffa, tffb with
      | false, true =>
        exists (hd : data a) (tl : data (list a)),
        x = cons hd tl /\ eval_seq_precond_body (@eval_precond_n) env _ _ _ bt psi (hd, (tl, SA))
      | true, false =>
        x = nil /\ eval_seq_precond_body (@eval_precond_n) env _ _ _ bf psi SA
      | true, true =>
        false
      | false, false =>
        match x with
        | cons hd tl => eval_seq_precond_body (@eval_precond_n) env _ _ _ bt psi (hd, (tl, SA))
        | nil => eval_seq_precond_body (@eval_precond_n) env _ _ _ bf psi SA
        end
      end
    | LOOP_ f body, env, psi, (x, SA) =>
      match (loop_family_destruct f x) with
      | inl SB =>
        eval_seq_precond_body (@eval_precond_n) env _ _ _ body
                           (eval_precond_n env (LOOP_ f body) psi)
                           (stack_app SB SA)
      | inr SB => psi (stack_app SB SA)
      end
    | EXEC, env, psi, (x, (existT _ _ f, SA)) =>
      eval_seq_precond_body (@eval_precond_n) (no_self env) _ _ _ f (fun '(y, tt) => psi (y, SA)) (x, tt)
    | PUSH a x, env, psi, SA => psi (concrete_data_to_data _ x, SA)
    | LAMBDA a b code, env, psi, SA => psi (existT _ _ code, SA)
    | @ITER _ _ _ s _ body, env, psi, (x, SA) =>
      match iter_destruct _ _ (iter_variant_field _ s) x with
      | None => psi SA
      | Some (a, y) =>
        eval_seq_precond_body (@eval_precond_n)
          env _ _ _ body
          (fun SB => eval_precond_n env (ITER body) psi (y, SB))
          (a, SA)
      end
    | @MAP _ _ _ s _ body, env, psi, (x, SA) =>
      let v := (map_variant_field _ _ s) in
      match map_destruct _ _ _ _ v x with
      | None => psi (map_empty _ _ _ _ v, SA)
      | Some (a, y) =>
        eval_seq_precond_body (@eval_precond_n)
          env _ _ _ body
          (fun '(b, SB) =>
             eval_precond_n
               env (MAP body)
               (fun '(c, SC) => psi (map_insert _ _ _ _ v a b c, SC))
               (y, SB))
          (a, SA)
      end
    | CREATE_CONTRACT g p an f, env, psi, (a, (b, (c, SA))) =>
      let (oper, addr) := create_contract env g p an _ a b f c in
      psi (oper, (addr, SA))
    | SELF ao H, env, psi, SA => psi (self env ao H, SA)
    | DIP n Hlen i, env, psi, SA =>
      let (S1, S2) := stack_split SA in
      eval_seq_precond_body (@eval_precond_n) env _ _ _ i (fun SB => psi (stack_app S1 SB)) S2
    | Instruction_opcode o, env, psi, SA =>
      eval_precond_opcode env _ _ o psi SA
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

  Definition eval_seq_precond (fuel : Datatypes.nat) :
    forall {self_type} env {tff0 A B},
      instruction_seq self_type tff0 A B ->
      (stack B -> Prop) -> (stack A -> Prop) :=
      @eval_seq_precond_body (@eval_precond fuel).

  Lemma eval_precond_opcode_correct {sty env A B} (o : opcode A B) st psi :
    precond (eval_opcode sty env o st) psi <-> eval_precond_opcode env _ _ o psi st.
  Proof.
    destruct o; simpl;
      try reflexivity;
      try (destruct st; reflexivity);
      try (destruct st as (x, (y, st)); reflexivity);
      try (destruct st as (x, (y, st)); rewrite precond_bind; reflexivity);
      try (destruct st as (x, (y, (z, SA))); reflexivity);
      try (destruct st as ((x, y), st); reflexivity).
    - destruct st as (x, ((tff, y), st)); reflexivity.
    - destruct (stack_split st); reflexivity.
  Qed.

  Lemma precond_eval_tf_both :
    (forall sty A B (i : instruction sty true A B) fuel env psi stA, precond (eval env i fuel stA) psi = false) *
    (forall sty A B (i : instruction_seq sty true A B) fuel env psi stA, precond (eval_seq env i fuel stA) psi = false).
  Proof.
    apply tail_fail_induction_and_seq; intros; (destruct fuel as [|fuel]; simpl; [intuition|]); simpl.
    - destruct stA; simpl.
      reflexivity.
    - destruct stA as (x, stA); simpl.
      destruct (if_family_destruct f x); [apply H|apply H0].
    - change (eval_seq env (SEQ i1 i2) ?fuel stA) with
          (let! r := eval env i1 fuel stA in eval_seq env i2 fuel r).
      rewrite precond_bind.
      destruct (eval env i1 (S fuel) stA); simpl.
      + reflexivity.
      + apply H.
    - change (eval_seq env (Tail_fail i) ?fuel stA) with
          (eval env i fuel stA).
      apply H.
    - apply H.
  Qed.

  Lemma precond_eval_tf : forall sty A B (i : instruction sty true A B) fuel env psi stA, precond (eval env i fuel stA) psi = false.
  Proof.
    apply precond_eval_tf_both.
  Qed.

  Lemma precond_eval_seq_tf : forall sty A B (i : instruction_seq sty true A B) fuel env psi stA, precond (eval_seq env i fuel stA) psi = false.
  Proof.
    apply precond_eval_tf_both.
  Qed.

  Lemma eval_seq_precond_correct_aux n
        (eval_precond_correct : forall sty env tff0 A B (i : instruction sty tff0 A B) st psi,
            precond (eval env i n st) psi <-> eval_precond n env i psi st)
        {sty env tff0 A B} (i : instruction_seq sty tff0 A B) st psi :
    precond (eval_seq env i n st) psi <-> eval_seq_precond n env i psi st.
  Proof.
    unfold eval_seq_precond in *.
    induction i; simpl; fold data stack.
     - reflexivity.
     - rewrite precond_eval_seq_tf.
       reflexivity.
     - destruct tff.
       + rewrite precond_eval_seq_tf.
         reflexivity.
       + unfold eval_seq.
         simpl.
         rewrite precond_bind.
         rewrite <- eval_precond_correct.
         apply precond_eqv.
         intro SB.
         apply IHi.
  Qed.

  Lemma eval_precond_correct {sty env tff0 A B} (i : instruction sty tff0 A B) n st psi :
    precond (eval env i n st) psi <-> eval_precond n env i psi st.
  Proof.
    generalize sty env tff0 A B i st psi; clear sty env tff0 A B i st psi.
    induction n; intros sty env tff0 A B i st psi; [simpl; intuition|].
    specialize (@eval_seq_precond_correct_aux n IHn).
    intro eval_seq_precond_correct.
    unfold eval_seq_precond in *.

    destruct i; fold data stack; simpl.
    - apply eval_seq_precond_correct.
    - destruct st; reflexivity.
    - destruct st as (x, st).
      case_eq (if_family_destruct i x); intros;
        refine (iff_trans (eval_seq_precond_correct _ _ _ _ _ _ _ _) _).
      + destruct i; destruct x; try discriminate; repeat destruct s;
          destruct tffa; try contradiction; destruct tffb;
            simpl; try reflexivity; (intuition + fail);
              simpl in H; try discriminate; try injection H; intros; subst;
                try assumption.
        * destruct H0 as (y, (He, _)); discriminate.
        * eexists; intuition.
        * destruct H0 as (y, (He, H1)); injection He; intros; subst; intuition.
        * destruct H0 as (y, (He, _)); discriminate.
        * eexists; eexists; intuition.
        * destruct H0 as (hd, (tl, (He, H1))); injection He; intros; subst; intuition.
      + destruct i; destruct x; try discriminate; repeat destruct s;
          destruct tffa; try contradiction; destruct tffb;
            simpl; try reflexivity; (intuition + fail);
              simpl in H; try discriminate; try injection H; intros; subst;
                try assumption.
        * eexists; intuition.
        * destruct H0 as (y, (He, H1)); injection He; intros; subst; intuition.
        * destruct H0 as (y, (He, _)); discriminate.
        * eexists; intuition.
        * destruct H0 as (y, (He, H1)); injection He; intros; subst; intuition.
        * destruct H0 as (hd, (tl, (He, _))); discriminate.
    - destruct st as (x, st); destruct (loop_family_destruct _ x).
      + rewrite precond_bind.
        change (eval_seq_precond_body_aux ?en env false ?A ?B ?i ?psi ?st)
          with (eval_seq_precond_body en env false A B i psi st).
        rewrite <- eval_seq_precond_correct.
        apply precond_eqv.
        intro st'.
        apply IHn.
      + simpl. reflexivity.
    - reflexivity.
    - reflexivity.
    - destruct st as (x, st).
      destruct (iter_destruct (iter_elt_type collection i) collection
                              (iter_variant_field collection i) x) as [(hd, tl)|].
      + rewrite precond_bind.
        change (eval_seq_precond_body_aux ?en env false ?A ?B ?i ?psi ?st)
          with (eval_seq_precond_body en env false A B i psi st).
        rewrite <- eval_seq_precond_correct.
        apply precond_eqv.
        intro SA.
        apply IHn.
      + reflexivity.
    - destruct st as (x, st).
      destruct (map_destruct (map_in_type collection b i) b collection
                             (map_out_collection_type collection b i)
                             (map_variant_field collection b i) x) as [(hd, tl)|].
      + rewrite precond_bind.
        change (eval_seq_precond_body_aux ?en env false ?A ?B ?i ?psi ?st)
          with (eval_seq_precond_body en env false A B i psi st).
        rewrite <- eval_seq_precond_correct.
        apply precond_eqv.
        intros (bb, SA).
        rewrite precond_bind.
        rewrite <- IHn.
        apply precond_eqv.
        intros (c, B).
        reflexivity.
      + reflexivity.
    - destruct st as (a, (b, (c, SA))).
      destruct (create_contract env g p an _ a b i c).
      reflexivity.
    - reflexivity.
    - destruct st as (x, ((tff, f), st)).
      rewrite precond_bind.
      rewrite <- (eval_seq_precond_correct _ _ _ _ _ f (x, tt) (fun '(y, tt) => psi (y, st))).
      apply precond_eqv.
      intros (y, []).
      simpl.
      reflexivity.
    - destruct (stack_split st).
      rewrite precond_bind.
      apply eval_seq_precond_correct.
    - apply eval_precond_opcode_correct.
  Qed.

  Lemma eval_precond_eqv self_type env tff A B (i : instruction self_type tff A B) n st phi psi :
    (forall st, phi st <-> psi st) ->
    eval_precond n env i phi st <-> eval_precond n env i psi st.
  Proof.
    intro H.
    do 2 rewrite <- eval_precond_correct.
    apply precond_eqv.
    assumption.
  Qed.

  Lemma eval_seq_precond_correct {sty env tff0 A B} (i : instruction_seq sty tff0 A B) n st psi :
    precond (eval_seq env i n st) psi <-> eval_seq_precond n env i psi st.
  Proof.
    apply eval_seq_precond_correct_aux.
    intros; apply eval_precond_correct.
  Qed.

  Lemma eval_seq_precond_eqv self_type env tff A B (i : instruction_seq self_type tff A B) n st phi psi :
    (forall st, phi st <-> psi st) ->
    eval_seq_precond n env i phi st <-> eval_seq_precond n env i psi st.
  Proof.
    intro H.
    do 2 rewrite <- eval_seq_precond_correct.
    apply precond_eqv.
    assumption.
  Qed.

  Lemma eval_seq_assoc_aux {sty env tffa tffb A B C}
        (i1 : instruction_seq sty tffa A B)
        (i2 : instruction_seq sty tffb B C) H n st psi :
    eval_seq_precond n env (instruction_app_aux i1 H i2) psi st <->
    eval_seq_precond n env i1 (eval_seq_precond n env i2 psi) st.
  Proof.
    induction i1.
    - reflexivity.
    - discriminate.
    - destruct tffb.
      + simpl eval_seq_precond.
        rewrite <- eval_seq_precond_correct.
        destruct (eval_seq env (SEQ i i1) n st); reflexivity.
      + subst tff.
        simpl.
        apply eval_precond_eqv.
        intro stB.
        apply (IHi1 _ _ _ _).
  Qed.

  Lemma eval_seq_assoc {sty env tff0 A B C}
        (i1 : instruction_seq sty Datatypes.false A B)
        (i2 : instruction_seq sty tff0 B C) n st psi :
    eval_seq_precond n env (instruction_app i1 i2) psi st <->
    eval_seq_precond n env i1 (eval_seq_precond n env i2 psi) st.
  Proof.
    apply eval_seq_assoc_aux.
  Qed.

  (* This is a helper lemma to reason on the semantics of the ITER instruction
     on lists in the particular (very common) case in which we know an upper
     bound to the fuel consumed by the ITER body (independent of the stack).

     In this special case, we show that precond (eval ... ITER) ... psi is
     a List.fold_right whose accumulator is the post condition.
   *)
  Lemma precond_iter_bounded st tff env a (l : data (list a)) A (body : instruction_seq st tff (a ::: A) A)
        fuel_bound body_spec
    (Hbody_correct :
       forall fuel (x : data a) (input_stack : stack A) (psi : stack A -> Prop),
        fuel_bound <= fuel ->
        precond (eval_seq env body fuel (x, input_stack)) psi
        <-> body_spec psi x input_stack)
    (Hbody_spec_extensional :
       forall psi1 psi2 x input_stack,
        (forall x, psi1 x <-> psi2 x) ->
        body_spec psi1 x input_stack <-> body_spec psi2 x input_stack) :
    forall fuel input_stack psi
      (Hfuel_bound : S fuel_bound + List.length l <= fuel),
      precond (eval env (ITER body) fuel (l, input_stack)) psi
      <->
      List.fold_right (fun x psi st => body_spec psi x st) psi l input_stack.
  Proof.
    induction l; intros fuel input_stack psi Hfuel.
    - simpl.
      more_fuel.
      reflexivity.
    - simpl.
      simpl in Hfuel.
      more_fuel.
      simpl.
      rewrite precond_bind.
      unfold eval_seq in Hbody_correct.
      rewrite Hbody_correct.
      + apply Hbody_spec_extensional.
        intro s.
        apply IHl.
        rewrite <- plus_n_Sm in Hfuel.
        exact Hfuel.
      + generalize Hfuel.
        lia.
  Qed.

  Definition precond_iter_fun st env a A fuel (body : instruction_seq st Datatypes.false (a ::: A) A) (x : data a) (psiacc : ((stack A -> Prop) * Datatypes.nat))
    :=
      (fun (st : stack A) => precond (eval_seq env body (snd psiacc + fuel) (x, st)) (fst psiacc),
                 S (snd psiacc)).

  Lemma precond_iter_fun_fold_right_length st env a A l psi body fuel :
    snd (List.fold_right (precond_iter_fun st env a A fuel body) (psi, 1) l) + fuel
    = List.length l + S fuel.
  Proof.
    induction l.
    - simpl.
      reflexivity.
    - simpl.
      f_equal.
      exact IHl.
  Qed.

  Lemma precond_iter st env a (l : data (list a)) A (body : instruction_seq st _ (a ::: A) A) :
    forall fuel (input_stack : stack A) (psi : stack A -> Prop),
    precond (eval env (ITER body) (List.length l + S fuel) (l, input_stack)) psi
    <->
    fst (List.fold_right (precond_iter_fun st env a A fuel body)
                  (psi, 1)
                  l) input_stack.
  Proof.
    induction l; intros fuel input_stack psi; simpl.
    - reflexivity.
    - rewrite precond_bind.
      rewrite precond_iter_fun_fold_right_length.
      apply precond_eqv.
      intros s.
      apply IHl.
  Qed.

  Lemma fold_eval_precond fuel :
    @eval_precond_body (@eval_precond fuel) =
    @eval_precond (S fuel).
  Proof.
    reflexivity.
  Qed.

  Lemma fold_eval_seq_precond_aux self_type fuel env :
    @eval_seq_precond_body_aux (@eval_precond fuel) self_type env false =
    @eval_seq_precond fuel self_type env false.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_eval_seq_precond fuel :
    @eval_seq_precond_body (@eval_precond fuel) =
    @eval_seq_precond fuel.
  Proof.
    reflexivity.
  Qed.

  Lemma precond_eval_iff :
    forall sf tff fuel env
           (A B : stack_type)
           (lam : instruction sf tff A B)
           psi psi',
      (forall st', psi st' <-> psi' st') ->
      forall st,
        eval_precond fuel env lam psi st <->
        eval_precond fuel env lam psi' st.
  Proof.
    intros sf tff fuel env0 A B lam psi psi' H st.
    do 2 rewrite <- eval_precond_correct.
    apply precond_eqv. assumption.
  Qed.

End Semantics.
