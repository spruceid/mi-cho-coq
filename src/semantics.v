(* Oprational semantics of the Michelson language *)

Require Import syntax.
Require Import ZArith.
Require Import String.
Require NPeano.

Require Import comparable error.
Import syntax.

Section semantics.

  Context {get_contract_type : contract_constant -> M type}.

  Implicit Types (get_contract_type : contract_constant -> M type).

  Fixpoint data (a : type) {struct a} : Set :=
    match a with
    | Comparable_type b => comparable_data b
    | address => address_constant
    | signature => signature_constant
    | operation => operation_constant
    | key => key_constant
    | unit => Datatypes.unit
    | pair a b => data a * data b
    | or a b => sum (data a) (data b)
    | option_ a => option (data a)
    | list_ a => list (data a)
    | set_ a => set.set (comparable_data a) (compare a)
    | map a b => map.map (comparable_data a) (data b) (compare a)
    | big_map a b => map.map (comparable_data a) (data b) (compare a)
    | lambda a b => @instruction get_contract_type (a ::: nil) (b ::: nil)
    | contract a => {s : contract_constant | get_contract_type s = Return _ a }
    end.

  Record node : Set :=
    mk_node
      {
        create_contract : forall g p,
          comparable_data key_hash ->
          option (comparable_data key_hash) ->
          Datatypes.bool -> Datatypes.bool -> tez.mutez ->
          data (lambda (pair p g) (pair (list_ operation) g)) ->
          data g -> M (data (pair operation address));
        create_account :
          comparable_data key_hash ->
          option (comparable_data key_hash) ->
          Datatypes.bool -> tez.mutez ->
          M (data operation * data (contract unit));
        transfer_tokens : forall p,
            data p -> tez.mutez -> data (contract p) ->
            M (data operation);
        set_delegate : option (comparable_data key_hash) ->
                       M (data operation);
        balance : M tez.mutez;
        address_ : forall p, data (contract p) -> M (data address);
        contract_ : forall p, data address -> M (option (data (contract p)));
        source : M (data address);
        sender : M (data address);
        self : forall p, M (data (contract p));
        amount : M tez.mutez;
        implicit_account :
          comparable_data key_hash -> M (data (contract unit));
        steps_to_quota : M N;
        now : M (comparable_data timestamp);
        hash_key : data key -> M (comparable_data key_hash);
        pack : forall a, data a -> M str;
        unpack : forall a, str -> M (option (data a));
        blake2b : str -> M str;
        sha256 : str -> M str;
        sha512 : str -> M str;
        check_signature :
          data key -> data signature -> String.string -> M Datatypes.bool;
        read_contract_constant a : forall cst : contract_constant,
            get_contract_type cst = Return _ a -> M (data (contract a))
      }.

  Variable nd : node.

  Fixpoint stack (t : stack_type) : Set :=
    match t with
    | nil => Datatypes.unit
    | cons a A => data a * stack A
    end.



  Fixpoint concrete_data_to_data (a : type) (d : concrete_data a) : data a :=
    match d with
    | Int_constant x => x
    | Nat_constant x => x
    | String_constant x => x
    | Timestamp_constant x => x
    | Signature_constant x => Mk_sig x
    | Key_constant x => Mk_key x
    | Key_hash_constant x => Mk_key_hash x
    | Mutez_constant (Mk_mutez x) => x
    | @Contract_constant _ a x H => exist _ x H
    | Unit => tt
    | True_ => true
    | False_ => false
    | Pair a b => (concrete_data_to_data _ a, concrete_data_to_data _ b)
    | Left a => inl (concrete_data_to_data _ a)
    | Right b => inr (concrete_data_to_data _ b)
    | Some_ a => Some (concrete_data_to_data _ a)
    | None_ => None
    | Concrete_list l => List.map (concrete_data_to_data _) l
    | @Concrete_set _ a l =>
      (fix concrete_data_set_to_data (l : list (concrete_data a)) :=
         match l with
         | nil => set.empty _ _
         | cons x l =>
           set.insert
             (data a)
             (comparable.compare a)
             (comparable.compare_eq_iff a)
             (comparable.lt_trans a)
             (comparable.gt_trans a)
             (concrete_data_to_data a x)
             (concrete_data_set_to_data l)
         end) l
    | @Concrete_map _ a b l =>
      (fix concrete_data_map_to_data
           (l : Datatypes.list (elt_pair (concrete_data a) (concrete_data b))) :=
         match l with
         | nil => map.empty _ _ _
         | cons (Elt _ _ x y) l =>
           map.update
             (data a)
             (data b)
             (comparable.compare a)
             (comparable.compare_eq_iff a)
             (comparable.lt_trans a)
             (comparable.gt_trans a)
             (concrete_data_to_data _ x)
             (Some (concrete_data_to_data _ y))
             (concrete_data_map_to_data l)
         end) l
    | Instruction i => i
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
    | Add_variant_nat_nat => fun x y => Return _ (x + y)%N
    | Add_variant_nat_int => fun x y => Return _ (Z.of_N x + y)%Z
    | Add_variant_int_nat => fun x y => Return _ (x + Z.of_N y)%Z
    | Add_variant_int_int => fun x y => Return _ (x + y)%Z
    | Add_variant_timestamp_int => fun x y => Return _ (x + y)%Z
    | Add_variant_int_timestamp => fun x y => Return _ (x + y)%Z
    | Add_variant_tez_tez =>
      fun x y => tez.of_Z (tez.to_Z x + tez.to_Z y)
    end.


  Definition sub a b c (v : sub_variant a b c) : data a -> data b -> M (data c) :=
    match v with
    | Sub_variant_nat_nat => fun x y => Return _ (Z.of_N x - Z.of_N y)%Z
    | Sub_variant_nat_int => fun x y => Return _ (Z.of_N x - y)%Z
    | Sub_variant_int_nat => fun x y => Return _ (x - Z.of_N y)%Z
    | Sub_variant_int_int => fun x y => Return _ (x - y)%Z
    | Sub_variant_timestamp_int => fun x y => Return _ (x - y)%Z
    | Sub_variant_timestamp_timestamp => fun x y => Return _ (x - y)%Z
    | Sub_variant_tez_tez => fun x y => tez.of_Z (tez.to_Z x - tez.to_Z y)
    end.

  Definition mul a b c (v : mul_variant a b c) : data a -> data b -> M (data c) :=
    match v with
    | Mul_variant_nat_nat => fun x y => Return _ (x * y)%N
    | Mul_variant_nat_int => fun x y => Return _ (Z.of_N x * y)%Z
    | Mul_variant_int_nat => fun x y => Return _ (x * Z.of_N y)%Z
    | Mul_variant_int_int => fun x y => Return _ (x * y)%Z
    | Mul_variant_tez_nat => fun x y => tez.of_Z (tez.to_Z x * Z.of_N y)
    | Mul_variant_nat_tez => fun x y => tez.of_Z (Z.of_N x * tez.to_Z y)
    end.

  Definition ediv_Z x y :=
    if (y =? 0)%Z then None else Some (x / y, Z.to_N (x mod y))%Z.
  Definition ediv_N x y :=
    if (y =? 0)%N then None else Some (x / y, x mod y)%N.

  Definition ediv a b c d (v : ediv_variant a b c d) : data a -> data b -> data (option_ (pair c d)) :=
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
          | Return _ quo, Return _ rem => Some (quo, rem)
          | _, _ => None
          end
        end
    | Ediv_variant_tez_tez =>
      fun x y =>
        match ediv_Z (tez.to_Z x) (tez.to_Z y) with
        | None => None
        | Some (quo, rem) =>
          match tez.of_Z (Z.of_N rem) with
          | Return _ rem => Some (Z.to_N quo, rem)
          | _ => None
          end
        end
    end.

  Definition concat a (v : stringlike_variant a) : data a -> data a -> data a :=
    match v with
    | Stringlike_variant_string => String.append
    | Stringlike_variant_bytes => String.append
    end.

  Definition slice a (v : stringlike_variant a) : data nat -> data nat -> data a -> data (option_ a) :=
    match v with
    | Stringlike_variant_string =>
      fun (n1 n2 : N) (s : data string) =>
        if (n1 + n2 <=? N.of_nat (String.length s))%N then
          (Some (String.substring (N.to_nat n1) (N.to_nat n2) s)
           : data (option_ string))
        else None
    | Stringlike_variant_bytes =>
      fun n1 n2 s =>
        if (n1 + n2 <=? N.of_nat (String.length s))%N then
          Some (String.substring (N.to_nat n1) (N.to_nat n2) s)
        else None
    end.

  Definition mem a b (v : mem_variant a b) : data a -> data b -> data bool :=
    match v with
    | Mem_variant_set a =>
      fun (x : data a) (y : data (set_ a)) => set.mem _ _ (compare_eq_iff a) x y
    | Mem_variant_map _ _ => map.mem _ _ _
    | Mem_variant_bigmap _ _ => map.mem _ _ _
    end.

  Definition update a b c (v : update_variant a b c) :
    data a -> data b -> data c -> data c :=
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
    | Size_variant_set a => set.size (data a) (compare a)
    | Size_variant_map k v => map.size (data k) (data v) (compare k)
    | Size_variant_string => String.length
    | Size_variant_bytes => String.length
    end.

  Definition iter_destruct a b (v : iter_variant a b)
    : data b -> data (option_ (pair a b)) :=
    match v with
    | Iter_variant_set _ => set.destruct _ _
    | Iter_variant_map _ _ => set.destruct _ _
    | Iter_variant_list _ =>
      fun l => match l with
               | nil => None
               | cons a l => Some (a, l)
               end
    end.

  Definition get k val c (v : get_variant k val c)
    : data k -> data c -> data (option_ val) :=
    match v with
    | Get_variant_map _ _ => map.get _ _ _
    | Get_variant_bigmap _ _ => map.get _ _ _
    end.

  Definition map_destruct a b ca cb (v : map_variant a b ca cb)
    : data ca -> data (option_ (pair a ca)) :=
    match v with
    | Map_variant_map _ _ _ => set.destruct _ _
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
        map.update _ _ _ (comparable.compare_eq_iff _) (comparable.lt_trans _) (comparable.gt_trans _) k (Some v) m
    | Map_variant_list _ _ =>
      fun _ => cons
    end.



  (* The gas argument is used to ensure termination, it is not the
  amount of gas that is actually required to run the contract because
  in the SEQ case, both instructions are run with gas n *)
  Fixpoint eval {A : stack_type} {B : stack_type}
           (i : instruction A B) (fuel : Datatypes.nat) {struct fuel} :
    stack A -> M (stack B) :=
    match fuel with
    | O => fun SA => Failed _ Out_of_fuel
    | S n =>
      match i in instruction A B return stack A -> M (stack B) with
      | @FAILWITH _ A B a =>
        fun '(x, _) => Failed _ (Assertion_Failure (data a) x)

      (* According to the documentation, FAILWITH's argument should
         not be part of the state reached by the instruction but the
         whole point of this instruction (compared to the FAIL macro)
         is to report the argument to the user. *)

      | NOOP => fun SA => Return _ SA
      | SEQ B C =>
        fun SA => bind (eval C n) (eval B n SA)
      | IF_ bt bf =>
        fun '(b, SA) => if b then eval bt n SA else eval bf n SA
      | LOOP body =>
        fun '(b, SA) => if b then eval (body;; (LOOP body)) n SA else Return _ SA
      | LOOP_LEFT body =>
        fun '(ab, SA) =>
          match ab return M (stack (_ ::: _)) with
          | inl x => eval (body;; LOOP_LEFT body) n (x, SA)
          | inr y => Return _ (y, SA)
          end
      | DIP i =>
        fun '(y, SA) => bind (fun SC => Return _ (y, SC)) (eval i n SA)
      | EXEC =>
        fun '(x, (f, SA)) =>
          bind (fun '(y, tt) => Return _ (y, SA)) (eval f n (x, tt))
      | DROP => fun '(_, SA) => Return _ SA
      | DUP => fun '(x, SA) => Return _ (x, (x, SA))
      | SWAP => fun '(x, (y, SA)) => Return _ (y, (x, SA))
      | PUSH a x => fun SA => Return _ (concrete_data_to_data _ x, SA)
      | UNIT => fun SA => Return _ (tt, SA)
      | LAMBDA a b code => fun SA => Return _ (code, SA)
      | EQ => fun '(x, SA) => Return _ ((x =? 0)%Z, SA)
      | NEQ => fun '(x, SA) => Return _ (negb (x =? 0)%Z, SA)
      | LT => fun '(x, SA) => Return _ ((x <? 0)%Z, SA)
      | GT => fun '(x, SA) => Return _ ((x >? 0)%Z, SA)
      | LE => fun '(x, SA) => Return _ ((x <=? 0)%Z, SA)
      | GE => fun '(x, SA) => Return _ ((x >=? 0)%Z, SA)
      | @OR _ _ s =>
        fun '(x, (y, SA)) => Return _ (or_fun _ (bitwise_variant_field _ s) x y, SA)
      | @AND _ _ s =>
        fun '(x, (y, SA)) => Return _ (and _ (bitwise_variant_field _ s) x y, SA)
      | @XOR _ _ s =>
        fun '(x, (y, SA)) => Return _ (xor _ (bitwise_variant_field _ s) x y, SA)
      | @NOT _ _ s =>
        fun '(x, SA) => Return _ (not _ _ (not_variant_field _ s) x, SA)
      | @NEG _ _ s =>
        fun '(x, SA) => Return _ (neg _ (neg_variant_field _ s) x, SA)
      | ABS => fun '(x, SA) => Return _ (Z.abs_N x, SA)
      | @ADD _ _ _ s =>
        fun '(x, (y, SA)) =>
          bind (fun r => Return _ (r, SA))
               (add _ _ _ (add_variant_field _ _ s) x y)
      | @SUB _ _ _ s =>
        fun '(x, (y, SA)) =>
          bind (fun r => Return _ (r, SA))
               (sub _ _ _ (sub_variant_field _ _ s) x y)
      | @MUL _ _ _ s =>
        fun '(x, (y, SA)) =>
          bind (fun r => Return _ (r, SA))
               (mul _ _ _ (mul_variant_field _ _ s) x y)
      | @EDIV _ _ _ s =>
        fun '(x, (y, SA)) =>
          Return _ (ediv _ _ _ _ (ediv_variant_field _ _ s) x y, SA)
      | LSL => fun '(x, (y, SA)) => Return _ (N.shiftl x y, SA)
      | LSR => fun '(x, (y, SA)) => Return _ (N.shiftr x y, SA)
      | COMPARE =>
        fun '(x, (y, SA)) => Return _ (comparison_to_int (compare _ x y), SA)
      | @CONCAT _ _ s =>
        fun '(x, (y, SA)) =>
          Return _ (concat _ (stringlike_variant_field _ s) x y, SA)
      | @SLICE _ _ i =>
        fun '(n1, (n2, (s, SA))) =>
          Return _ (slice _ (stringlike_variant_field _ i) n1 n2 s, SA)
      | PAIR => fun '(x, (y, SA)) => Return _ ((x, y), SA)
      | CAR => fun '((x, y), SA) => Return _ (x, SA)
      | CDR => fun '((x, y), SA) => Return _ (y, SA)
      | EMPTY_SET a => fun SA => Return _ (set.empty _ (compare a), SA)
      | @MEM _ _ _ s =>
        fun '(x, (y, SA)) =>
          Return _ (mem _ _ (mem_variant_field _ _ s) x y, SA)
      | @UPDATE _ _ _ _ s =>
        fun '(x, (y, (z, SA))) =>
          Return _ (update _ _ _ (update_variant_field _ _ _ s) x y z, SA)
      | @ITER _ _ s _ body =>
        fun '(x, SA) =>
          match iter_destruct _ _ (iter_variant_field _ s) x with
          | None => Return _ SA
          | Some (a, y) =>
            bind (fun SB =>
                    eval (ITER body) n (y, SB))
                 (eval body n (a, SA))
          end
      | @SIZE _ _ s =>
        fun '(x, SA) => Return _ (N.of_nat (size _ (size_variant_field _ s) x), SA)
      | EMPTY_MAP k val =>
        fun SA => Return _ (map.empty (comparable_data k) (data val) _, SA)
      | @GET _ _ _ s =>
        fun '(x, (y, SA)) =>
          Return _ (get _ _ _ (get_variant_field _ _ s) x y, SA)
      | @MAP _ _ _ s _ body =>
        let v := (map_variant_field _ _ s) in
        fun '(x, SA) =>
          match map_destruct _ _ _ _ v x with
          | None => Return _ (map_empty _ _ _ _ v, SA)
          | Some (a, y) =>
            bind (fun '(b, SB) =>
                    bind (fun '(c, SC) =>
                            Return _ (map_insert _ _ _ _ v a b c,
                                      SC))
                         (eval (MAP body) n (y, SB)))
                 (eval body n (a, SA))
          end
      | SOME => fun '(x, SA) => Return _ (Some x, SA)
      | NONE _ => fun SA => Return _ (None, SA)
      | IF_NONE bt bf =>
        fun '(b, SA) =>
          match b with
          | None => eval bt n SA
          | Some b => eval bf n (b, SA)
          end
      | LEFT _ => fun '(x, SA) => Return _ (inl x, SA)
      | RIGHT _ => fun '(x, SA) => Return _ (inr x, SA)
      | IF_LEFT bt bf =>
        fun '(b, SA) =>
          match b with
          | inl a => eval bt n (a, SA)
          | inr b => eval bf n (b, SA)
          end
      | IF_RIGHT bt bf =>
        fun '(b, SA) =>
          match b with
          | inl a => eval bf n (a, SA)
          | inr b => eval bt n (b, SA)
          end
      | CONS => fun '(x, (y, SA)) => Return _ (cons x y, SA)
      | NIL _ => fun SA => Return _ (nil, SA)
      | IF_CONS bt bf =>
        fun '(l, SA) =>
          match l with
          | cons a b => eval bt n (a, (b, SA))
          | nil => eval bf n SA
          end
      | CREATE_CONTRACT =>
        fun '(a, (b, (c, (d, (e, (f, (g, SA))))))) =>
          bind (fun '(a, b) => Return _ (a, (b, SA)))
               (create_contract nd _ _ a b c d e f g)
      | CREATE_CONTRACT_literal _ _ f =>
        fun '(a, (b, (c, (d, (e, (g, SA)))))) =>
          bind (fun '(a, b) => Return _ (a, (b, SA)))
               (create_contract nd _ _ a b c d e f g)
      | CREATE_ACCOUNT =>
        fun '(a, (b, (c, (d, SA)))) =>
          bind (fun '(a, b) => Return _ (a, (b, SA)))
               (create_account nd a b c d)
      | TRANSFER_TOKENS =>
        fun '(a, (b, (c, SA))) =>
          bind (fun r => Return _ (r, SA))
               (transfer_tokens nd _ a b c)
      | SET_DELEGATE =>
        fun '(x, SA) =>
          bind (fun r => Return _ (r, SA))
               (set_delegate nd x)
      | BALANCE => fun SA => bind (fun r => Return _ (r, SA)) (balance nd)
      | ADDRESS =>
        fun '(x, SA) => bind (fun r => Return _ (r, SA)) (address_ nd _ x)
      | CONTRACT _ =>
        fun '(x, SA) => bind (fun r => Return _ (r, SA)) (contract_ nd _ x)
      | SOURCE => fun SA => bind (fun r => Return _ (r, SA)) (source nd)
      | SENDER => fun SA => bind (fun r => Return _ (r, SA)) (sender nd)
      | SELF => fun SA => bind (fun r => Return _ (r, SA)) (self nd _)
      | AMOUNT => fun SA => bind (fun r => Return _ (r, SA)) (amount nd)
      | IMPLICIT_ACCOUNT =>
        fun '(x, SA) => bind (fun r => Return _ (r, SA)) (implicit_account nd x)
      | STEPS_TO_QUOTA =>
        fun SA => bind (fun r => Return _ (r, SA)) (steps_to_quota nd)
      | NOW => fun SA => bind (fun r => Return _ (r, SA)) (now nd)
      | PACK => fun '(x, SA) => bind (fun r => Return _ (r, SA)) (pack nd _ x)
      | UNPACK => fun '(x, SA) => bind (fun r => Return _ (r, SA)) (unpack nd _ x)
      | HASH_KEY => fun '(x, SA) => bind (fun r => Return _ (r, SA)) (hash_key nd x)
      | BLAKE2B => fun '(x, SA) => bind (fun r => Return _ (r, SA)) (blake2b nd x)
      | SHA256 => fun '(x, SA) => bind (fun r => Return _ (r, SA)) (sha256 nd x)
      | SHA512 => fun '(x, SA) => bind (fun r => Return _ (r, SA)) (sha512 nd x)
      | CHECK_SIGNATURE =>
        fun '(x, (y, (z, SA))) =>
          bind (fun r => Return _ (r, SA)) (check_signature nd x y z)
      end
    end.

  (* The evaluator does not depend on the amount of fuel provided *)
  Lemma eval_deterministic_le :
    forall fuel1 fuel2,
      fuel1 <= fuel2 ->
      forall {A B} (i : instruction A B) st,
        success (eval i fuel1 st) ->
        eval i fuel1 st = eval i fuel2 st.
  Proof.
    induction fuel1; intros fuel2 Hle A B i st Hsucc.
    - apply not_false in Hsucc.
      contradiction.
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
        * destruct st; rewrite IHfuel1.
          -- reflexivity.
          -- simpl in Hsucc.
             destruct (success_bind _ _ Hsucc) as (x, (H1, H2)).
             apply success_eq_return in H1.
             exact H1.
        * destruct st as (x, (f, SA)).
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
  Qed.

  Lemma eval_deterministic_success_both fuel1 fuel2 {A B} (i : instruction A B) S :
    success (eval i fuel1 S) ->
    success (eval i fuel2 S) ->
    eval i fuel1 S = eval i fuel2 S.
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
             (eval_precond_n : forall {A B}, instruction A B -> (stack B -> Prop) -> stack A -> Prop)
             A B
             (i : instruction A B) :
    (stack B -> Prop) -> (stack A -> Prop) :=
    match i with
    | FAILWITH => fun _ _ => false
    | NOOP => fun psi st => psi st
    | SEQ B C => fun psi =>
                   eval_precond_n B (eval_precond_n C psi)
    | IF_ bt bf =>
      fun psi '(b, SA) => if b then eval_precond_n bt psi SA
                          else eval_precond_n bf psi SA
    | LOOP body =>
      fun psi '(b, SA) => if b then eval_precond_n (body;; (LOOP body)) psi SA
                          else psi SA
    | LOOP_LEFT body =>
      fun psi '(ab, SA) =>
        match ab with
        | inl x => eval_precond_n (body;; LOOP_LEFT body) psi (x, SA)
        | inr y => psi (y, SA)
        end
    | DIP i =>
      fun psi '(y, SA) => eval_precond_n i (fun SB => psi (y, SB)) SA
    | EXEC =>
      fun psi '(x, (f, SA)) =>
        eval_precond_n f (fun '(y, tt) => psi (y, SA)) (x, tt)
    | DROP => fun psi '(_, SA) => psi SA
    | DUP => fun psi '(x, SA) => psi (x, (x, SA))
    | SWAP => fun psi '(x, (y, SA)) => psi (y, (x, SA))
    | PUSH a x => fun psi SA => psi (concrete_data_to_data _ x, SA)
    | UNIT => fun psi SA => psi (tt, SA)
    | LAMBDA a b code => fun psi SA => psi (code, SA)
    | EQ => fun psi '(x, SA) => psi ((x =? 0)%Z, SA)
    | NEQ => fun psi '(x, SA) => psi (negb (x =? 0)%Z, SA)
    | LT => fun psi '(x, SA) => psi ((x <? 0)%Z, SA)
    | GT => fun psi '(x, SA) => psi ((x >? 0)%Z, SA)
    | LE => fun psi '(x, SA) => psi ((x <=? 0)%Z, SA)
    | GE => fun psi '(x, SA) => psi ((x >=? 0)%Z, SA)
    | @OR _ _ s =>
      fun psi '(x, (y, SA)) => psi (or_fun _ (bitwise_variant_field _ s) x y, SA)
    | @AND _ _ s =>
      fun psi '(x, (y, SA)) => psi (and _ (bitwise_variant_field _ s) x y, SA)
    | @XOR _ _ s =>
      fun psi '(x, (y, SA)) => psi (xor _ (bitwise_variant_field _ s) x y, SA)
    | @NOT _ _ s =>
      fun psi '(x, SA) => psi (not _ _ (not_variant_field _ s) x, SA)
    | @NEG _ _ s =>
      fun psi '(x, SA) => psi (neg _ (neg_variant_field _ s) x, SA)
    | ABS => fun psi '(x, SA) => psi (Z.abs_N x, SA)
    | @ADD _ _ _ s =>
      fun psi '(x, (y, SA)) =>
        precond (add _ _ _ (add_variant_field _ _ s) x y) (fun z => psi (z, SA))
    | @SUB _ _ _ s =>
      fun psi '(x, (y, SA)) =>
        precond (sub _ _ _ (sub_variant_field _ _ s) x y) (fun z => psi (z, SA))
    | @MUL _ _ _ s =>
      fun psi '(x, (y, SA)) =>
        precond (mul _ _ _ (mul_variant_field _ _ s) x y) (fun z => psi (z, SA))
    | @EDIV _ _ _ s =>
      fun psi '(x, (y, SA)) =>
        psi (ediv _ _ _ _ (ediv_variant_field _ _ s) x y, SA)
    | LSL => fun psi '(x, (y, SA)) => psi (N.shiftl x y, SA)
    | LSR => fun psi '(x, (y, SA)) => psi (N.shiftr x y, SA)
    | COMPARE =>
      fun psi '(x, (y, SA)) => psi (comparison_to_int (compare _ x y), SA)
    | @CONCAT _ _ s =>
      fun psi '(x, (y, SA)) =>
        psi (concat _ (stringlike_variant_field _ s) x y, SA)
    | @SLICE _ _ i =>
      fun psi '(n1, (n2, (s, SA))) =>
        psi (slice _ (stringlike_variant_field _ i) n1 n2 s, SA)
    | PAIR => fun psi '(x, (y, SA)) => psi ((x, y), SA)
    | CAR => fun psi '((x, y), SA) => psi (x, SA)
    | CDR => fun psi '((x, y), SA) => psi (y, SA)
    | EMPTY_SET a => fun psi SA => psi (set.empty _ (compare a), SA)
    | @MEM _ _ _ s =>
      fun psi '(x, (y, SA)) =>
        psi (mem _ _ (mem_variant_field _ _ s) x y, SA)
    | @UPDATE _ _ _ _ s =>
      fun psi '(x, (y, (z, SA))) =>
        psi (update _ _ _ (update_variant_field _ _ _ s) x y z, SA)
    | @ITER _ _ s _ body =>
      fun psi '(x, SA) =>
        match iter_destruct _ _ (iter_variant_field _ s) x with
        | None => psi SA
        | Some (a, y) =>
          eval_precond_n body
                       (fun SB => eval_precond_n (ITER body) psi (y, SB))
                       (a, SA)
        end
    | @SIZE _ _ s =>
      fun psi '(x, SA) => psi (N.of_nat (size _ (size_variant_field _ s) x), SA)
    | EMPTY_MAP k val =>
      fun psi SA => psi (map.empty (comparable_data k) (data val) _, SA)
    | @GET _ _ _ s =>
      fun psi '(x, (y, SA)) => psi (get _ _ _ (get_variant_field _ _ s) x y, SA)
    | @MAP _ _ _ s _ body =>
      let v := (map_variant_field _ _ s) in
      fun psi '(x, SA) =>
        match map_destruct _ _ _ _ v x with
        | None => psi (map_empty _ _ _ _ v, SA)
        | Some (a, y) =>
          eval_precond_n body
            (fun '(b, SB) =>
               eval_precond_n (MAP body)
                 (fun '(c, SC) => psi (map_insert _ _ _ _ v a b c, SC))
                 (y, SB))
            (a, SA)
        end
    | SOME => fun psi '(x, SA) => psi (Some x, SA)
    | NONE _ => fun psi SA => psi (None, SA)
    | IF_NONE bt bf =>
      fun psi '(b, SA) =>
        match b with
        | None => eval_precond_n bt psi SA
        | Some b => eval_precond_n bf psi (b, SA)
        end
    | LEFT _ => fun psi '(x, SA) => psi (inl x, SA)
    | RIGHT _ => fun psi '(x, SA) => psi (inr x, SA)
    | IF_LEFT bt bf =>
      fun psi '(b, SA) =>
        match b with
        | inl a => eval_precond_n bt psi (a, SA)
        | inr b => eval_precond_n bf psi (b, SA)
        end
    | IF_RIGHT bt bf =>
      fun psi '(b, SA) =>
        match b with
        | inl a => eval_precond_n bf psi (a, SA)
        | inr b => eval_precond_n bt psi (b, SA)
        end
    | CONS => fun psi '(x, (y, SA)) => psi (cons x y, SA)
    | NIL _ => fun psi SA => psi (nil, SA)
    | IF_CONS bt bf =>
      fun psi '(l, SA) =>
        match l with
        | cons a b => eval_precond_n bt psi (a, (b, SA))
        | nil => eval_precond_n bf psi SA
        end
    | CREATE_CONTRACT =>
      fun psi '(a, (b, (c, (d, (e, (f, (g, SA))))))) =>
        precond_ex (create_contract nd _ _ a b c d e f g)
                   (fun '(oper, addr) => psi (oper, (addr, SA)))
    | CREATE_CONTRACT_literal _ _ f =>
      fun psi '(a, (b, (c, (d, (e, (g, SA)))))) =>
        precond_ex (create_contract nd _ _ a b c d e f g)
                   (fun '(oper, addr) => psi (oper, (addr, SA)))
    | CREATE_ACCOUNT =>
      fun psi '(a, (b, (c, (d, SA)))) =>
        precond_ex (create_account nd a b c d)
                   (fun '(oper, contr) => psi (oper, (contr, SA)))
    | TRANSFER_TOKENS =>
      fun psi '(a, (b, (c, SA))) =>
        precond_ex (transfer_tokens nd _ a b c)
                   (fun oper => psi (oper, SA))
    | SET_DELEGATE =>
      fun psi '(x, SA) =>
        precond_ex (set_delegate nd x) (fun oper => psi (oper, SA))
    | BALANCE =>
      fun psi SA => precond_ex (balance nd) (fun r => psi (r, SA))
    | ADDRESS =>
      fun psi '(x, SA) => precond_ex (address_ nd _ x) (fun r => psi (r, SA))
    | CONTRACT _ =>
      fun psi '(x, SA) => precond_ex (contract_ nd _ x) (fun r => psi (r, SA))
    | SOURCE => fun psi SA => precond_ex (source nd) (fun r => psi (r, SA))
    | SENDER => fun psi SA => precond_ex (sender nd) (fun r => psi (r, SA))
    | SELF => fun psi SA => precond_ex (self nd _) (fun r => psi (r, SA))
    | AMOUNT => fun psi SA => precond_ex (amount nd) (fun r => psi (r, SA))
    | IMPLICIT_ACCOUNT =>
      fun psi '(x, SA) => precond_ex (implicit_account nd x) (fun r => psi (r, SA))
    | STEPS_TO_QUOTA =>
      fun psi SA => precond_ex (steps_to_quota nd) (fun r => psi (r, SA))
    | NOW => fun psi SA => precond_ex (now nd) (fun r => psi (r, SA))
    | PACK => fun psi '(x, SA) => precond_ex (pack nd _ x) (fun r => psi (r, SA))
    | UNPACK =>
      fun psi '(x, SA) => precond_ex (unpack nd _ x) (fun r => psi (r, SA))
    | HASH_KEY =>
      fun psi '(x, SA) => precond_ex (hash_key nd x) (fun r => psi (r, SA))
    | BLAKE2B =>
      fun psi '(x, SA) => precond_ex (blake2b nd x) (fun r => psi (r, SA))
    | SHA256 => fun psi '(x, SA) => precond_ex (sha256 nd x) (fun r => psi (r, SA))
    | SHA512 => fun psi '(x, SA) => precond_ex (sha512 nd x) (fun r => psi (r, SA))
    | CHECK_SIGNATURE =>
      fun psi '(x, (y, (z, SA))) =>
        precond_ex (check_signature nd x y z) (fun r => psi (r, SA))
    end.

  Fixpoint eval_precond (fuel : Datatypes.nat) :
    forall {A B},
      instruction A B ->
      (stack B -> Prop) -> (stack A -> Prop) :=
    match fuel with
    | O => fun _ _ _ _ _ => false
    | S n =>
      eval_precond_body (@eval_precond n)
    end.

  Lemma eval_precond_correct {A B} (i : instruction A B) n st psi :
    precond (eval i n st) psi <-> eval_precond n i psi st.
  Proof.
    generalize A B i st psi; clear A B i st psi.
    induction n; intros A B i st psi; [simpl; intuition|].
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
      + apply (IHn _ _ (i;; LOOP_LEFT i)).
      + reflexivity.
    - destruct st as (y, st).
      rewrite precond_bind.
      apply IHn.
    - destruct st as (x, (f, st)).
      rewrite precond_bind.
      rewrite <- (IHn _ _ f (x, tt) (fun '(y, tt) => psi (y, st))).
      apply precond_eqv.
      intros (y, []).
      simpl.
      reflexivity.
    - destruct st; reflexivity.
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
    - destruct st as (x, (y, st)); rewrite precond_bind; reflexivity.
    - destruct st as (x, (y, st)); rewrite precond_bind; reflexivity.
    - destruct st as (x, (y, st)); rewrite precond_bind; reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
    - destruct st as (x, (y, st)); reflexivity.
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
    - destruct st as (a, (b, (c, (d, (e, (f, (g0, SA))))))).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      intros (x, y).
      reflexivity.
    - destruct st as (a, (b, (c, (d, (e, (g0, SA)))))).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      intros (x, y).
      reflexivity.
    - destruct st as (a, (b, (c, (d, SA)))).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      intros (x, y).
      reflexivity.
    - destruct st as (a, (b, (c, SA))).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (a, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (a, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (a, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (a, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (x, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (x, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (x, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (x, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (x, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (x, SA).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
    - destruct st as (a, (b, (c, SA))).
      rewrite precond_bind.
      rewrite <- precond_exists.
      apply precond_eqv.
      reflexivity.
  Qed.

End semantics.
