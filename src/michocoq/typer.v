Require Import ZArith List Nat.
Require Import syntax semantics.
Require Import untyped_syntax error.


Lemma andb_and a b : (a && b)%bool <-> a /\ b.
Proof.
  split.
  - apply Bool.andb_prop_elim.
  - apply Bool.andb_prop_intro.
Qed.

Module Typer(ST: SelfType)(C:ContractContext).

  Module syntax := Syntax ST C.
  Import syntax. Import untyped_syntax.

  Definition instruction := syntax.instruction.

  Definition safe_instruction_cast {tff} A A' B B' :
    instruction tff A B -> A = A' -> B = B' -> instruction tff A' B'.
  Proof.
    intros i [] [].
    exact i.
  Defined.

  Definition instruction_cast {tff} A A' B B' i : M (instruction tff A' B') :=
    match stype_dec A A', stype_dec B B' with
    | left HA, left HB => Return _ (safe_instruction_cast A A' B B' i HA HB)
    | _, _ => Failed _ Typing
    end.

  Definition instruction_cast_range {tff} A B B' (i : instruction tff A B)
    : M (instruction tff A B') := instruction_cast A A B B' i.

  Definition instruction_cast_domain {tff} A A' B (i : instruction tff A B)
    : M (instruction tff A' B) := instruction_cast A A' B B i.

  Inductive typer_result A : Set :=
  | Inferred_type B : instruction false A B -> typer_result A
  | Any_type : (forall B, instruction true A B) -> typer_result A.

  Definition type_check_instruction
             (type_instruction :
                forall (i : untyped_syntax.instruction) A,
                  M (typer_result A))
             i A B : M {b : Datatypes.bool & instruction b A B} :=
    bind (fun r1 =>
            match r1 with
            | Inferred_type _ B' i =>
              bind (fun i =>
                      Return _ (existT _ false i))
                   (instruction_cast_range A B' B i)
            | Any_type _ i => Return _ (existT _ true (i B))
            end)
         (type_instruction i A).

  Definition type_check_instruction_no_tail_fail
             (type_instruction :
                forall (i : untyped_syntax.instruction) A,
                  M (typer_result A))
             i A B : M (instruction Datatypes.false A B) :=
    bind (fun r1 =>
            match r1 with
            | Inferred_type _ B' i => instruction_cast_range A B' B i
            | Any_type _ i => Failed _ Typing
            end)
         (type_instruction i A).

  Definition assert_not_tail_fail A (r : typer_result A) :
    M {B & instruction Datatypes.false A B} :=
    match r with
    | Inferred_type _ B i => Return _ (existT _ B i)
    | Any_type _ _ => Failed _ Typing
    end.

  Definition type_instruction_no_tail_fail
             (type_instruction :
                forall (i : untyped_syntax.instruction) A,
                  M (typer_result A))
             i A : M {B & instruction Datatypes.false A B} :=
    bind (assert_not_tail_fail A)
         (type_instruction i A).

  Definition type_branches
             (type_instruction :
                forall (i : untyped_syntax.instruction) A,
                  M (typer_result A))
             i1 i2 A1 A2 A
             (IF_instr : forall B tffa tffb,
                 instruction tffa A1 B ->
                 instruction tffb A2 B ->
                 instruction (tffa && tffb) A B)
    : M (typer_result A) :=
    bind (fun r1 =>
            bind (fun r2 =>
                    match r1, r2 with
                    | Inferred_type _ B1 i1, Inferred_type _ B2 i2 =>
                      bind (fun i2 =>
                              Return _
                                     (Inferred_type _ _
                                                    (IF_instr B1 false false i1 i2)))
                           (instruction_cast_range A2 B2 B1 i2)
                    | Inferred_type _ B i1, Any_type _ i2 =>
                      Return _ (Inferred_type _ _ (IF_instr B false true i1 (i2 B)))
                    | Any_type _ i1, Inferred_type _ B i2 =>
                      Return _ (Inferred_type _ _ (IF_instr B true false (i1 B) i2))
                    | Any_type _ i1, Any_type _ i2 =>
                      Return _ (Any_type _ (fun B =>
                                              IF_instr B true true (i1 B) (i2 B)))
                    end)
                 (type_instruction i2 A2))
         (type_instruction i1 A1).

  Definition take_one (S : stack_type) : M (type * stack_type) :=
    match S with
    | nil => Failed _ Typing
    | cons a l => Return _ (a, l)
    end.

  Fixpoint take_n (A : stack_type) n : M ({B | length B = n} * stack_type) :=
    match n as n return M ({B | length B = n} * stack_type) with
    | 0 => Return ({B | length B = 0} * stack_type) (exist (fun B => length B = 0) nil eq_refl, A)
    | S n =>
      bind (fun '(a, A) =>
              bind (fun '(exist _ B H, C) =>
                      Return _ (exist _ (cons a B) (f_equal S H), C))
                   (take_n A n))
           (take_one A)
    end.

  Lemma take_n_length n S1 S2 H1 : take_n (S1 ++ S2) n = Return _ (exist _ S1 H1, S2).
  Proof.
    generalize dependent S1.
    induction n; destruct S1; simpl; intro H1.
    - repeat f_equal.
      apply Eqdep_dec.UIP_dec.
      repeat decide equality.
    - discriminate.
    - discriminate.
    - assert (length S1 = n) as H2.
      + apply (f_equal pred) in H1.
        exact H1.
      + rewrite (IHn S1 H2).
        simpl.
        repeat f_equal.
        apply Eqdep_dec.UIP_dec.
        repeat decide equality.
  Qed.

  Definition type_check_dig n (S:stack_type) : M (typer_result S) :=
    bind (fun '((exist _ S1 H1), tS2) =>
            bind (fun '(t, S2) =>
                    bind (fun i => Return _ (Inferred_type S (t ::: S1 +++ S2) i))
                         (instruction_cast_domain (S1 +++ t ::: S2) S _ (syntax.DIG n H1)))
                 (take_one tS2))
         (take_n S n).

  Definition type_check_dug n (S:stack_type) : M (typer_result S) :=
    bind (fun '(t, S12) =>
            bind (fun '((exist _ S1 H1), S2) =>
                    bind (fun i => Return _ (Inferred_type S (S1 +++ t ::: S2) i))
                         (instruction_cast_domain (t ::: S1 +++ S2) S _ (syntax.DUG n H1)))
                 (take_n S12 n))
         (take_one S).

  Fixpoint as_comparable (a : type) : M comparable_type :=
    match a with
    | Comparable_type a => Return _ (Comparable_type_simple a)
    | pair (Comparable_type a) b =>
      bind (fun b =>
              Return _ (Cpair a b))
           (as_comparable b)
    | _ => Failed _ Typing
    end.

  Lemma as_comparable_comparable (a : comparable_type) :
    as_comparable a = Return _ a.
  Proof.
    induction a.
    - reflexivity.
    - simpl.
      rewrite IHa.
      reflexivity.
  Qed.

  Fixpoint type_data (d : concrete_data) {struct d}
    : forall ty, M (syntax.concrete_data ty) :=
    match d with
    | Int_constant z =>
      fun ty =>
        match ty with
        | Comparable_type int => Return _ (syntax.Int_constant z)
        | _ => Failed _ Typing
        end
    | Nat_constant n =>
      fun ty =>
        match ty with
        | Comparable_type nat => Return _ (syntax.Nat_constant n)
        | Comparable_type int => Return _ (syntax.Int_constant (Z.of_N n))
        | _ => Failed _ Typing
        end
    | String_constant s =>
      fun ty =>
        match ty with
        | Comparable_type string => Return _ (syntax.String_constant s)
        | _ => Failed _ Typing
        end
    | Mutez_constant m =>
      fun ty =>
        match ty with
        | Comparable_type mutez => Return _ (syntax.Mutez_constant m)
        | _ => Failed _ Typing
        end
    | Bytes_constant s =>
      fun ty =>
        match ty with
        | Comparable_type bytes => Return _ (syntax.Bytes_constant s)
        | _ => Failed _ Typing
        end
    | Timestamp_constant s =>
      fun ty =>
        match ty with
        | Comparable_type timestamp => Return _ (syntax.Timestamp_constant s)
        | _ => Failed _ Typing
        end
    | Signature_constant s =>
      fun ty =>
        match ty with
        | signature => Return _ (syntax.Signature_constant s)
        | _ => Failed _ Typing
        end
    | Key_constant s =>
      fun ty =>
        match ty with
        | key => Return _ (syntax.Key_constant s)
        | _ => Failed _ Typing
        end
    | Key_hash_constant s =>
      fun ty =>
        match ty with
        | Comparable_type key_hash => Return _ (syntax.Key_hash_constant s)
        | _ => Failed _ Typing
        end
    | Contract_constant c =>
      fun ty =>
        match ty with
        | contract a =>
          match (mtype_dec (C.get_contract_type c) (Return _ a)) with
          | left H => Return _ (syntax.Contract_constant c H)
          | _ => Failed _ Typing
          end
        | _ => Failed _ Typing
        end
    | Address_constant c =>
      fun ty =>
        match ty with
        | Comparable_type address =>
          Return _ (syntax.Address_constant c)
        | _ => Failed _ Typing
        end
    | Unit =>
      fun ty =>
        match ty with
        | unit => Return _ syntax.Unit
        | _ => Failed _ Typing
        end
    | True_ =>
      fun ty =>
        match ty with
        | Comparable_type bool => Return _ syntax.True_
        | _ => Failed _ Typing
        end
    | False_ =>
      fun ty =>
        match ty with
        | Comparable_type bool => Return _ syntax.False_
        | _ => Failed _ Typing
        end
    | Pair x y =>
      fun ty =>
        match ty with
        | pair a b =>
          bind (fun x =>
                  bind (fun y =>
                          Return _ (syntax.Pair x y))
                       (type_data y b))
               (type_data x a)
        | _ => Failed _ Typing
        end
    | Left x =>
      fun ty =>
        match ty with
        | or a b =>
          bind (fun x =>
                  Return _ (syntax.Left x))
               (type_data x a)
        | _ => Failed _ Typing
        end
    | Right y =>
      fun ty =>
        match ty with
        | or a b =>
          bind (fun y =>
                  Return _ (syntax.Right y))
               (type_data y b)
        | _ => Failed _ Typing
        end
    | Some_ x =>
      fun ty =>
        match ty with
        | option a =>
          bind (fun x =>
                  Return _ (syntax.Some_ x))
               (type_data x a)
        | _ => Failed _ Typing
        end
    | None_ =>
      fun ty =>
        match ty with
        | option a => Return _ syntax.None_
        | _ => Failed _ Typing
        end
    | Concrete_seq l =>
      fun ty =>
        match ty with
        | list a =>
          bind (fun l => Return _ (syntax.Concrete_list l))
               ((fix type_data_list l :=
                   match l with
                   | nil => Return _ nil
                   | cons x l =>
                     bind (fun x =>
                             bind (fun l =>
                                     Return _ (cons x l))
                                  (type_data_list l))
                          (type_data x a)
                   end) l)
        | set a =>
          bind (fun l => Return _ (syntax.Concrete_set l))
               ((fix type_data_list l :=
                   match l with
                   | nil => Return _ nil
                   | cons x l =>
                     bind (fun x =>
                             bind (fun l =>
                                     Return _ (cons x l))
                                  (type_data_list l))
                          (type_data x a)
                   end) l)
        | map a b =>
          bind (fun l => Return _ (syntax.Concrete_map l))
               ((fix type_data_list l :=
                   match l with
                   | nil => Return _ nil
                   | cons (Elt x y) l =>
                     bind (fun x =>
                             bind (fun y =>
                                     bind (fun l =>
                                             Return _ (cons (syntax.Elt _ _ x y) l))
                                          (type_data_list l))
                                  (type_data y b))
                          (type_data x a)
                   | _ => Failed _ Typing
                   end) l)
        | _ => Failed _ Typing
        end
    | Instruction i =>
      fun ty =>
        match ty with
        | syntax.lambda a b =>
          bind
            (fun '(existT _ tff i) => Return _ (syntax.Instruction _ i))
            (type_check_instruction type_instruction i (cons a nil) (cons b nil))
        | _ => Failed _ Typing
        end
    | Chain_id_constant c =>
      fun ty =>
        match ty with
        | chain_id =>
          Return _ (syntax.Chain_id_constant c)
        | _ => Failed _ Typing
        end
    | _ => fun _ => Failed _ Typing
    end

  with
  type_instruction i A {struct i} : M (typer_result A) :=
    match i, A with
    | NOOP, A => Return _ (Inferred_type _ _ syntax.NOOP)
    | FAILWITH, a :: A => Return _ (Any_type _ (fun B => syntax.FAILWITH))
    | SEQ i1 i2, A =>
      bind (fun '(existT _ B i1) =>
              bind (fun r2 =>
                      match r2 with
                      | Inferred_type _ C i2 =>
                        Return _ (Inferred_type _ _ (syntax.SEQ i1 i2))
                      | Any_type _ i2 =>
                        Return _ (Any_type _ (fun C => syntax.SEQ i1 (i2 C)))
                      end)
                   (type_instruction i2 B))
           (type_instruction_no_tail_fail type_instruction i1 A)
    | IF_ i1 i2, Comparable_type bool :: A =>
      type_branches type_instruction i1 i2 _ _ _ (fun B tffa tffb => syntax.IF_)
    | IF_NONE i1 i2, option a :: A =>
      type_branches type_instruction i1 i2 _ _ _ (fun B tffa tffb => syntax.IF_NONE)
    | IF_LEFT i1 i2, or a b :: A =>
      type_branches type_instruction i1 i2 _ _ _ (fun B tffa tffb => syntax.IF_LEFT)
    | IF_RIGHT i1 i2, or a b :: A =>
      type_branches type_instruction i1 i2 _ _ _ (fun B tffa tffb => syntax.IF_RIGHT)
    | IF_CONS i1 i2, list a :: A =>
      type_branches type_instruction i1 i2 _ _ _ (fun B tffa tffb => syntax.IF_CONS)
    | LOOP i, Comparable_type bool :: A =>
      bind (fun i => Return _ (Inferred_type _ _ (syntax.LOOP i)))
           (type_check_instruction_no_tail_fail
              type_instruction i A (bool ::: A))
    | LOOP_LEFT i, syntax.or a b :: A =>
      bind (fun i => Return _ (Inferred_type _ _ (syntax.LOOP_LEFT i)))
           (type_check_instruction_no_tail_fail
              type_instruction i (a :: A) (syntax.or a b :: A))
    | EXEC, a :: lambda a' b :: B =>
      let A := a :: lambda a' b :: B in
      let A' := a :: lambda a b :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain A' A _ syntax.EXEC)
    | APPLY, a :: lambda (pair a' b) c :: B =>
      let A := a :: lambda (pair a' b) c :: B in
      let A' := a :: lambda (pair a b) c :: B in
      (if is_packable a as b return is_packable a = b -> _
       then fun i =>
              bind (fun i => Return _ (Inferred_type _ _ i))
                   (instruction_cast_domain A' A _ (@syntax.APPLY _ _ _ _ (IT_eq_rev _ i)))
       else fun _ => Failed _ Typing) eq_refl
    | DUP, a :: A =>
      Return _ (Inferred_type _ _ syntax.DUP)
    | SWAP, a :: b :: A =>
      Return _ (Inferred_type _ _ syntax.SWAP)
    | PUSH a v, A =>
      bind (fun d => Return _ (Inferred_type _ _ (syntax.PUSH a d)))
           (type_data v a)
    | UNIT, A => Return _ (Inferred_type _ _ syntax.UNIT)
    | LAMBDA a b i, A =>
      bind (fun '(existT _ tff i) =>
              Return _ (Inferred_type _ _ (syntax.LAMBDA a b i)))
           (type_check_instruction
              type_instruction i (a :: nil) (b :: nil))
    | EQ, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ syntax.EQ)
    | NEQ, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ syntax.NEQ)
    | LT, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ syntax.LT)
    | GT, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ syntax.GT)
    | LE, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ syntax.LE)
    | GE, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ syntax.GE)
    | OR, Comparable_type bool :: Comparable_type bool :: A =>
      Return _ (Inferred_type _ _ (@syntax.OR _ syntax.bitwise_bool _))
    | OR, Comparable_type nat :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.OR _ syntax.bitwise_nat _))
    | AND, Comparable_type bool :: Comparable_type bool :: A =>
      Return _ (Inferred_type _ _ (@syntax.AND _ syntax.bitwise_bool _))
    | AND, Comparable_type nat :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.AND _ syntax.bitwise_nat _))
    | XOR, Comparable_type bool :: Comparable_type bool :: A =>
      Return _ (Inferred_type _ _ (@syntax.XOR _ syntax.bitwise_bool _))
    | XOR, Comparable_type nat :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.XOR _ syntax.bitwise_nat _))
    | NOT, Comparable_type bool :: A =>
      Return _ (Inferred_type _ _ (@syntax.NOT _ syntax.not_bool _))
    | NOT, Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.NOT _ syntax.not_nat _))
    | NOT, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.NOT _ syntax.not_int _))
    | NEG, Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.NEG _ syntax.neg_nat _))
    | NEG, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.NEG _ syntax.neg_int _))
    | ABS, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ syntax.ABS)
    | INT, Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ syntax.INT)
    | ISNAT, Comparable_type int :: A =>
      Return _ (Inferred_type _ _ syntax.ISNAT)
    | ADD, Comparable_type nat :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.ADD _ _ syntax.add_nat_nat _))
    | ADD, Comparable_type nat :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.ADD _ _ syntax.add_nat_int _))
    | ADD, Comparable_type int :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.ADD _ _ syntax.add_int_nat _))
    | ADD, Comparable_type int :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.ADD _ _ syntax.add_int_int _))
    | ADD, Comparable_type timestamp :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.ADD _ _ syntax.add_timestamp_int _))
    | ADD, Comparable_type int :: Comparable_type timestamp :: A =>
      Return _ (Inferred_type _ _ (@syntax.ADD _ _ syntax.add_int_timestamp _))
    | ADD, Comparable_type mutez :: Comparable_type mutez :: A =>
      Return _ (Inferred_type _ _ (@syntax.ADD _ _ syntax.add_tez_tez _))
    | SUB, Comparable_type nat :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.SUB _ _ syntax.sub_nat_nat _))
    | SUB, Comparable_type nat :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.SUB _ _ syntax.sub_nat_int _))
    | SUB, Comparable_type int :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.SUB _ _ syntax.sub_int_nat _))
    | SUB, Comparable_type int :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.SUB _ _ syntax.sub_int_int _))
    | SUB, Comparable_type timestamp :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.SUB _ _ syntax.sub_timestamp_int _))
    | SUB, Comparable_type timestamp :: Comparable_type timestamp :: A =>
      Return _ (Inferred_type _ _ (@syntax.SUB _ _ syntax.sub_timestamp_timestamp _))
    | SUB, Comparable_type mutez :: Comparable_type mutez :: A =>
      Return _ (Inferred_type _ _ (@syntax.SUB _ _ syntax.sub_tez_tez _))
    | MUL, Comparable_type nat :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.MUL _ _ syntax.mul_nat_nat _))
    | MUL, Comparable_type nat :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.MUL _ _ syntax.mul_nat_int _))
    | MUL, Comparable_type int :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.MUL _ _ syntax.mul_int_nat _))
    | MUL, Comparable_type int :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.MUL _ _ syntax.mul_int_int _))
    | MUL, Comparable_type mutez :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.MUL _ _ syntax.mul_tez_nat _))
    | MUL, Comparable_type nat :: Comparable_type mutez :: A =>
      Return _ (Inferred_type _ _ (@syntax.MUL _ _ syntax.mul_nat_tez _))
    | EDIV, Comparable_type nat :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.EDIV _ _ syntax.ediv_nat_nat _))
    | EDIV, Comparable_type nat :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.EDIV _ _ syntax.ediv_nat_int _))
    | EDIV, Comparable_type int :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.EDIV _ _ syntax.ediv_int_nat _))
    | EDIV, Comparable_type int :: Comparable_type int :: A =>
      Return _ (Inferred_type _ _ (@syntax.EDIV _ _ syntax.ediv_int_int _))
    | EDIV, Comparable_type mutez :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ (@syntax.EDIV _ _ syntax.ediv_tez_nat _))
    | EDIV, Comparable_type mutez :: Comparable_type mutez :: A =>
      Return _ (Inferred_type _ _ (@syntax.EDIV _ _ syntax.ediv_tez_tez _))
    | LSL, Comparable_type nat :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ syntax.LSL)
    | LSR, Comparable_type nat :: Comparable_type nat :: A =>
      Return _ (Inferred_type _ _ syntax.LSR)
    | COMPARE, a :: a' :: B =>
      let A := a ::: a' ::: B in
      bind (fun a : comparable_type =>
              bind (fun a' : comparable_type =>
                      let A' := a ::: a ::: B in
                      bind (fun i => Return _ (Inferred_type _ _ i))
                           (instruction_cast_domain
                              A' A (int ::: B) (syntax.COMPARE (a := a))))
                   (as_comparable a'))
           (as_comparable a)
    | CONCAT, Comparable_type string :: Comparable_type string :: B =>
      Return _ (Inferred_type _ _ (@syntax.CONCAT _ stringlike_string _))
    | CONCAT, Comparable_type bytes :: Comparable_type bytes :: B =>
      Return _ (Inferred_type _ _ (@syntax.CONCAT _ stringlike_bytes _))
    | SIZE, set a :: A =>
      Return _ (Inferred_type _ _ (@syntax.SIZE _ (size_set a) _))
    | SIZE, cons (list a) A =>
      Return _ (Inferred_type _ _ (@syntax.SIZE _ (size_list a) _))
    | SIZE, cons (map a b) A =>
      Return _ (Inferred_type _ _ (@syntax.SIZE _ (size_map a b) _))
    | SIZE, Comparable_type string :: A =>
      Return _ (Inferred_type _ _ (@syntax.SIZE _ size_string _))
    | SIZE, Comparable_type bytes :: A =>
      Return _ (Inferred_type _ _ (@syntax.SIZE _ size_bytes _))
    | SLICE, Comparable_type nat :: Comparable_type nat :: Comparable_type string :: A =>
      Return _ (Inferred_type _ _ (@syntax.SLICE _ stringlike_string _))
    | SLICE, Comparable_type nat :: Comparable_type nat :: Comparable_type bytes :: A =>
      Return _ (Inferred_type _ _ (@syntax.SLICE _ stringlike_bytes _))
    | PAIR, a :: b :: A =>
      Return _ (Inferred_type _ _ syntax.PAIR)
    | CAR, pair a b :: A =>
      Return _ (Inferred_type _ _ syntax.CAR)
    | CDR, pair a b :: A =>
      Return _ (Inferred_type _ _ syntax.CDR)
    | EMPTY_SET c, A =>
      Return _ (Inferred_type _ _ (syntax.EMPTY_SET c))
    | MEM, elt' :: set elt :: B =>
      let A := elt' :: set elt :: B in
      let A' := elt ::: set elt :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain
              A' A _ (@syntax.MEM _ _ (mem_set elt) _))
    | MEM, kty' :: map kty vty :: B =>
      let A := kty' :: map kty vty :: B in
      let A' := kty ::: map kty vty :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain
              A' A _ (@syntax.MEM _ _ (mem_map kty vty) _))
    | MEM, kty' :: big_map kty vty :: B =>
      let A := kty' :: big_map kty vty :: B in
      let A' := kty ::: big_map kty vty :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain
              A' A _ (@syntax.MEM _ _ (mem_bigmap kty vty) _))
    | UPDATE, elt' :: Comparable_type bool :: set elt :: B =>
      let A := elt' ::: bool ::: set elt :: B in
      let A' := elt ::: bool ::: set elt :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain
              A' A _ (@syntax.UPDATE _ _ _ (update_set elt) _))
    | UPDATE, kty' :: option vty' :: map kty vty :: B =>
      let A := kty' ::: option vty' ::: map kty vty :: B in
      let A' := kty ::: option vty ::: map kty vty :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain
              A' A _ (@syntax.UPDATE _ _ _ (update_map kty vty) _))
    | UPDATE, kty' :: option vty' :: big_map kty vty :: B =>
      let A := kty' ::: option vty' ::: big_map kty vty :: B in
      let A' := kty ::: option vty ::: big_map kty vty :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain
              A' A _ (@syntax.UPDATE _ _ _ (update_bigmap kty vty) _))
    | ITER i, list a :: A =>
      bind (fun i => Return _ (Inferred_type _ _ (syntax.ITER i)))
           (type_check_instruction_no_tail_fail type_instruction i (a :: A) A)
    | ITER i, set a :: A =>
      bind (fun i => Return _ (Inferred_type _ _ (syntax.ITER i)))
           (type_check_instruction_no_tail_fail type_instruction i (a ::: A) A)
    | ITER i, map kty vty :: A =>
      bind (fun i => Return _ (Inferred_type _ _ (syntax.ITER i)))
           (type_check_instruction_no_tail_fail type_instruction i (pair kty vty :: A) A)
    | EMPTY_MAP kty vty, A =>
      Return _ (Inferred_type _ _ (syntax.EMPTY_MAP kty vty))
    | GET, kty' :: map kty vty :: B =>
      let A := kty' :: map kty vty :: B in
      let A' := kty ::: map kty vty :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain
              A' A _ (@syntax.GET _ _ (get_map kty vty) _))
    | GET, kty' :: big_map kty vty :: B =>
      let A := kty' :: big_map kty vty :: B in
      let A' := kty ::: big_map kty vty :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain
              A' A _ (@syntax.GET _ _ (get_bigmap kty vty) _))
    | MAP i, list a :: A =>
      bind (fun r =>
              match r with
              | existT _ (b :: A') i =>
                bind (fun i => Return _ (Inferred_type _ _ (syntax.MAP i)))
                     (instruction_cast_range (a :: A) (b :: A') (b :: A) i)
              | _ => Failed _ Typing
              end)
           (type_instruction_no_tail_fail type_instruction i (a :: A))
    | MAP i, map kty vty :: A =>
      bind (fun r =>
              match r with
              | existT _ (b :: A') i =>
                bind (fun i => Return _ (Inferred_type _ _ (syntax.MAP i)))
                     (instruction_cast_range (pair kty vty :: A) (b :: A') (b :: A) i)
              | _ => Failed _ Typing
              end)
           (type_instruction_no_tail_fail type_instruction i (pair kty vty ::: A))
    | SOME, a :: A => Return _ (Inferred_type _ _ syntax.SOME)
    | NONE a, A => Return _ (Inferred_type _ _ (syntax.NONE a))
    | LEFT b, a :: A => Return _ (Inferred_type _ _ (syntax.LEFT b))
    | RIGHT a, b :: A => Return _ (Inferred_type _ _ (syntax.RIGHT a))
    | CONS, a' :: list a :: B =>
      let A := a' :: list a :: B in
      let A' := a :: list a :: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain A' A _ (syntax.CONS))
    | NIL a, A => Return _ (Inferred_type _ _ (syntax.NIL a))
    | CREATE_CONTRACT g p i,
      option (Comparable_type key_hash) :: Comparable_type mutez :: g2 :: B =>
      let A :=
          option key_hash ::: mutez ::: g2 :: B in
      let A' :=
          option key_hash ::: mutez ::: g ::: B in
      bind (fun '(existT _ tff i) =>
              bind (fun i => Return _ (Inferred_type _ _ i))
                   (instruction_cast_domain A' A _ (syntax.CREATE_CONTRACT g p i)))
           (type_check_instruction type_instruction i (pair p g :: nil) (pair (list operation) g :: nil))
    | TRANSFER_TOKENS, p1 :: Comparable_type mutez :: contract p2 :: B =>
      let A := p1 ::: mutez ::: contract p2 ::: B in
      let A' := p1 ::: mutez ::: contract p1 ::: B in
      bind (fun i => Return _ (Inferred_type _ _ i))
           (instruction_cast_domain A' A _ syntax.TRANSFER_TOKENS)
    | SET_DELEGATE, option (Comparable_type key_hash) :: A =>
      Return _ (Inferred_type _ _ syntax.SET_DELEGATE)
    | BALANCE, A =>
      Return _ (Inferred_type _ _ syntax.BALANCE)
    | ADDRESS, contract _ :: A =>
      Return _ (Inferred_type _ _ syntax.ADDRESS)
    | CONTRACT ty, Comparable_type address :: A =>
      Return _ (Inferred_type _ _ (syntax.CONTRACT ty))
    | SOURCE, A =>
      Return _ (Inferred_type _ _ syntax.SOURCE)
    | SENDER, A =>
      Return _ (Inferred_type _ _ syntax.SENDER)
    | SELF, A =>
      Return _ (Inferred_type _ _ syntax.SELF)
    | AMOUNT, A =>
      Return _ (Inferred_type _ _ syntax.AMOUNT)
    | IMPLICIT_ACCOUNT, Comparable_type key_hash :: A =>
      Return _ (Inferred_type _ _ syntax.IMPLICIT_ACCOUNT)
    | NOW, A =>
      Return _ (Inferred_type _ _ syntax.NOW)
    | PACK, a :: A =>
      Return _ (Inferred_type _ _ syntax.PACK)
    | UNPACK ty, Comparable_type bytes :: A =>
      Return _ (Inferred_type _ _ (syntax.UNPACK ty))
    | HASH_KEY, key :: A =>
      Return _ (Inferred_type _ _ syntax.HASH_KEY)
    | BLAKE2B, Comparable_type bytes :: A =>
      Return _ (Inferred_type _ _ syntax.BLAKE2B)
    | SHA256, Comparable_type bytes :: A =>
      Return _ (Inferred_type _ _ syntax.SHA256)
    | SHA512, Comparable_type bytes :: A =>
      Return _ (Inferred_type _ _ syntax.SHA512)
    | CHECK_SIGNATURE, key :: signature :: Comparable_type bytes :: A =>
      Return _ (Inferred_type _ _ syntax.CHECK_SIGNATURE)
    | DIG n, A => type_check_dig n _
    | DUG n, A => type_check_dug n _
    | DIP n i, S12 =>
      bind (fun '((exist _ S1 H1), S2) =>
              bind (fun '(existT _ B i) =>
                      bind (fun i => Return _ (Inferred_type S12 (S1 +++ B) i))
                           (instruction_cast_domain (S1 +++ S2) S12 _ (syntax.DIP n H1 i)))
                   (type_instruction_no_tail_fail type_instruction i S2))
           (take_n S12 n)
    | DROP n, S12 =>
      bind (fun '((exist _ S1 H1), S2) =>
                      bind (fun i => Return _ (Inferred_type S12 S2 i))
                           (instruction_cast_domain (S1 +++ S2) S12 _ (syntax.DROP n H1)))
           (take_n S12 n)
    | CHAIN_ID, _ =>
      Return _ (Inferred_type _ _ syntax.CHAIN_ID)
    | _, _ => Failed _ Typing
    end.
End Typer.
