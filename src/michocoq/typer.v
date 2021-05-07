Require Import ZArith List Nat Ascii String.
Require Import ListString.All.
Require Import Moment.All.
Require syntax semantics.
Require Import syntax_type comparable entrypoints.
Require Import untyped_syntax error.
Import error.Notations.

Inductive type_mode := Readable | Optimized | Any.


Lemma andb_and a b : (a && b)%bool <-> a /\ b.
Proof.
  split.
  - apply Bool.andb_prop_elim.
  - apply Bool.andb_prop_intro.
Qed.

  Definition instruction := syntax.instruction.

  Definition instruction_seq := syntax.instruction_seq.

  Definition safe_opcode_cast {self_type} A A' B B' :
    syntax.opcode (self_type := self_type) A B -> A = A' -> B = B' ->
    syntax.opcode (self_type := self_type) A' B'.
  Proof.
    intros o [] [].
    exact o.
  Defined.

  Definition safe_instruction_cast {self_type tff} A A' B B' :
    instruction self_type tff A B -> A = A' -> B = B' -> instruction self_type tff A' B'.
  Proof.
    intros i [] [].
    exact i.
  Defined.

  Definition safe_instruction_seq_cast {self_type tff} A A' B B' :
    instruction_seq self_type tff A B -> A = A' -> B = B' -> instruction_seq self_type tff A' B'.
  Proof.
    intros i [] [].
    exact i.
  Defined.

  Record cast_error :=
    Mk_cast_error
      {
        input : Datatypes.list type;
        output :  Datatypes.list type;
        expected_input : Datatypes.list type;
        expected_output : Datatypes.list type;
        tff : Datatypes.bool;
        self_type_ : syntax.self_info;
        i : instruction_seq self_type_ tff input output;
      }.

  Definition opcode_cast {self_type} A A' B B' o : M (syntax.opcode A' B') :=
    match stype_dec A A', stype_dec B B' with
    | left HA, left HB => Return (safe_opcode_cast A A' B B' o HA HB)
    | _, _ =>
      Failed _ (Typing cast_error
                       (Mk_cast_error A B A' B' Datatypes.false self_type
                                      (syntax.instruction_wrap
                                         (syntax.Instruction_opcode o))))
    end.

  Definition instruction_cast {self_type tff} A A' B B' i : M (instruction self_type tff A' B') :=
    match stype_dec A A', stype_dec B B' with
    | left HA, left HB => Return (safe_instruction_cast A A' B B' i HA HB)
    | _, _ => Failed _ (Typing cast_error (Mk_cast_error A B A' B' tff _ (syntax.instruction_wrap i)))
    end.

  Definition instruction_seq_cast {self_type tff} A A' B B' i : M (instruction_seq self_type tff A' B') :=
    match stype_dec A A', stype_dec B B' with
    | left HA, left HB => Return (safe_instruction_seq_cast A A' B B' i HA HB)
    | _, _ => Failed _ (Typing cast_error (Mk_cast_error A B A' B' tff _ i))
    end.

  Definition instruction_cast_range {self_type tff} A B B' (i : instruction self_type tff A B)
    : M (instruction self_type tff A B') := instruction_cast A A B B' i.

  Definition instruction_seq_cast_range {self_type tff} A B B' (i : instruction_seq self_type tff A B)
    : M (instruction_seq self_type tff A B') := instruction_seq_cast A A B B' i.

  Definition instruction_cast_domain {self_type tff} A A' B (i : instruction self_type tff A B)
    : M (instruction self_type tff A' B) := instruction_cast A A' B B i.

  Definition opcode_cast_domain self_type A A' B (o : @syntax.opcode self_type A B)
    : M (@syntax.opcode self_type A' B) := opcode_cast A A' B B o.

  Inductive typer_result {self_type} A : Set :=
  | Inferred_type B : instruction self_type false A B -> typer_result A
  | Any_type : (forall B, instruction self_type true A B) -> typer_result A.

  Inductive typer_result_seq {self_type} A : Set :=
  | Inferred_type_seq B : instruction_seq self_type false A B -> typer_result_seq A
  | Any_type_seq : (forall B, instruction_seq self_type true A B) -> typer_result_seq A.

  Definition type_check_instruction {self_type}
             (type_instruction :
                forall (i : untyped_syntax.instruction) A,
                  M (typer_result A))
             i A B : M {b : Datatypes.bool & instruction self_type b A B} :=
    let! r1 := type_instruction i A in
    match r1 with
    | Inferred_type _ B' i =>
      let! i := instruction_cast_range A B' B i in
      Return (existT _ false i)
    | Any_type _ i => Return (existT _ true (i B))
    end.

  Definition type_check_instruction_seq {self_type}
             (type_instruction_seq :
                forall (i : untyped_syntax.instruction_seq) A,
                  M (typer_result_seq A))
             i A B : M {b : Datatypes.bool & instruction_seq self_type b A B} :=
    let! r1 := type_instruction_seq i A in
    match r1 with
    | Inferred_type_seq _ B' i =>
      let! i := instruction_seq_cast_range A B' B i in
      Return (existT _ false i)
    | Any_type_seq _ i => Return (existT _ true (i B))
    end.

  Definition type_check_instruction_seq_no_tail_fail {self_type}
             (type_instruction_seq :
                forall (i : untyped_syntax.instruction_seq) A,
                  M (typer_result_seq A))
             i A B : M (instruction_seq self_type Datatypes.false A B) :=
    let! r1 := type_instruction_seq i A in
    match r1 with
    | Inferred_type_seq _ B' i => instruction_seq_cast_range A B' B i
    | Any_type_seq _ i => Failed _ (Typing _ tt)
    end.

  Definition assert_not_tail_fail {self_type} A (r : typer_result A) :
    M {B & instruction self_type Datatypes.false A B} :=
    match r with
    | Inferred_type _ B i => Return (existT _ B i)
    | Any_type _ _ => Failed _ (Typing _ tt)
    end.

  Definition type_instruction_no_tail_fail {self_type}
             (type_instruction :
                forall (i : untyped_syntax.instruction) A,
                  M (typer_result A))
             i A : M {B & instruction self_type Datatypes.false A B} :=
    let! r := type_instruction i A in
    assert_not_tail_fail A r.

  Definition assert_not_tail_fail_seq {self_type} A (r : typer_result_seq A) :
    M {B & instruction_seq self_type Datatypes.false A B} :=
    match r with
    | Inferred_type_seq _ B i => Return (existT _ B i)
    | Any_type_seq _ _ => Failed _ (Typing _ tt)
    end.

  Definition type_instruction_seq_no_tail_fail {self_type}
             (type_instruction_seq :
                forall (i : untyped_syntax.instruction_seq) A,
                  M (typer_result_seq A))
             i A : M {B & instruction_seq self_type Datatypes.false A B} :=
    let! r := type_instruction_seq i A in
    assert_not_tail_fail_seq A r.

  Definition type_if_family (f : if_family) (t : type) :
    M {A & {B & syntax.if_family A B t}} :=
    match f, t with
    | IF_bool, Comparable_type bool => Return (existT _ _ (existT _ _ syntax.IF_bool))
    | IF_option, option a => Return (existT _ _ (existT _ _ (syntax.IF_option a)))
    | IF_or, or a b => Return (existT _ _ (existT _ _ (syntax.IF_or a b)))
    | IF_list, list a => Return (existT _ _ (existT _ _ (syntax.IF_list a)))
    | _, _ => Failed _ (Typing _ "type_family"%string)
    end.

  Definition type_branches {self_type} (f : if_family) (t : type)
             (type_instruction_seq :
                forall (i : untyped_syntax.instruction_seq) A,
                  M (typer_result_seq A))
             i1 i2 A
    : M (typer_result (self_type := self_type) (t ::: A)) :=
    let! (existT _ B1 (existT _ B2 f)) := type_if_family f t in
    let! r1 := type_instruction_seq i1 (B1 ++ A) in
    let! r2 := type_instruction_seq i2 (B2 ++ A) in
    match r1, r2 with
    | Inferred_type_seq _ C1 i1, Inferred_type_seq _ C2 i2 =>
      let! i2 := instruction_seq_cast_range (B2 ++ A) C2 C1 i2 in
      Return
              (Inferred_type _ _
                            (syntax.IF_ f i1 i2))
    | Inferred_type_seq _ C i1, Any_type_seq _ i2 =>
      Return (Inferred_type _ _ (syntax.IF_ f i1 (i2 C)))
    | Any_type_seq _ i1, Inferred_type_seq _ C i2 =>
      Return (Inferred_type _ _ (syntax.IF_ f (i1 C) i2))
    | Any_type_seq _ i1, Any_type_seq _ i2 =>
      Return (Any_type _ (fun C =>
                              syntax.IF_ f (i1 C) (i2 C)))
    end.

  Definition type_loop_family (f : loop_family) (t : type) :
    M {A & {B & syntax.loop_family A B t}} :=
    match f, t with
    | LOOP_bool, Comparable_type bool => Return (existT _ _ (existT _ _ syntax.LOOP_bool))
    | LOOP_or, or a b => Return (existT _ _ (existT _ _ (syntax.LOOP_or a b)))
    | _, _ => Failed _ (Typing _ "type_family"%string)
    end.

  Definition type_loop {self_type} (f : loop_family) (t : type)
             (type_instruction_seq :
                forall (i : untyped_syntax.instruction_seq) A,
                  M (typer_result_seq A))
             (i : untyped_syntax.instruction_seq) A
    : M (typer_result (self_type := self_type) (t ::: A)) :=
    let! (existT _ B1 (existT _ B2 f)) := type_loop_family f t in
    let! (existT _ _ r) := type_check_instruction_seq type_instruction_seq i (B1 ++ A) (t ::: A) in
    Return (Inferred_type _ _ (syntax.LOOP_ f r)).

  Definition take_one (S : syntax.stack_type) : M (type * syntax.stack_type) :=
    match S with
    | nil => Failed _ (Typing _ "take_one"%string)
    | cons a l => Return (a, l)
    end.

  Fixpoint take_n (A : syntax.stack_type) n : M ({B | List.length B = n} * syntax.stack_type) :=
    match n as n return M ({B | List.length B = n} * syntax.stack_type) with
    | 0 => Return (exist (fun B => List.length B = 0) nil eq_refl, A)
    | S n =>
      let! (a, A) := take_one A in
      let! (exist _ B H, C) := take_n A n in
      Return (exist _ (cons a B) (f_equal S H), C)
    end.

  Lemma take_n_length n S1 S2 H1 : take_n (S1 ++ S2) n = Return (exist _ S1 H1, S2).
  Proof.
    generalize dependent S1.
    induction n; destruct S1; simpl; intro H1.
    - repeat f_equal.
      apply Eqdep_dec.UIP_dec.
      repeat decide equality.
    - discriminate.
    - discriminate.
    - assert (List.length S1 = n) as H2.
      + apply (f_equal pred) in H1.
        exact H1.
      + rewrite (IHn S1 H2).
        simpl.
        repeat f_equal.
        apply Eqdep_dec.UIP_dec.
        repeat decide equality.
  Qed.

  Definition type_check_dig {self_type} n (S:syntax.stack_type) : M { B : syntax.stack_type & syntax.opcode S B} :=
    let! (exist _ S1 H1, tS2) := take_n S n in
    let! (t, S2) := take_one tS2 in
    let! o := opcode_cast_domain self_type (S1 +++ t ::: S2) S _ (syntax.DIG n H1) in
    Return (existT _ (t ::: S1 +++ S2) o).

  Definition type_check_dug {self_type} n (S:syntax.stack_type) : M { B : syntax.stack_type & syntax.opcode S B} :=
    let! (t, S12) := take_one S in
    let! (exist _ S1 H1, S2) := take_n S12 n in
    let! o := opcode_cast_domain self_type (t ::: S1 +++ S2) S _ (syntax.DUG n H1) in
    Return (existT _ (S1 +++ t ::: S2) o).

  Fixpoint as_comparable (a : type) : M comparable_type :=
    match a with
    | Comparable_type a => Return (Comparable_type_simple a)
    | pair (Comparable_type a) b =>
      let! b := as_comparable b in
      Return (Cpair a b)
    | _ => Failed _ (Typing _ ("not a comparable type"%string, a))
    end.

  Lemma as_comparable_comparable (a : comparable_type) :
    as_comparable a = Return a.
  Proof.
    induction a.
    - reflexivity.
    - simpl.
      rewrite IHa.
      reflexivity.
  Qed.

  Definition type_opcode {self_type} (o : opcode) A : M { B : syntax.stack_type & @syntax.opcode self_type A B} :=
    match o, A with
    | APPLY, a :: lambda (pair a' b) c :: B =>
      let A := a :: lambda (pair a' b) c :: B in
      let A' := a :: lambda (pair a b) c :: B in
      let! Ha := error.assume (is_pushable a) (Typing _ "APPLY"%string) in
      let o := @syntax.APPLY _ _ _ _ _ Ha in
      let! o := opcode_cast_domain self_type A' A _ o in
      Return (existT _ _ o)
    | DUP, a :: A =>
      Return (existT _ _ syntax.DUP)
    | SWAP, a :: b :: A =>
      Return (existT _ _ syntax.SWAP)
    | UNIT, A => Return (existT _ _ syntax.UNIT)
    | EQ, Comparable_type int :: A =>
      Return (existT _ _ syntax.EQ)
    | NEQ, Comparable_type int :: A =>
      Return (existT _ _ syntax.NEQ)
    | LT, Comparable_type int :: A =>
      Return (existT _ _ syntax.LT)
    | GT, Comparable_type int :: A =>
      Return (existT _ _ syntax.GT)
    | LE, Comparable_type int :: A =>
      Return (existT _ _ syntax.LE)
    | GE, Comparable_type int :: A =>
      Return (existT _ _ syntax.GE)
    | OR, Comparable_type bool :: Comparable_type bool :: A =>
      Return (existT _ _ (@syntax.OR _ _ syntax.bitwise_bool _))
    | OR, Comparable_type nat :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.OR _ _ syntax.bitwise_nat _))
    | AND, Comparable_type bool :: Comparable_type bool :: A =>
      Return (existT _ _ (@syntax.AND _ _ _ syntax.and_bool _))
    | AND, Comparable_type nat :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.AND _ _ _ syntax.and_nat _))
    | AND, Comparable_type int :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.AND _ _ _ syntax.and_int _))
    | XOR, Comparable_type bool :: Comparable_type bool :: A =>
      Return (existT _ _ (@syntax.XOR _ _ syntax.bitwise_bool _))
    | XOR, Comparable_type nat :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.XOR _ _ syntax.bitwise_nat _))
    | NOT, Comparable_type bool :: A =>
      Return (existT _ _ (@syntax.NOT _ _ syntax.not_bool _))
    | NOT, Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.NOT _ _ syntax.not_nat _))
    | NOT, Comparable_type int :: A =>
      Return (existT _ _ (@syntax.NOT _ _ syntax.not_int _))
    | NEG, Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.NEG _ _ syntax.neg_nat _))
    | NEG, Comparable_type int :: A =>
      Return (existT _ _ (@syntax.NEG _ _ syntax.neg_int _))
    | ABS, Comparable_type int :: A =>
      Return (existT _ _ syntax.ABS)
    | INT, Comparable_type nat :: A =>
      Return (existT _ _ syntax.INT)
    | ISNAT, Comparable_type int :: A =>
      Return (existT _ _ syntax.ISNAT)
    | ADD, Comparable_type nat :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.ADD _ _ _ syntax.add_nat_nat _))
    | ADD, Comparable_type nat :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.ADD _ _ _ syntax.add_nat_int _))
    | ADD, Comparable_type int :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.ADD _ _ _ syntax.add_int_nat _))
    | ADD, Comparable_type int :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.ADD _ _ _ syntax.add_int_int _))
    | ADD, Comparable_type timestamp :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.ADD _ _ _ syntax.add_timestamp_int _))
    | ADD, Comparable_type int :: Comparable_type timestamp :: A =>
      Return (existT _ _ (@syntax.ADD _ _ _ syntax.add_int_timestamp _))
    | ADD, Comparable_type mutez :: Comparable_type mutez :: A =>
      Return (existT _ _ (@syntax.ADD _ _ _ syntax.add_tez_tez _))
    | SUB, Comparable_type nat :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.SUB _ _ _ syntax.sub_nat_nat _))
    | SUB, Comparable_type nat :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.SUB _ _ _ syntax.sub_nat_int _))
    | SUB, Comparable_type int :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.SUB _ _ _ syntax.sub_int_nat _))
    | SUB, Comparable_type int :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.SUB _ _ _ syntax.sub_int_int _))
    | SUB, Comparable_type timestamp :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.SUB _ _ _ syntax.sub_timestamp_int _))
    | SUB, Comparable_type timestamp :: Comparable_type timestamp :: A =>
      Return (existT _ _ (@syntax.SUB _ _ _ syntax.sub_timestamp_timestamp _))
    | SUB, Comparable_type mutez :: Comparable_type mutez :: A =>
      Return (existT _ _ (@syntax.SUB _ _ _ syntax.sub_tez_tez _))
    | MUL, Comparable_type nat :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.MUL _ _ _ syntax.mul_nat_nat _))
    | MUL, Comparable_type nat :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.MUL _ _ _ syntax.mul_nat_int _))
    | MUL, Comparable_type int :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.MUL _ _ _ syntax.mul_int_nat _))
    | MUL, Comparable_type int :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.MUL _ _ _ syntax.mul_int_int _))
    | MUL, Comparable_type mutez :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.MUL _ _ _ syntax.mul_tez_nat _))
    | MUL, Comparable_type nat :: Comparable_type mutez :: A =>
      Return (existT _ _ (@syntax.MUL _ _ _ syntax.mul_nat_tez _))
    | EDIV, Comparable_type nat :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.EDIV _ _ _ syntax.ediv_nat_nat _))
    | EDIV, Comparable_type nat :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.EDIV _ _ _ syntax.ediv_nat_int _))
    | EDIV, Comparable_type int :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.EDIV _ _ _ syntax.ediv_int_nat _))
    | EDIV, Comparable_type int :: Comparable_type int :: A =>
      Return (existT _ _ (@syntax.EDIV _ _ _ syntax.ediv_int_int _))
    | EDIV, Comparable_type mutez :: Comparable_type nat :: A =>
      Return (existT _ _ (@syntax.EDIV _ _ _ syntax.ediv_tez_nat _))
    | EDIV, Comparable_type mutez :: Comparable_type mutez :: A =>
      Return (existT _ _ (@syntax.EDIV _ _ _ syntax.ediv_tez_tez _))
    | LSL, Comparable_type nat :: Comparable_type nat :: A =>
      Return (existT _ _ syntax.LSL)
    | LSR, Comparable_type nat :: Comparable_type nat :: A =>
      Return (existT _ _ syntax.LSR)
    | COMPARE, a :: a' :: B =>
      let A := a ::: a' ::: B in
      let! a : comparable_type := as_comparable a in
      let! a' : comparable_type := as_comparable a' in
      let A' := a ::: a ::: B in
      let! o := opcode_cast_domain self_type A' A (int ::: B) (syntax.COMPARE (a := a)) in
      Return (existT _ _ o)
    | CONCAT, Comparable_type string :: Comparable_type string :: B =>
      Return (existT _ _ (@syntax.CONCAT _ _ syntax.stringlike_string _))
    | CONCAT, Comparable_type bytes :: Comparable_type bytes :: B =>
      Return (existT _ _ (@syntax.CONCAT _ _ syntax.stringlike_bytes _))
    | CONCAT, list (Comparable_type string) :: B =>
      Return (existT _ _ (@syntax.CONCAT_list _ _ syntax.stringlike_string _))
    | CONCAT, list (Comparable_type bytes) :: B =>
      Return (existT _ _ (@syntax.CONCAT_list _ _ syntax.stringlike_bytes _))
    | SIZE, set a :: A =>
      Return (existT _ _ (@syntax.SIZE _ _ (syntax.size_set a) _))
    | SIZE, cons (list a) A =>
      Return (existT _ _ (@syntax.SIZE _ _ (syntax.size_list a) _))
    | SIZE, cons (map a b) A =>
      Return (existT _ _ (@syntax.SIZE _ _ (syntax.size_map a b) _))
    | SIZE, Comparable_type string :: A =>
      Return (existT _ _ (@syntax.SIZE _ _ syntax.size_string _))
    | SIZE, Comparable_type bytes :: A =>
      Return (existT _ _ (@syntax.SIZE _ _ syntax.size_bytes _))
    | SLICE, Comparable_type nat :: Comparable_type nat :: Comparable_type string :: A =>
      Return (existT _ _ (@syntax.SLICE _ _ syntax.stringlike_string _))
    | SLICE, Comparable_type nat :: Comparable_type nat :: Comparable_type bytes :: A =>
      Return (existT _ _ (@syntax.SLICE _ _ syntax.stringlike_bytes _))
    | PAIR, a :: b :: A =>
      Return (existT _ _ syntax.PAIR)
    | CAR, pair a b :: A =>
      Return (existT _ _ syntax.CAR)
    | CDR, pair a b :: A =>
      Return (existT _ _ syntax.CDR)
    | EMPTY_SET c, A =>
      Return (existT _ _ (syntax.EMPTY_SET c))
    | MEM, elt' :: set elt :: B =>
      let A := elt' :: set elt :: B in
      let A' := elt ::: set elt :: B in
      let! o := opcode_cast_domain
        self_type A' A _ (@syntax.MEM _ _ _ (syntax.mem_set elt) _) in
      Return (existT _ _ o)
    | MEM, kty' :: map kty vty :: B =>
      let A := kty' :: map kty vty :: B in
      let A' := kty ::: map kty vty :: B in
      let! o := opcode_cast_domain
        self_type A' A _ (@syntax.MEM _ _ _ (syntax.mem_map kty vty) _) in
      Return (existT _ _ o)
    | MEM, kty' :: big_map kty vty :: B =>
      let A := kty' :: big_map kty vty :: B in
      let A' := kty ::: big_map kty vty :: B in
      let! o := opcode_cast_domain
        self_type A' A _ (@syntax.MEM _ _ _ (syntax.mem_bigmap kty vty) _) in
      Return (existT _ _ o)
    | UPDATE, elt' :: Comparable_type bool :: set elt :: B =>
      let A := elt' ::: bool ::: set elt :: B in
      let A' := elt ::: bool ::: set elt :: B in
      let! o := opcode_cast_domain
        self_type A' A _ (@syntax.UPDATE _ _ _ _ (syntax.update_set elt) _) in
      Return (existT _ _ o)
    | UPDATE, kty' :: option vty' :: map kty vty :: B =>
      let A := kty' ::: option vty' ::: map kty vty :: B in
      let A' := kty ::: option vty ::: map kty vty :: B in
      let! o := opcode_cast_domain
        self_type A' A _ (@syntax.UPDATE _ _ _ _ (syntax.update_map kty vty) _) in
      Return (existT _ _ o)
    | UPDATE, kty' :: option vty' :: big_map kty vty :: B =>
      let A := kty' ::: option vty' ::: big_map kty vty :: B in
      let A' := kty ::: option vty ::: big_map kty vty :: B in
      let! o := opcode_cast_domain
        self_type A' A _ (@syntax.UPDATE _ _ _ _ (syntax.update_bigmap kty vty) _) in
      Return (existT _ _ o)
    | EMPTY_MAP kty vty, A =>
      Return (existT _ _ (syntax.EMPTY_MAP kty vty))
    | EMPTY_BIG_MAP kty vty, A =>
      let! H :=
         error.assume
           (is_big_map_value vty)
           (Typing _ "EMPTY_BIG_MAP"%string)
      in
      Return (existT _ _ (syntax.EMPTY_BIG_MAP kty vty H))
    | GET, kty' :: map kty vty :: B =>
      let A := kty' :: map kty vty :: B in
      let A' := kty ::: map kty vty :: B in
      let! o := opcode_cast_domain
        self_type A' A _ (@syntax.GET _ _ _ (syntax.get_map kty vty) _) in
      Return (existT _ _ o)
    | GET, kty' :: big_map kty vty :: B =>
      let A := kty' :: big_map kty vty :: B in
      let A' := kty ::: big_map kty vty :: B in
      let! o := opcode_cast_domain
        self_type A' A _ (@syntax.GET _ _ _ (syntax.get_bigmap kty vty) _) in
      Return (existT _ _ o)
    | SOME, a :: A => Return (existT _ _ syntax.SOME)
    | NONE a, A => Return (existT _ _ (syntax.NONE a))
    | LEFT b, a :: A => Return (existT _ _ (syntax.LEFT b))
    | RIGHT a, b :: A => Return (existT _ _ (syntax.RIGHT a))
    | CONS, a' :: list a :: B =>
      let A := a' :: list a :: B in
      let A' := a :: list a :: B in
      let! o := opcode_cast_domain self_type A' A _ (syntax.CONS) in
      Return (existT _ _ o)
    | NIL a, A => Return (existT _ _ (syntax.NIL a))
    | TRANSFER_TOKENS, p1 :: Comparable_type mutez :: contract p2 :: B =>
      let A := p1 ::: mutez ::: contract p2 ::: B in
      let A' := p1 ::: mutez ::: contract p1 ::: B in
      let! H :=
         error.assume
           (is_passable p1)
           (Typing _ "TRANSFER_TOKENS"%string)
      in
      let! o := opcode_cast_domain self_type A' A _ (syntax.TRANSFER_TOKENS H) in
      Return (existT _ _ o)
    | SET_DELEGATE, option (Comparable_type key_hash) :: A =>
      Return (existT _ _ syntax.SET_DELEGATE)
    | BALANCE, A =>
      Return (existT _ _ syntax.BALANCE)
    | ADDRESS, contract _ :: A =>
      Return (existT _ _ syntax.ADDRESS)
    | CONTRACT an ty, Comparable_type address :: A =>
      let! H :=
         error.assume
           (is_passable ty)
           (Typing _ "CONTRACT"%string)
      in
      Return (existT _ _ (syntax.CONTRACT an ty H))
    | SOURCE, A =>
      Return (existT _ _ syntax.SOURCE)
    | SENDER, A =>
      Return (existT _ _ syntax.SENDER)
    | AMOUNT, A =>
      Return (existT _ _ syntax.AMOUNT)
    | IMPLICIT_ACCOUNT, Comparable_type key_hash :: A =>
      Return (existT _ _ syntax.IMPLICIT_ACCOUNT)
    | NOW, A =>
      Return (existT _ _ syntax.NOW)
    | PACK, a :: A =>
      let! H :=
         error.assume
           (is_packable a)
           (Typing _ "PACK"%string)
      in
      Return (existT _ _ (syntax.PACK H))
    | UNPACK ty, Comparable_type bytes :: A =>
      let! H :=
         error.assume
           (is_packable ty)
           (Typing _ "UNPACK"%string)
      in
      Return (existT _ _ (syntax.UNPACK ty H))
    | HASH_KEY, key :: A =>
      Return (existT _ _ syntax.HASH_KEY)
    | BLAKE2B, Comparable_type bytes :: A =>
      Return (existT _ _ syntax.BLAKE2B)
    | SHA256, Comparable_type bytes :: A =>
      Return (existT _ _ syntax.SHA256)
    | SHA512, Comparable_type bytes :: A =>
      Return (existT _ _ syntax.SHA512)
    | CHECK_SIGNATURE, key :: signature :: Comparable_type bytes :: A =>
      Return (existT _ _ syntax.CHECK_SIGNATURE)
    | DIG n, A => type_check_dig n _
    | DUG n, A => type_check_dug n _
    | DROP n, S12 =>
      let! (exist _ S1 H1, S2) := take_n S12 n in
      let! o := opcode_cast_domain self_type (S1 +++ S2) S12 _ (syntax.DROP n H1) in
      Return (existT _ _ o)
    | CHAIN_ID, _ =>
      Return (existT _ _ syntax.CHAIN_ID)
    | _, _ => Failed _ (Typing _ (instruction_opcode o, A))
    end.

  Fixpoint type_comparable_data (tm : type_mode) (d : concrete_data) {struct d} : forall a,
      M (comparable_data a) :=
    match d with
    | Int_constant z =>
      fun ty =>
        match ty with
        | int => Return z
        | nat =>
          if (z >=? 0)%Z then Return (Z.to_N z)
          else Failed _ (Typing _ ("Negative value cannot be typed in nat"%string, d))
        | mutez => tez.of_Z z
        | timestamp =>
          match tm with
          | Optimized | Any => Return z
          | Readable => Failed _ (Typing _ ("Not readable"%string, (d, ty)))
          end
        | _ => Failed _ (Typing _ (d, ty))
        end
    | String_constant s =>
      fun ty =>
        match ty with
        | string => Return s
        | key_hash => Return (Mk_key_hash s)
        | address =>
          let fail :=
              Failed
                _
                (Typing
                   _
                   ("Address litterals should start by 'tz' or by 'KT1'"%string,
                    s))
          in
          match s with
          | String c1 (String c2 s) =>
            if ascii_dec c1 "t" then
              if ascii_dec c2 "z" then
                Return (comparable.Implicit (comparable.Mk_key_hash s))
              else fail
            else
              match s with
              | String c3 s =>
                if ascii_dec c1 "K" then
                  if ascii_dec c2 "T" then
                    if ascii_dec c3 "1" then
                      Return (comparable.Originated
                                (comparable.Mk_smart_contract_address s))
                    else
                      fail
                  else
                    fail
                else fail
              | _ => fail
              end
          | _ => fail
          end
        | timestamp =>
          match tm with
          | Optimized => Failed _ (Typing _ ("Not optimized"%string, (d, ty)))
          | Readable
          | Any =>
            match Moment.Parse.rfc3339_non_strict (LString.s s) with
            | Some (moment, nil) =>
              let z := Moment.to_epoch moment in
              Return z
            | _ =>
              Failed _ (Typing _ ("Cannot parse timestamp according to rfc3339"%string, s))
            end
          end
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Bytes_constant s =>
      fun ty =>
        match ty with
        | bytes => Return s
        | _ => Failed _ (Typing _ (d, ty))
        end
    | True_ =>
      fun ty =>
        match ty with
        | bool => Return true
        | _ => Failed _ (Typing _ (d, ty))
        end
    | False_ =>
      fun ty =>
        match ty with
        | bool => Return false
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Pair x y =>
      fun ty =>
        match ty with
        | Cpair a b =>
          let! x := type_comparable_data tm x a in
          let! y := type_comparable_data tm y b in
          Return (x, y)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | d => fun ty => Failed _ (Typing _ (d, ty))
    end.

  Fixpoint type_data_set tm
           (l : List.list concrete_data) (a : comparable_type) {struct l} :=
    match l with
    | nil => Return nil
    | cons x l =>
      let! x := type_comparable_data tm x a in
      let! l := type_data_set tm l a in
      Return (cons x l)
    end.

  Fixpoint type_data (tm : type_mode) (d : concrete_data) {struct d}
    : forall ty, M (syntax.concrete_data ty) :=
    match d with
    | Int_constant _ =>
      fun ty =>
        match ty with
        | Comparable_type a =>
          let! r := type_comparable_data tm d a in
          Return (syntax.Comparable_constant a r)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Bytes_constant s =>
      fun ty =>
        match ty with
        | Comparable_type a =>
          let! r := type_comparable_data tm d a in
          Return (syntax.Comparable_constant a r)
        | chain_id => Return (syntax.Chain_id_constant (comparable.Mk_chain_id s))
        | _ => Failed _ (Typing _ (d, ty))
        end
    | String_constant s =>
      fun ty =>
        match ty with
        | signature => Return (syntax.Signature_constant s)
        | key => Return (syntax.Key_constant s)
        | Comparable_type a =>
          let! r := type_comparable_data tm d a in
          Return (syntax.Comparable_constant a r)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Unit =>
      fun ty =>
        match ty with
        | unit => Return syntax.Unit
        | _ => Failed _ (Typing _ (d, ty))
        end
    | True_ =>
      fun ty =>
        match ty with
        | Comparable_type bool => Return (syntax.Comparable_constant bool true)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | False_ =>
      fun ty =>
        match ty with
        | Comparable_type bool => Return (syntax.Comparable_constant bool false)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Pair x y =>
      fun ty =>
        match ty with
        | pair a b =>
          let! x := type_data tm x a in
          let! y := type_data tm y b in
          Return (syntax.Pair x y)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Left x =>
      fun ty =>
        match ty with
        | or a b =>
          let! x := type_data tm x a in
          Return (syntax.Left x)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Right y =>
      fun ty =>
        match ty with
        | or a b =>
          let! y := type_data tm y b in
          Return (syntax.Right y)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Some_ x =>
      fun ty =>
        match ty with
        | option a =>
          let! x := type_data tm x a in
          Return (syntax.Some_ x)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | None_ =>
      fun ty =>
        match ty with
        | option a => Return syntax.None_
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Concrete_seq l =>
      fun ty =>
        match ty with
        | list a =>
          let! l :=
            (fix type_data_list l :=
              match l with
              | nil => Return nil
              | cons x l =>
                let! x := type_data tm x a in
                let! l := type_data_list l in
                Return (cons x l)
              end
            ) l in
          Return (syntax.Concrete_list l)
        | set a =>
          let! l := type_data_set tm l a in
          match set.sorted_dec _ _ (compare_eq_iff a) (lt_trans a) l with
          | left H => Return (syntax.Concrete_set (exist (fun l => Sorted.StronglySorted _ l) l H))
          | right _ => Failed _ (Typing _ ("set literals have to be sorted"%string))
          end
        | map a b =>
          let! l :=
            (fix type_data_list l :=
              match l with
              | nil => Return nil
              | cons (Elt x y) l =>
                let! x := type_comparable_data tm x a in
                let! y := type_data tm y b in
                let! l := type_data_list l in
                Return (cons (x, y) l)
              | _ => Failed _ (Typing _ ("map literals are sequences of the form {Elt k1 v1; ...; Elt kn vn}"%string))
              end
            ) l in
          match map.sorted_dec _ _ _ l with
          | left H => Return (syntax.Concrete_map (map.of_list _ _ _ l H))
          | right _ => Failed _ (Typing _ ("map literals have to be sorted by keys"%string))
          end
        | big_map a b =>
          let! l :=
            (fix type_data_list l :=
              match l with
              | nil => Return nil
              | cons (Elt x y) l =>
                let! x := type_comparable_data tm x a in
                let! y := type_data tm y b in
                let! l := type_data_list l in
                Return (cons (x, y) l)
              | _ => Failed _ (Typing _ ("big map literals are sequences of the form {Elt k1 v1; ...; Elt kn vn}"%string))
              end
            ) l in
          match map.sorted_dec _ _ _ l with
          | left H => Return (syntax.Concrete_big_map (map.of_list _ _ _ l H))
          | right _ => Failed _ (Typing _ ("big map literals have to be sorted by keys"%string))
          end
        | _ => Failed _ (Typing _ (d, ty))
        end
    | Instruction i =>
      fun ty =>
        match ty with
        | lambda a b =>
          let! existT _ tff i := type_check_instruction_seq (type_instruction_seq tm) i (cons a nil) (cons b nil) in
          Return (syntax.Instruction _ i)
        | _ => Failed _ (Typing _ (d, ty))
        end
    | d => fun ty => Failed _ (Typing _ (d, ty))
    end

  with
  type_instruction {self_type} tm i A {struct i} : M (typer_result (self_type := self_type) A) :=
    match i, A with
    | Instruction_seq i, _ =>
      let! i := type_instruction_seq tm i A in
      match i with
      | Any_type_seq _ i => Return (Any_type _ (fun B => syntax.Instruction_seq (i B)))
      | Inferred_type_seq _ _ i => Return (Inferred_type _ _ (syntax.Instruction_seq i))
      end
    | FAILWITH, a :: A =>
      let! H :=
         error.assume
           (is_packable a)
           (Typing _ "FAILWITH"%string)
      in
      Return (Any_type _ (fun B => syntax.FAILWITH H))
    | IF_ f i1 i2, t :: A =>
      type_branches f t (type_instruction_seq tm) i1 i2 A
    | LOOP_ f i, t :: A =>
      type_loop f t (type_instruction_seq tm) i A
    | EXEC, a :: lambda a' b :: B =>
      let A := a :: lambda a' b :: B in
      let A' := a :: lambda a b :: B in
      let! i := instruction_cast_domain A' A _ syntax.EXEC in
      Return (Inferred_type _ _ i)
    | PUSH a v, A =>
      let! d := type_data tm v a in
      Return (Inferred_type _ _ (syntax.PUSH a d))
    | LAMBDA a b i, A =>
      let! existT _ tff i :=
        type_check_instruction_seq (type_instruction_seq tm) i (a :: nil) (b :: nil) in
      Return (Inferred_type _ _ (syntax.LAMBDA a b i))
    | ITER i, list a :: A =>
      let! (existT _ _ i) := type_check_instruction_seq (type_instruction_seq tm) i (a :: A) A in
      Return (Inferred_type _ _ (syntax.ITER (i := syntax.iter_list _) i))
    | ITER i, set a :: A =>
      let! (existT _ _ i) := type_check_instruction_seq (type_instruction_seq tm) i (a ::: A) A in
      Return (Inferred_type _ _ (syntax.ITER (i := syntax.iter_set _)i))
    | ITER i, map kty vty :: A =>
      let! (existT _ _ i) := type_check_instruction_seq (type_instruction_seq tm) i (pair kty vty :: A) A in
      Return (Inferred_type _ _ (syntax.ITER (i := syntax.iter_map _ _) i))
    | MAP i, list a :: A =>
      let! r := type_instruction_seq_no_tail_fail (type_instruction_seq tm) i (a :: A) in
      match r with
      | existT _ (b :: A') i =>
        let! i := instruction_seq_cast_range (a :: A) (b :: A') (b :: A) i in
        Return (Inferred_type _ _ (syntax.MAP (i := syntax.map_list _ _) i))
      | _ => Failed _ (Typing _ tt)
      end
    | MAP i, map kty vty :: A =>
      let! r := type_instruction_seq_no_tail_fail (type_instruction_seq tm) i (pair kty vty ::: A) in
      match r with
      | existT _ (b :: A') i =>
        let! i := instruction_seq_cast_range (pair kty vty :: A) (b :: A') (b :: A) i in
        Return (Inferred_type _ _ (syntax.MAP (i := syntax.map_map _ _ _) i))
      | _ => Failed _ (Typing _ tt)
      end
    | CREATE_CONTRACT g p an i,
      option (Comparable_type key_hash) :: Comparable_type mutez :: g2 :: B =>

      let! Hp :=
         error.assume
           (is_passable (entrypoints.entrypoint_tree_to_type p))
           (Typing
              _
              "CREATE_CONTACT: parameter type is not passable"%string)
      in

      let! Hg :=
         error.assume
           (is_storable g)
           (Typing
              _
              "CREATE_CONTACT: storage type is not storable"%string)
      in

      let A :=
          option key_hash ::: mutez ::: g2 :: B in
      let A' :=
          option key_hash ::: mutez ::: g ::: B in
      let! existT _ tff i :=
        type_check_instruction_seq (self_type := (Some (p, an))) (type_instruction_seq tm) i (pair (entrypoints.entrypoint_tree_to_type p) g :: nil) (pair (list operation) g :: nil) in
      let! i := instruction_cast_domain A' A _ (syntax.CREATE_CONTRACT g p an Hp Hg i) in
      Return (Inferred_type _ _ i)
    | SELF an, A =>
      match self_type with
      | Some (sty, san) =>
        let error := Typing _ "No such self entrypoint"%string in
        let! H := syntax.isSome_maybe error (entrypoints.get_entrypoint_opt an sty san) in
        Return (Inferred_type _ _ (syntax.SELF an H))
      | None => Failed _ (Typing _ "SELF is not allowed inside lambdas"%string)
      end
    | DIP n i, S12 =>
      let! (exist _ S1 H1, S2) := take_n S12 n in
      let! existT _ B i := type_instruction_seq_no_tail_fail (type_instruction_seq tm) i S2 in
      let! i := instruction_cast_domain (S1 +++ S2) S12 _ (syntax.DIP n H1 i) in
      Return (Inferred_type S12 (S1 +++ B) i)
    | instruction_opcode o, A =>
      let! (existT _ B o) := type_opcode o A in
      Return (Inferred_type A B (syntax.Instruction_opcode o))
    | _, _ => Failed _ (Typing _ (i, A))
    end
  with
  type_instruction_seq {self_type} tm i A {struct i} : M (typer_result_seq (self_type := self_type) A) :=
    match i, A with
    | NOOP, A => Return (Inferred_type_seq _ _ syntax.NOOP)
    | SEQ i1 i2, A =>
      let! r1 := type_instruction tm i1 A in
      match r1, i2 with
      | Inferred_type _ B i1, i2 =>
        let! r2 := type_instruction_seq tm i2 B in
        match r2 with
        | Inferred_type_seq _ C i2 =>
          Return (Inferred_type_seq _ _ (syntax.SEQ i1 i2))
        | Any_type_seq _ i2 =>
          Return (Any_type_seq _ (fun C => syntax.SEQ i1 (i2 C)))
        end
      | Any_type _ i1, NOOP =>
        Return (Any_type_seq _ (fun C => syntax.Tail_fail (i1 C)))
      | Any_type _ _, _ =>
        Failed _ (Typing _
                         "FAILWITH instruction can only appear at the tail of application sequences"%string)
      end
    end.

