Require Import String List.
Require Import untyped_syntax micheline_syntax error location.

Open Scope string.

Definition dummy_loc : location := Mk_loc 0 0.
Definition dummy_mich (m:micheline) : loc_micheline :=
  Mk_loc_micheline (dummy_loc, dummy_loc, m).
Definition dummy_prim (p:string) (l:list loc_micheline) :=
  dummy_mich (PRIM (dummy_loc, dummy_loc, p) l).

Definition michelson2micheline_ctype (ct: syntax.comparable_type) : loc_micheline :=
  match ct with
  | syntax.string => dummy_prim "string" nil
  | syntax.nat => dummy_prim "nat" nil
  | syntax.int => dummy_prim "int" nil
  | syntax.bytes => dummy_prim "bytes" nil
  | syntax.bool => dummy_prim "bool" nil
  | syntax.mutez => dummy_prim "mutez" nil
  | syntax.key_hash => dummy_prim "key_hash" nil
  | syntax.timestamp => dummy_prim "timestamp" nil
  | syntax.address => dummy_prim "address" nil
  end.

Fixpoint michelson2micheline_type (t : syntax.type) : loc_micheline :=
  match t with
  | syntax.Comparable_type ct => michelson2micheline_ctype ct
  | syntax.key => dummy_prim "key" nil
  | syntax.unit => dummy_prim "unit" nil
  | syntax.signature => dummy_prim "signature" nil
  | syntax.operation => dummy_prim "operation" nil
  | syntax.option t' => dummy_prim "option" ((michelson2micheline_type t')::nil)
  | syntax.list t' => dummy_prim "list" ((michelson2micheline_type t')::nil)
  | syntax.set ct => dummy_prim "set" ((michelson2micheline_ctype ct)::nil)
  | syntax.contract t' => dummy_prim "contract" ((michelson2micheline_type t')::nil)
  | syntax.pair t1 t2 =>
    dummy_prim "pair" ((michelson2micheline_type t1)::(michelson2micheline_type t2)::nil)
  | syntax.or t1 t2 =>
    dummy_prim "or" ((michelson2micheline_type t1)::(michelson2micheline_type t2)::nil)
  | syntax.lambda t1 t2 =>
    dummy_prim "lambda" ((michelson2micheline_type t1)::(michelson2micheline_type t2)::nil)
  | syntax.map ct1 t2 =>
    dummy_prim "map" ((michelson2micheline_ctype ct1)::(michelson2micheline_type t2)::nil)
  | syntax.big_map ct1 t2 =>
    dummy_prim "big_map" ((michelson2micheline_ctype ct1)::(michelson2micheline_type t2)::nil)
  end.

Fixpoint michelson2micheline_data (d : concrete_data) : loc_micheline :=
  match d with
  | Int_constant z => dummy_mich (NUMBER z)
  | Nat_constant n => dummy_mich (NUMBER (BinInt.Z.of_N n))
  | Timestamp_constant ts => dummy_mich (NUMBER ts)
  | Mutez_constant (syntax.Mk_mutez m) => dummy_mich (NUMBER (tez.to_Z m))
  | String_constant s => dummy_mich (STR s)
  | Bytes_constant b => dummy_mich (BYTES b)
  | Signature_constant s => dummy_mich (STR s)
  | Key_constant k => dummy_mich (STR k)
  | Key_hash_constant h => dummy_mich (STR h)
  | Contract_constant (syntax.Mk_contract c) => dummy_mich (STR c)
  | Unit => dummy_prim "Unit" nil
  | True_ => dummy_prim "True" nil
  | False_ => dummy_prim "False" nil
  | Pair a b =>
    dummy_prim "Pair" ((michelson2micheline_data a)::(michelson2micheline_data b)::nil)
  | Left a => dummy_prim "Left" ((michelson2micheline_data a)::nil)
  | Right a => dummy_prim "Right" ((michelson2micheline_data a)::nil)
  | Some_ a => dummy_prim "Some" ((michelson2micheline_data a)::nil)
  | None_ => dummy_prim "None" nil
  | Elt a b =>
    dummy_prim "Elt" ((michelson2micheline_data a)::(michelson2micheline_data b)::nil)
  | Concrete_seq s => dummy_mich (SEQ (map michelson2micheline_data s))
  | Instruction _ => dummy_prim "NOOP" nil (* Should never occur *)
  end.

Fixpoint michelson2micheline_instruction (i : instruction) : loc_micheline :=
  match i with
  | NOOP => dummy_prim "NOOP" nil
  | untyped_syntax.SEQ i1 i2 => dummy_mich (SEQ ((michelson2micheline_instruction i1)::(michelson2micheline_instruction i2)::nil))
  | FAILWITH => dummy_prim "FAILWITH" nil
  | EXEC => dummy_prim "EXEC" nil
  | DROP => dummy_prim "DROP" nil
  | DUP => dummy_prim "DUP" nil
  | SWAP => dummy_prim "SWAP" nil
  | UNIT => dummy_prim "UNIT" nil
  | EQ => dummy_prim "EQ" nil
  | NEQ => dummy_prim "NEQ" nil
  | LT => dummy_prim "LT" nil
  | GT => dummy_prim "GT" nil
  | LE => dummy_prim "LE" nil
  | GE => dummy_prim "GE" nil
  | OR => dummy_prim "OR" nil
  | AND => dummy_prim "AND" nil
  | XOR => dummy_prim "XOR" nil
  | NOT => dummy_prim "NOT" nil
  | NEG => dummy_prim "NEG" nil
  | ABS => dummy_prim "ABS" nil
  | ADD => dummy_prim "ADD" nil
  | SUB => dummy_prim "SUB" nil
  | MUL => dummy_prim "MUL" nil
  | EDIV => dummy_prim "EDIV" nil
  | LSL => dummy_prim "LSL" nil
  | LSR => dummy_prim "LSR" nil
  | COMPARE => dummy_prim "COMPARE" nil
  | CONCAT => dummy_prim "CONCAT" nil
  | SIZE => dummy_prim "SIZE" nil
  | SLICE => dummy_prim "SLICE" nil
  | PAIR => dummy_prim "PAIR" nil
  | CAR => dummy_prim "CAR" nil
  | CDR => dummy_prim "CDR" nil
  | GET => dummy_prim "GET" nil
  | SOME => dummy_prim "SOME" nil
  | NONE t => dummy_prim "NONE" ((michelson2micheline_type t)::nil)
  | LEFT t => dummy_prim "LEFT" ((michelson2micheline_type t)::nil)
  | RIGHT t => dummy_prim "RIGHT" ((michelson2micheline_type t)::nil)
  | CONS => dummy_prim "CONS" nil
  | NIL t => dummy_prim "NIL" ((michelson2micheline_type t)::nil)
  | EMPTY_SET ct => dummy_prim "EMPTY_SET" ((michelson2micheline_ctype ct)::nil)
  | EMPTY_MAP ct t => dummy_prim "EMPTY_MAP" ((michelson2micheline_ctype ct)
                                               ::(michelson2micheline_type t)::nil)
  | MEM => dummy_prim "MEM" nil
  | UPDATE => dummy_prim "UPDATE" nil
  | CREATE_CONTRACT => dummy_prim "CREATE_CONTRACT" nil
  | CREATE_CONTRACT_literal t1 t2 i => dummy_prim "CREATE_CONTRACT_literal"
                                                 ((michelson2micheline_type t1)
                                                    ::(michelson2micheline_type t2)
                                                    ::(michelson2micheline_instruction i)::nil)
  | CREATE_ACCOUNT => dummy_prim "CREATE_ACCOUNT" nil
  | TRANSFER_TOKENS => dummy_prim "TRANSFER_TOKENS" nil
  | SET_DELEGATE => dummy_prim "SET_DELEGATE" nil
  | BALANCE => dummy_prim "BALANCE" nil
  | ADDRESS => dummy_prim "ADDRESS" nil
  | CONTRACT t => dummy_prim "CONTRACT" ((michelson2micheline_type t)::nil)
  | SOURCE => dummy_prim "SOURCE" nil
  | SENDER => dummy_prim "SENDER" nil
  | SELF => dummy_prim "SELF" nil
  | AMOUNT => dummy_prim "AMOUNT" nil
  | IMPLICIT_ACCOUNT => dummy_prim "IMPLICIT_ACCOUNT" nil
  | STEPS_TO_QUOTA => dummy_prim "STEPS_TO_QUOTA" nil
  | NOW => dummy_prim "NOW" nil
  | PACK => dummy_prim "PACK" nil
  | UNPACK t => dummy_prim "UNPACK" ((michelson2micheline_type t)::nil)
  | HASH_KEY => dummy_prim "HASH_KEY" nil
  | BLAKE2B => dummy_prim "BLAKE2B" nil
  | SHA256 => dummy_prim "SHA256" nil
  | SHA512 => dummy_prim "SHA512" nil
  | CHECK_SIGNATURE => dummy_prim "CHECK_SIGNATURE" nil
  | IF_ i1 i2 => dummy_prim "IF" ((michelson2micheline_instruction i1)
                                   ::(michelson2micheline_instruction i2)::nil)
  | IF_NONE i1 i2 => dummy_prim "IF_NONE" ((michelson2micheline_instruction i1)
                                            ::(michelson2micheline_instruction i2)::nil)
  | IF_LEFT i1 i2 => dummy_prim "IF_LEFT" ((michelson2micheline_instruction i1)
                                            ::(michelson2micheline_instruction i2)::nil)
  | IF_RIGHT i1 i2 => dummy_prim "IF_RIGHT" ((michelson2micheline_instruction i1)
                                          ::(michelson2micheline_instruction i2)::nil)
  | IF_CONS i1 i2 => dummy_prim "IF_CONS" ((michelson2micheline_instruction i1)
                                          ::(michelson2micheline_instruction i2)::nil)
  | LOOP i => dummy_prim "LOOP" ((michelson2micheline_instruction i)::nil)
  | LOOP_LEFT i => dummy_prim "LOOP_LEFT" ((michelson2micheline_instruction i)::nil)
  | DIP i => dummy_prim "DIP" ((michelson2micheline_instruction i)::nil)
  | ITER i => dummy_prim "ITER" ((michelson2micheline_instruction i)::nil)
  | MAP i => dummy_prim "MAP" ((michelson2micheline_instruction i)::nil)
  | PUSH t d =>
    let t' := (michelson2micheline_type t) in
    match d with
    | Instruction d' => dummy_prim "PUSH" (t'::(michelson2micheline_instruction d')::nil)
    | _ => dummy_prim "PUSH" (t'::(michelson2micheline_data d)::nil)
    end
  | LAMBDA t1 t2 i =>
    dummy_prim "LAMBDA" ((michelson2micheline_type t1)
                           ::(michelson2micheline_type t2)
                           ::(michelson2micheline_instruction i)::nil)
  | DIG n => dummy_prim "DIG" ((dummy_mich (NUMBER (BinInt.Z.of_nat n)))::nil)
  | DUG n => dummy_prim "DUG" ((dummy_mich (NUMBER (BinInt.Z.of_nat n)))::nil)
  end.