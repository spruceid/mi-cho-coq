Require Import Ascii String Bool List.
Require Import untyped_syntax micheline_syntax error location syntax_type.

Open Scope string.

Definition dummy_loc : location := Mk_loc 0 0.
Definition dummy_mich (m:micheline) : loc_micheline :=
  Mk_loc_micheline (dummy_loc, dummy_loc, m).
Definition dummy_prim (p:String.string) (l:Datatypes.list loc_micheline) :=
  dummy_mich (PRIM (dummy_loc, dummy_loc, p) l).
Definition dummy_seq (m : loc_micheline) : loc_micheline :=
  match m with
  | Mk_loc_micheline (_, _, SEQ _) => m
  | _ => dummy_mich (SEQ (m :: nil))
  end.

Definition michelson2micheline_sctype (ct: simple_comparable_type) : loc_micheline :=
  match ct with
  | string => dummy_prim "string" nil
  | nat => dummy_prim "nat" nil
  | int => dummy_prim "int" nil
  | bytes => dummy_prim "bytes" nil
  | bool => dummy_prim "bool" nil
  | mutez => dummy_prim "mutez" nil
  | key_hash => dummy_prim "key_hash" nil
  | timestamp => dummy_prim "timestamp" nil
  | address => dummy_prim "address" nil
  end.

Fixpoint michelson2micheline_ctype (ct: comparable_type) : loc_micheline :=
  match ct with
  | Comparable_type_simple sct => michelson2micheline_sctype sct
  | Cpair sct ct =>
    dummy_prim "pair" (michelson2micheline_sctype sct :: michelson2micheline_ctype ct :: nil)
  end.

Fixpoint michelson2micheline_type (t : type) : loc_micheline :=
  match t with
  | Comparable_type ct => michelson2micheline_sctype ct
  | key => dummy_prim "key" nil
  | unit => dummy_prim "unit" nil
  | signature => dummy_prim "signature" nil
  | operation => dummy_prim "operation" nil
  | option t' => dummy_prim "option" ((michelson2micheline_type t')::nil)
  | list t' => dummy_prim "list" ((michelson2micheline_type t')::nil)
  | set ct => dummy_prim "set" ((michelson2micheline_ctype ct)::nil)
  | contract t' => dummy_prim "contract" ((michelson2micheline_type t')::nil)
  | pair t1 t2 =>
    dummy_prim "pair" ((michelson2micheline_type t1)::(michelson2micheline_type t2)::nil)
  | or t1 t2 =>
    dummy_prim "or" ((michelson2micheline_type t1)::(michelson2micheline_type t2)::nil)
  | lambda t1 t2 =>
    dummy_prim "lambda" ((michelson2micheline_type t1)::(michelson2micheline_type t2)::nil)
  | map ct1 t2 =>
    dummy_prim "map" ((michelson2micheline_ctype ct1)::(michelson2micheline_type t2)::nil)
  | big_map ct1 t2 =>
    dummy_prim "big_map" ((michelson2micheline_ctype ct1)::(michelson2micheline_type t2)::nil)
  | chain_id => dummy_prim "chain_id" nil
  end.

Fixpoint michelson2micheline_data (d : concrete_data) : loc_micheline :=
  match d with
  | Int_constant z => dummy_mich (NUMBER z)
  | String_constant s => dummy_mich (STR s)
  | Bytes_constant b => dummy_mich (BYTES b)
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
  | Concrete_seq s => dummy_mich (SEQ (List.map michelson2micheline_data s))
  | Instruction _ => dummy_prim "NOOP" nil (* Should never occur *)
  end.

Fixpoint michelson2micheline_ins (i : instruction) : loc_micheline :=
  match i with
  | NOOP => dummy_mich (SEQ nil)
  | untyped_syntax.SEQ i1 i2 =>
    let m1 := michelson2micheline_ins i1 in
    let m2 := michelson2micheline_ins i2 in
    let ls1 :=
        match m1 with
        | Mk_loc_micheline (_, _, (SEQ ls1)) => ls1
        | _ => m1 :: nil
        end in
    let ls2 :=
        match m2 with
        | Mk_loc_micheline (_, _, (SEQ ls2)) => ls2
        | _ => m2 :: nil
        end in
    dummy_mich (SEQ (List.app ls1 ls2))
  | FAILWITH => dummy_prim "FAILWITH" nil
  | EXEC => dummy_prim "EXEC" nil
  | APPLY => dummy_prim "APPLY" nil
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
  | INT => dummy_prim "INT" nil
  | ISNAT => dummy_prim "ISNAT" nil
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
  | EMPTY_BIG_MAP ct t => dummy_prim "EMPTY_BIG_MAP"
                                     ((michelson2micheline_ctype ct)
                                        ::(michelson2micheline_type t)::nil)
  | MEM => dummy_prim "MEM" nil
  | UPDATE => dummy_prim "UPDATE" nil
  | CREATE_CONTRACT t1 t2 i => dummy_prim "CREATE_CONTRACT"
                                          ((michelson2micheline_type t1)
                                             ::(michelson2micheline_type t2)
                                             ::(dummy_seq (michelson2micheline_ins i))::nil)
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
  | NOW => dummy_prim "NOW" nil
  | PACK => dummy_prim "PACK" nil
  | UNPACK t => dummy_prim "UNPACK" ((michelson2micheline_type t)::nil)
  | HASH_KEY => dummy_prim "HASH_KEY" nil
  | BLAKE2B => dummy_prim "BLAKE2B" nil
  | SHA256 => dummy_prim "SHA256" nil
  | SHA512 => dummy_prim "SHA512" nil
  | CHECK_SIGNATURE => dummy_prim "CHECK_SIGNATURE" nil
  | IF_ i1 i2 =>
    dummy_prim "IF" ((dummy_seq (michelson2micheline_ins i1))
                       ::(dummy_seq (michelson2micheline_ins i2))::nil)
  | IF_NONE i1 i2 =>
    dummy_prim "IF_NONE" ((dummy_seq (michelson2micheline_ins i1))
                            ::(dummy_seq (michelson2micheline_ins i2))::nil)
  | IF_LEFT i1 i2 =>
    dummy_prim "IF_LEFT" ((dummy_seq (michelson2micheline_ins i1))
                            ::(dummy_seq (michelson2micheline_ins i2))::nil)
  | IF_RIGHT i1 i2 =>
    dummy_prim "IF_RIGHT" ((dummy_seq (michelson2micheline_ins i1))
                             ::(dummy_seq (michelson2micheline_ins i2))::nil)
  | IF_CONS i1 i2 =>
    dummy_prim "IF_CONS" ((dummy_seq (michelson2micheline_ins i1))
                            ::(dummy_seq (michelson2micheline_ins i2))::nil)
  | LOOP i =>
    dummy_prim "LOOP" ((dummy_seq (michelson2micheline_ins i))::nil)
  | LOOP_LEFT i =>
    dummy_prim "LOOP_LEFT" ((dummy_seq (michelson2micheline_ins i))::nil)
  | ITER i =>
    dummy_prim "ITER" ((dummy_seq (michelson2micheline_ins i))::nil)
  | MAP i =>
    dummy_prim "MAP" ((dummy_seq (michelson2micheline_ins i))::nil)
  | PUSH t d =>
    let t' := (michelson2micheline_type t) in
    match d with
    | Instruction d' => dummy_prim "PUSH" (t'::(dummy_seq (michelson2micheline_ins d'))::nil)
    | _ => dummy_prim "PUSH" (t'::(michelson2micheline_data d)::nil)
    end
  | LAMBDA t1 t2 i =>
    dummy_prim "LAMBDA" ((michelson2micheline_type t1)
                           ::(michelson2micheline_type t2)
                           ::(dummy_seq (michelson2micheline_ins i))::nil)
  | DIG n => dummy_prim "DIG" ((dummy_mich (NUMBER (BinInt.Z.of_nat n)))::nil)
  | DUG n => dummy_prim "DUG" ((dummy_mich (NUMBER (BinInt.Z.of_nat n)))::nil)
  | DROP n => dummy_prim "DROP" ((dummy_mich (NUMBER (BinInt.Z.of_nat n)))::nil)
  | DIP n i => dummy_prim "DIP" ((dummy_mich (NUMBER (BinInt.Z.of_nat n))) :: (dummy_seq (michelson2micheline_ins i))::nil)
  | CHAIN_ID => dummy_prim "CHAIN_ID" nil
  end.

Definition eqb_ascii (a b : ascii) : Datatypes.bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Bool.eqb a0 b0 && Bool.eqb a1 b1 && Bool.eqb a2 b2 && Bool.eqb a3 b3
    && Bool.eqb a4 b4 && Bool.eqb a5 b5 && Bool.eqb a6 b6 && Bool.eqb a7 b7
 end.

Fixpoint eqb_string (s1 s2 : String.string) : Datatypes.bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String a1 s1, String a2 s2 => andb (eqb_ascii a1 a2) (eqb_string s1 s2)
  | _, _ => false
  end.

Definition michelson2micheline_instruction (i : instruction) : loc_micheline :=
  dummy_seq (michelson2micheline_ins i).
