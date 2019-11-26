Require Import Ascii String Bool.
Require List.
Require Import untyped_syntax micheline_syntax error location syntax_type.
Import List.ListNotations.

Open Scope string.

Definition dummy_loc : location := Mk_loc 0 0.
Definition dummy_mich (m : micheline) : loc_micheline :=
  Mk_loc_micheline (dummy_loc, dummy_loc, m).
Definition dummy_prim (p : String.string) (l : Datatypes.list loc_micheline) :=
  dummy_mich (PRIM (dummy_loc, dummy_loc, p) l).
Definition dummy_seq (m : loc_micheline) : loc_micheline :=
  match m with
  | Mk_loc_micheline (_, _, SEQ _) => m
  | _ => dummy_mich (SEQ [m])
  end.

Definition michelson2micheline_sctype (ct : simple_comparable_type) :=
  match ct with
  | string => dummy_prim "string" []
  | nat => dummy_prim "nat" []
  | int => dummy_prim "int" []
  | bytes => dummy_prim "bytes" []
  | bool => dummy_prim "bool" []
  | mutez => dummy_prim "mutez" []
  | key_hash => dummy_prim "key_hash" []
  | timestamp => dummy_prim "timestamp" []
  | address => dummy_prim "address" []
  end.

Fixpoint michelson2micheline_ctype (ct: comparable_type) : loc_micheline :=
  match ct with
  | Comparable_type_simple sct => michelson2micheline_sctype sct
  | Cpair sct ct =>
    dummy_prim "pair"
               [michelson2micheline_sctype sct; michelson2micheline_ctype ct]
  end.

Fixpoint michelson2micheline_type (t : type) : loc_micheline :=
  match t with
  | Comparable_type ct => michelson2micheline_sctype ct
  | key => dummy_prim "key" []
  | unit => dummy_prim "unit" []
  | signature => dummy_prim "signature" []
  | operation => dummy_prim "operation" []
  | option t' => dummy_prim "option" [michelson2micheline_type t']
  | list t' => dummy_prim "list" [michelson2micheline_type t']
  | set ct => dummy_prim "set" [michelson2micheline_ctype ct]
  | contract t' => dummy_prim "contract" [michelson2micheline_type t']
  | pair t1 t2 =>
    dummy_prim "pair" [michelson2micheline_type t1; michelson2micheline_type t2]
  | or t1 t2 =>
    dummy_prim "or" [michelson2micheline_type t1; michelson2micheline_type t2]
  | lambda t1 t2 =>
    dummy_prim "lambda" [michelson2micheline_type t1; michelson2micheline_type t2]
  | map ct1 t2 =>
    dummy_prim "map" [michelson2micheline_ctype ct1; michelson2micheline_type t2]
  | big_map ct1 t2 =>
    dummy_prim "big_map" [michelson2micheline_ctype ct1; michelson2micheline_type t2]
  | chain_id => dummy_prim "chain_id" []
  end.

Fixpoint michelson2micheline_data (d : concrete_data) : loc_micheline :=
  match d with
  | Int_constant z => dummy_mich (NUMBER z)
  | String_constant s => dummy_mich (STR s)
  | Bytes_constant b => dummy_mich (BYTES b)
  | Unit => dummy_prim "Unit" []
  | True_ => dummy_prim "True" []
  | False_ => dummy_prim "False" []
  | Pair a b =>
    dummy_prim "Pair" [michelson2micheline_data a; michelson2micheline_data b]
  | Left a => dummy_prim "Left" [michelson2micheline_data a]
  | Right a => dummy_prim "Right" [michelson2micheline_data a]
  | Some_ a => dummy_prim "Some" [michelson2micheline_data a]
  | None_ => dummy_prim "None" []
  | Elt a b =>
    dummy_prim "Elt" [michelson2micheline_data a; michelson2micheline_data b]
  | Concrete_seq s => dummy_mich (SEQ (List.map michelson2micheline_data s))
  | Instruction _ => dummy_prim "NOOP" [] (* Should never occur *)
  end.

Fixpoint michelson2micheline_ins (i : instruction) : loc_micheline :=
  match i with
  | NOOP => dummy_mich (SEQ [])
  | untyped_syntax.SEQ i1 i2 =>
    let m1 := michelson2micheline_ins i1 in
    let m2 := michelson2micheline_ins i2 in
    let ls1 :=
        match m1 with
        | Mk_loc_micheline (_, _, (SEQ ls1)) => ls1
        | _ => [m1]%list
        end in
    let ls2 :=
        match m2 with
        | Mk_loc_micheline (_, _, (SEQ ls2)) => ls2
        | _ => [m2]%list
        end in
    dummy_mich (SEQ (List.app ls1 ls2))
  | FAILWITH => dummy_prim "FAILWITH" []
  | EXEC => dummy_prim "EXEC" []
  | APPLY => dummy_prim "APPLY" []
  | DUP => dummy_prim "DUP" []
  | SWAP => dummy_prim "SWAP" []
  | UNIT => dummy_prim "UNIT" []
  | EQ => dummy_prim "EQ" []
  | NEQ => dummy_prim "NEQ" []
  | LT => dummy_prim "LT" []
  | GT => dummy_prim "GT" []
  | LE => dummy_prim "LE" []
  | GE => dummy_prim "GE" []
  | OR => dummy_prim "OR" []
  | AND => dummy_prim "AND" []
  | XOR => dummy_prim "XOR" []
  | NOT => dummy_prim "NOT" []
  | NEG => dummy_prim "NEG" []
  | ABS => dummy_prim "ABS" []
  | INT => dummy_prim "INT" []
  | ISNAT => dummy_prim "ISNAT" []
  | ADD => dummy_prim "ADD" []
  | SUB => dummy_prim "SUB" []
  | MUL => dummy_prim "MUL" []
  | EDIV => dummy_prim "EDIV" []
  | LSL => dummy_prim "LSL" []
  | LSR => dummy_prim "LSR" []
  | COMPARE => dummy_prim "COMPARE" []
  | CONCAT => dummy_prim "CONCAT" []
  | SIZE => dummy_prim "SIZE" []
  | SLICE => dummy_prim "SLICE" []
  | PAIR => dummy_prim "PAIR" []
  | CAR => dummy_prim "CAR" []
  | CDR => dummy_prim "CDR" []
  | GET => dummy_prim "GET" []
  | SOME => dummy_prim "SOME" []
  | NONE t => dummy_prim "NONE" [michelson2micheline_type t]
  | LEFT t => dummy_prim "LEFT" [michelson2micheline_type t]
  | RIGHT t => dummy_prim "RIGHT" [michelson2micheline_type t]
  | CONS => dummy_prim "CONS" nil
  | NIL t => dummy_prim "NIL" [michelson2micheline_type t]
  | EMPTY_SET ct => dummy_prim "EMPTY_SET" [michelson2micheline_ctype ct]
  | EMPTY_MAP ct t => dummy_prim "EMPTY_MAP"
                                 [michelson2micheline_ctype ct;
                                    michelson2micheline_type t]
  | EMPTY_BIG_MAP ct t => dummy_prim "EMPTY_BIG_MAP"
                                     [michelson2micheline_ctype ct;
                                        michelson2micheline_type t]
  | MEM => dummy_prim "MEM" nil
  | UPDATE => dummy_prim "UPDATE" nil
  | CREATE_CONTRACT t1 t2 i => dummy_prim "CREATE_CONTRACT"
                                          [michelson2micheline_type t1;
                                             michelson2micheline_type t2;
                                             dummy_seq (michelson2micheline_ins i)]
  | TRANSFER_TOKENS => dummy_prim "TRANSFER_TOKENS" []
  | SET_DELEGATE => dummy_prim "SET_DELEGATE" []
  | BALANCE => dummy_prim "BALANCE" []
  | ADDRESS => dummy_prim "ADDRESS" []
  | CONTRACT t => dummy_prim "CONTRACT" [michelson2micheline_type t]
  | SOURCE => dummy_prim "SOURCE" []
  | SENDER => dummy_prim "SENDER" []
  | SELF => dummy_prim "SELF" []
  | AMOUNT => dummy_prim "AMOUNT" []
  | IMPLICIT_ACCOUNT => dummy_prim "IMPLICIT_ACCOUNT" []
  | NOW => dummy_prim "NOW" []
  | PACK => dummy_prim "PACK" []
  | UNPACK t => dummy_prim "UNPACK" [michelson2micheline_type t]
  | HASH_KEY => dummy_prim "HASH_KEY" []
  | BLAKE2B => dummy_prim "BLAKE2B" []
  | SHA256 => dummy_prim "SHA256" []
  | SHA512 => dummy_prim "SHA512" []
  | CHECK_SIGNATURE => dummy_prim "CHECK_SIGNATURE" []
  | IF_ i1 i2 =>
    dummy_prim "IF" [dummy_seq (michelson2micheline_ins i1);
                       dummy_seq (michelson2micheline_ins i2)]
  | IF_NONE i1 i2 =>
    dummy_prim "IF_NONE" [dummy_seq (michelson2micheline_ins i1);
                            dummy_seq (michelson2micheline_ins i2)]
  | IF_LEFT i1 i2 =>
    dummy_prim "IF_LEFT" [dummy_seq (michelson2micheline_ins i1);
                            dummy_seq (michelson2micheline_ins i2)]
  | IF_CONS i1 i2 =>
    dummy_prim "IF_CONS" [dummy_seq (michelson2micheline_ins i1);
                            dummy_seq (michelson2micheline_ins i2)]
  | LOOP i =>
    dummy_prim "LOOP" [dummy_seq (michelson2micheline_ins i)]
  | LOOP_LEFT i =>
    dummy_prim "LOOP_LEFT" [dummy_seq (michelson2micheline_ins i)]
  | ITER i =>
    dummy_prim "ITER" [dummy_seq (michelson2micheline_ins i)]
  | MAP i =>
    dummy_prim "MAP" [dummy_seq (michelson2micheline_ins i)]
  | PUSH t d =>
    let t' := (michelson2micheline_type t) in
    match d with
    | Instruction d' =>
      dummy_prim "PUSH" [t'; dummy_seq (michelson2micheline_ins d')]
    | _ =>
      dummy_prim "PUSH" [t'; michelson2micheline_data d]
    end
  | LAMBDA t1 t2 i =>
    dummy_prim "LAMBDA" [ michelson2micheline_type t1;
                            michelson2micheline_type t2;
                            dummy_seq (michelson2micheline_ins i)]
  | DIG n => dummy_prim "DIG" [dummy_mich (NUMBER (BinInt.Z.of_nat n))]
  | DUG n => dummy_prim "DUG" [dummy_mich (NUMBER (BinInt.Z.of_nat n))]
  | DROP n => dummy_prim "DROP" [dummy_mich (NUMBER (BinInt.Z.of_nat n))]
  | DIP n i => dummy_prim "DIP" [dummy_mich (NUMBER (BinInt.Z.of_nat n));
                                   dummy_seq (michelson2micheline_ins i)]
  | CHAIN_ID => dummy_prim "CHAIN_ID" []
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
