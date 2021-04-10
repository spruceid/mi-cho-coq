Require Import Ascii String List.
Require Import untyped_syntax micheline_syntax error location.
Require Import syntax_type.
Require Import Lia.
Require micheline_lexer.
Require Coq.Program.Wf.
Import error.Notations.
Import untyped_syntax.notations.
Open Scope string.

Definition micheline2michelson_sctype (bem : loc_micheline) : M simple_comparable_type :=
  let 'Mk_loc_micheline ((b, e), m) := bem in
  match m with
  | PRIM (_, "string") _ nil => Return string
  | PRIM (_, "nat") _ nil => Return nat
  | PRIM (_, "int") _ nil => Return int
  | PRIM (_, "bytes") _ nil => Return bytes
  | PRIM (_, "bool") _ nil => Return bool
  | PRIM (_, "mutez") _ nil => Return mutez
  | PRIM (_, "key_hash") _ nil => Return key_hash
  | PRIM (_, "timestamp") _ nil => Return timestamp
  | PRIM (_, "address") _ nil => Return address
  | _ => Failed _ (Expansion b e)
  end.

Fixpoint micheline2michelson_ctype (bem : loc_micheline) : M comparable_type :=
  let 'Mk_loc_micheline ((b, e), m) := bem in
  match m with
  | PRIM (_, "pair") _ (a :: b :: nil) =>
    let! a := micheline2michelson_sctype a in
    let! b := micheline2michelson_ctype b in
    Return (Cpair a b)
  | _ =>
    let! a := micheline2michelson_sctype bem in
    Return (Comparable_type_simple a)
  end.

Definition extract_one_field_annot_from_list annots : M annot_o :=
  match annots with
  | nil => Return None
  | Mk_annot (_, _, annot) :: nil => Return (Some annot)
  | _ :: Mk_annot (b, e, _) :: _ => Failed _ (Expansion b e)
  end.

Definition is_field_annot annot :=
  match annot with
  | Mk_annot (_, _, EmptyString) => false
  | Mk_annot (_, _, String c _) => Ascii.eqb c "%"%char
  end.

Definition extract_one_field_annot (bem : loc_micheline) : M annot_o :=
  let 'Mk_loc_micheline ((b, e), m) := bem in
  match m with
  | PRIM p annots args =>
    let filtered_annots := List.filter is_field_annot annots in
    extract_one_field_annot_from_list filtered_annots
  | _ => Return None
  end.

Fixpoint micheline2michelson_atype
         (keep_annots : Datatypes.bool) (bem : loc_micheline) : M type :=
  try (let! ty := micheline2michelson_sctype bem in Return (Comparable_type ty))
      (let 'Mk_loc_micheline ((b, e), m) := bem in
       match m with
       | PRIM (_, "key") _ nil => Return key
       | PRIM (_, "unit") _ nil => Return unit
       | PRIM (_, "signature") _ nil => Return signature
       | PRIM (_, "operation") _ nil => Return operation
       | PRIM (_, "chain_id") _ nil => Return chain_id
       | PRIM (_, "option") _ (a :: nil) =>
        let! a := micheline2michelson_atype keep_annots a in
        Return (option a)
       | PRIM (_, "list") _ (a :: nil) =>
        let! a := micheline2michelson_atype keep_annots a in
        Return (list a)
       | PRIM (_, "contract") _ (a :: nil) =>
        let! a := micheline2michelson_atype keep_annots a in
        Return (contract a)
       | PRIM (_, "set") _ (a :: nil) =>
        let! a := micheline2michelson_ctype a in
        Return (set a)
       | PRIM (_, "pair") _ (a :: b :: nil) =>
        let! a := micheline2michelson_atype keep_annots a in
        let! b := micheline2michelson_atype keep_annots b in
        Return (pair a b)
       | PRIM (_, "or") _ (a :: b :: nil) =>
        let! an := extract_one_field_annot a in
        let! bn := extract_one_field_annot b in
        let an := if keep_annots then an else None in
        let bn := if keep_annots then bn else None in
        let! a := micheline2michelson_atype keep_annots a in
        let! b := micheline2michelson_atype keep_annots b in
        Return (or a an b bn)
       | PRIM (_, "lambda") _ (a :: b :: nil) =>
        let! a := micheline2michelson_atype keep_annots a in
        let! b := micheline2michelson_atype keep_annots b in
        Return (lambda a b)
       | PRIM (_, "map") _ (a :: b :: nil) =>
        let! a := micheline2michelson_ctype a in
        let! b := micheline2michelson_atype keep_annots b in
        Return (map a b)
       | PRIM (_, "big_map") _ (a :: b :: nil) =>
        let! a := micheline2michelson_ctype a in
        let! b := micheline2michelson_atype keep_annots b in
        Return (big_map a b)
       | _ => Failed _ (Expansion b e)
       end).

Definition micheline2michelson_type := micheline2michelson_atype false.

Fixpoint micheline2michelson_data (bem : loc_micheline) : M concrete_data :=
  let 'Mk_loc_micheline ((b, e), m) := bem in
  match m with
  | SEQ l =>
    let! l :=
      (fix micheline2michelson_data_list (l : Datatypes.list loc_micheline) : M (Datatypes.list concrete_data) :=
        match l with
        | nil => Return nil
        | m :: l =>
          let! d := micheline2michelson_data m in
          let! l := micheline2michelson_data_list l in
          Return (d :: l)
        end
      ) l in
    Return (Concrete_seq l)
  | STR s => Return (String_constant s)
  | NUMBER z => Return (Int_constant z)
  | BYTES s => Return (Bytes_constant s)
  | PRIM (_, "Unit") _ nil => Return Unit
  | PRIM (_, "True") _ nil => Return True_
  | PRIM (_, "False") _ nil => Return False_
  | PRIM (_, "Pair") _ (a :: b :: nil) =>
    let! a := micheline2michelson_data a in
    let! b := micheline2michelson_data b in
    Return (Pair a b)
  | PRIM (_, "Elt") _ (a :: b :: nil) =>
    let! a := micheline2michelson_data a in
    let! b := micheline2michelson_data b in
    Return (Elt a b)
  | PRIM (_, "Left") _ (a :: nil) =>
    let! a := micheline2michelson_data a in
    Return (Left a)
  | PRIM (_, "Right") _ (a :: nil) =>
    let! a := micheline2michelson_data a in
    Return (Right a)
  | PRIM (_, "Some") _ (a :: nil) =>
    let! a := micheline2michelson_data a in
    Return (Some_ a)
  | PRIM (_, "None") _ nil => Return None_
  | PRIM _ _ _ => Failed _ (Expansion b e)
  end.

Definition op_of_string (s : String.string) b e :=
  match s with
  | "EQ" => Return EQ
  | "NEQ" => Return NEQ
  | "LE" => Return LE
  | "GE" => Return GE
  | "LT" => Return LT
  | "GT" => Return GT
  | _ => Failed _ (Expansion b e)
  end.

Definition FAIL := Instruction_seq {UNIT; FAILWITH}.
Definition ASSERT := Instruction_seq {IF_ IF_bool {} {FAIL}}.

Definition IF_op_of_string (s : String.string) b e bt bf :=
  match s with
  | String "I" (String "F" s) =>
    let! op := op_of_string s b e in
    Return (op ;; IF_ IF_bool bt bf ;; NOOP)
  | _ => Failed _ (Expansion b e)
  end.

Definition ASSERT_op_of_string (s : String.string) b e :=
  match s with
  | String "A" (String "S" (String "S" (String "E" (String "R" (String "T" (String "_" s)))))) =>
    let! op := op_of_string s b e in
    Return (op ;; ASSERT ;; NOOP)
  | _ => Failed _ (Expansion b e)
  end.

Definition ASSERT_NONE := Instruction_seq {IF_NONE {} {FAIL}}.
Definition ASSERT_SOME := Instruction_seq {IF_NONE {FAIL} {}}.
Definition ASSERT_LEFT := Instruction_seq {IF_LEFT {} {FAIL}}.
Definition ASSERT_RIGHT := Instruction_seq {IF_LEFT {FAIL} {}}.

Fixpoint DUP_Sn n : instruction_seq :=
  match n with
  | 0 => {DUP}
  | S n => {DIP 1 (DUP_Sn n); SWAP}
  end.

Definition IF_SOME bt bf := Instruction_seq {IF_NONE bf bt}.
Definition IF_RIGHT bt bf := Instruction_seq {IF_LEFT bf bt}.
Definition IF_NIL bt bf := Instruction_seq {IF_CONS bf bt}.

Inductive cadr : Set :=
| Cadr_CAR : cadr -> cadr
| Cadr_CDR : cadr -> cadr
| Cadr_nil : cadr.

Fixpoint micheline2michelson_cadr (x : cadr) : instruction_seq :=
  match x with
  | Cadr_CAR x => CAR ;; micheline2michelson_cadr x
  | Cadr_CDR x => CDR ;; micheline2michelson_cadr x
  | Cadr_nil => {}
  end.

Fixpoint micheline2michelson_set_cadr (x : cadr) : instruction_seq :=
  match x with
  | Cadr_CAR Cadr_nil =>
    {CDR; SWAP; PAIR}
  | Cadr_CDR Cadr_nil =>
    {CAR; PAIR}
  | Cadr_CAR x =>
    {DUP; DIP 1 (CAR;; micheline2michelson_set_cadr x); CDR; SWAP; PAIR}
  | Cadr_CDR x =>
    {DUP; DIP 1 (CDR;; micheline2michelson_set_cadr x); CAR; PAIR}
  | Cadr_nil => {} (* Should not happen *)
  end.

Fixpoint micheline2michelson_map_cadr (x : cadr) (code : instruction_seq) : instruction_seq :=
  match x with
  | Cadr_CAR Cadr_nil =>
    {DUP; CDR; DIP 1 (CAR;; code); SWAP; PAIR}
  | Cadr_CDR Cadr_nil =>
    {DUP; CDR} ;;; code ;;; {SWAP; CAR; PAIR}
  | Cadr_CAR x =>
    {DUP; DIP 1 (CAR;; micheline2michelson_map_cadr x code); CDR; SWAP; PAIR}
  | Cadr_CDR x =>
    {DUP; DIP 1 (CDR;; micheline2michelson_map_cadr x code); CAR; PAIR}
  | Cadr_nil => code (* Should not happen *)
  end.

(* PAPAIR stuff *)

Inductive direction := Left | Right.

Inductive papair_token := token_P | token_A | token_I.

Fixpoint lex_papair (s : String.string) (fail : exception) :
  M (Datatypes.list papair_token) :=
  match s with
  | String "P" s =>
    let! l := lex_papair s fail in
    Return (cons token_P l)
  | String "A" s =>
    let! l := lex_papair s fail in
    Return (cons token_A l)
  | String "I" s =>
    let! l := lex_papair s fail in
    Return (cons token_I l)
  | "R"%string => Return nil
  | _ => Failed _ fail
  end.

Inductive papair_d : direction -> Set :=
| Papair_d_P d : papair_d Left -> papair_d Right -> papair_d d
| Papair_d_A : papair_d Left
| Papair_d_I : papair_d Right.

Fixpoint parse_papair (d : direction) (s : Datatypes.list papair_token) (fail : exception)
         (fuel : Datatypes.nat) (Hs : List.length s < fuel) {struct fuel} :
  M (papair_d d * sig (fun r : Datatypes.list papair_token => List.length r < List.length s)).
Proof.
  destruct fuel.
  - destruct (PeanoNat.Nat.nlt_0_r _ Hs).
  - destruct s as [|c s].
    + exact (Failed _ fail).
    + refine (match c, d
              return M (papair_d d *
                        (sig (fun r : Datatypes.list papair_token => List.length r < S (List.length s))))
              with
              | token_P, d1 =>
                let! (l, exist _ s1 Hl) := parse_papair Left s fail fuel _ in
                let! (r, exist _ s2 Hr) := parse_papair Right s1 fail fuel _ in
                Return (Papair_d_P d l r, exist _ s2 _)
              | token_A, Left => Return (Papair_d_A, exist _ s _)
              | token_I, Right => Return (Papair_d_I, exist _ s _)
              | _, _ => Failed _ fail
              end); simpl in *; lia.
Defined.

Inductive papair_left : Set :=
| Papair_l_P : papair_left -> papair_right -> papair_left
| Papair_l_A : papair_left
with papair_right : Set :=
| Papair_r_P : papair_left -> papair_right -> papair_right
| Papair_r_I : papair_right.

Fixpoint papair_l_of_papair_d (x : papair_d Left) : papair_left :=
  match x in papair_d Left return papair_left with
  | Papair_d_A => Papair_l_A
  | Papair_d_P Left l r =>
    Papair_l_P (papair_l_of_papair_d l) (papair_r_of_papair_d r)
  end
with
papair_r_of_papair_d (x : papair_d Right) : papair_right :=
  match x in papair_d Right return papair_right with
  | Papair_d_I => Papair_r_I
  | Papair_d_P Right l r =>
    Papair_r_P (papair_l_of_papair_d l) (papair_r_of_papair_d r)
  end.

Fixpoint size_l (x : papair_left) :=
  match x with
  | Papair_l_A => 0
  | Papair_l_P l r => 1 + size_l l + size_r r
  end
with
size_r (y : papair_right) :=
  match y with
  | Papair_r_I => 0
  | Papair_r_P l r => 1 + size_l l + size_r r
  end.

Inductive papair : Set :=
| Papair_PAIR : papair
| Papair_A : papair -> papair
| Papair_I : papair -> papair
| Papair_P : papair -> papair -> papair.

Program Fixpoint papair_of_l_r (x : papair_left) (y : papair_right) {measure (size_l x + size_r y)}: papair :=
  match x, y with
  | Papair_l_A, Papair_r_I => Papair_PAIR
  | Papair_l_A, Papair_r_P l r =>
    Papair_A (papair_of_l_r l r)
  | Papair_l_P l r, Papair_r_I =>
    Papair_I (papair_of_l_r l r)
  | Papair_l_P xl xr, Papair_r_P yl yr =>
    Papair_P (papair_of_l_r xl xr) (papair_of_l_r yl yr)
  end.
Next Obligation.
  simpl.
  lia.
Defined.
Next Obligation.
  simpl.
  lia.
Defined.
Next Obligation.
  simpl.
  lia.
Defined.

Fixpoint micheline2michelson_papair (x : papair) : instruction_seq :=
  match x with
  | Papair_PAIR => {PAIR}
  | Papair_A y => {DIP 1 (micheline2michelson_papair y); PAIR}
  | Papair_I x => micheline2michelson_papair x ;;; {PAIR}
  | Papair_P x y => micheline2michelson_papair x ;;;
                    {DIP 1 (micheline2michelson_papair y); PAIR}
  end.

Fixpoint micheline2michelson_unpapair (x : papair) : instruction :=
  match x with
  | Papair_PAIR => UNPAIR
  | Papair_A y => Instruction_seq {UNPAIR; DIP 1 { micheline2michelson_unpapair y }}
  | Papair_I x => Instruction_seq {UNPAIR; micheline2michelson_unpapair x}
  | Papair_P x y => Instruction_seq {UNPAIR;
                    DIP 1 {micheline2michelson_unpapair y};
                    micheline2michelson_unpapair x}
  end.

Definition parse_papair_full (s : String.string) (fail : exception) :
  M instruction_seq :=
  let! toks : Datatypes.list papair_token := lex_papair s fail in
  let! (l, exist _ toks2 Htoks2) := parse_papair Left toks fail (S (List.length toks)) ltac:(simpl; lia) in
  let! (r, exist _ toks3 Htoks3) := parse_papair Right toks2 fail (S (List.length toks2)) ltac:(simpl; lia) in
  match toks3 with
  | nil => Return
                  (micheline2michelson_papair
                      (papair_of_l_r
                        (papair_l_of_papair_d l)
                        (papair_r_of_papair_d r)))
  | _ => Failed _ fail
  end.

Definition parse_unpapair_full (s : String.string) (fail : exception)
  : M instruction :=
  let! toks : Datatypes.list papair_token := lex_papair s fail in
  let! (l, exist _ toks2 Htoks2) := parse_papair Left toks fail (S (List.length toks)) ltac:(simpl; lia) in
  let! (r, exist _ toks3 Htoks3) := parse_papair Right toks2 fail (S (List.length toks2)) ltac:(simpl; lia) in
  match toks3 with
  | nil => Return
                  (micheline2michelson_unpapair
                      (papair_of_l_r
                        (papair_l_of_papair_d l)
                        (papair_r_of_papair_d r)))
  | _ => Failed _ fail
  end.


Definition return_instruction (i : instruction) : M instruction_seq :=
  Return {i}%michelson_untyped.

Definition return_opcode (op : opcode) : M instruction_seq :=
  return_instruction (instruction_opcode op).

Definition return_macro (i : instruction_seq) : M instruction_seq :=
  return_instruction (Instruction_seq i).

Fixpoint micheline2michelson_instruction (bem : loc_micheline) : M instruction_seq :=
  let 'Mk_loc_micheline ((b, e), m) := bem in
  match m with
  | SEQ l =>
    (fix micheline2michelson_instr_seq (l : Datatypes.list loc_micheline) : M instruction_seq :=
       match l with
       | nil => Return NOOP
       | i1 :: i2 =>
        let! i1 := micheline2michelson_instruction i1 in
        let! i2 := micheline2michelson_instr_seq i2 in
        Return (i1 ;;; i2)
       end) l
  | PRIM (_, "FAILWITH") _ nil => return_instruction FAILWITH
  | PRIM (_, "EXEC") _ nil => return_instruction EXEC
  | PRIM (_, "APPLY") _ nil => return_opcode APPLY
  | PRIM (_, "DROP") _ nil => return_opcode (DROP 1)
  | PRIM (_, "DROP") _ (Mk_loc_micheline (_, NUMBER n) :: nil) =>
    return_opcode (DROP (BinInt.Z.to_nat n))
  | PRIM (_, "DUP") _ nil => return_opcode DUP
  | PRIM (_, "SWAP") _ nil => return_opcode SWAP
  | PRIM (_, "UNIT") _ nil => return_opcode UNIT
  | PRIM (_, "EQ") _ nil => return_opcode EQ
  | PRIM (_, "NEQ") _ nil => return_opcode NEQ
  | PRIM (_, "LT") _ nil => return_opcode LT
  | PRIM (_, "GT") _ nil => return_opcode GT
  | PRIM (_, "LE") _ nil => return_opcode LE
  | PRIM (_, "GE") _ nil => return_opcode GE
  | PRIM (_, "OR") _ nil => return_opcode OR
  | PRIM (_, "AND") _ nil => return_opcode AND
  | PRIM (_, "XOR") _ nil => return_opcode XOR
  | PRIM (_, "NOT") _ nil => return_opcode NOT
  | PRIM (_, "NEG") _ nil => return_opcode NEG
  | PRIM (_, "ABS") _ nil => return_opcode ABS
  | PRIM (_, "ISNAT") _ nil => return_opcode ISNAT
  | PRIM (_, "INT") _ nil => return_opcode INT
  | PRIM (_, "ADD") _ nil => return_opcode ADD
  | PRIM (_, "SUB") _ nil => return_opcode SUB
  | PRIM (_, "MUL") _ nil => return_opcode MUL
  | PRIM (_, "EDIV") _ nil => return_opcode EDIV
  | PRIM (_, "LSL") _ nil => return_opcode LSL
  | PRIM (_, "LSR") _ nil => return_opcode LSR
  | PRIM (_, "COMPARE") _ nil => return_opcode COMPARE
  | PRIM (_, "CONCAT") _ nil => return_opcode CONCAT
  | PRIM (_, "SIZE") _ nil => return_opcode SIZE
  | PRIM (_, "SLICE") _ nil => return_opcode SLICE
  | PRIM (_, "PAIR") _ nil => return_opcode PAIR
  | PRIM (_, "CAR") _ nil => return_opcode CAR
  | PRIM (_, "CDR") _ nil => return_opcode CDR
  | PRIM (_, "GET") _ nil => return_opcode GET
  | PRIM (_, "SOME") _ nil => return_opcode SOME
  | PRIM (_, "NONE") _ (ty :: nil) =>
    let! ty := micheline2michelson_type ty in
    return_opcode (NONE ty)
  | PRIM (_, "LEFT") _ (ty :: nil) =>
    let! ty := micheline2michelson_type ty in
    return_opcode (LEFT ty)
  | PRIM (_, "RIGHT") _ (ty :: nil) =>
    let! ty := micheline2michelson_type ty in
    return_opcode (RIGHT ty)
  | PRIM (_, "CONS") _ nil => return_opcode CONS
  | PRIM (_, "NIL") _ (ty :: nil) =>
    let! ty := micheline2michelson_type ty in
    return_opcode (NIL ty)
  | PRIM (_, "TRANSFER_TOKENS") _ nil =>
    return_opcode TRANSFER_TOKENS
  | PRIM (_, "SET_DELEGATE") _ nil => return_opcode SET_DELEGATE
  | PRIM (_, "BALANCE") _ nil => return_opcode BALANCE
  | PRIM (_, "ADDRESS") _ nil => return_opcode ADDRESS
  | PRIM (_, "CONTRACT") _ (ty :: nil) =>
    let! an := extract_one_field_annot bem in
    let! ty := micheline2michelson_type ty in
    return_opcode (CONTRACT an ty)
  | PRIM (_, "SOURCE") _ nil => return_opcode SOURCE
  | PRIM (_, "SENDER") _ nil => return_opcode SENDER
  | PRIM (_, "SELF") _ nil =>
    let! an := extract_one_field_annot bem in
    return_instruction (SELF an)
  | PRIM (_, "AMOUNT") _ nil => return_opcode AMOUNT
  | PRIM (_, "IMPLICIT_ACCOUNT") _ nil => return_opcode IMPLICIT_ACCOUNT
  | PRIM (_, "NOW") _ nil => return_opcode NOW
  | PRIM (_, "PACK") _ nil => return_opcode PACK
  | PRIM (_, "UNPACK") _ (ty :: nil) =>
    let! ty := micheline2michelson_type ty in
    return_opcode (UNPACK ty)
  | PRIM (_, "HASH_KEY") _ nil => return_opcode HASH_KEY
  | PRIM (_, "BLAKE2B") _ nil => return_opcode BLAKE2B
  | PRIM (_, "SHA256") _ nil => return_opcode SHA256
  | PRIM (_, "SHA512") _ nil => return_opcode SHA512
  | PRIM (_, "CHECK_SIGNATURE") _ nil =>
    return_opcode CHECK_SIGNATURE
  | PRIM (_, "MEM") _ nil => return_opcode MEM
  | PRIM (_, "UPDATE") _ nil => return_opcode UPDATE
  | PRIM (_, "CHAIN_ID") _ nil => return_opcode CHAIN_ID
  | PRIM (_, "LOOP") _ (i :: nil) =>
    let! i := micheline2michelson_instruction i in
    return_instruction (LOOP i)
  | PRIM (_, "LOOP_LEFT") _ (i :: nil) =>
    let! i := micheline2michelson_instruction i in
    return_instruction (LOOP_LEFT i)
  | PRIM (_, "DIP") _ (i :: nil) =>
    let! i := micheline2michelson_instruction i in
    return_instruction (DIP 1 i)
  | PRIM (_, "DIP") _ (Mk_loc_micheline (_, NUMBER n) :: i :: nil) =>
    let! i := micheline2michelson_instruction i in
    return_instruction (DIP (BinInt.Z.to_nat n) i)
  | PRIM (_, "DIG") _ (Mk_loc_micheline (_, NUMBER n) :: nil) =>
    return_opcode (DIG (BinInt.Z.to_nat n))
  | PRIM (_, "DUG") _ (Mk_loc_micheline (_, NUMBER n) :: nil) =>
    return_opcode (DUG (BinInt.Z.to_nat n))
  | PRIM (_, "ITER") _ (i :: nil) =>
    let! i := micheline2michelson_instruction i in
    return_instruction (ITER i)
  | PRIM (_, "MAP") _ (i :: nil) =>
    let! i := micheline2michelson_instruction i in
    return_instruction (MAP i)
  | PRIM (_, "CREATE_CONTRACT") _
               (Mk_loc_micheline
                  (_, SEQ
                        ((Mk_loc_micheline (_, PRIM (_, "storage") _ (storage_ty :: nil))) ::
                        (Mk_loc_micheline (_, PRIM (_, "parameter") _ (params_ty :: nil)) as param) ::
                        (Mk_loc_micheline (_, PRIM (_, "code") _ (i :: nil))) :: nil)) ::
                  nil) =>
    let! an := extract_one_field_annot param in
    let! i := micheline2michelson_instruction i in
    let! sty := micheline2michelson_type storage_ty in
    let! pty := micheline2michelson_type params_ty in
    return_instruction (CREATE_CONTRACT sty pty an i)
  | PRIM (_, "CREATE_CONTRACT") _
               (Mk_loc_micheline
                  (_, SEQ
                        ((Mk_loc_micheline (_, PRIM (_, "parameter") _ (params_ty :: nil)) as param) ::
                        (Mk_loc_micheline (_, PRIM (_, "storage") _ (storage_ty :: nil))) ::
                        (Mk_loc_micheline (_, PRIM (_, "code") _ (i :: nil))) :: nil)) ::
                  nil) =>
    let! an := extract_one_field_annot param in
    let! i := micheline2michelson_instruction i in
    let! sty := micheline2michelson_type storage_ty in
    let! pty := micheline2michelson_type params_ty in
    return_instruction (CREATE_CONTRACT sty pty an i)
  | PRIM (_, "EMPTY_SET") _ (cty :: nil) =>
    let! cty := micheline2michelson_ctype cty in
    return_opcode (EMPTY_SET cty)
  | PRIM (_, "EMPTY_MAP") _ (kty :: vty :: nil) =>
    let! kty := micheline2michelson_ctype kty in
    let! vty := micheline2michelson_type vty in
    return_opcode (EMPTY_MAP kty vty)
  | PRIM (_, "EMPTY_BIG_MAP") _ (kty :: vty :: nil) =>
    let! kty := micheline2michelson_ctype kty in
    let! vty := micheline2michelson_type vty in
    return_opcode (EMPTY_BIG_MAP kty vty)
  | PRIM (_, "IF") _ (i1 :: i2 :: nil) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    return_instruction (IF_ IF_bool i1 i2)
  | PRIM (_, "IF_NONE") _ (i1 :: i2 :: nil) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    return_instruction (IF_NONE i1 i2)
  | PRIM (_, "IF_LEFT") _ (i1 :: i2 :: nil) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    return_instruction (IF_LEFT i1 i2)
  | PRIM (_, "IF_CONS") _ (i1 :: i2 :: nil) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    return_instruction (IF_CONS i1 i2)
  | PRIM (_, "LAMBDA") _ (a :: b :: i :: nil) =>
    let! a := micheline2michelson_type a in
    let! b := micheline2michelson_type b in
    let! i := micheline2michelson_instruction i in
    return_instruction (LAMBDA a b i)
  | PRIM (_, "PUSH") _ (a :: v :: nil) =>
    let! a := micheline2michelson_type a in
    let! v :=
      match a with
      | lambda _ _ =>
        let! i := micheline2michelson_instruction v in
        Return (Instruction i)
      | _ => micheline2michelson_data v
      end in
    return_instruction (PUSH a v)

  | PRIM (_, "RENAME") _ _ => Return NOOP
  | PRIM (_, "CAST") _ _ => Return NOOP


  (* Macros *)
  | PRIM (_, "FAIL") _ nil => return_instruction FAIL
  | PRIM (_, "ASSERT") _ nil => return_instruction ASSERT
  | PRIM (_, "ASSERT_NONE") _ nil => return_instruction ASSERT_NONE
  | PRIM (_, "ASSERT_SOME") _ nil => return_instruction ASSERT_SOME
  | PRIM (_, "ASSERT_LEFT") _ nil => return_instruction ASSERT_LEFT
  | PRIM (_, "ASSERT_RIGHT") _ nil => return_instruction ASSERT_RIGHT

  | PRIM (_, "IF_SOME") _ (i1 :: i2 :: nil) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    return_instruction (IF_SOME i1 i2)
  | PRIM (_, "IF_RIGHT") _ (i1 :: i2 :: nil) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    return_instruction (IF_RIGHT i1 i2)
  | PRIM (_, "IF_NIL") _ (i1 :: i2 :: nil) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    return_instruction (IF_NIL i1 i2)

  | PRIM (_, String "C" (String "M" (String "P" s))) _ nil =>
    let! op := op_of_string s b e in
    return_macro {COMPARE; op}
  | PRIM (_,
       String "I" (String "F" (String "C" (String "M" (String "P" s))))) _ (i1 :: i2 :: nil) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    let! op := op_of_string s b e in
    return_macro {COMPARE; op; IF_ IF_bool i1 i2}
  | PRIM (_,
       String "I" (String "F" s)) _ (i1 :: i2 :: nil) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    let! op := op_of_string s b e in
    return_macro {op; IF_ IF_bool i1 i2}
  | PRIM (_,
      String "A" (String "S" (String "S" (String "E" (String "R" (String "T"
      (String "_" (String "C" (String "M" (String "P" s)))))))))) _ nil =>
    let! op := op_of_string s b e in
    return_macro {COMPARE; op; IF_ IF_bool {} {FAIL}}

  | PRIM (_, String "A" (String "S" (String "S" (String "E" (String "R" (String "T"
      (String "_" s))))))) _ nil =>
    let! op := op_of_string s b e in
    return_macro {op; IF_ IF_bool {} {FAIL}}

  | PRIM (_, "CR") _ nil =>
    Failed _ (Expansion_prim b e "CR")
  | PRIM (_, "SET_CR") _ nil =>
    Failed _ (Expansion_prim b e "SET_CR")
  | PRIM (_, "MAP_CR") _ nil =>
    Failed _ (Expansion_prim b e "MAP_CR")

  (* CADAAR *)
  | PRIM (_, String "C" s) _ nil =>
    let prim := String "C" s in
    let get_cadr := fix get_cadr s :=
                      match s with
                      | "R" => Return Cadr_nil
                      | String "A" s =>
                        let! x := get_cadr s in
                        Return (Cadr_CAR x)
                      | String "D" s =>
                        let! x := get_cadr s in
                        Return (Cadr_CDR x)
                      | _ => Failed _ (Expansion_prim b e prim)
                      end in
    let! x := get_cadr s in
    return_macro (micheline2michelson_cadr x)

  | PRIM (_, String "S" (String "E"(String "T"(String "_"(String "C" s)))))
         _ nil =>
    let prim := String "S" (String "E"(String "T"(String "_"(String "C" s)))) in
    let get_cadr := fix get_cadr s :=
                      match s with
                      | "R" => Return Cadr_nil
                      | String "A" s =>
                        let! x := get_cadr s in
                        Return (Cadr_CAR x)
                      | String "D" s =>
                        let! x := get_cadr s in
                        Return (Cadr_CDR x)
                      | _ => Failed _ (Expansion_prim b e prim)
                      end in
    let! x := get_cadr s in
    return_macro (micheline2michelson_set_cadr x)

  | PRIM (_, String "M" (String "A"(String "P"(String "_"(String "C" s)))))
         _ (a :: nil) =>
    let prim := String "M" (String "A"(String "P"(String "_"(String "C" s)))) in
    let get_cadr := fix get_cadr s :=
                      match s with
                      | "R" => Return Cadr_nil
                      | String "A" s =>
                        let! x := get_cadr s in
                        Return (Cadr_CAR x)
                      | String "D" s =>
                        let! x := get_cadr s in
                        Return (Cadr_CDR x)
                      | _ => Failed _ (Expansion_prim b e prim)
                      end in
    let! x := get_cadr s in
    let! code := micheline2michelson_instruction a in
    return_macro (micheline2michelson_map_cadr x code)

  | PRIM (_, String "D" (String "I" s)) _ (a :: nil) =>
    let is_diip := fix is_diip s :=
                     match s with
                     | "P" => true
                     | String "I" s => is_diip s
                     | _ => false
                     end in
    if is_diip s then
      let! a := micheline2michelson_instruction a in
      return_instruction (DIP (String.length s) a)
    else Failed _ (Expansion_prim b e (String "D" (String "I" s)))
  | PRIM (_, "DUP") _ (Mk_loc_micheline (_, NUMBER n) :: nil) =>
    match BinInt.Z.to_nat n with
    | S n => return_macro (DUP_Sn n)
    | O => Failed _ (Expansion b e)
    end
  | PRIM (_, String "D" (String "U" (String "U" s))) _ nil =>
    let is_duup := fix is_duup s :=
                     match s with
                     | "P" => true
                     | String "U" s => is_duup s
                     | _ => false
                     end in
    if is_duup s then return_macro (DUP_Sn (String.length s))
    else Failed _ (Expansion_prim b e (String "D" (String "U" (String "U" s))))

  (* PAPAIR *)
  | PRIM (_, String "P" s) _ nil =>
    let prim := String "P" s in
    let fail := Expansion_prim b e prim in
    let! full := parse_papair_full s fail in
    return_macro full

  (* UNPAPAIR *)
  | PRIM (_, String "U" (String "N" (String "P" s))) _ nil =>
    let prim := String "U" (String "N" (String "P" s)) in
    let fail := Expansion_prim b e prim in
    let! full := parse_unpapair_full s fail in
    return_instruction full

  (* Unknown case *)
  | PRIM (_, s) _ _ => Failed _ (Expansion_prim b e s)
  | _ => Failed _ (Expansion b e)
  end.

Record untyped_michelson_file :=
  Mk_untyped_michelson_file
    { root_annotation : annot_o;
      parameter : type;
      storage : type;
      code : instruction_seq }.

Record untyped_michelson_file_opt :=
  Mk_untyped_michelson_file_opt
    { root_annot : annot_o;
      parameter_opt : Datatypes.option type;
      storage_opt : Datatypes.option type;
      code_opt : Datatypes.option instruction_seq }.

Definition read_parameter (ty : type) (root_annot : annot_o)
           (f : untyped_michelson_file_opt) :=
  match f.(parameter_opt) with
  | None => Return {| root_annot := root_annot;
                      parameter_opt := Some ty;
                      storage_opt := f.(storage_opt);
                      code_opt := f.(code_opt) |}
  | Some _ => Failed _ Parsing
  end.

Definition read_storage (ty : type) (f : untyped_michelson_file_opt) :=
  match f.(storage_opt) with
  | None => Return {| root_annot := f.(root_annot);
                      parameter_opt := f.(parameter_opt);
                      storage_opt := Some ty;
                      code_opt := f.(code_opt) |}
  | Some _ => Failed _ Parsing
  end.

Definition read_code (c : instruction_seq) (f : untyped_michelson_file_opt) :=
  match f.(code_opt) with
  | None => Return {| root_annot := f.(root_annot);
                      parameter_opt := f.(parameter_opt);
                      storage_opt := f.(storage_opt);
                      code_opt := Some c |}
  | Some _ => Failed _ Parsing
  end.

Definition micheline2michelson_file (m : Datatypes.list loc_micheline) : M untyped_michelson_file :=
  let l :=
      match m with
      | Mk_loc_micheline (_, SEQ l) :: nil => l
      | l => l
      end
  in
  let! a :=
    error.list_fold_left
      (fun (a : untyped_michelson_file_opt) (lm : loc_micheline) =>
        let 'Mk_loc_micheline (_, _, m) := lm in
        match m with
        | PRIM (_, _, "parameter") _ (cons param nil) =>
          let! an := extract_one_field_annot lm in
          let! ty := micheline2michelson_atype true param in
          read_parameter ty an a
        | PRIM (_, _, "storage") _ (cons storage nil) =>
          let! ty := micheline2michelson_type storage in
          read_storage ty a
        | PRIM (_, _, "code") _ (cons code nil) =>
          let! c := micheline2michelson_instruction code in
          read_code c a
        | _ => Failed _ Parsing
        end)
      l
      {| root_annot := None;
         parameter_opt := None;
         storage_opt := None;
         code_opt := None |} in
    match a.(parameter_opt), a.(storage_opt), a.(code_opt) with
    | Some param, Some storage, Some code =>
      Return {| root_annotation := a.(root_annot);
                parameter := param;
                storage := storage;
                code := code |}
    | _, _, _ => Failed _ Parsing
    end.
