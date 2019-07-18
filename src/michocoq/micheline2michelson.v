Require Import String List.
Require Import untyped_syntax micheline_syntax error location.

Open Scope string.

Definition micheline2michelson_sctype (bem : loc_micheline) : M syntax.simple_comparable_type :=
  let 'Mk_loc_micheline ((b, e), m) := bem in
  match m with
  | PRIM (_, "string") nil => Return _ syntax.string
  | PRIM (_, "nat") nil => Return _ syntax.nat
  | PRIM (_, "int") nil => Return _ syntax.int
  | PRIM (_, "bytes") nil => Return _ syntax.bytes
  | PRIM (_, "bool") nil => Return _ syntax.bool
  | PRIM (_, "mutez") nil => Return _ syntax.mutez
  | PRIM (_, "key_hash") nil => Return _ syntax.key_hash
  | PRIM (_, "timestamp") nil => Return _ syntax.timestamp
  | PRIM (_, "address") nil => Return _ syntax.address
  | _ => Failed _ (Expansion b e)
  end.

Fixpoint micheline2michelson_ctype (bem : loc_micheline) : M syntax.comparable_type :=
  let 'Mk_loc_micheline ((b, e), m) := bem in
  match m with
  | PRIM (_, "pair") (a :: b :: nil) =>
    bind (fun a =>
            bind (fun b => Return _ (syntax.Cpair a b))
              (micheline2michelson_ctype b)
         )
         (micheline2michelson_sctype a)
  | _ =>
    bind (fun a => Return _ (syntax.Comparable_type_simple a))
         (micheline2michelson_sctype bem)
  end.

Fixpoint micheline2michelson_type (bem : loc_micheline) : M syntax.type :=
  try (bind (fun ty => Return _ (syntax.Comparable_type ty)) (micheline2michelson_sctype bem))
      (match bem with
       | Mk_loc_micheline (_, PRIM (_, "key") nil) => Return _ syntax.key
       | Mk_loc_micheline (_, PRIM (_, "unit") nil) => Return _ syntax.unit
       | Mk_loc_micheline (_, PRIM (_, "signature") nil) => Return _ syntax.signature
       | Mk_loc_micheline (_, PRIM (_, "operation") nil) => Return _ syntax.operation
       | Mk_loc_micheline (_, PRIM (_, "option") (a :: nil)) =>
         bind (fun a => Return _ (syntax.option a))
              (micheline2michelson_type a)
       | Mk_loc_micheline (_, PRIM (_, "list") (a :: nil)) =>
         bind (fun a => Return _ (syntax.list a))
              (micheline2michelson_type a)
       | Mk_loc_micheline (_, PRIM (_, "contract") (a :: nil)) =>
         bind (fun a => Return _ (syntax.contract a))
              (micheline2michelson_type a)
       | Mk_loc_micheline (_, PRIM (_, "set") (a :: nil)) =>
         bind (fun a => Return _ (syntax.set a))
              (micheline2michelson_ctype a)
       | Mk_loc_micheline (_, PRIM (_, "pair") (a :: b :: nil)) =>
         bind (fun a =>
                 bind (fun b => Return _ (syntax.pair a b))
                      (micheline2michelson_type b))
              (micheline2michelson_type a)
       | Mk_loc_micheline (_, PRIM (_, "or") (a :: b :: nil)) =>
         bind (fun a =>
                 bind (fun b => Return _ (syntax.or a b))
                      (micheline2michelson_type b))
              (micheline2michelson_type a)
       | Mk_loc_micheline (_, PRIM (_, "lambda") (a :: b :: nil)) =>
         bind (fun a =>
                 bind (fun b => Return _ (syntax.lambda a b))
                      (micheline2michelson_type b))
              (micheline2michelson_type a)
       | Mk_loc_micheline (_, PRIM (_, "map") (a :: b :: nil)) =>
         bind (fun a =>
                 bind (fun b => Return _ (syntax.map a b))
                      (micheline2michelson_type b))
              (micheline2michelson_ctype a)
       | Mk_loc_micheline (_, PRIM (_, "big_map") (a :: b :: nil)) =>
         bind (fun a =>
                 bind (fun b => Return _ (syntax.big_map a b))
                      (micheline2michelson_type b))
              (micheline2michelson_ctype a)
       | Mk_loc_micheline ((b, e), _) => Failed _ (Expansion b e)
       end).

Fixpoint micheline2michelson_data (bem : loc_micheline) : M concrete_data :=
  match bem with
  | Mk_loc_micheline (_, SEQ l) =>
    bind (fun l => Return _ (Concrete_seq l))
         ((fix micheline2michelson_data_list (l : Datatypes.list loc_micheline) : M (Datatypes.list concrete_data) :=
       match l with
       | nil => Return _ nil
       | m :: l =>
         bind (fun d =>
                 bind (fun l => Return _ (d :: l))
                      (micheline2michelson_data_list l))
              (micheline2michelson_data m)
       end) l)
  | Mk_loc_micheline (_, STR s) => Return _ (String_constant s)
  | Mk_loc_micheline (_, NUMBER z) => Return _ (Int_constant z)
  | Mk_loc_micheline (_, BYTES s) => Return _ (Bytes_constant s)
  | Mk_loc_micheline (_, PRIM (_, "Unit") nil) => Return _ Unit
  | Mk_loc_micheline (_, PRIM (_, "True") nil) => Return _ True_
  | Mk_loc_micheline (_, PRIM (_, "False") nil) => Return _ False_
  | Mk_loc_micheline (_, PRIM (_, "Pair") (a :: b :: nil)) =>
    bind (fun a =>
            bind (fun b => Return _ (Pair a b))
                 (micheline2michelson_data b))
         (micheline2michelson_data a)
  | Mk_loc_micheline (_, PRIM (_, "Elt") (a :: b :: nil)) =>
    bind (fun a =>
            bind (fun b => Return _ (Elt a b))
                 (micheline2michelson_data b))
         (micheline2michelson_data a)
  | Mk_loc_micheline (_, PRIM (_, "Left") (a :: nil)) =>
    bind (fun a => Return _ (Left a)) (micheline2michelson_data a)
  | Mk_loc_micheline (_, PRIM (_, "Right") (a :: nil)) =>
    bind (fun a => Return _ (Right a)) (micheline2michelson_data a)
  | Mk_loc_micheline (_, PRIM (_, "Some") (a :: nil)) =>
    bind (fun a => Return _ (Some_ a)) (micheline2michelson_data a)
  | Mk_loc_micheline (_, PRIM (_, "None") nil) => Return _ None_
  | Mk_loc_micheline ((b, e), PRIM s _) => Failed _ (Expansion b e)
  end.

Fixpoint micheline2michelson_instruction (m : loc_micheline) : M instruction :=
  match m with
  | Mk_loc_micheline (_, SEQ l) =>
    (fix micheline2michelson_instr_seq (l : Datatypes.list loc_micheline) : M instruction :=
       match l with
       | nil => Return _ NOOP
       | i1 :: l =>
         bind (fun i1 =>
                 bind (fun i2 => Return _ (untyped_syntax.SEQ i1 i2))
                      (micheline2michelson_instr_seq l))
              (micheline2michelson_instruction i1)
       end) l
  | Mk_loc_micheline (_, PRIM (_, "FAILWITH") nil) => Return _ FAILWITH
  | Mk_loc_micheline (_, PRIM (_, "EXEC") nil) => Return _ EXEC
  | Mk_loc_micheline (_, PRIM (_, "DROP") nil) => Return _ (DROP 1)
  | Mk_loc_micheline (_, PRIM (_, "DROP")
                              (Mk_loc_micheline (_, NUMBER n) :: nil)) =>
    Return _ (DROP (BinInt.Z.to_nat n))
  | Mk_loc_micheline (_, PRIM (_, "DUP") nil) => Return _ DUP
  | Mk_loc_micheline (_, PRIM (_, "SWAP") nil) => Return _ SWAP
  | Mk_loc_micheline (_, PRIM (_, "UNIT") nil) => Return _ UNIT
  | Mk_loc_micheline (_, PRIM (_, "EQ") nil) => Return _ EQ
  | Mk_loc_micheline (_, PRIM (_, "NEQ") nil) => Return _ NEQ
  | Mk_loc_micheline (_, PRIM (_, "LT") nil) => Return _ LT
  | Mk_loc_micheline (_, PRIM (_, "GT") nil) => Return _ GT
  | Mk_loc_micheline (_, PRIM (_, "LE") nil) => Return _ LE
  | Mk_loc_micheline (_, PRIM (_, "GE") nil) => Return _ GE
  | Mk_loc_micheline (_, PRIM (_, "OR") nil) => Return _ OR
  | Mk_loc_micheline (_, PRIM (_, "AND") nil) => Return _ AND
  | Mk_loc_micheline (_, PRIM (_, "XOR") nil) => Return _ XOR
  | Mk_loc_micheline (_, PRIM (_, "NOT") nil) => Return _ NOT
  | Mk_loc_micheline (_, PRIM (_, "NEG") nil) => Return _ NEG
  | Mk_loc_micheline (_, PRIM (_, "ABS") nil) => Return _ ABS
  | Mk_loc_micheline (_, PRIM (_, "ADD") nil) => Return _ ADD
  | Mk_loc_micheline (_, PRIM (_, "SUB") nil) => Return _ SUB
  | Mk_loc_micheline (_, PRIM (_, "MUL") nil) => Return _ MUL
  | Mk_loc_micheline (_, PRIM (_, "EDIV") nil) => Return _ EDIV
  | Mk_loc_micheline (_, PRIM (_, "LSL") nil) => Return _ LSL
  | Mk_loc_micheline (_, PRIM (_, "LSR") nil) => Return _ LSR
  | Mk_loc_micheline (_, PRIM (_, "COMPARE") nil) => Return _ COMPARE
  | Mk_loc_micheline (_, PRIM (_, "CONCAT") nil) => Return _ CONCAT
  | Mk_loc_micheline (_, PRIM (_, "SIZE") nil) => Return _ SIZE
  | Mk_loc_micheline (_, PRIM (_, "SLICE") nil) => Return _ SLICE
  | Mk_loc_micheline (_, PRIM (_, "PAIR") nil) => Return _ PAIR
  | Mk_loc_micheline (_, PRIM (_, "CAR") nil) => Return _ CAR
  | Mk_loc_micheline (_, PRIM (_, "CDR") nil) => Return _ CDR
  | Mk_loc_micheline (_, PRIM (_, "GET") nil) => Return _ GET
  | Mk_loc_micheline (_, PRIM (_, "SOME") nil) => Return _ SOME
  | Mk_loc_micheline (_, PRIM (_, "NONE") (ty :: nil)) =>
    bind (fun ty => Return _ (NONE ty)) (micheline2michelson_type ty)
  | Mk_loc_micheline (_, PRIM (_, "LEFT") (ty :: nil)) =>
    bind (fun ty => Return _ (LEFT ty)) (micheline2michelson_type ty)
  | Mk_loc_micheline (_, PRIM (_, "RIGHT") (ty :: nil)) =>
    bind (fun ty => Return _ (RIGHT ty)) (micheline2michelson_type ty)
  | Mk_loc_micheline (_, PRIM (_, "CONS") nil) => Return _ CONS
  | Mk_loc_micheline (_, PRIM (_, "NIL") (ty :: nil)) =>
    bind (fun ty => Return _ (NIL ty)) (micheline2michelson_type ty)
  | Mk_loc_micheline (_, PRIM (_, "TRANSFER_TOKENS") nil) => Return _ TRANSFER_TOKENS
  | Mk_loc_micheline (_, PRIM (_, "SET_DELEGATE") nil) => Return _ SET_DELEGATE
  | Mk_loc_micheline (_, PRIM (_, "BALANCE") nil) => Return _ BALANCE
  | Mk_loc_micheline (_, PRIM (_, "ADDRESS") nil) => Return _ ADDRESS
  | Mk_loc_micheline (_, PRIM (_, "CONTRACT") (ty :: nil)) =>
    bind (fun ty => Return _ (CONTRACT ty)) (micheline2michelson_type ty)
  | Mk_loc_micheline (_, PRIM (_, "SOURCE") nil) => Return _ SOURCE
  | Mk_loc_micheline (_, PRIM (_, "SENDER") nil) => Return _ SENDER
  | Mk_loc_micheline (_, PRIM (_, "SELF") nil) => Return _ SELF
  | Mk_loc_micheline (_, PRIM (_, "AMOUNT") nil) => Return _ AMOUNT
  | Mk_loc_micheline (_, PRIM (_, "IMPLICIT_ACCOUNT") nil) => Return _ IMPLICIT_ACCOUNT
  | Mk_loc_micheline (_, PRIM (_, "NOW") nil) => Return _ NOW
  | Mk_loc_micheline (_, PRIM (_, "PACK") nil) => Return _ PACK
  | Mk_loc_micheline (_, PRIM (_, "UNPACK") (ty :: nil)) =>
    bind (fun ty => Return _ (UNPACK ty)) (micheline2michelson_type ty)
  | Mk_loc_micheline (_, PRIM (_, "HASH_KEY") nil) => Return _ HASH_KEY
  | Mk_loc_micheline (_, PRIM (_, "BLAKE2B") nil) => Return _ BLAKE2B
  | Mk_loc_micheline (_, PRIM (_, "SHA256") nil) => Return _ SHA256
  | Mk_loc_micheline (_, PRIM (_, "SHA512") nil) => Return _ SHA512
  | Mk_loc_micheline (_, PRIM (_, "CHECK_SIGNATURE") nil) => Return _ CHECK_SIGNATURE
  | Mk_loc_micheline (_, PRIM (_, "MEM") nil) => Return _ MEM
  | Mk_loc_micheline (_, PRIM (_, "UPDATE") nil) => Return _ UPDATE
  | Mk_loc_micheline (_, PRIM (_, "LOOP") (i :: nil)) =>
    bind (fun i => Return _ (LOOP i)) (micheline2michelson_instruction i)
  | Mk_loc_micheline (_, PRIM (_, "LOOP_LEFT") (i :: nil)) =>
    bind (fun i => Return _ (LOOP_LEFT i)) (micheline2michelson_instruction i)
  | Mk_loc_micheline (_, PRIM (_, "DIP") (i :: nil)) =>
    bind (fun i => Return _ (DIP 1 i)) (micheline2michelson_instruction i)
  | Mk_loc_micheline (_, PRIM (_, "DIP") (Mk_loc_micheline (_, NUMBER n) :: i :: nil)) =>
    bind (fun i => Return _ (DIP (BinInt.Z.to_nat n) i)) (micheline2michelson_instruction i)
  | Mk_loc_micheline (_, PRIM (_, "ITER") (i :: nil)) =>
    bind (fun i => Return _ (ITER i)) (micheline2michelson_instruction i)
  | Mk_loc_micheline (_, PRIM (_, "MAP") (i :: nil)) =>
    bind (fun i => Return _ (MAP i)) (micheline2michelson_instruction i)
  | Mk_loc_micheline
      (_, PRIM (_, "CREATE_CONTRACT")
               (Mk_loc_micheline
                  (_, SEQ
                        ((Mk_loc_micheline (_, PRIM (_, "storage") (storage_ty :: nil))) ::
                        (Mk_loc_micheline (_, PRIM (_, "params") (params_ty :: nil))) ::
                        (Mk_loc_micheline (_, PRIM (_, "code") (i :: nil))) :: nil)) ::
                  nil)) =>
    bind (fun i =>
            bind (fun sty =>
                    bind (fun pty =>
                            Return _ (CREATE_CONTRACT sty pty i))
                         (micheline2michelson_type params_ty))
                 (micheline2michelson_type storage_ty))
         (micheline2michelson_instruction i)
  | Mk_loc_micheline (_, PRIM (_, "EMPTY_SET") (cty :: nil)) =>
    bind (fun cty => Return _ (EMPTY_SET cty))
         (micheline2michelson_ctype cty)
  | Mk_loc_micheline (_, PRIM (_, "EMPTY_MAP") (kty :: vty :: nil)) =>
    bind (fun kty =>
            bind (fun vty =>
                    Return _ (EMPTY_MAP kty vty))
                 (micheline2michelson_type vty))
         (micheline2michelson_ctype kty)
  | Mk_loc_micheline (_, PRIM (_, "IF") (i1 :: i2 :: nil)) =>
    bind (fun i1 =>
            bind (fun i2 =>
                    Return _ (IF_ i1 i2))
                 (micheline2michelson_instruction i2))
         (micheline2michelson_instruction i1)
  | Mk_loc_micheline (_, PRIM (_, "IF_NONE") (i1 :: i2 :: nil)) =>
    bind (fun i1 =>
            bind (fun i2 =>
                    Return _ (IF_NONE i1 i2))
                 (micheline2michelson_instruction i2))
         (micheline2michelson_instruction i1)
  | Mk_loc_micheline (_, PRIM (_, "IF_LEFT") (i1 :: i2 :: nil)) =>
    bind (fun i1 =>
            bind (fun i2 =>
                    Return _ (IF_LEFT i1 i2))
                 (micheline2michelson_instruction i2))
         (micheline2michelson_instruction i1)
  | Mk_loc_micheline (_, PRIM (_, "IF_RIGHT") (i1 :: i2 :: nil)) =>
    bind (fun i1 =>
            bind (fun i2 =>
                    Return _ (IF_RIGHT i1 i2))
                 (micheline2michelson_instruction i2))
         (micheline2michelson_instruction i1)
  | Mk_loc_micheline (_, PRIM (_, "IF_CONS") (i1 :: i2 :: nil)) =>
    bind (fun i1 =>
            bind (fun i2 =>
                    Return _ (IF_CONS i1 i2))
                 (micheline2michelson_instruction i2))
         (micheline2michelson_instruction i1)
  | Mk_loc_micheline (_, PRIM (_, "LAMBDA") (a :: b :: i :: nil)) =>
    bind (fun a =>
            bind (fun b =>
                    bind (fun i =>
                            Return _ (LAMBDA a b i))
                         (micheline2michelson_instruction i))
                 (micheline2michelson_type b))
         (micheline2michelson_type a)
  | Mk_loc_micheline (_, PRIM (_, "PUSH") (a :: v :: nil)) =>
    bind (fun a =>
            bind (fun v => Return _ (PUSH a v))
                 (match a with
                  | syntax.lambda _ _ =>
                    bind (fun i => Return _ (Instruction i))
                         (micheline2michelson_instruction v)
                  | _ => micheline2michelson_data v
                  end))
         (micheline2michelson_type a)
  | Mk_loc_micheline ((b, e), _) => Failed _ (Expansion b e)
  end.
