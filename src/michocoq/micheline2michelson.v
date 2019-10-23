Require Import Ascii String List.
Require Import untyped_syntax micheline_syntax error location.
Require Import syntax_type.
Require Import Lia.
Require Coq.Program.Wf.
Import error.Notations.

Open Scope string.

Definition micheline2michelson_sctype (bem : loc_micheline) : M simple_comparable_type :=
  let 'Mk_loc_micheline ((b, e), m) := bem in
  match m with
  | PRIM (_, "string") nil => Return _ string
  | PRIM (_, "nat") nil => Return _ nat
  | PRIM (_, "int") nil => Return _ int
  | PRIM (_, "bytes") nil => Return _ bytes
  | PRIM (_, "bool") nil => Return _ bool
  | PRIM (_, "mutez") nil => Return _ mutez
  | PRIM (_, "key_hash") nil => Return _ key_hash
  | PRIM (_, "timestamp") nil => Return _ timestamp
  | PRIM (_, "address") nil => Return _ address
  | _ => Failed _ (Expansion b e)
  end.

Fixpoint micheline2michelson_ctype (bem : loc_micheline) : M comparable_type :=
  let 'Mk_loc_micheline ((b, e), m) := bem in
  match m with
  | PRIM (_, "pair") (a :: b :: nil) =>
    let! a := micheline2michelson_sctype a in
    let! b := micheline2michelson_ctype b in
    Return _ (Cpair a b)
  | _ =>
    let! a := micheline2michelson_sctype bem in
    Return _ (Comparable_type_simple a)
  end.

Notation "A ;; B" := (untyped_syntax.SEQ A B) (at level 100, right associativity).

Fixpoint micheline2michelson_type (bem : loc_micheline) : M type :=
  try (let! ty := micheline2michelson_sctype bem in Return _ (Comparable_type ty))
      (match bem with
       | Mk_loc_micheline (_, PRIM (_, "key") nil) => Return _ key
       | Mk_loc_micheline (_, PRIM (_, "unit") nil) => Return _ unit
       | Mk_loc_micheline (_, PRIM (_, "signature") nil) => Return _ signature
       | Mk_loc_micheline (_, PRIM (_, "operation") nil) => Return _ operation
       | Mk_loc_micheline (_, PRIM (_, "option") (a :: nil)) =>
        let! a := micheline2michelson_type a in
        Return _ (option a)
       | Mk_loc_micheline (_, PRIM (_, "list") (a :: nil)) =>
        let! a := micheline2michelson_type a in
        Return _ (list a)
       | Mk_loc_micheline (_, PRIM (_, "contract") (a :: nil)) =>
        let! a := micheline2michelson_type a in
        Return _ (contract a)
       | Mk_loc_micheline (_, PRIM (_, "set") (a :: nil)) =>
        let! a := micheline2michelson_ctype a in
        Return _ (set a)
       | Mk_loc_micheline (_, PRIM (_, "pair") (a :: b :: nil)) =>
        let! a := micheline2michelson_type a in
        let! b := micheline2michelson_type b in
        Return _ (pair a b)
       | Mk_loc_micheline (_, PRIM (_, "or") (a :: b :: nil)) =>
        let! a := micheline2michelson_type a in
        let! b := micheline2michelson_type b in
        Return _ (or a b)
       | Mk_loc_micheline (_, PRIM (_, "lambda") (a :: b :: nil)) =>
        let! a := micheline2michelson_type a in
        let! b := micheline2michelson_type b in
        Return _ (lambda a b)
       | Mk_loc_micheline (_, PRIM (_, "map") (a :: b :: nil)) =>
        let! a := micheline2michelson_ctype a in
        let! b := micheline2michelson_type b in
        Return _ (map a b)
       | Mk_loc_micheline (_, PRIM (_, "big_map") (a :: b :: nil)) =>
        let! a := micheline2michelson_ctype a in
        let! b := micheline2michelson_type b in
        Return _ (big_map a b)
       | Mk_loc_micheline ((b, e), _) => Failed _ (Expansion b e)
       end).

Fixpoint micheline2michelson_data (bem : loc_micheline) : M concrete_data :=
  match bem with
  | Mk_loc_micheline (_, SEQ l) =>
    let! l :=
      (fix micheline2michelson_data_list (l : Datatypes.list loc_micheline) : M (Datatypes.list concrete_data) :=
        match l with
        | nil => Return _ nil
        | m :: l =>
          let! d := micheline2michelson_data m in
          let! l := micheline2michelson_data_list l in
          Return _ (d :: l)
        end
      ) l in
    Return _ (Concrete_seq l)
  | Mk_loc_micheline (_, STR s) => Return _ (String_constant s)
  | Mk_loc_micheline (_, NUMBER z) => Return _ (Int_constant z)
  | Mk_loc_micheline (_, BYTES s) => Return _ (Bytes_constant s)
  | Mk_loc_micheline (_, PRIM (_, "Unit") nil) => Return _ Unit
  | Mk_loc_micheline (_, PRIM (_, "True") nil) => Return _ True_
  | Mk_loc_micheline (_, PRIM (_, "False") nil) => Return _ False_
  | Mk_loc_micheline (_, PRIM (_, "Pair") (a :: b :: nil)) =>
    let! a := micheline2michelson_data a in
    let! b := micheline2michelson_data b in
    Return _ (Pair a b)
  | Mk_loc_micheline (_, PRIM (_, "Elt") (a :: b :: nil)) =>
    let! a := micheline2michelson_data a in
    let! b := micheline2michelson_data b in
    Return _ (Elt a b)
  | Mk_loc_micheline (_, PRIM (_, "Left") (a :: nil)) =>
    let! a := micheline2michelson_data a in
    Return _ (Left a)
  | Mk_loc_micheline (_, PRIM (_, "Right") (a :: nil)) =>
    let! a := micheline2michelson_data a in
    Return _ (Right a)
  | Mk_loc_micheline (_, PRIM (_, "Some") (a :: nil)) =>
    let! a := micheline2michelson_data a in
    Return _ (Some_ a)
  | Mk_loc_micheline (_, PRIM (_, "None") nil) => Return _ None_
  | Mk_loc_micheline ((b, e), PRIM s _) => Failed _ (Expansion b e)
  end.

Definition op_of_string (s : String.string) b e :=
  match s with
  | "EQ" => Return _ EQ
  | "NEQ" => Return _ NEQ
  | "LE" => Return _ LE
  | "GE" => Return _ GE
  | "LT" => Return _ LT
  | "GT" => Return _ GT
  | _ => Failed _ (Expansion b e)
  end.

Definition FAIL := UNIT ;; FAILWITH.
Definition ASSERT := IF_ NOOP FAIL.

Definition IF_op_of_string (s : String.string) b e bt bf :=
  match s with
  | String "I" (String "F" s) =>
    let! op := op_of_string s b e in
    Return _ (op ;; IF_ bt bf)
  | _ => Failed _ (Expansion b e)
  end.

Definition ASSERT_op_of_string (s : String.string) b e :=
  match s with
  | String "A" (String "S" (String "S" (String "E" (String "R" (String "T" (String "_" s)))))) =>
    let! op := op_of_string s b e in
    Return _ (op ;; IF_ NOOP FAIL)
  | _ => Failed _ (Expansion b e)
  end.

Definition ASSERT_NONE := IF_NONE NOOP FAIL.
Definition ASSERT_SOME := IF_NONE FAIL NOOP.
Definition ASSERT_LEFT := IF_LEFT NOOP FAIL.
Definition ASSERT_RIGHT := IF_LEFT FAIL NOOP.

Fixpoint DIPn n code :=
  match n with
  | 0 => code
  | S n => DIP 1 (DIPn n code)
  end.

Fixpoint DUP_Sn n :=
  match n with
  | 0 => DUP
  | S n => DIP 1 (DUP_Sn n) ;; SWAP
  end.

Definition IF_SOME bt bf := IF_NONE bf bt.
Definition IF_RIGHT bt bf := IF_LEFT bf bt.
Definition IF_NIL bt bf := IF_CONS bf bt.

Inductive cadr : Set :=
| Cadr_CAR : cadr -> cadr
| Cadr_CDR : cadr -> cadr
| Cadr_nil : cadr.

Fixpoint micheline2michelson_cadr (x : cadr) : instruction :=
  match x with
  | Cadr_CAR x => CAR ;; micheline2michelson_cadr x
  | Cadr_CDR x => CDR ;; micheline2michelson_cadr x
  | Cadr_nil => NOOP
  end.

Fixpoint micheline2michelson_set_cadr (x : cadr) : instruction :=
  match x with
  | Cadr_CAR Cadr_nil =>
    CDR ;; SWAP ;; PAIR
  | Cadr_CDR Cadr_nil =>
    CAR ;; PAIR
  | Cadr_CAR x =>
    DUP ;; DIP 1 (CAR;; micheline2michelson_set_cadr x) ;; CDR ;; SWAP ;; PAIR
  | Cadr_CDR x =>
    DUP ;; DIP 1 (CDR;; micheline2michelson_set_cadr x) ;; CAR ;; PAIR
  | Cadr_nil => NOOP (* Should not happen *)
  end.

Fixpoint micheline2michelson_map_cadr (x : cadr) (code : instruction) : instruction :=
  match x with
  | Cadr_CAR Cadr_nil =>
    DUP ;; CDR ;; DIP 1 ( CAR ;; code ) ;; SWAP ;; PAIR
  | Cadr_CDR Cadr_nil =>
    DUP ;; CDR ;; code ;; SWAP ;; CAR ;; PAIR
  | Cadr_CAR x =>
    DUP ;; DIP 1 (CAR;; micheline2michelson_map_cadr x code) ;; CDR ;; SWAP ;; PAIR
  | Cadr_CDR x =>
    DUP ;; DIP 1 (CDR;; micheline2michelson_map_cadr x code) ;; CAR ;; PAIR
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
    Return _ (cons token_P l)
  | String "A" s =>
    let! l := lex_papair s fail in
    Return _ (cons token_A l)
  | String "I" s =>
    let! l := lex_papair s fail in
    Return _ (cons token_I l)
  | "R"%string => Return _ nil
  | _ => Failed _ fail
  end.

Inductive papair_d : direction -> Set :=
| Papair_d_P d : papair_d Left -> papair_d Right -> papair_d d
| Papair_d_A : papair_d Left
| Papair_d_I : papair_d Right.

Fixpoint parse_papair (d : direction) (s : Datatypes.list papair_token) (fail : exception)
         (fuel : Datatypes.nat) (Hs : List.length s < fuel) {struct fuel} :
  M (papair_d d * { r : Datatypes.list papair_token | List.length r < List.length s}).
Proof.
  destruct fuel.
  - destruct (PeanoNat.Nat.nlt_0_r _ Hs).
  - destruct s as [|c s].
    + exact (Failed _ fail).
    + refine (match c, d
              return M (papair_d d *
                        { r : Datatypes.list papair_token | List.length r < S (List.length s)})
              with
              | token_P, d1 =>
                let! (l, exist _ s1 Hl) := parse_papair Left s fail fuel _ in
                let! (r, exist _ s2 Hr) := parse_papair Right s1 fail fuel _ in
                Return _ (Papair_d_P d l r, exist _ s2 _)
              | token_A, Left => Return _ (Papair_d_A, exist _ s _)
              | token_I, Right => Return _ (Papair_d_I, exist _ s _)
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

Fixpoint micheline2michelson_papair (x : papair) : instruction :=
  match x with
  | Papair_PAIR => PAIR
  | Papair_A y => DIP 1 (micheline2michelson_papair y) ;; PAIR
  | Papair_I x => micheline2michelson_papair x ;; PAIR
  | Papair_P x y => micheline2michelson_papair x ;;
                    DIP 1 (micheline2michelson_papair y) ;;
                    PAIR
  end.

Definition UNPAIR := DUP ;; CAR ;; DIP 1 CDR.

Fixpoint micheline2michelson_unpapair (x : papair) : instruction :=
  match x with
  | Papair_PAIR => UNPAIR
  | Papair_A y => UNPAIR ;; DIP 1 (micheline2michelson_unpapair y)
  | Papair_I x => UNPAIR ;; micheline2michelson_unpapair x
  | Papair_P x y => UNPAIR ;;
                    DIP 1 (micheline2michelson_unpapair y) ;;
                    micheline2michelson_unpapair x
  end.

Definition parse_papair_full (s : String.string) (fail : exception): M instruction :=
  let! toks : Datatypes.list papair_token := lex_papair s fail in
  let! (l, exist _ toks2 Htoks2) := parse_papair Left toks fail (S (List.length toks)) ltac:(simpl; lia) in
  let! (r, exist _ toks3 Htoks3) := parse_papair Right toks2 fail (S (List.length toks2)) ltac:(simpl; lia) in
  match toks3 with
  | nil => Return _
                  (micheline2michelson_papair
                      (papair_of_l_r
                        (papair_l_of_papair_d l)
                        (papair_r_of_papair_d r)))
  | _ => Failed _ fail
  end.

Definition parse_unpapair_full (s : String.string) (fail : exception): M instruction :=
  let! toks : Datatypes.list papair_token := lex_papair s fail in
  let! (l, exist _ toks2 Htoks2) := parse_papair Left toks fail (S (List.length toks)) ltac:(simpl; lia) in
  let! (r, exist _ toks3 Htoks3) := parse_papair Right toks2 fail (S (List.length toks2)) ltac:(simpl; lia) in
  match toks3 with
  | nil => Return _
                  (micheline2michelson_unpapair
                      (papair_of_l_r
                        (papair_l_of_papair_d l)
                        (papair_r_of_papair_d r)))
  | _ => Failed _ fail
  end.

Fixpoint micheline2michelson_instruction (m : loc_micheline) : M instruction :=
  match m with
  | Mk_loc_micheline (_, SEQ l) =>
    (fix micheline2michelson_instr_seq (l : Datatypes.list loc_micheline) : M instruction :=
       match l with
       | nil => Return _ NOOP
       | cons i nil => micheline2michelson_instruction i
       | i1 :: l =>
        let! i1 := micheline2michelson_instruction i1 in
        let! i2 := micheline2michelson_instr_seq l in
        Return _ (i1 ;; i2)
       end) l
  | Mk_loc_micheline (_, PRIM (_, "FAILWITH") nil) => Return _ FAILWITH
  | Mk_loc_micheline (_, PRIM (_, "EXEC") nil) => Return _ EXEC
  | Mk_loc_micheline (_, PRIM (_, "APPLY") nil) => Return _ APPLY
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
  | Mk_loc_micheline (_, PRIM (_, "ISNAT") nil) => Return _ ISNAT
  | Mk_loc_micheline (_, PRIM (_, "INT") nil) => Return _ INT
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
    let! ty := micheline2michelson_type ty in
    Return _ (NONE ty)
  | Mk_loc_micheline (_, PRIM (_, "LEFT") (ty :: nil)) =>
    let! ty := micheline2michelson_type ty in
    Return _ (LEFT ty)
  | Mk_loc_micheline (_, PRIM (_, "RIGHT") (ty :: nil)) =>
    let! ty := micheline2michelson_type ty in
    Return _ (RIGHT ty)
  | Mk_loc_micheline (_, PRIM (_, "CONS") nil) => Return _ CONS
  | Mk_loc_micheline (_, PRIM (_, "NIL") (ty :: nil)) =>
    let! ty := micheline2michelson_type ty in
    Return _ (NIL ty)
  | Mk_loc_micheline (_, PRIM (_, "TRANSFER_TOKENS") nil) => Return _ TRANSFER_TOKENS
  | Mk_loc_micheline (_, PRIM (_, "SET_DELEGATE") nil) => Return _ SET_DELEGATE
  | Mk_loc_micheline (_, PRIM (_, "BALANCE") nil) => Return _ BALANCE
  | Mk_loc_micheline (_, PRIM (_, "ADDRESS") nil) => Return _ ADDRESS
  | Mk_loc_micheline (_, PRIM (_, "CONTRACT") (ty :: nil)) =>
    let! ty := micheline2michelson_type ty in
    Return _ (CONTRACT ty)
  | Mk_loc_micheline (_, PRIM (_, "SOURCE") nil) => Return _ SOURCE
  | Mk_loc_micheline (_, PRIM (_, "SENDER") nil) => Return _ SENDER
  | Mk_loc_micheline (_, PRIM (_, "SELF") nil) => Return _ SELF
  | Mk_loc_micheline (_, PRIM (_, "AMOUNT") nil) => Return _ AMOUNT
  | Mk_loc_micheline (_, PRIM (_, "IMPLICIT_ACCOUNT") nil) => Return _ IMPLICIT_ACCOUNT
  | Mk_loc_micheline (_, PRIM (_, "NOW") nil) => Return _ NOW
  | Mk_loc_micheline (_, PRIM (_, "PACK") nil) => Return _ PACK
  | Mk_loc_micheline (_, PRIM (_, "UNPACK") (ty :: nil)) =>
    let! ty := micheline2michelson_type ty in
    Return _ (UNPACK ty)
  | Mk_loc_micheline (_, PRIM (_, "HASH_KEY") nil) => Return _ HASH_KEY
  | Mk_loc_micheline (_, PRIM (_, "BLAKE2B") nil) => Return _ BLAKE2B
  | Mk_loc_micheline (_, PRIM (_, "SHA256") nil) => Return _ SHA256
  | Mk_loc_micheline (_, PRIM (_, "SHA512") nil) => Return _ SHA512
  | Mk_loc_micheline (_, PRIM (_, "CHECK_SIGNATURE") nil) => Return _ CHECK_SIGNATURE
  | Mk_loc_micheline (_, PRIM (_, "MEM") nil) => Return _ MEM
  | Mk_loc_micheline (_, PRIM (_, "UPDATE") nil) => Return _ UPDATE
  | Mk_loc_micheline (_, PRIM (_, "CHAIN_ID") nil) => Return _ CHAIN_ID
  | Mk_loc_micheline (_, PRIM (_, "LOOP") (i :: nil)) =>
    let! i := micheline2michelson_instruction i in
    Return _ (LOOP i)
  | Mk_loc_micheline (_, PRIM (_, "LOOP_LEFT") (i :: nil)) =>
    let! i := micheline2michelson_instruction i in
    Return _ (LOOP_LEFT i)
  | Mk_loc_micheline (_, PRIM (_, "DIP") (i :: nil)) =>
    let! i := micheline2michelson_instruction i in
    Return _ (DIP 1 i)
  | Mk_loc_micheline (_, PRIM (_, "DIP") (Mk_loc_micheline (_, NUMBER n) :: i :: nil)) =>
    let! i := micheline2michelson_instruction i in
    Return _ (DIP (BinInt.Z.to_nat n) i)
  | Mk_loc_micheline (_, PRIM (_, "DIG") (Mk_loc_micheline (_, NUMBER n) :: nil)) =>
    Return _ (DIG (BinInt.Z.to_nat n))
  | Mk_loc_micheline (_, PRIM (_, "DUG") (Mk_loc_micheline (_, NUMBER n) :: nil)) =>
    Return _ (DUG (BinInt.Z.to_nat n))
  | Mk_loc_micheline (_, PRIM (_, "ITER") (i :: nil)) =>
    let! i := micheline2michelson_instruction i in
    Return _ (ITER i)
  | Mk_loc_micheline (_, PRIM (_, "MAP") (i :: nil)) =>
    let! i := micheline2michelson_instruction i in
    Return _ (MAP i)
  | Mk_loc_micheline
      (_, PRIM (_, "CREATE_CONTRACT")
               (Mk_loc_micheline
                  (_, SEQ
                        ((Mk_loc_micheline (_, PRIM (_, "storage") (storage_ty :: nil))) ::
                        (Mk_loc_micheline (_, PRIM (_, "parameter") (params_ty :: nil))) ::
                        (Mk_loc_micheline (_, PRIM (_, "code") (i :: nil))) :: nil)) ::
                  nil)) =>
    let! i := micheline2michelson_instruction i in
    let! sty := micheline2michelson_type storage_ty in
    let! pty := micheline2michelson_type params_ty in
    Return _ (CREATE_CONTRACT sty pty i)
  | Mk_loc_micheline
      (_, PRIM (_, "CREATE_CONTRACT")
               (Mk_loc_micheline
                  (_, SEQ
                        ((Mk_loc_micheline (_, PRIM (_, "parameter") (params_ty :: nil))) ::
                        (Mk_loc_micheline (_, PRIM (_, "storage") (storage_ty :: nil))) ::
                        (Mk_loc_micheline (_, PRIM (_, "code") (i :: nil))) :: nil)) ::
                  nil)) =>
    let! i := micheline2michelson_instruction i in
    let! sty := micheline2michelson_type storage_ty in
    let! pty := micheline2michelson_type params_ty in
    Return _ (CREATE_CONTRACT sty pty i)
  | Mk_loc_micheline (_, PRIM (_, "EMPTY_SET") (cty :: nil)) =>
    let! cty := micheline2michelson_ctype cty in
    Return _ (EMPTY_SET cty)
  | Mk_loc_micheline (_, PRIM (_, "EMPTY_MAP") (kty :: vty :: nil)) =>
    let! kty := micheline2michelson_ctype kty in
    let! vty := micheline2michelson_type vty in
    Return _ (EMPTY_MAP kty vty)
  | Mk_loc_micheline (_, PRIM (_, "EMPTY_BIG_MAP") (kty :: vty :: nil)) =>
    let! kty := micheline2michelson_ctype kty in
    let! vty := micheline2michelson_type vty in
    Return _ (EMPTY_BIG_MAP kty vty)
  | Mk_loc_micheline (_, PRIM (_, "IF") (i1 :: i2 :: nil)) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    Return _ (IF_ i1 i2)
  | Mk_loc_micheline (_, PRIM (_, "IF_NONE") (i1 :: i2 :: nil)) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    Return _ (IF_NONE i1 i2)
  | Mk_loc_micheline (_, PRIM (_, "IF_LEFT") (i1 :: i2 :: nil)) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    Return _ (IF_LEFT i1 i2)
  | Mk_loc_micheline (_, PRIM (_, "IF_CONS") (i1 :: i2 :: nil)) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    Return _ (IF_CONS i1 i2)
  | Mk_loc_micheline (_, PRIM (_, "LAMBDA") (a :: b :: i :: nil)) =>
    let! a := micheline2michelson_type a in
    let! b := micheline2michelson_type b in
    let! i := micheline2michelson_instruction i in
    Return _ (LAMBDA a b i)
  | Mk_loc_micheline (_, PRIM (_, "PUSH") (a :: v :: nil)) =>
    let! a := micheline2michelson_type a in
    let! v :=
      match a with
      | lambda _ _ =>
        let! i := micheline2michelson_instruction v in
        Return _ (Instruction i)
      | _ => micheline2michelson_data v
      end in
    Return _ (PUSH a v)

  | Mk_loc_micheline (_, PRIM (_, "RENAME") _) => Return _ NOOP
  | Mk_loc_micheline (_, PRIM (_, "CAST") _) => Return _ NOOP


  (* Macros *)
  | Mk_loc_micheline ((b, e), PRIM (_, "FAIL") nil) => Return _ FAIL
  | Mk_loc_micheline ((b, e), PRIM (_, "ASSERT") nil) => Return _ ASSERT
  | Mk_loc_micheline ((b, e), PRIM (_, "ASSERT_NONE") nil) => Return _ ASSERT_NONE
  | Mk_loc_micheline ((b, e), PRIM (_, "ASSERT_SOME") nil) => Return _ ASSERT_SOME
  | Mk_loc_micheline ((b, e), PRIM (_, "ASSERT_LEFT") nil) => Return _ ASSERT_LEFT
  | Mk_loc_micheline ((b, e), PRIM (_, "ASSERT_RIGHT") nil) => Return _ ASSERT_RIGHT

  | Mk_loc_micheline (_, PRIM (_, "IF_SOME") (i1 :: i2 :: nil)) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    Return _ (IF_SOME i1 i2)
  | Mk_loc_micheline (_, PRIM (_, "IF_RIGHT") (i1 :: i2 :: nil)) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    Return _ (IF_RIGHT i1 i2)
  | Mk_loc_micheline (_, PRIM (_, "IF_NIL") (i1 :: i2 :: nil)) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    Return _ (IF_NIL i1 i2)

  | Mk_loc_micheline ((b, e), PRIM (_, String "C" (String "M" (String "P" s))) nil) =>
    let! op := op_of_string s b e in
    Return _ (COMPARE ;; op)
  | Mk_loc_micheline ((b, e), PRIM (_,
       String "I" (String "F" (String "C" (String "M" (String "P" s))))) (i1 :: i2 :: nil)) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    let! op := op_of_string s b e in
    Return _ (COMPARE ;; op ;; IF_ i1 i2)
  | Mk_loc_micheline ((b, e), PRIM (_,
       String "I" (String "F" s)) (i1 :: i2 :: nil)) =>
    let! i1 := micheline2michelson_instruction i1 in
    let! i2 := micheline2michelson_instruction i2 in
    let! op := op_of_string s b e in
    Return _ (op ;; IF_ i1 i2)
  | Mk_loc_micheline ((b, e), PRIM (_,
      String "A" (String "S" (String "S" (String "E" (String "R" (String "T"
      (String "_" (String "C" (String "M" (String "P" s)))))))))) nil) =>
    let! op := op_of_string s b e in
    Return _ (COMPARE;; op ;; IF_ NOOP FAIL)

  | Mk_loc_micheline ((b, e), PRIM (_,
      String "A" (String "S" (String "S" (String "E" (String "R" (String "T"
      (String "_" s))))))) nil) =>
    let! op := op_of_string s b e in
    Return _ (op ;; IF_ NOOP FAIL)

  | Mk_loc_micheline ((b, e), PRIM (_, "CR") nil) =>
    Failed _ (Expansion_prim b e "CR")
  | Mk_loc_micheline ((b, e), PRIM (_, "SET_CR") nil) =>
    Failed _ (Expansion_prim b e "SET_CR")
  | Mk_loc_micheline ((b, e), PRIM (_, "MAP_CR") nil) =>
    Failed _ (Expansion_prim b e "MAP_CR")

  (* CADAAR *)
  | Mk_loc_micheline ((b, e), PRIM (_, String "C" s) nil) =>
    let prim := String "C" s in
    let get_cadr := fix get_cadr s :=
                      match s with
                      | "R" => Return _ Cadr_nil
                      | String "A" s =>
                        let! x := get_cadr s in
                        Return _ (Cadr_CAR x)
                      | String "D" s =>
                        let! x := get_cadr s in
                        Return _ (Cadr_CDR x)
                      | _ => Failed _ (Expansion_prim b e prim)
                      end in
    let! x := get_cadr s in
    Return _ (micheline2michelson_cadr x)

  | Mk_loc_micheline ((b, e),
      PRIM (_, String "S" (String "E"(String "T"(String "_"(String "C" s)))))
           nil) =>
    let prim := String "S" (String "E"(String "T"(String "_"(String "C" s)))) in
    let get_cadr := fix get_cadr s :=
                      match s with
                      | "R" => Return _ Cadr_nil
                      | String "A" s =>
                        let! x := get_cadr s in
                        Return _ (Cadr_CAR x)
                      | String "D" s =>
                        let! x := get_cadr s in
                        Return _ (Cadr_CDR x)
                      | _ => Failed _ (Expansion_prim b e prim)
                      end in
    let! x := get_cadr s in
    Return _ (micheline2michelson_set_cadr x)

  | Mk_loc_micheline ((b, e),
      PRIM (_, String "M" (String "A"(String "P"(String "_"(String "C" s)))))
           (a :: nil)) =>
    let prim := String "M" (String "A"(String "P"(String "_"(String "C" s)))) in
    let get_cadr := fix get_cadr s :=
                      match s with
                      | "R" => Return _ Cadr_nil
                      | String "A" s =>
                        let! x := get_cadr s in
                        Return _ (Cadr_CAR x)
                      | String "D" s =>
                        let! x := get_cadr s in
                        Return _ (Cadr_CDR x)
                      | _ => Failed _ (Expansion_prim b e prim)
                      end in
    let! x := get_cadr s in
    let! code := micheline2michelson_instruction a in
    Return _ (micheline2michelson_map_cadr x code)

  | Mk_loc_micheline ((b, e), PRIM (_, String "D" (String "I" s)) (a :: nil)) =>
    let is_diip := fix is_diip s :=
                     match s with
                     | "P" => true
                     | String "I" s => is_diip s
                     | _ => false
                     end in
    if is_diip s then
      let! a := micheline2michelson_instruction a in
      Return _ (DIPn (String.length s) a)
    else Failed _ (Expansion_prim b e (String "D" (String "I" s)))
  | Mk_loc_micheline ((b, e), PRIM (_, "DUP") (Mk_loc_micheline (_, NUMBER n) :: nil)) =>
    match BinInt.Z.to_nat n with
    | S n => Return _ (DUP_Sn n)
    | O => Failed _ (Expansion b e)
    end
  | Mk_loc_micheline ((b, e), PRIM (_, String "D" (String "U" (String "U" s))) nil) =>
    let is_duup := fix is_duup s :=
                     match s with
                     | "P" => true
                     | String "U" s => is_duup s
                     | _ => false
                     end in
    if is_duup s then Return _ (DUP_Sn (String.length s))
    else Failed _ (Expansion_prim b e (String "D" (String "U" (String "U" s))))

  (* PAPAIR *)
  | Mk_loc_micheline ((b, e), PRIM (_, String "P" s) nil) =>
    let prim := String "P" s in
    let fail := Expansion_prim b e prim in
    parse_papair_full s fail

  (* UNPAPAIR *)
  | Mk_loc_micheline ((b, e), PRIM (_, String "U" (String "N" (String "P" s))) nil) =>
    let prim := String "U" (String "N" (String "P" s)) in
    let fail := Expansion_prim b e prim in
    parse_unpapair_full s fail

  (* Unknown case *)
  | Mk_loc_micheline ((b, e), PRIM (_, s) _) => Failed _ (Expansion_prim b e s)
  | Mk_loc_micheline ((b, e), _) => Failed _ (Expansion b e)
  end.

Record untyped_michelson_file :=
  Mk_untyped_michelson_file
    { parameter : type;
      storage : type;
      code : instruction }.

Record untyped_michelson_file_opt :=
  Mk_untyped_michelson_file_opt
    { parameter_opt : Datatypes.option type;
      storage_opt : Datatypes.option type;
      code_opt : Datatypes.option instruction }.

Definition read_parameter (ty : type) (f : untyped_michelson_file_opt) :=
  match f.(parameter_opt) with
  | None => Return _ {| parameter_opt := Some ty;
                        storage_opt := f.(storage_opt);
                        code_opt := f.(code_opt) |}
  | Some _ => Failed _ Parsing
  end.

Definition read_storage (ty : type) (f : untyped_michelson_file_opt) :=
  match f.(storage_opt) with
  | None => Return _ {| parameter_opt := f.(parameter_opt);
                        storage_opt := Some ty;
                        code_opt := f.(code_opt) |}
  | Some _ => Failed _ Parsing
  end.

Definition read_code (c : instruction) (f : untyped_michelson_file_opt) :=
  match f.(code_opt) with
  | None => Return _ {| parameter_opt := f.(parameter_opt);
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
        | PRIM (_, _, "parameter") (cons param nil) =>
          let! ty := micheline2michelson_type param in
          read_parameter ty a
        | PRIM (_, _, "storage") (cons storage nil) =>
          let! ty := micheline2michelson_type storage in
          read_storage ty a
        | PRIM (_, _, "code") (cons code nil) =>
          let! c := micheline2michelson_instruction code in
          read_code c a
        | _ => Failed _ Parsing
        end)
      l
    {| parameter_opt := None; storage_opt := None; code_opt := None |} in
    match a.(parameter_opt), a.(storage_opt), a.(code_opt) with
    | Some param, Some storage, Some code =>
      Return _ {| parameter := param; storage := storage; code := code |}
    | _, _, _ => Failed _ Parsing
    end.

