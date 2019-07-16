(** Comparison of the OCaml and MiChoCoq syntax. *)
Require of_ocaml.script_typed_ir_ml.
Require of_ocaml.syntax_type_equiv.
Require syntax.
Require syntax_type.

Import of_ocaml.syntax_type_equiv.Option.
Import syntax syntax_type of_ocaml.script_typed_ir_ml.

Parameter default_location
  : Tezos_raw_protocol_alpha.Alpha_context.Script.location.

Definition comparable_coq_to_ocaml
  (comparable : syntax_type.comparable_type)
  : script_typed_ir_ml.comparable_ty
    (syntax_type_equiv.typ.coq_to_ocaml_typ
      (comparable_type_to_type comparable)
    ).
  rewrite <- syntax_type_equiv.typ.coq_comparable_to_ocaml_typ_eq.
  apply syntax_type_equiv.comparable.coq_to_ocaml.
Defined.

(** We define a partial injection from the MiChoCoq syntax to the OCaml AST. *)
Definition to_coq_concrete_data
  {type : syntax_type.type}
  (concrete_data : syntax.concrete_data type)
  : Datatypes.option (of_ocaml.syntax_type_equiv.typ.coq_to_ocaml_typ type) :=
  match concrete_data with
  | Int_constant _ =>
    Some (
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.num_make
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z_sample
    )
  | Nat_constant _ =>
    Some (
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.num_make
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n_sample
    )
  | _ => None
  end.

Fixpoint of_coq
  {self_type : syntax.self_info}
  {tail_fail_flag : Datatypes.bool}
  {A B : Datatypes.list syntax_type.type}
  (instruction : syntax.instruction self_type tail_fail_flag A B)
  : Datatypes.option (
    of_ocaml.script_typed_ir_ml.instr
      (of_ocaml.syntax_type_equiv.typ.coq_to_ocaml_typs A)
      (of_ocaml.syntax_type_equiv.typ.coq_to_ocaml_typs B)
    ) :=
  match instruction with
  | NOOP => Some Nop
  | @FAILWITH _ _ _ a =>
    let? ty_a := of_ocaml.syntax_type_equiv.typ.coq_to_ocaml a in
    Some (Failwith ty_a)
  | @SEQ _ A B C _ instruction_a instruction_b =>
    let? bef := of_ocaml.syntax_type_equiv.typ.coq_to_ocamls A in
    let? trans := of_ocaml.syntax_type_equiv.typ.coq_to_ocamls B in
    let? aft := of_ocaml.syntax_type_equiv.typ.coq_to_ocamls C in
    let? instruction_a' := of_coq instruction_a in
    let? instruction_b' := of_coq instruction_b in
    Some (Seq
      {|
        loc := default_location;
        bef := bef;
        aft := trans;
        instr_ := instruction_a';
      |}
      {|
        loc := default_location;
        bef := trans;
        aft := aft;
        instr_ := instruction_b';
      |}
    )
  | @IF_ _ A B _ _ instruction_a instruction_b =>
    let? bef := of_ocaml.syntax_type_equiv.typ.coq_to_ocamls A in
    let? aft := of_ocaml.syntax_type_equiv.typ.coq_to_ocamls B in
    let? instruction_a' := of_coq instruction_a in
    let? instruction_b' := of_coq instruction_b in
    Some (If
      {|
        loc := default_location;
        bef := bef;
        aft := aft;
        instr_ := instruction_a';
      |}
      {|
        loc := default_location;
        bef := bef;
        aft := aft;
        instr_ := instruction_a';
      |}
    )
  | @LOOP _ A instruction =>
    let? rest := of_ocaml.syntax_type_equiv.typ.coq_to_ocamls A in
    let? instruction' := of_coq instruction in
    Some (Loop
      {|
        loc := default_location;
        bef := rest;
        aft := Item_t (Bool_t None) rest None;
        instr_ := instruction';
      |}
    )
  | @LOOP_LEFT _ a b an bn A instruction =>
    let? bef := of_ocaml.syntax_type_equiv.typ.coq_to_ocamls (a :: A) in
    let? aft := of_ocaml.syntax_type_equiv.typ.coq_to_ocamls (or a an b bn :: A) in
    let? instruction' := of_coq instruction in
    Some (Loop_left
      {|
        loc := default_location;
        bef := bef;
        aft := aft;
        instr_ := instruction';
      |}
    )
  | EXEC => None
  | APPLY => None
  | DUP => Some Dup
  | SWAP => Some Swap
  | PUSH _ x =>
    let? x' := to_coq_concrete_data x in
    Some (Const x')
  (** FIXME: the `UNIT` instruction is not in the OCaml AST. It should be
      added rather than removed during type-checking.
  *)
  | UNIT => None
  | LAMBDA _ _ _ => None
  | EQ => Some Eq
  | NEQ => Some Neq
  | LT => Some Lt
  | GT => Some Gt
  | LE => Some Le
  | GE => Some Ge
  | @OR _ _ s _ =>
    let 'syntax.Mk_bitwise _ variant := s in
    match variant with
    | syntax.Bitwise_variant_bool => Some Or
    | syntax.Bitwise_variant_nat => Some Or_nat
    end
  | @AND _ _ s _ =>
    let 'syntax.Mk_bitwise _ variant := s in
    match variant with
    | syntax.Bitwise_variant_bool => Some And
    | syntax.Bitwise_variant_nat => Some And_nat
    end
  | @XOR _ _ s _ =>
    let 'syntax.Mk_bitwise _ variant := s in
    match variant with
    | syntax.Bitwise_variant_bool => Some Xor
    | syntax.Bitwise_variant_nat => Some Xor_nat
    end
  | @NOT _ _ s _ =>
    let 'syntax.Mk_not _ _ variant := s in
    match variant with
    | syntax.Not_variant_bool => Some Not
    | syntax.Not_variant_nat => Some Not_nat
    | syntax.Not_variant_int => Some Not_int
    end
  | @NEG _ _ s _ =>
    let 'syntax.Mk_neg _ variant := s in
    match variant with
    | syntax.Neg_variant_nat => Some Neg_nat
    | syntax.Neg_variant_int => Some Neg_int
    end
  | ABS => Some Abs_int
  | ISNAT => Some Is_nat
  | INT => Some Int_nat
  | @ADD _ _ _ s _ =>
    let 'syntax.Mk_add _ _ _ variant := s in
    match variant with
    | syntax.Add_variant_nat_nat => Some Add_natnat
    | syntax.Add_variant_nat_int => Some Add_natint
    | syntax.Add_variant_int_nat => Some Add_intnat
    | syntax.Add_variant_int_int => Some Add_intint
    | syntax.Add_variant_timestamp_int => Some Add_timestamp_to_seconds
    | syntax.Add_variant_int_timestamp => Some Add_seconds_to_timestamp
    | syntax.Add_variant_tez_tez => Some Add_tez
    end
  | @SUB _ _ _ s _ =>
    let 'syntax.Mk_sub _ _ _ variant := s in
    match variant with
    | syntax.Sub_variant_nat_nat => Some Sub_int
    | syntax.Sub_variant_nat_int => Some Sub_int
    | syntax.Sub_variant_int_nat => Some Sub_int
    | syntax.Sub_variant_int_int => Some Sub_int
    | syntax.Sub_variant_timestamp_int => Some Sub_timestamp_seconds
    | syntax.Sub_variant_timestamp_timestamp => Some Diff_timestamps
    | syntax.Sub_variant_tez_tez => Some Sub_tez
    end
  | @MUL _ _ _ s _ =>
    let 'syntax.Mk_mul _ _ _ variant := s in
    match variant with
    | syntax.Mul_variant_nat_nat => Some Mul_natnat
    | syntax.Mul_variant_nat_int => Some Mul_natint
    | syntax.Mul_variant_int_nat => Some Mul_intnat
    | syntax.Mul_variant_int_int => Some Mul_intint
    | syntax.Mul_variant_tez_nat => Some Mul_teznat
    | syntax.Mul_variant_nat_tez => Some Mul_nattez
    end
  | @EDIV _ _ _ s _ =>
    let 'syntax.Mk_ediv _ _ _ _ variant := s in
    match variant with
    | syntax.Ediv_variant_nat_nat => Some Ediv_natnat
    | syntax.Ediv_variant_nat_int => Some Ediv_natint
    | syntax.Ediv_variant_int_nat => Some Ediv_intnat
    | syntax.Ediv_variant_int_int => Some Ediv_intint
    | syntax.Ediv_variant_tez_nat => Some Ediv_teznat
    | syntax.Ediv_variant_tez_tez => Some Ediv_tez
    end
  | LSL => Some Lsl_nat
  | LSR => Some Lsr_nat
  | @COMPARE _ a _ => Some (Compare (comparable_coq_to_ocaml a))
  | @CONCAT _ _ i _ =>
    let 'syntax.Mk_stringlike _ variant := i in
    match variant with
    | syntax.Stringlike_variant_string => Some Concat_string_pair
    | syntax.Stringlike_variant_bytes => Some Concat_bytes_pair
    end
  | @CONCAT_list _ _ i _ =>
    let 'syntax.Mk_stringlike _ variant := i in
    match variant with
    | syntax.Stringlike_variant_string => Some Concat_string
    | syntax.Stringlike_variant_bytes => Some Concat_bytes
    end
  | @SIZE _ _ i _ =>
    let 'syntax.Mk_size _ variant := i in
    match variant with
    | syntax.Size_variant_set _ => Some Set_size
    | syntax.Size_variant_map _ _ => Some Map_size
    | syntax.Size_variant_list _ => Some List_size
    | syntax.Size_variant_string => Some String_size
    | syntax.Size_variant_bytes => Some Bytes_size
    end
  | @SLICE _ _ i _ =>
    let 'syntax.Mk_stringlike _ variant := i in
    match variant with
    | syntax.Stringlike_variant_string => Some Slice_string
    | syntax.Stringlike_variant_bytes => Some Slice_bytes
    end
  | PAIR => Some Cons_pair
  | CAR => Some Car
  | CDR => Some Cdr
  | EMPTY_SET elt =>
    Some (Empty_set (syntax_type_equiv.comparable.coq_to_ocaml elt))
  | _ => None
  end.
