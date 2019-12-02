Require of_ocaml.script_typed_ir_ml syntax_type.

Module comparable.
  Import script_typed_ir_ml syntax_type.

  Definition ocaml_leaf_to_coq {A Kind : Type}
    (comparable : script_typed_ir_ml.comparable_struct A Kind)
    : syntax_type.simple_comparable_type :=
    match comparable with
    | Int_key _ => int
    | Nat_key _ => nat
    | String_key _ => string
    | Bytes_key _ => bytes
    | Mutez_key _ => mutez
    | Bool_key _ => bool
    | Key_hash_key _ => key_hash
    | Timestamp_key _ => timestamp
    | Address_key _ => address
    (* This case should not be used with GADTs *)
    | Pair_key _ _ _ => bool
    end.

  Fixpoint ocaml_to_coq {A Kind : Type}
    (comparable : script_typed_ir_ml.comparable_struct A Kind)
    : syntax_type.comparable_type :=
    match comparable with
    | Pair_key (comparable_a, _) (comparable_b, _) _ =>
      Cpair
        (ocaml_leaf_to_coq comparable_a)
        (ocaml_to_coq comparable_b)
    | _ => Comparable_type_simple (ocaml_leaf_to_coq comparable)
    end.

  Definition coq_simple_to_ocaml_typ
    (comparable : syntax_type.simple_comparable_type)
    : Type :=
    match comparable with
    | string => String.string
    | nat =>
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.n
    | int =>
      Tezos_raw_protocol_alpha.Alpha_context.Script_int.num
        Tezos_raw_protocol_alpha.Alpha_context.Script_int.z
    | bytes =>
      Tezos_protocol_environment_alpha.Environment.MBytes.t
    | bool => Datatypes.bool
    | mutez => Tezos_raw_protocol_alpha.Alpha_context.Tez.t
    | address => script_typed_ir_ml.address
    | key_hash => Tezos_raw_protocol_alpha.Alpha_context.public_key_hash
    | timestamp => Tezos_raw_protocol_alpha.Alpha_context.Script_timestamp.t
    end.

  Definition coq_simple_to_ocaml
    (Kind : Type)
    (comparable : syntax_type.simple_comparable_type)
    : script_typed_ir_ml.comparable_struct
      (coq_simple_to_ocaml_typ comparable)
      Kind
    :=
    match comparable with
    | string => String_key None
    | nat => Nat_key None
    | int => Int_key None
    | bytes => Bytes_key None
    | bool => Bool_key None
    | mutez => Mutez_key None
    | address => Address_key None
    | key_hash => Key_hash_key None
    | timestamp => Timestamp_key None
    end.

  Fixpoint coq_to_ocaml_typ
    (comparable : syntax_type.comparable_type)
    : Type :=
    match comparable with
    | Comparable_type_simple comparable => coq_simple_to_ocaml_typ comparable
    | Cpair comparable_a comparable_b =>
      coq_simple_to_ocaml_typ comparable_a * coq_to_ocaml_typ comparable_b
    end.

  Definition coq_to_ocaml_kind (comparable : syntax_type.comparable_type) : Type :=
    match comparable with
    | Comparable_type_simple _ => leaf
    | Cpair _ _ => comb
    end.

  Fixpoint coq_to_ocaml (comparable : syntax_type.comparable_type)
    : script_typed_ir_ml.comparable_ty (coq_to_ocaml_typ comparable) :=
    match comparable with
    | Comparable_type_simple comparable =>
      coq_simple_to_ocaml comb comparable
    | Cpair comparable_a comparable_b =>
      Pair_key
        (coq_simple_to_ocaml leaf comparable_a, None)
        (coq_to_ocaml comparable_b, None)
        None
    end.

  Fixpoint coq_simple_to_ocaml_to_coq_eq {Kind : Type}
    (comparable : syntax_type.simple_comparable_type)
    : ocaml_leaf_to_coq (coq_simple_to_ocaml Kind comparable) = comparable.
    destruct comparable; reflexivity.
  Qed.

  Fixpoint coq_to_ocaml_to_coq_eq (comparable : syntax_type.comparable_type)
    : ocaml_to_coq (coq_to_ocaml comparable) = comparable.
    destruct comparable as [simple | simple comparable]; simpl.
    - destruct simple; reflexivity.
    - rewrite coq_simple_to_ocaml_to_coq_eq.
      rewrite coq_to_ocaml_to_coq_eq.
      reflexivity.
  Qed.
End comparable.

Module typ.
  Import script_typed_ir_ml syntax_type.

  Fixpoint ocaml_to_coq {ty : Type} (typ : script_typed_ir_ml.Ty ty)
    : syntax_type.type :=
    match typ with
    | Unit_t _ => unit
    | Int_t _ => Comparable_type int
    | Nat_t _ => Comparable_type nat
    | Signature_t _ => signature
    | String_t _ => Comparable_type string
    | Bytes_t _ => Comparable_type bytes
    | Mutez_t _ => Comparable_type mutez
    | Key_hash_t _ => Comparable_type key_hash
    | Key_t _ => key
    | Timestamp_t _ => Comparable_type timestamp
    | Address_t _ => Comparable_type address
    | Bool_t _ => Comparable_type bool
    | Pair_t (typ_a, _, _) (typ_b, _, _) _ _ =>
      pair (ocaml_to_coq typ_a) (ocaml_to_coq typ_b)
    | Union_t (typ_a, _) (typ_b, _) _ _ =>
      or (ocaml_to_coq typ_a) (ocaml_to_coq typ_b)
    | Lambda_t typ_arg typ_ret _ =>
      lambda (ocaml_to_coq typ_arg) (ocaml_to_coq typ_ret)
    | Option_t typ _ _ => option (ocaml_to_coq typ)
    | List_t typ _ _ => list (ocaml_to_coq typ)
    | Set_t typ_key _ => set (comparable.ocaml_to_coq typ_key)
    | Map_t typ_key typ _ _ =>
      map (comparable.ocaml_to_coq typ_key) (ocaml_to_coq typ)
    | Operation_t _ => operation
    | Chain_id_t _ => chain_id
    end.

  Fixpoint coq_to_ocaml_typ (typ : syntax_type.type) : Type :=
    match typ with
    | Comparable_type comparable_typ =>
      comparable.coq_simple_to_ocaml_typ comparable_typ
    | key => Tezos_raw_protocol_alpha.Alpha_context.public_key
    | unit => Datatypes.unit
    | signature => Tezos_raw_protocol_alpha.Alpha_context.signature
    | option typ => Datatypes.option (coq_to_ocaml_typ typ)
    | list typ => Datatypes.list (coq_to_ocaml_typ typ)
    | set comparable_typ =>
      script_typed_ir_ml.set (comparable.coq_to_ocaml_typ comparable_typ)
    | contract typ => typed_contract (coq_to_ocaml_typ typ)
    | operation => script_typed_ir_ml.operation
    | pair typ_a typ_b => coq_to_ocaml_typ typ_a * coq_to_ocaml_typ typ_b
    | or typ_a typ_b => union (coq_to_ocaml_typ typ_a) (coq_to_ocaml_typ typ_b)
    | lambda typ_arg typ_res =>
      script_typed_ir_ml.lambda
        (coq_to_ocaml_typ typ_arg)
        (coq_to_ocaml_typ typ_res)
    | map comparable_typ typ =>
      script_typed_ir_ml.map
        (comparable.coq_to_ocaml_typ comparable_typ)
        (coq_to_ocaml_typ typ)
    | big_map comparable_typ typ =>
      script_typed_ir_ml.big_map
        (comparable.coq_to_ocaml_typ comparable_typ)
        (coq_to_ocaml_typ typ)
    | chain_id => Tezos_protocol_environment_alpha.Environment.Chain_id.t
    end.

  Fixpoint coq_to_ocaml (typ : syntax_type.type)
    : Datatypes.option (script_typed_ir_ml.Ty (coq_to_ocaml_typ typ)) :=
    match typ with
    | Comparable_type comparable_typ =>
      Some (
        match comparable_typ return
          script_typed_ir_ml.Ty (comparable.coq_simple_to_ocaml_typ comparable_typ)
        with
        | string => String_t None
        | nat => Nat_t None
        | int => Int_t None
        | bytes => Bytes_t None
        | bool => Bool_t None
        | mutez => Mutez_t None
        | address => Address_t None
        | key_hash => Key_hash_t None
        | timestamp => Timestamp_t None
        end
      )
    | key => Some (Key_t None)
    | unit => Some (Unit_t None)
    | signature => Some (Signature_t None)
    | option typ =>
      match coq_to_ocaml typ with
      | Some typ => Some (Option_t typ None false)
      | _ => None
      end
    | list typ =>
      match coq_to_ocaml typ with
      | Some typ => Some (List_t typ None false)
      | _ => None
      end
    | set typ_key =>
      Some (Set_t (comparable.coq_to_ocaml typ_key) None)
    | operation => Some (Operation_t None)
    | pair typ_a typ_b =>
      match (coq_to_ocaml typ_a, coq_to_ocaml typ_b) with
      | (Some typ_a, Some typ_b) =>
        Some (Pair_t
          (typ_a, None, None)
          (typ_b, None, None)
          None
          false
        )
      | _ => None
      end
    | or typ_a typ_b =>
      match (coq_to_ocaml typ_a, coq_to_ocaml typ_b) with
      | (Some typ_a, Some typ_b) =>
        Some (Union_t
          (typ_a, None)
          (typ_b, None)
          None
          false
        )
      | _ => None
      end
    | lambda typ_arg typ_ret =>
      match (coq_to_ocaml typ_arg, coq_to_ocaml typ_ret) with
      | (Some typ_arg, Some typ_ret) =>
        Some (Lambda_t typ_arg typ_ret None)
      | _ => None
      end
    | map typ_key typ =>
      match coq_to_ocaml typ with
      | Some typ =>
        Some (Map_t (comparable.coq_to_ocaml typ_key) typ None false)
      | _ => None
      end
    | chain_id => Some (Chain_id_t None)
    | _ => None
    end.

  Fixpoint coq_to_ocaml_to_coq_eq (typ : syntax_type.type)
    : match coq_to_ocaml typ with
      | Some typ' => ocaml_to_coq typ' = typ
      | _ => True
      end.
    destruct typ; simpl;
      try reflexivity;
      (* One recursive call *)
      try (
        case_eq (coq_to_ocaml typ); trivial;
        intros s Heq;
        set (Heq' := coq_to_ocaml_to_coq_eq typ);
        rewrite Heq in Heq'; simpl;
        rewrite Heq'; trivial
      );
      (* Two recusive calls *)
      try (
        case_eq (coq_to_ocaml typ1); trivial;
        intros ty1' Heq1;
        case_eq (coq_to_ocaml typ2); trivial;
        intros ty2' Heq2;
        set (Heq1' := coq_to_ocaml_to_coq_eq typ1);
        rewrite Heq1 in Heq1';
        set (Heq2' := coq_to_ocaml_to_coq_eq typ2);
        rewrite Heq2 in Heq2';
        simpl; rewrite Heq1'; rewrite Heq2'; trivial
      ).
    - destruct s; simpl; reflexivity.
    - now rewrite comparable.coq_to_ocaml_to_coq_eq.
    - now rewrite comparable.coq_to_ocaml_to_coq_eq.
  Qed.
End typ.
