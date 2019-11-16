Require of_ocaml.script_typed_ir_ml syntax_type.

Fixpoint typ_ocaml_to_coq {ty : Type} (typ : script_typed_ir_ml.Ty ty)
  : syntax_type.type :=
  match typ with
  | script_typed_ir_ml.Unit_t _ => syntax_type.unit
  | script_typed_ir_ml.Int_t _ => syntax_type.Comparable_type syntax_type.int
  | script_typed_ir_ml.Nat_t _ => syntax_type.Comparable_type syntax_type.nat
  | script_typed_ir_ml.Signature_t _ => syntax_type.signature
  | script_typed_ir_ml.String_t _ => syntax_type.Comparable_type syntax_type.string
  | script_typed_ir_ml.Bytes_t _ => syntax_type.Comparable_type syntax_type.bytes
  | script_typed_ir_ml.Mutez_t _ => syntax_type.Comparable_type syntax_type.mutez
  | script_typed_ir_ml.Key_hash_t _ => syntax_type.Comparable_type syntax_type.key_hash
  | script_typed_ir_ml.Key_t _ => syntax_type.key
  | script_typed_ir_ml.Timestamp_t _ => syntax_type.Comparable_type syntax_type.timestamp
  | script_typed_ir_ml.Address_t _ => syntax_type.Comparable_type syntax_type.address
  | script_typed_ir_ml.Bool_t _ => syntax_type.Comparable_type syntax_type.bool
  | script_typed_ir_ml.Pair_t (typ_a, _, _) (typ_b, _, _) _ _ =>
    syntax_type.pair (typ_ocaml_to_coq typ_a) (typ_ocaml_to_coq typ_b)
  | script_typed_ir_ml.Union_t (typ_a, _) (typ_b, _) _ _ =>
    syntax_type.or (typ_ocaml_to_coq typ_a) (typ_ocaml_to_coq typ_b)
  | script_typed_ir_ml.Lambda_t typ_arg typ_ret _ =>
    syntax_type.lambda (typ_ocaml_to_coq typ_arg) (typ_ocaml_to_coq typ_ret)
  | script_typed_ir_ml.Option_t typ _ _ => syntax_type.option (typ_ocaml_to_coq typ)
  | script_typed_ir_ml.List_t typ _ _ => syntax_type.list (typ_ocaml_to_coq typ)
  | script_typed_ir_ml.Operation_t _ => syntax_type.operation
  | script_typed_ir_ml.Chain_id_t _ => syntax_type.chain_id
  | _ => syntax_type.unit
  end.

Fixpoint typ_coq_to_ocaml (typ : syntax_type.type)
  : option {ty : Type & script_typed_ir_ml.Ty ty} :=
  match typ with
  | syntax_type.Comparable_type comparable_typ =>
    Some (
      match comparable_typ with
      | syntax_type.string => existT _ _ (script_typed_ir_ml.String_t None)
      | syntax_type.nat => existT _ _ (script_typed_ir_ml.Nat_t None)
      | syntax_type.int => existT _ _ (script_typed_ir_ml.Int_t None)
      | syntax_type.bytes => existT _ _ (script_typed_ir_ml.Bytes_t None)
      | syntax_type.bool => existT _ _ (script_typed_ir_ml.Bool_t None)
      | syntax_type.mutez => existT _ _ (script_typed_ir_ml.Mutez_t None)
      | syntax_type.address => existT _ _ (script_typed_ir_ml.Address_t None)
      | syntax_type.key_hash => existT _ _ (script_typed_ir_ml.Key_hash_t None)
      | syntax_type.timestamp => existT _ _ (script_typed_ir_ml.Timestamp_t None)
      end
    )
  | syntax_type.key => Some (existT _ _ (script_typed_ir_ml.Key_t None))
  | syntax_type.unit => Some (existT _ _ (script_typed_ir_ml.Unit_t None))
  | syntax_type.signature => Some (existT _ _ (script_typed_ir_ml.Signature_t None))
  | syntax_type.option typ =>
    match typ_coq_to_ocaml typ with
    | Some (existT _ _ typ) => Some (existT _ _ (script_typed_ir_ml.Option_t typ None false))
    | _ => None
    end
  | syntax_type.list typ =>
    match typ_coq_to_ocaml typ with
    | Some (existT _ _ typ) => Some (existT _ _ (script_typed_ir_ml.List_t typ None false))
    | _ => None
    end
  | syntax_type.operation => Some (existT _ _ (script_typed_ir_ml.Operation_t None))
  | syntax_type.pair typ_a typ_b =>
    match (typ_coq_to_ocaml typ_a, typ_coq_to_ocaml typ_b) with
    | (Some (existT _ _ typ_a), Some (existT _ _ typ_b)) =>
      Some (existT _ _ (script_typed_ir_ml.Pair_t
        (typ_a, None, None)
        (typ_b, None, None)
        None
        false
      ))
    | _ => None
    end
  | syntax_type.or typ_a typ_b =>
    match (typ_coq_to_ocaml typ_a, typ_coq_to_ocaml typ_b) with
    | (Some (existT _ _ typ_a), Some (existT _ _ typ_b)) =>
      Some (existT _ _ (script_typed_ir_ml.Union_t
        (typ_a, None)
        (typ_b, None)
        None
        false
      ))
    | _ => None
    end
  | syntax_type.lambda typ_arg typ_ret =>
    match (typ_coq_to_ocaml typ_arg, typ_coq_to_ocaml typ_ret) with
    | (Some (existT _ _ typ_arg), Some (existT _ _ typ_ret)) =>
      Some (existT _ _ (script_typed_ir_ml.Lambda_t typ_arg typ_ret None))
    | _ => None
    end
  | syntax_type.chain_id => Some (existT _ _ (script_typed_ir_ml.Chain_id_t None))
  | _ => None
  end.

Fixpoint coq_to_ocaml_to_coq_eq (typ : syntax_type.type)
  : match typ_coq_to_ocaml typ with
    | Some (existT _ _ typ') => typ_ocaml_to_coq typ' = typ
    | _ => True
    end.
  destruct typ; simpl;
    try reflexivity;
    (* One recursive call *)
    try (
      case_eq (typ_coq_to_ocaml typ); trivial;
      intros s Heq;
      set (Heq' := coq_to_ocaml_to_coq_eq typ);
      rewrite Heq in Heq';
      destruct s; simpl;
      now rewrite Heq'
    );
    (* two recusive calls *)
    try (
      case_eq (typ_coq_to_ocaml typ1); trivial;
      destruct s as [ty1' typ1'];
      intro Heq1;
      set (Heq1' := coq_to_ocaml_to_coq_eq typ1);
      rewrite Heq1 in Heq1';
      case_eq (typ_coq_to_ocaml typ2); trivial;
      destruct s as [ty2' typ2'];
      intro Heq2;
      set (Heq2' := coq_to_ocaml_to_coq_eq typ2);
      rewrite Heq2 in Heq2';
      now simpl; rewrite Heq1'; rewrite Heq2'
    ).
  destruct s; simpl; reflexivity.
Qed.
