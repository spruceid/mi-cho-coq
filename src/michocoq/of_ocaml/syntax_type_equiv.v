(** Comparison of the OCaml and MiChoCoq types. *)
Require Import Coq.Lists.List.
Require of_ocaml.script_typed_ir_ml syntax_type.

Import ListNotations.

(** Utilities and notations to manipulate the option type. *)
Module Option.
  Definition bind {A B : Type}
    (x : Datatypes.option A) (f : A -> Datatypes.option B)
    : Datatypes.option B :=
    match x with
    | Some x => f x
    | None => None
    end.

  (** Notation for the bind with a typed answer. *)
  Notation "'let?' x : A ':=' X 'in' Y" :=
    (bind X (fun (x : A) => Y))
    (at level 200, x pattern, X at level 100, A at level 200, Y at level 200).

  (** Notation for the bind. *)
  Notation "'let?' x ':=' X 'in' Y" :=
    (bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Definition true_or_None (A : Datatypes.option Prop) : Prop :=
    match A with
    | Some A => A
    | None => True
    end.

  Lemma true_or_None_case_eq
    {T : Type} {e1 : Datatypes.option T} {e2 : T -> Prop}
    (A : true_or_None (let? x := e1 in Some (e2 x)))
    {x : T}
    (H : e1 = Some x)
    : e2 x.
    rewrite H in A; simpl in A.
    exact A.
  Qed.
End Option.

Import Option.

(** Bijection between OCaml and MiChoCoq comparable types. This bijection is
    not a true bijection for the following reasons:
    * some cases from OCaml are not imported by coq-of-ocaml;
    * most of the annotations are missing in MiChoCoq;
    * we define the equality on OCaml terms with an inductive, as this equality
      is heterogeneous and we did not achieve to use the heterogeneous equality
      of the Coq standard library with success.
*)
Module comparable.
  Import script_typed_ir_ml syntax_type.

  Definition ocaml_leaf_to_coq {A Kind : Type}
    (comparable : script_typed_ir_ml.comparable_struct A Kind)
    : Datatypes.option syntax_type.simple_comparable_type :=
    match comparable with
    | Int_key _ => Some int
    | Nat_key _ => Some nat
    | String_key _ => Some string
    | Bytes_key _ => Some bytes
    | Mutez_key _ => Some mutez
    | Bool_key _ => Some bool
    | Key_hash_key _ => Some key_hash
    | Timestamp_key _ => Some timestamp
    | Address_key _ => Some address
    (* This case should not be used with GADTs *)
    | Pair_key _ _ _ => None
    end.

  Fixpoint ocaml_to_coq {A Kind : Type}
    (comparable : script_typed_ir_ml.comparable_struct A Kind)
    : Datatypes.option syntax_type.comparable_type :=
    match comparable with
    | Pair_key (comparable_a, _) (comparable_b, _) _ =>
      let? comparable_a' := ocaml_leaf_to_coq comparable_a in
      let? comparable_b' := ocaml_to_coq comparable_b in
      Some (Cpair comparable_a' comparable_b')
    | _ =>
      let? comparable' := ocaml_leaf_to_coq comparable in
      Some (Comparable_type_simple comparable')
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
    : ocaml_leaf_to_coq (coq_simple_to_ocaml Kind comparable) = Some comparable.
    destruct comparable; reflexivity.
  Qed.

  Fixpoint coq_to_ocaml_to_coq_eq (comparable : syntax_type.comparable_type)
    : ocaml_to_coq (coq_to_ocaml comparable) = Some comparable.
    destruct comparable as [simple | simple comparable]; simpl.
    - destruct simple; reflexivity.
    - rewrite coq_simple_to_ocaml_to_coq_eq.
      rewrite coq_to_ocaml_to_coq_eq.
      reflexivity.
  Qed.

  Definition ocaml_leaf_to_coq_to_ocaml_typ_eq {A : Type}
    (comparable : comparable_struct A leaf)
    : true_or_None (
        let? comparable' := ocaml_leaf_to_coq comparable in
        Some (coq_simple_to_ocaml_typ comparable' = A)
      ).
    destruct comparable; simpl; reflexivity.
  Qed.

  Fixpoint ocaml_to_coq_to_ocaml_typ_eq {A Kind : Type}
    (comparable : script_typed_ir_ml.comparable_struct A Kind)
    : true_or_None (
        let? comparable' := ocaml_to_coq comparable in
        Some (coq_to_ocaml_typ comparable' = A)
      ).
    destruct comparable; simpl; try reflexivity.
    destruct p; destruct p0; simpl.
    case_eq (ocaml_leaf_to_coq c); simpl; trivial.
    intros s Hs.
    case_eq (ocaml_to_coq c0); simpl; trivial.
    intros c1 Hc1.
    rewrite (true_or_None_case_eq (ocaml_leaf_to_coq_to_ocaml_typ_eq c) Hs).
    rewrite (true_or_None_case_eq (ocaml_to_coq_to_ocaml_typ_eq _ _ c0) Hc1).
    reflexivity.
  Qed.

  Module eq.
    Import script_typed_ir_ml.

    Inductive t :
      forall {A B : Type} (Kind_A Kind_B : Type),
        script_typed_ir_ml.comparable_struct A Kind_A ->
        script_typed_ir_ml.comparable_struct B Kind_B ->
        Prop :=
    | Int :
      forall Kind_A Kind_B annot_a annot_b,
      t Kind_A Kind_B (Int_key annot_a) (Int_key annot_b)
    | Nat :
      forall Kind_A Kind_B annot_a annot_b,
      t Kind_A Kind_B (Nat_key annot_a) (Nat_key annot_b)
    | String_key :
      forall Kind_A Kind_B annot_a annot_b,
      t Kind_A Kind_B (String_key annot_a) (String_key annot_b)
    | Bytes_key :
      forall Kind_A Kind_B annot_a annot_b,
      t Kind_A Kind_B (Bytes_key annot_a) (Bytes_key annot_b)
    | Mutez_key :
      forall Kind_A Kind_B annot_a annot_b,
      t Kind_A Kind_B (Mutez_key annot_a) (Mutez_key annot_b)
    | Bool_key :
      forall Kind_A Kind_B annot_a annot_b,
      t Kind_A Kind_B (Bool_key annot_a) (Bool_key annot_b)
    | Key_hash_key :
      forall Kind_A Kind_B annot_a annot_b,
      t Kind_A Kind_B (Key_hash_key annot_a) (Key_hash_key annot_b)
    | Timestamp_key :
      forall Kind_A Kind_B annot_a annot_b,
      t Kind_A Kind_B (Timestamp_key annot_a) (Timestamp_key annot_b)
    | Address_key :
      forall Kind_A Kind_B annot_a annot_b,
      t Kind_A Kind_B (Address_key annot_a) (Address_key annot_b)
    | Pair :
      forall {A_A A_B B_A B_B : Type},
      forall Kind_A Kind_B,
      forall annot_a_a annot_a_b annot_a annot_b_a annot_b_b annot_b,
      forall
        (comparable_a_a : script_typed_ir_ml.comparable_struct A_A leaf)
        (comparable_a_b : script_typed_ir_ml.comparable_struct A_B Kind_A)
        (comparable_b_a : script_typed_ir_ml.comparable_struct B_A leaf)
        (comparable_b_b : script_typed_ir_ml.comparable_struct B_B Kind_B),
      t leaf leaf comparable_a_a comparable_b_a ->
      t Kind_A Kind_B comparable_a_b comparable_b_b ->
      t
        comb comb
        (Pair_key (comparable_a_a, annot_a_a) (comparable_a_b, annot_a_b) annot_a)
        (Pair_key (comparable_b_a, annot_b_a) (comparable_b_b, annot_b_b) annot_b).
    Arguments t {_ _ _ _} _ _.
  End eq.

  Definition ocaml_leaf_to_coq_to_ocaml_eq {A Kind : Type}
    (comparable : script_typed_ir_ml.comparable_struct A Kind)
    : true_or_None (
        let? comparable' := ocaml_leaf_to_coq comparable in
        Some (eq.t (coq_simple_to_ocaml Kind comparable') comparable)
      ).
    destruct comparable; simpl; constructor.
  Qed.

  Fixpoint ocaml_to_coq_to_ocaml_eq {A Kind : Type}
    (comparable : script_typed_ir_ml.comparable_struct A Kind)
    : true_or_None (
        let? comparable' := ocaml_to_coq comparable in
        Some (eq.t (coq_to_ocaml comparable') comparable)
      ).
    destruct comparable; simpl; try constructor.
    destruct p; destruct p0; simpl.
    case_eq (ocaml_leaf_to_coq c); simpl; trivial.
    intros s Hs.
    case_eq (ocaml_to_coq c0); simpl; trivial.
    intros c1 Hc1.
    constructor.
    - apply (true_or_None_case_eq (ocaml_leaf_to_coq_to_ocaml_eq c) Hs).
    - apply (true_or_None_case_eq (ocaml_to_coq_to_ocaml_eq _ _ c0) Hc1).
  Qed.
End comparable.

(** Injection from MiChoCoq types to OCaml types. We should be able to show that
    this injection is actually a bijection. This bijection would be partial, for
    the same reasons as for the comparable types.
*)
Module typ.
  Import script_typed_ir_ml syntax_type.

  Fixpoint ocaml_to_coq {ty : Type} (typ : script_typed_ir_ml.Ty ty)
    : Datatypes.option syntax_type.type :=
    match typ with
    | Unit_t _ => Some (unit)
    | Int_t _ => Some (Comparable_type int)
    | Nat_t _ => Some (Comparable_type nat)
    | Signature_t _ => Some (signature)
    | String_t _ => Some (Comparable_type string)
    | Bytes_t _ => Some (Comparable_type bytes)
    | Mutez_t _ => Some (Comparable_type mutez)
    | Key_hash_t _ => Some (Comparable_type key_hash)
    | Key_t _ => Some (key)
    | Timestamp_t _ => Some (Comparable_type timestamp)
    | Address_t _ => Some (Comparable_type address)
    | Bool_t _ => Some (Comparable_type bool)
    | Pair_t (typ_a, _, _) (typ_b, _, _) _ _ =>
      let? typ_a' := ocaml_to_coq typ_a in
      let? typ_b' := ocaml_to_coq typ_b in
      Some (pair typ_a' typ_b')
    | Union_t (typ_a, _) (typ_b, _) _ _ =>
      let? typ_a' := ocaml_to_coq typ_a in
      let? typ_b' := ocaml_to_coq typ_b in
      Some (or typ_a' typ_b')
    | Lambda_t typ_arg typ_ret _ =>
      let? typ_arg' := ocaml_to_coq typ_arg in
      let? typ_ret' := ocaml_to_coq typ_ret in
      Some (lambda typ_arg' typ_ret')
    | Option_t typ _ _ =>
      let? typ' := ocaml_to_coq typ in
      Some (option typ')
    | List_t typ _ _ =>
      let? typ' := ocaml_to_coq typ in
      Some (list typ')
    | Set_t typ_key _ =>
      let? typ_key' := comparable.ocaml_to_coq typ_key in
      Some (set typ_key')
    | Map_t typ_key typ _ _ =>
      let? typ_key' := comparable.ocaml_to_coq typ_key in
      let? typ' := ocaml_to_coq typ in
      Some (map typ_key' typ')
    | Operation_t _ => Some operation
    | Chain_id_t _ => Some chain_id
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

  Fixpoint coq_comparable_to_ocaml_typ_eq
    (comparable : syntax_type.comparable_type)
    : comparable.coq_to_ocaml_typ comparable =
      coq_to_ocaml_typ (syntax_type.comparable_type_to_type comparable).
    destruct comparable; simpl.
    - reflexivity.
    - rewrite coq_comparable_to_ocaml_typ_eq.
      reflexivity.
  Qed.

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
      let? typ' := coq_to_ocaml typ in
      Some (Option_t typ' None false)
    | list typ =>
      let? typ' := coq_to_ocaml typ in
      Some (List_t typ' None false)
    | set typ_key =>
      let typ_key' := comparable.coq_to_ocaml typ_key in
      Some (Set_t typ_key' None)
    | operation => Some (Operation_t None)
    | pair typ_a typ_b =>
      let? typ_a' := coq_to_ocaml typ_a in
      let? typ_b' := coq_to_ocaml typ_b in
      Some (Pair_t
        (typ_a', None, None)
        (typ_b', None, None)
        None
        false
      )
    | or typ_a typ_b =>
      let? typ_a' := coq_to_ocaml typ_a in
      let? typ_b' := coq_to_ocaml typ_b in
      Some (Union_t
        (typ_a', None)
        (typ_b', None)
        None
        false
      )
    | lambda typ_arg typ_ret =>
      let? typ_arg' := coq_to_ocaml typ_arg in
      let? typ_ret' := coq_to_ocaml typ_ret in
      Some (Lambda_t typ_arg' typ_ret' None)
    | map typ_key typ =>
      let typ_key' := comparable.coq_to_ocaml typ_key in
      let? typ' := coq_to_ocaml typ in
      Some (Map_t typ_key' typ' None false)
    | chain_id => Some (Chain_id_t None)
    | _ => None
    end.

  Ltac case_eq_rewrite_in_H e e' He H:=
    case_eq e; simpl; trivial;
    intros e' He;
    rewrite He in H; simpl in H;
    clear He.

  Fixpoint coq_to_ocaml_to_coq_eq (typ : syntax_type.type)
    : true_or_None (
        let? typ' := coq_to_ocaml typ in
        let? typ'' := ocaml_to_coq typ' in
        Some (typ'' = typ)
      ).
    destruct typ; simpl;
      try reflexivity;
      (* one recursive case *)
      try (
        assert (H_ind := coq_to_ocaml_to_coq_eq typ);
        case_eq_rewrite_in_H (coq_to_ocaml typ) typ' Htyp H_ind;
        case_eq_rewrite_in_H (ocaml_to_coq typ') typ'' Htyp' H_ind;
        congruence
      );
      (* two recursive cases *)
      try (
        assert (H_ind_typ1 := coq_to_ocaml_to_coq_eq typ1);
        assert (H_ind_typ2 := coq_to_ocaml_to_coq_eq typ2);
        case_eq_rewrite_in_H (coq_to_ocaml typ1) typ1' Htyp1 H_ind_typ1;
        case_eq_rewrite_in_H (coq_to_ocaml typ2) typ2' Htyp2 H_ind_typ2;
        case_eq_rewrite_in_H (ocaml_to_coq typ1') typ1'' Htyp1' H_ind_typ1;
        case_eq_rewrite_in_H (ocaml_to_coq typ2') typ2'' Htyp2' H_ind_typ2;
        congruence
      ).
    - destruct s; simpl; reflexivity.
    - rewrite comparable.coq_to_ocaml_to_coq_eq; simpl.
      reflexivity.
    - assert (H_ind_typ := coq_to_ocaml_to_coq_eq typ).
      case_eq_rewrite_in_H (coq_to_ocaml typ) typ' Htyp H_ind_typ.
      rewrite comparable.coq_to_ocaml_to_coq_eq; simpl.
      case_eq_rewrite_in_H (ocaml_to_coq typ') typ'' Htyp' H_ind_typ.
      congruence.
  Qed.

  Fixpoint coq_to_ocaml_typs (typs : Datatypes.list syntax_type.type) : Type :=
    match typs with
    | [] => Datatypes.unit
    | typ :: typs => coq_to_ocaml_typ typ * coq_to_ocaml_typs typs
    end.

  Fixpoint coq_to_ocamls (typs : Datatypes.list syntax_type.type)
    : Datatypes.option (script_typed_ir_ml.stack_ty (coq_to_ocaml_typs typs)) :=
    match typs with
    | [] => Some Empty_t
    | typ :: typs =>
      let? typ' := coq_to_ocaml typ in
      let? typs' := coq_to_ocamls typs in
      Some (Item_t typ' typs' None)
    end.
End typ.
