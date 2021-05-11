(* Open Source License *)
(* Copyright (c) 2021 Michael J. Klein, TQ Tezos, Spruce Systems, Inc. *)

(* Permission is hereby granted, free of charge, to any person obtaining a *)
(* copy of this software and associated documentation files (the "Software"), *)
(* to deal in the Software without restriction, including without limitation *)
(* the rights to use, copy, modify, merge, publish, distribute, sublicense, *)
(* and/or sell copies of the Software, and to permit persons to whom the *)
(* Software is furnished to do so, subject to the following conditions: *)

(* The above copyright notice and this permission notice shall be included *)
(* in all copies or substantial portions of the Software. *)

(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *)
(* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, *)
(* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL *)
(* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *)
(* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING *)
(* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER *)
(* DEALINGS IN THE SOFTWARE. *)

Require Import Coq.Classes.EquivDec.
Require Import Michocoq.macros.
Require Import syntax macros main semantics comparable util.
Require Import ZArith.
Require Import Lia.
Import error.
Require List.
Require tez.
Require map.
Require String.

Require did_manager_string.
(* Require did_manager_michelson_string. *)

(* Module raw. *)

(* Import String. *)

(* Definition did_manager_michelson_string : string := " *)
(* parameter *)
(*   (or (or (address %rotateAuthentication) (address %rotateOwner)) *)
(*       (pair %rotateService (string %endpoint) (string %type_))); *)
(* storage *)
(*   (pair (pair (big_map %metadata string bytes) (address %owner)) *)
(*         (pair (pair %service (string %endpoint) (string %type_)) *)
(*               (address %verification_method))); *)
(* code { UNPAIR; *)
(*        SWAP; *)
(*        UNPAIR; *)
(*        UNPAIR; *)
(*        SWAP; *)
(*        DUP; *)
(*        SENDER; *)
(*        COMPARE; *)
(*        EQ; *)
(*        IF { SWAP; *)
(*             DIP { DIG 2; *)
(*                   IF_LEFT *)
(*                     { IF_LEFT *)
(*                         { SWAP; DIP { SWAP; UNPAIR; SWAP; DROP; PAIR } } *)
(*                         { SWAP; DROP } } *)
(*                     { SWAP; DIP { SWAP; DUP; CAR; DROP; CDR; SWAP; PAIR } } }; *)
(*             AMOUNT; *)
(*             PUSH mutez 0; *)
(*             COMPARE; *)
(*             EQ; *)
(*             IF { PAIR; PAIR; NIL operation; PAIR } *)
(*                { SWAP; FAILWITH } } *)
(*           { FAILWITH } }". *)
(* End raw. *)

Module source.
  Definition contract_file_M :=
    main.contract_file_M did_manager_string.did_manager_string 15.

  Definition contract_file := Eval cbv in (error.extract contract_file_M I).

  (* Definition contract_file_michelson_M := *)
  (*   main.contract_file_M did_manager_michelson_string.did_manager_michelson_string 30. *)

  (* Definition contract_file_michelson := Eval cbv in (error.extract contract_file_michelson_M I). *)
End source.

Module annots.
  Import String.
  Definition rotateAuthentication : string := "%rotateAuthentication".
  Definition rotateOwner : string := "%rotateOwner".
  Definition rotateService : string := "%rotateService".
End annots.

Definition parameter_ty :=
  (or
    (or
      address
      (Some annots.rotateAuthentication)
      address
      (Some annots.rotateOwner))
    None
    (pair string string)
    (Some annots.rotateService)).

Module did_manager(C:ContractContext).

  (* (pair (pair (big_map %metadata string bytes) (address %owner)) *)
  (*       (pair (pair %service (string %endpoint) (string %type_)) *)
  (*             (address %verification_method))). *)
Definition storage_ty :=
  (pair (pair (big_map string bytes) address)
        (pair (pair string string) address)).

Definition did_manager : full_contract _ parameter_ty None storage_ty :=
  Eval cbv in contract_file_code source.contract_file.

(* Definition did_manager_michelson : full_contract _ parameter_ty None storage_ty := *)
(*   Eval cbv in contract_file_code source.contract_file_michelson. *)


Module semantics := Semantics C. Import semantics.

Definition did_manager_spec_helper
           (env : @proto_env (Some (parameter_ty, None)))
           (metadata : data (big_map string bytes))
           (owner : data address)
           (endpoint : data string)
           (type_ : data string)
           (verification_method : data address)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  let storage : data storage_ty :=
    ((metadata, owner),
          ((endpoint, type_), verification_method)) in

  negb (comparison_to_int (address_compare (sender env) owner) =? 0)%Z = false /\
  (comparison_to_int (tez.compare (amount env) (0 ~Mutez)) >? 0)%Z = false /\
  match param with
  | inl (inl rotateAuth) =>
      (nil, (metadata, owner, (endpoint, type_, rotateAuth)), tt) =
      (returned_operations, new_storage, tt)
  | inl (inr rotateOwner) =>
      (nil, (metadata, rotateOwner, (endpoint, type_, verification_method)), tt) =
      (returned_operations, new_storage, tt)
  | inr rotateService =>
      (nil, (metadata, owner, (rotateService, verification_method)), tt) =
      (returned_operations, new_storage, tt)
  end.

Lemma did_manager_spec_helper_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (metadata : data (big_map string bytes))
      (owner : data address)
      (endpoint : data string)
      (type_ : data string)
      (verification_method : data address)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  let storage : data storage_ty :=
    ((metadata, owner),
          ((endpoint, type_), verification_method)) in
  eval_seq env did_manager (100 + fuel) ((param, storage), tt) =
    Return ((returned_operations, new_storage), tt)
  <-> did_manager_spec_helper env metadata owner endpoint type_ verification_method
    param new_storage returned_operations.
Proof.
  intro Hfuel.
  remember (100 + fuel) as fuel2.
  assert (100 <= fuel2) by lia.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  unfold did_manager_spec_helper.
  destruct param as [[rotateAuth | rotateOwner] | rotateService];
  (do 3 (more_fuel; simpl); reflexivity).
Qed.

(* Lemma did_manager_spec_helper_correct_2 *)
(*       (env : @proto_env (Some (parameter_ty, None))) *)
(*       (metadata : data (big_map string bytes)) *)
(*       (owner : data address) *)
(*       (endpoint : data string) *)
(*       (type_ : data string) *)
(*       (verification_method : data address) *)
(*       (param : data parameter_ty) *)
(*       (new_storage : data storage_ty) *)
(*       (returned_operations : data (list operation)) *)
(*       (fuel : Datatypes.nat) : *)
(*   let storage : data storage_ty := *)
(*     ((metadata, owner), *)
(*           ((endpoint, type_), verification_method)) in *)
(*   eval_seq env did_manager_michelson (100 + fuel) ((param, storage), tt) = *)
(*     Return ((returned_operations, new_storage), tt) *)
(*   <-> did_manager_spec_helper env metadata owner endpoint type_ verification_method *)
(*     param new_storage returned_operations. *)
(* Proof. *)
(*   intro Hfuel. *)
(*   remember (100 + fuel) as fuel2. *)
(*   assert (100 <= fuel2) by lia. *)
(*   rewrite return_precond. *)
(*   rewrite eval_seq_precond_correct. *)
(*   unfold eval_seq_precond. *)
(*   unfold did_manager_spec_helper. *)

(*   assert (H_negb : forall x, negb x = false <-> x = true). *)
(*   { *)
(*     intro x; destruct x; simpl; split; intro H_x; congruence. *)
(*   } *)

(* (1*   Search (negb _ = _). *1) *)
(* (1*   Search eq negb. *1) *)

(*   destruct param as [[rotateAuth | rotateOwner] | rotateService]; *)
(*       idtac. *)

(*     (1* (do 5 (more_fuel; simpl); repeat rewrite H_negb; reflexivity). *1) *)


(*   1: { *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)

(*     repeat rewrite H_negb. *)


(*     split; intro H_x. *)
(*     + clear Heqfuel2; clear H. *)
(*       repeat match goal with *)
(*       | H_x : _ /\ _ |- _ => destruct H_x *)
(*       | H_x : _ = _ |- _ => inversion H_x; destruct H_x *)
(*       | |- (let (x, y) := ?z in _) => destruct z *)
(*       end. *)
(*       congruence. *)
(*       tauto. *)
(*     + repeat match goal with *)
(*       | H_x : (let (x, y) := ?z in _) |- _ => destruct z *)
(*       | H_x : _ /\ _ |- _ => destruct H_x *)
(*       end; *)
(*       repeat split; try congruence; *)
(*       repeat f_equal; intuition. *)

(*     split; intro H; *) 
    

(*     (1* rewrite and_iff_compat_l. *1) *)

(*     (1* rewrite <- (and_iff_compat_l (sender env = owner)). *1) *)
(*     (1* rewrite <- and_iff_compat_l. *1) *)
(*     (1* Search iff ( _ /\ _). *1) *)
(*     (1* Check and_pair_eq. *1) *)
(*     (1* Check and_left. *1) *)


(*     reflexivity. *)
(*     _ *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)
(*     do 1 (more_fuel; simpl). *)

(*     _ *)
(*   } *)

(*   (do 4 (more_fuel; simpl)). *)
(*   (do 3 (more_fuel; simpl); intuition). *)
(* Qed. *)

Definition did_manager_spec
           (env : @proto_env (Some (parameter_ty, None)))
           (metadata : data (big_map string bytes))
           (owner : data address)
           (endpoint : data string)
           (type_ : data string)
           (verification_method : data address)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  let storage : data storage_ty :=
    ((metadata, owner),
    ((endpoint, type_),
      verification_method)) in

  match new_storage with
  | ((new_metadata, new_owner),
    ((new_endpoint, new_type_),
      new_verification_method)) =>

    sender env = owner /\

    (* amount env = (0 ~Mutez) /\ *)
    (int64bv.to_Z (tez.to_int64 (amount env)) <= 0)%Z /\

    returned_operations = nil /\
    new_metadata = metadata /\

    match param with
    | inl (inl rotateAuth) =>
        new_owner = owner /\
        new_endpoint = endpoint /\
        new_type_ = type_ /\
        new_verification_method = rotateAuth
    | inl (inr rotateOwner) =>
        new_owner = rotateOwner /\
        new_endpoint = endpoint /\
        new_type_ = type_ /\
        new_verification_method = verification_method
    | inr (rotateEndpoint, rotateType_) =>
        new_owner = owner /\
        new_endpoint = rotateEndpoint /\
        new_type_ = rotateType_ /\
        new_verification_method = verification_method
    end
  end.


Section case_compare_lemmas.

Definition case_compare_Eq ty (s1 s2 : comparable_data ty) :
  sumbool
    ( compare ty s1 s2 = Eq /\ s1 = s2 )
    ( compare ty s1 s2 <> Eq /\ s1 <> s2 ).
Proof.
  pose proof (compare_diff ty s1 s2).
  destruct (compare ty s1 s2) eqn:Hcmp; intuition (try apply compare_eq_iff; congruence).
Qed.

Definition case_string_compare_Eq (s1 s2 : str) :
  sumbool
    ( string_compare s1 s2 = Eq /\ s1 = s2 )
    ( string_compare s1 s2 <> Eq /\ s1 <> s2 ).
Proof.
  replace string_compare with (compare string) by reflexivity.
  apply case_compare_Eq.
Qed.

Definition case_tez_compare_Eq (s1 s2 : tez.mutez) :
  sumbool
    ( tez.compare s1 s2 = Eq /\ s1 = s2 )
    ( tez.compare s1 s2 <> Eq /\ s1 <> s2 ).
Proof.
  replace tez.compare with (compare mutez) by reflexivity.
  apply case_compare_Eq.
Qed.

Definition case_address_compare_Eq (s1 s2 : address_constant) :
  sumbool
    ( address_compare s1 s2 = Eq /\ s1 = s2 )
    ( address_compare s1 s2 <> Eq /\ s1 <> s2 ).
Proof.
  replace address_compare with (compare address) by reflexivity.
  apply case_compare_Eq.
Qed.

Lemma address_compare_iff (a1 a2 : data address) :
  negb (comparison_to_int (address_compare a1 a2) =? 0)%Z = false <->
  a1 = a2.
Proof.
  destruct (case_address_compare_Eq a1 a2) as
    [(str_cmp_eq & str_eq) | (str_cmp_neq & str_neq)].
  - rewrite str_cmp_eq; tauto.
  - destruct (address_compare a1 a2); intuition.
Qed.

End case_compare_lemmas.


Lemma tez_not_gt_0 (a1 : tez.mutez) :
  (comparison_to_int (tez.compare a1 (0 ~Mutez)) >? 0)%Z = false <->
  (int64bv.to_Z (tez.to_int64 a1) <= 0)%Z.
Proof.
  destruct (case_tez_compare_Eq a1 (0 ~Mutez)) as
    [(str_cmp_eq & str_eq) | (str_cmp_neq & str_neq)].
  - rewrite str_cmp_eq; simpl.
    rewrite tez.compare_eq_iff in str_cmp_eq.
    apply (f_equal (fun x => int64bv.to_Z (tez.to_int64 x))) in str_cmp_eq.
    replace (int64bv.to_Z (tez.to_int64 (0 ~Mutez)))
       with (0%Z) in str_cmp_eq.
    + intuition.
    + unfold tez.to_int64.
      match goal with
      | |- _ = int64bv.to_Z (int64bv.of_Z_safe 0 ?H) =>
        rewrite (int64bv.of_Z_to_Z_eqv 0 (int64bv.of_Z_safe 0 H));
        rewrite (int64bv.of_Z_safe_is_of_Z 0 H)
      end.
      reflexivity.
  - pose (cmp := tez.compare a1 (0 ~Mutez)).
    assert (cmp_eq : tez.compare a1 (0 ~Mutez) = cmp) by reflexivity.
    rewrite cmp_eq.
    destruct cmp; try intuition.

    unfold tez.compare in cmp_eq.
    unfold tez.to_int64 in cmp_eq |- *.
    unfold int64bv.int64_compare in cmp_eq.
    unfold int64bv.compare in cmp_eq.
    rewrite Z.compare_lt_iff in cmp_eq.

    match goal with
    | cmp_eq : (_ < ?x)%Z |- _ =>
        assert (x_eq : x = 0%Z)
    end.
    + match goal with
      | |- int64bv.to_Z (int64bv.of_Z_safe 0 ?H) = _ =>
        rewrite (int64bv.of_Z_to_Z_eqv 0 (int64bv.of_Z_safe 0 H));
        rewrite (int64bv.of_Z_safe_is_of_Z 0 H)
      end; reflexivity.
    + congruence.
Qed.


Lemma did_manager_spec_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (metadata : data (big_map string bytes))
      (owner : data address)
      (endpoint : data string)
      (type_ : data string)
      (verification_method : data address)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  let storage : data storage_ty :=
    ((metadata, owner),
          ((endpoint, type_), verification_method)) in
  eval_seq env did_manager (100 + fuel) ((param, storage), tt) =
    Return ((returned_operations, new_storage), tt)
  <-> did_manager_spec env metadata owner endpoint type_ verification_method
    param new_storage returned_operations.
Proof.
  Arguments Nat.add : simpl never.
  simpl.
  Arguments Nat.add : simpl nomatch.

  rewrite did_manager_spec_helper_correct.
  unfold did_manager_spec_helper.
  unfold did_manager_spec.

  rewrite address_compare_iff, tez_not_gt_0.


  destruct param as [[rotateAuth | rotateOwner] | rotateService].

  - split; intro H.
    + repeat match goal with
      | H : _ /\ _ |- _ => destruct H
      | H : _ = _ |- _ => inversion H; destruct H
      | |- (let (x, y) := ?z in _) => destruct z
      end;
      tauto.
    + repeat match goal with
      | H : (let (x, y) := ?z in _) |- _ => destruct z
      | H : _ /\ _ |- _ => destruct H
      end;
      repeat split; try congruence;
      repeat f_equal; intuition.

  - split; intro H.
    + repeat match goal with
      | H : _ /\ _ |- _ => destruct H
      | H : _ = _ |- _ => inversion H; destruct H
      | |- (let (x, y) := ?z in _) => destruct z
      end;
      tauto.
    + repeat match goal with
      | H : (let (x, y) := ?z in _) |- _ => destruct z
      | H : _ /\ _ |- _ => destruct H
      end;
      repeat split; try congruence;
      repeat f_equal; intuition.

  - split; intro H.
    + repeat match goal with
      | H : _ /\ _ |- _ => destruct H
      | H : _ = _ |- _ => inversion H; destruct H
      | |- (let (x, y) := ?z in _) => destruct z
      end;
      tauto.
    + repeat match goal with
      | H : (let (x, y) := ?z in _) |- _ => destruct z
      | H : _ /\ _ |- _ => destruct H
      end;
      repeat split; try congruence;
      repeat f_equal; intuition.
Qed.

      (* ______ *)

  (* _____ *)

  (* - *)


      (* f_equal; intuition. *)
      (* split; try congruence. *)
      (* intuition tauto. *)
      (* repeat match goal with *)
      (* | H : _ = _ |- _ => inversion H; destruct H *)
      (* end. *)
      (* tauto. *)
      (* (1* repeat match goal with *1) *)
      (* (1* | H : _ /\ _ |- _ => destruct H *1) *)
      (* (1* end. *1) *)
      (* (1* destruct H. *1) *)
    (* rewrite <- (and_iff_compat_l (sender env = owner)). *)
    (* rewrite <- and_iff_compat_l. *)
    (* Search iff ( _ /\ _). *)
    (* Check and_pair_eq. *)
    (* Check and_left. *)
    (* Check and_left. *)
    (* refine (iff_trans (and_left eq_refl (iff_refl _)) _). *)
    (* refine (iff_trans (and_left eq_refl (iff_refl _)) _). *)
    (* Search *) 
    (* Search compare. *)
    (* _ *)

  (* (1* Search (let (x, y) := _ in _). *1) *)
  (* _ *)

  (* let (new_metadata_and_owner, new_endpoint_and_verification_method) := new_storage in *)
  (* let (new_metadata, new_owner) := new_metadata_and_owner in *)
  (* let (new_endpoint_and_type, new_verification_method) := new_endpoint_and_verification_method in *)
  (* let (new_endpoint, new_type_) *) 

  (* let ((new_metadata, new_owner), ((new_endpoint, new_type_), new_verification_method)) := new_storage in *)
  (* let ((new_metadata, new_owner), ((new_endpoint, new_type_), new_verification_method)) := new_storage in *)





End did_manager.

(* Check TODO_simplify_raw_spec. *)





(*     Arguments compare : simpl never.    (1* do not unfold compare *1) *)
(*     Arguments tez.mutez : simpl never. *)
(*     Arguments comparable_data : simpl never. *)
(*     Arguments simple_comparable_data : simpl never. *)
(*     Arguments data_to_comparable_data : simpl never. *)
(*     Arguments concrete_data_to_data : simpl never. *)

(*     Arguments int64bv.of_Z_safe : simpl never. *)
(*     (1* Arguments Comparable_constant : simpl never. *1) *)

(*     (1* Locate "~". *1) *)
(*     (1* Search Mutez. *1) *)
(*     (1* :Notation "n ~mutez" := (Comparable_constant mutez (n ~Mutez)) (at level 100). *1) *)


(*     Opaque int64bv.int64. *)
(*     Opaque tez.mutez. *)

(*     (1* Print data_to_comparable_data. *1) *)
(*     (1* Print simple_comparable_data. *1) *)
(*     (1* Search simple_comparable_type. *1) *)
(*     (1* Print Comparable_type_simple. *1) *)
(*     (1* Print Comparable_type_simpl. *1) *)


(*     (1* Print tez.mutez. *1) *)
(*     (1* Print simple_comparable_data. *1) *)
(*     (1* Search mutez. *1) *)
(*     (1* simpl. *1) *)

(*     destruct env. *)
(*     simpl. *)

(*     (1* do 1 (more_fuel; simpl). *1) *)
(*     do 3 (more_fuel; simpl). *)

(*     _ *)

(*     fold (int64bv.of_Z_safe 0 eq_refl). *)
(*     fold (0 ~Mutez). *)

(*     Transparent tez.mutez. *)
(*     fold tez.mutez. *)
(*     fold tez.mutez. *)

(*     _ *)
(*     fold tez.mutez. *)

(*     _ *)
(*     simpl. *)
(*     Arguments compare : simpl nomatch.  (1* unfold if extra simplification is possible *1) *)


(*     Check compare. *)
(*     Locate eval_seq_precond. *)
(*     Locate compare. *)
(*     Search mutez. *)
(*     Search COMPARE. *)
(*     Print eval_seq_precond_body_aux. *)
(*     Print eval_seq_precond_body. *)
(*     Print eval_precond. *)
(*     Print eval_seq_precond. *)
(*     simpl. *)
(*     _ *)
(*   } *)

