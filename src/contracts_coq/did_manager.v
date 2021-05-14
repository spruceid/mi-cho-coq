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

Module source.
  Definition contract_file_M :=
    main.contract_file_M did_manager_string.did_manager_string 15.

  Definition contract_file := Eval cbv in (error.extract contract_file_M I).
End source.

Module annots.
  Import String.
  Definition rotateAuthentication : string := "%auth".
  Definition rotateOwner : string := "%owner".
  Definition rotateService : string := "%service".
End annots.

Definition parameter_ty :=
  (or
    address
    (Some annots.rotateOwner)
    (or
      address
      (Some annots.rotateAuthentication)
      (pair string string)
      (Some annots.rotateService))
    None).

Module did_manager(C:ContractContext).

  (* (pair (pair (big_map %metadata string bytes) (address %owner)) *)
  (*       (pair (pair %service (string %endpoint) (string %type_)) *)
  (*             (address %verification_method))). *)
Definition storage_ty :=
  (pair (pair (big_map string bytes) address)
        (pair (pair string string) address)).

Definition did_manager : full_contract _ parameter_ty None storage_ty :=
  Eval cbv in contract_file_code source.contract_file.

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
  | inl rotateOwner =>
      (nil, (metadata, rotateOwner, (endpoint, type_, verification_method)), tt) =
      (returned_operations, new_storage, tt)
  | inr (inl rotateAuth) =>
      (nil, (metadata, owner, (endpoint, type_, rotateAuth)), tt) =
      (returned_operations, new_storage, tt)
  | inr (inr rotateService) =>
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

    (int64bv.to_Z (tez.to_int64 (amount env)) <= 0)%Z /\

    returned_operations = nil /\
    new_metadata = metadata /\

    match param with
    | inl rotateOwner =>
        new_owner = rotateOwner /\
        new_endpoint = endpoint /\
        new_type_ = type_ /\
        new_verification_method = verification_method
    | inr (inl rotateAuth) =>
        new_owner = owner /\
        new_endpoint = endpoint /\
        new_type_ = type_ /\
        new_verification_method = rotateAuth
    | inr (inr (rotateEndpoint, rotateType)) =>
        new_owner = owner /\
        new_endpoint = rotateEndpoint /\
        new_type_ = rotateType /\
        new_verification_method = verification_method
    end
  end.

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

  destruct param as [rotateOwner | [rotateAuth | (rotateEndpoint & rotateType)]].

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
      end.
      repeat split; try congruence;
      repeat f_equal; intuition.
Qed.

End did_manager.

