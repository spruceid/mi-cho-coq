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
  Definition rotateAuthentication : string := "%rotateAuthentication".
  Definition rotateService : string := "%rotateService".
End annots.

Definition parameter_ty :=
  (or (pair
         (pair address
               (pair (pair (pair bytes bytes)
                           (pair bytes key))
                     nat))
         signature)
      (Some annots.rotateAuthentication)
      (pair
         (pair (pair string string)
               (pair (pair (pair bytes bytes)
                           (pair bytes key))
                     nat))
         signature)
      (Some annots.rotateService)).

Module did_manager(C:ContractContext).

Definition storage_ty :=
    pair (pair (pair key (big_map string bytes))
               (pair nat (pair string string)))
         address.

Definition did_manager : full_contract _ parameter_ty None storage_ty :=
  Eval cbv in contract_file_code source.contract_file.

Module semantics := Semantics C. Import semantics.

Definition did_manager_spec
           (env : @proto_env (Some (parameter_ty, None)))
           (metadata : data (big_map string bytes))
           (active_key : data key)
           (rotation_count : data nat)
           (endpoint : data string)
           (type_ : data string)
           (verification_method : data address)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  let storage : data storage_ty :=
    ((active_key, metadata),
     (rotation_count, (endpoint, type_)),
     verification_method) in

  (* %rotateAuthentication: _ *)
  match param with
  | inl ((user, (((chain, digest), (next_digest, user_key)), count)), sig) =>
    negb
    (check_signature env active_key sig
      (pack env
          (pair
             (pair (pair (Comparable_type bytes) (Comparable_type bytes))
                (pair (Comparable_type bytes) key)) 
             (Comparable_type nat))
          (chain, digest, (next_digest, user_key), count))) = false /\
    negb
      (comparison_to_int
        (string_compare chain (pack env chain_id (chain_id_ env))) =? 0)%Z = false /\
    negb (comparison_to_int (count ?= rotation_count + 1)%N =? 0)%Z = false /\
    (nil, (user_key, metadata, (count, (endpoint, type_)), user), tt) =
      (returned_operations, new_storage, tt)

  (* %rotateService: _ *)
  | inr (((endpoint_param, type_param),
        (((current_chain, current_value_digest),
        (next_value_digest, public_key)), rotation_count_param)), sig) =>


    negb
      (check_signature env active_key sig
         (pack env
            (pair
               (pair (pair (Comparable_type bytes) (Comparable_type bytes))
                  (pair (Comparable_type bytes) key)) 
               (Comparable_type nat))
            (current_chain, current_value_digest,
            (next_value_digest, public_key), rotation_count_param))) = false /\
    negb
      (comparison_to_int
         (string_compare current_chain (pack env chain_id (chain_id_ env))) =? 0)%Z = false /\
    negb
      (comparison_to_int (rotation_count_param ?= rotation_count + 1)%N =? 0)%Z = false /\
    (nil, (active_key, metadata,
      (rotation_count_param, (endpoint_param, type_param
      )), verification_method), tt) =
      (returned_operations, new_storage, tt)
  end.

Lemma did_manager_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (metadata : data (big_map string bytes))
      (active_key : data key)
      (rotation_count : data nat)
      (endpoint : data string)
      (type_ : data string)
      (verification_method : data address)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  let storage : data storage_ty :=
    ((active_key, metadata),
     (rotation_count, (endpoint, type_)),
     verification_method) in
  eval_seq env did_manager (100 + fuel) ((param, storage), tt) =
    Return ((returned_operations, new_storage), tt)
  <-> did_manager_spec env metadata active_key rotation_count endpoint type_
        verification_method param new_storage returned_operations.
Proof.
  intro Hfuel.
  remember (100 + fuel) as fuel2.
  assert (100 <= fuel2) by lia.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  unfold did_manager_spec.
  destruct param as [authParams | serviceParams].
  - simpl.
    do 4 (more_fuel; simpl).
    destruct authParams as ((user & (((chain & digest) & (next_digest & user_key)) & count)) & sig).
    reflexivity.
  - simpl.
    do 4 (more_fuel; simpl).
    destruct serviceParams as (((endpoint_param & type_param) &
      (((current_chain & current_value_digest) &
      (next_value_digest & public_key)) & rotation_count_param)) & sig).
    reflexivity.
Qed.

End did_manager.


