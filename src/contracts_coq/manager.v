(* Open Source License *)
(* Copyright (c) 2019 Nomadic Labs. <contact@nomadic-labs.com> *)

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


Require Import String.
Require Import Michocoq.macros.
Import syntax.
Import comparable.
Require Import NArith.
Require Import semantics.
Require Import util.
Import error.
Require List.

Section manager.

Definition parameter_ty := option (or (pair key_hash mutez) (or key_hash (or unit key_hash))).

Context {get_contract_type : contract_constant -> error.M type} {env : @proto_env get_contract_type parameter_ty}.

Definition instruction := @syntax.instruction get_contract_type parameter_ty.
Definition data := @semantics.data get_contract_type parameter_ty.
Definition stack := @semantics.stack get_contract_type parameter_ty.
Definition eval {A B : stack_type} := @semantics.eval _ _ env A B.
Definition eval_precond := @semantics.eval_precond _ _ env.
Definition full_contract := @syntax.full_contract get_contract_type.

Definition storage_ty := key_hash.

Definition manager : full_contract parameter_ty storage_ty :=
  (UNPAIR ;;
   IF_SOME (
   DUUP ;;
   IMPLICIT_ACCOUNT ;; ADDRESS ;;
   SENDER ;;
   IFCMPNEQ (a := address)
     (SENDER ;; PUSH string (String_constant "Only the owner can operate.") ;; PAIR ;; FAILWITH)
     (DIP (NIL operation) ;;
      IF_LEFT
        (DUP ;; DIP (CAR ;; IMPLICIT_ACCOUNT) ;; CDR ;; UNIT ;; TRANSFER_TOKENS ;; CONS ;; PAIR)
        (IF_LEFT
           (SOME ;; SET_DELEGATE ;; CONS ;; PAIR)
           (IF_LEFT
              (DROP ;; NONE key_hash ;; SET_DELEGATE ;; CONS ;; PAIR)
              (DIIP DROP;; SWAP ;; PAIR)))))
   (NIL operation;; PAIR)).

Definition manager_spec
           (storage : data storage_ty)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  match param with
  | None => new_storage = storage /\ returned_operations = nil
  | Some param =>
    sender env = address_ env unit (implicit_account env storage) /\
    match param with
    | inl (destination, amount) =>
      new_storage = storage /\ returned_operations = (transfer_tokens env unit tt amount (implicit_account env destination) :: nil)%list
    | inr (inl new_delegate) =>
      new_storage = storage /\ returned_operations = (set_delegate env (Some new_delegate) :: nil)%list
    | inr (inr (inl tt)) =>
      new_storage = storage /\ returned_operations = (set_delegate env None :: nil)%list
    | inr (inr (inr new_manager)) =>
      new_storage = new_manager /\ returned_operations = nil
    end
  end.

Lemma eqb_eq a c1 c2 :
  BinInt.Z.eqb (comparison_to_int (compare a c1 c2)) Z0 = true <->
  c1 = c2.
Proof.
  rewrite BinInt.Z.eqb_eq.
  rewrite comparison_to_int_Eq.
  apply comparable.compare_eq_iff.
Qed.

Lemma eqb_neq a c1 c2 :
  BinInt.Z.eqb (comparison_to_int (compare a c1 c2)) Z0 = false <->
  c1 <> c2.
Proof.
  split.
  - intros H He.
    apply eqb_eq in He.
    congruence.
  - intro Hneq.
    rewrite <- eqb_eq in Hneq.
    generalize (BinInt.Z.eqb (comparison_to_int (compare a c1 c2)) Z0) Hneq.
    intros []; congruence.
Qed.

Lemma and_right {P Q R : Prop} : P -> (Q <-> R) -> (Q <-> (P /\ R)).
Proof.
  intuition.
Qed.

Lemma manager_correct
      (storage : data storage_ty)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  fuel >= 42 ->
  eval manager fuel ((param, storage), tt) = Return _ ((returned_operations, new_storage), tt)
  <-> manager_spec storage param new_storage returned_operations.
Proof.
  intro Hfuel.
  unfold ">=" in Hfuel.
  unfold eval.
  rewrite return_precond.
  rewrite eval_precond_correct.
  unfold manager_spec.
  do 5 (more_fuel; simplify_instruction).
  destruct param as [param|].
  - do 4 (more_fuel; simplify_instruction).
    case_eq (BinInt.Z.eqb (comparison_to_int (address_compare (sender env) (address_ env unit (implicit_account env storage)))) Z0).
    + intro Htrue.
      apply (eqb_eq address) in Htrue.
      apply and_right.

      * assumption.
      * simpl.
        do 3 (more_fuel; simplify_instruction).
        destruct param as [(destination, amount)|[new_delegate|[()|new_manager]]];
          repeat (more_fuel; simplify_instruction); intuition congruence.
    + intro Hfalse.
      apply (eqb_neq address) in Hfalse.
      simpl.
      repeat (more_fuel; simplify_instruction).
      split.
      * intros Hf; inversion Hf.
      * intros (H, _).
        contradiction.
  - intuition congruence.
Qed.

End manager.
