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
Require Import Lia.

Definition parameter_ty := or (lambda unit (list operation)) unit.
Definition storage_ty := key_hash.

Module ST : (SelfType with Definition self_type := parameter_ty).
  Definition self_type := parameter_ty.
End ST.

Module manager(C:ContractContext)(E:Env ST C).

Module semantics := Semantics ST C E. Import semantics.

Definition manager : full_contract storage_ty :=
  (UNPAIR ;;
   IF_LEFT
        (DUUP ;;
        IMPLICIT_ACCOUNT ;; ADDRESS ;;
        SENDER ;;
        IFCMPNEQ (a := address)
          (SENDER ;; PUSH string (String_constant "Only the owner can operate.") ;; PAIR ;; FAILWITH)
          (UNIT ;; EXEC ;; PAIR))
        (DROP ;; NIL operation ;; PAIR)).

Definition manager_spec
           (storage : data storage_ty)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation))
           (fuel : Datatypes.nat) :=
  match param with
  | inr tt =>
    (* %default: anybody can send tokens this does not modify the
    storage and produces no operation. *)
    new_storage = storage /\ returned_operations = nil
  | inl lam =>
    (* %do is only available to the stored manager. *)
    sender env = address_ env unit (implicit_account env storage) /\
    new_storage = storage /\
    eval lam fuel (tt, tt) = Return _ (returned_operations, tt)
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

Lemma fold_eval_precond fuel :
  eval_precond_body env (@semantics.eval_precond _ _ env fuel) =
  @semantics.eval_precond _ _ env (S fuel).
Proof.
  reflexivity.
Qed.


Lemma manager_correct
      (storage : data storage_ty)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  fuel >= 42 ->
  eval manager (12 + fuel) ((param, storage), tt) = Return _ ((returned_operations, new_storage), tt)
  <-> manager_spec storage param new_storage returned_operations fuel.
Proof.
  intro Hfuel.
  remember (12 + fuel) as fuel2.
  assert (30 <= fuel2) by lia.
  unfold eval.
  rewrite return_precond.
  rewrite eval_precond_correct.
  unfold manager_spec.
  do 5 (more_fuel; simplify_instruction).
  destruct param as [lam|].
  - do 4 (more_fuel; simplify_instruction).
    case_eq (BinInt.Z.eqb (comparison_to_int (address_compare (sender env) (address_ env unit (implicit_account env storage)))) Z0).
    + intro Htrue.
      apply (eqb_eq address) in Htrue.
      apply and_right.
      * assumption.
      * simpl.
        do 3 (more_fuel; simplify_instruction).
        repeat (more_fuel; simplify_instruction).
        simpl in Heqfuel2.
        assert (fuel = S fuel2) by lia.
        rewrite fold_eval_precond.
        subst fuel. clear Hfuel.
        simplify_instruction.
        rewrite fold_eval_precond.
        rewrite <- eval_precond_correct.
        rewrite precond_exists.
        unfold precond_ex.
        split.
        ++ intros ((ops, []), (Hops, Hs)).
           unfold eval.
           injection Hs; intros; subst.
           auto.
        ++ intros ([], Hlam).
           exists (returned_operations, tt).
           auto.
    + intro Hfalse.
      apply (eqb_neq address) in Hfalse.
      simpl.
      repeat (more_fuel; simplify_instruction).
      split.
      * intros Hf; inversion Hf.
      * intros (He, _).
        contradiction.
  - destruct d.
    intuition congruence.
Qed.

End manager.
