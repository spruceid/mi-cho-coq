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
Require Import ZArith.
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

Definition manager : full_contract _ ST.self_type storage_ty :=
  (UNPAIR ;;
   IF_LEFT
   ( (* 'do' entrypoint *)
     (* Assert no token was sent: *)
     (* to send tokens, the default entry point should be used *)
     PUSH mutez (0 ~mutez) ;;
     AMOUNT ;;
     ASSERT_CMPEQ ;;
     (* Assert that the sender is the manager *)
     DUUP ;;
     IMPLICIT_ACCOUNT ;;
     ADDRESS ;;
     SENDER ;;
     ASSERT_CMPEQ ;;
     (* Execute the lambda argument *)
     UNIT ;;
     EXEC ;;
     PAIR
   )
   ( (* 'default' entrypoint *)
     DROP1 ;;
     NIL operation ;;
     PAIR
   )
  ).

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
  | inl (existT _ _ lam) =>
    (* %do is only available to the stored manager and rejects non-null amounts*)
    amount env = (0 ~Mutez) /\
    sender env = address_ env unit (implicit_account env storage) /\
    new_storage = storage /\
    eval (no_self env) lam fuel (tt, tt) = Return (returned_operations, tt)
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

Lemma and_both {P Q R : Prop} : (Q <-> R) -> ((P /\ Q) <-> (P /\ R)).
Proof.
  intuition.
Qed.

Lemma fold_eval_precond fuel :
  @eval_precond_body (@semantics.eval_precond fuel) =
  @semantics.eval_precond (S fuel).
Proof.
  reflexivity.
Qed.

Lemma if_false_is_and (b : Datatypes.bool) P : (if b then P else false) <-> b = true /\ P.
Proof.
  destruct b.
  - intuition.
  - simpl.
    intuition discriminate.
Qed.

Lemma manager_correct
      (storage : data storage_ty)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  fuel >= 42 ->
  eval env manager (13 + fuel) ((param, storage), tt) = Return ((returned_operations, new_storage), tt)
  <-> manager_spec storage param new_storage returned_operations fuel.
Proof.
  intro Hfuel.
  remember (13 + fuel) as fuel2.
  assert (30 <= fuel2) by lia.
  rewrite return_precond.
  rewrite eval_precond_correct.
  unfold manager_spec.
  do 5 (more_fuel; simpl).
  destruct param as [(tff, lam)|[]].
  - do 5 (more_fuel; simpl).
    simpl.
    rewrite if_false_is_and.
    rewrite (eqb_eq mutez).
    apply and_both.
    do 5 (more_fuel; simpl).
    rewrite if_false_is_and.
    rewrite (eqb_eq address).
    apply and_both.
    simpl in Heqfuel2.
    repeat rewrite fold_eval_precond.
    assert (fuel = S (S fuel2)) by lia.
    subst fuel. clear Hfuel.
    rewrite <- eval_precond_correct.
    rewrite precond_exists.
    unfold precond_ex.
    split.
    ++ intros ((ops, []), (Hops, Hs)).
       injection Hs; intros; subst.
       auto.
    ++ intros ([], Hlam).
       exists (returned_operations, tt).
       auto.
  - simpl.
    intuition congruence.
Qed.

End manager.
