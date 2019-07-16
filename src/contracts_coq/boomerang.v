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

Require Import Michocoq.macros.
Import syntax.
Import comparable.
Require Import ZArith.
Require Import semantics.
Require Import util.
Import error.
Require List.

Definition parameter_ty := unit.
Definition storage_ty := unit.

Module boomerang(C:ContractContext).
Module semantics := Semantics C. Import semantics.

Definition boomerang : full_contract _ parameter_ty None storage_ty :=
  (
    CDR ;;
    NIL operation ;;
       AMOUNT;;
       PUSH mutez (0 ~mutez);;
       IFCMPEQ NOOP
         (
           SOURCE ;;
           CONTRACT None unit ;;
           ASSERT_SOME ;;
           AMOUNT ;;
           UNIT ;;
           TRANSFER_TOKENS ;;
           CONS
         );;
       PAIR
  ).

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
  - intros Hf He.
    rewrite <- eqb_eq in He.
    congruence.
  - intro Hneq.
    rewrite <- eqb_eq in Hneq.
    destruct ((comparison_to_int (compare a c1 c2) =? 0)%Z); congruence.
Qed.

Lemma boomerang_correct :
  forall env (ops : data (list operation)) (fuel : Datatypes.nat),
  fuel >= 42 ->
  eval env boomerang fuel ((tt, tt), tt) = Return ((ops, tt), tt)
  <->
  (amount env = (0 ~Mutez) /\ ops = nil) \/
  (amount env <> (0 ~Mutez) /\
    exists ctr, contract_ env None unit (source env) = Some ctr /\
           ops = ((transfer_tokens env unit tt (amount env) ctr) :: nil)%list).
Proof.
  intros env ops fuel Hfuel.
  rewrite return_precond.
  unfold eval.
  rewrite eval_precond_correct.
  unfold ">=" in Hfuel.
  repeat (more_fuel ; simpl).
  rewrite destruct_if.
  apply or_both; apply and_both_0.
  - rewrite (eqb_eq mutez).
    intuition.
  - intuition congruence.
  - rewrite bool_not_false.
    rewrite (eqb_eq mutez).
    intuition.
  - pose (c := contract_ env None unit (source env)).
    pose (transfer := transfer_tokens env unit tt (amount env)).
    change (match c with Some b => ((transfer b :: nil)%list, tt, tt) = (ops, tt, tt) | None => False end <-> (exists ctr, c = Some ctr /\ ops = (transfer ctr :: nil)%list)).
    destruct c.
    + split.
      * intro H.
        exists d.
        intuition congruence.
      * intros (c, (Hc, Hops)).
        injection Hc; clear Hc.
        intro; subst.
        reflexivity.
    + split; [contradiction|].
      intros (c, (Habs, _)).
      discriminate.
Qed.

End boomerang.
