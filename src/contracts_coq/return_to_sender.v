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

Module ST : (SelfType with Definition self_type := parameter_ty).
  Definition self_type := parameter_ty.
End ST.

Module return_to_sender(C:ContractContext)(E:Env ST C).

Module semantics := Semantics ST C E. Import semantics.

Definition return_to_sender : full_contract storage_ty :=
  (
    CDR ;;
    NIL operation ;;
       AMOUNT;;
       PUSH mutez (0 ~mutez);;
       IFCMPEQ NOOP
         (
           SOURCE ;;
           CONTRACT unit ;;
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

Lemma return_to_sender_correct :
  forall (ops : data (list operation)) (fuel : Datatypes.nat),
  fuel >= 42 ->
  eval return_to_sender fuel ((tt, tt), tt) = Return _ ((ops, tt), tt)
  <->
  (amount env = (0 ~Mutez) /\ ops = nil) \/
  (amount env <> (0 ~Mutez) /\
    exists ctr, contract_ env unit (source env) = Some ctr /\
           ops = ((transfer_tokens env unit tt (amount env) ctr) :: nil)%list).
Proof.
  intros ops fuel Hfuel.
  rewrite return_precond.
  unfold eval.
  rewrite eval_precond_correct.
  unfold ">=" in Hfuel.
  do 8 (more_fuel ; simplify_instruction).
  fold (simple_compare mutez).
  fold (compare mutez).
  case_eq ((comparison_to_int (compare mutez (0 ~Mutez) (amount env)) =? 0)%Z).
  - (* true *)
    intro Heq.
    rewrite eqb_eq in Heq.
    do 1 (more_fuel ; simplify_instruction).
    split.
    + intro Hops.
      injection Hops.
      intro; subst ops.
      intuition.
    + intros [(Hl, Hops)|(Hr, _)].
      * destruct Hl; congruence.
      * symmetry in Heq.
        contradiction.
  - intro Hneq.
    rewrite eqb_neq in Hneq.
    do 7 (more_fuel ; simplify_instruction).
    destruct (contract_ env unit (source env)).
    + (* Some *)
      split.
      * intro H ; right; split.
        -- congruence.
        -- eexists ; intuition ; injection H.
           symmetry; assumption.
      * intros [(Habs, _)| (_, (ctr, (He, Hops)))].
        -- congruence.
        -- injection He; intro; subst d; subst ops; reflexivity.
    + (* None *)
      simplify_instruction. split.
      * intro H; inversion H.
      * intros [(Habs, _)|(ctr, (He, (Hops, _)))].
        -- congruence.
        -- discriminate.
Qed.

End return_to_sender.
