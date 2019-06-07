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
Require Import NArith.
Require Import semantics.
Require Import util.
Import error.
Require List.

Section boomerang.



Definition parameter_ty := unit.
Definition storage_ty := unit.

Context {get_contract_type : contract_constant -> error.M type} {env : @proto_env get_contract_type parameter_ty}.

Definition instruction := @syntax.instruction get_contract_type parameter_ty.
Definition data := @semantics.data get_contract_type parameter_ty.
Definition stack := @semantics.stack get_contract_type parameter_ty.
Definition eval {A B : stack_type} := @semantics.eval _ _ env A B.
Definition eval_precond := @semantics.eval_precond _ _ env.


Definition boomerang : @full_contract get_contract_type parameter_ty storage_ty :=
  (
    CDR ;;
    NIL operation ;;
    SOURCE ;;
    CONTRACT unit ;;
    ASSERT_SOME ;;
    AMOUNT ;;
    UNIT ;;
    TRANSFER_TOKENS ;;
    CONS ;;
    PAIR
  ).

Lemma boomerang_correct :
  forall (ops : data (list operation)) (fuel : Datatypes.nat),
  fuel >= 42 ->
  eval boomerang fuel ((tt, tt), tt) = Return _ ((ops, tt), tt)
  <-> exists ctr, contract_ env unit (source env) = Some ctr /\
           ops = ((transfer_tokens env unit tt (amount env) ctr) :: nil)%list.
Proof.
  intros ops fuel Hfuel.
  rewrite return_precond.
  unfold eval.
  rewrite eval_precond_correct.
  unfold ">=" in Hfuel.
  do 10 (more_fuel ; simplify_instruction).
  destruct (contract_ env unit (source env)).
  (* Some *)
  - split.
    + intro H ; eexists ; intuition ; injection H ; intuition.
    + intros (ctr, (He, Hops)). injection He ; intros Heq ; subst d. clear He. subst ops. reflexivity.
  (* None *)
  - simplify_instruction. split.
    + intro H; inversion H.
    + intros (ctr, (He, Hops)). discriminate.
Qed.

End boomerang.
