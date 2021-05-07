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
Require Import entrypoints.
Import error.
Require List.


Definition parameter_ty := (ep_node (ep_leaf unit) None (ep_leaf mutez) None).
Definition storage_ty := address.

Module deposit(C:ContractContext).

Module semantics := Semantics C. Import semantics.

Open Scope michelson_scope.

Definition deposit : full_contract _ parameter_ty None storage_ty :=
  {
    DUP; CAR; DIP1 { CDR };
    IF_LEFT
      { DROP1; (NIL operation) }
      { DIP1 { DUP; DUP;
               SENDER; COMPARE;
               EQ; IF_TRUE {} { FAILWITH (a := address) I };
               (CONTRACT None unit I); IF_NONE { FAILWITH (a := address) I } {} };
        PUSH unit Unit; TRANSFER_TOKENS (p := unit) I;
        (NIL operation); SWAP; CONS };
    PAIR }.

Lemma deposit_correct :
  forall (env : @proto_env (Some (parameter_ty, None)))
         (input : data (or unit mutez)) storage_in
         (ops : data (list operation)) storage_out
         (fuel : Datatypes.nat),
  fuel >= 42 ->
  eval_seq env deposit fuel ((input, storage_in), tt) = Return ((ops, storage_out), tt)
  <->
  (storage_in = storage_out /\
   match input with
   | inl tt => ops = nil
   | inr am => (storage_in = sender env /\
                exists c : data (contract unit),
                  contract_ None unit I storage_in = Some c /\
                  ops = cons (transfer_tokens unit I tt am c) nil)
   end).
Proof.
  intros env input storage_in ops storage_out fuel Hfuel.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  unfold ">=" in Hfuel.
  unfold eval_seq_precond.
  do 5 (more_fuel ; simpl).
  destruct input as [[]|am].
  - unfold data; simpl. intuition congruence.
  - rewrite (eqb_eq address).
    split.
    + intros (Hsender, (y, (Hy, H))).
      injection H; clear H; intros; subst.
      repeat (split; try reflexivity).
      exists y; intuition.
    + intros (Hout, (Hsender, (y, (Hy, Hops)))).
      subst.
      split; try reflexivity.
      exists y; intuition.
Qed.

End deposit.

