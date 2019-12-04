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


Definition parameter_ty := (or unit mutez).
Definition storage_ty := address.

Module deposit(C:ContractContext).

Module semantics := Semantics C. Import semantics.

Definition deposit : full_contract _ parameter_ty storage_ty :=
  ( DUP;; CAR;; DIP1 CDR;;
    IF_LEFT
      ( DROP1;; NIL operation )
      ( DIP1 ( DUP;;
               DUP;; SENDER;; COMPARE;; EQ;; IF NOOP FAILWITH;;
               CONTRACT unit;; IF_NONE FAILWITH NOOP);;
        PUSH unit Unit;; TRANSFER_TOKENS;;
        NIL operation;; SWAP;; CONS);;
    PAIR ).

Lemma deposit_correct :
  forall (env : @proto_env (Some parameter_ty))
         (input : data (or unit mutez)) storage_in
         (ops : data (list operation)) storage_out
         (fuel : Datatypes.nat),
  fuel >= 42 ->
  eval env deposit fuel ((input, storage_in), tt) = Return ((ops, storage_out), tt)
  <->
  (storage_in = storage_out /\
   match input with
   | inl tt => ops = nil
   | inr am => (storage_in = sender env /\
                exists c : data (contract unit),
                  contract_ env unit storage_in = Some c /\
                  ops = cons (transfer_tokens env unit tt am c) nil)
   end).
Proof.
  intros env input storage_in ops storage_out fuel Hfuel.
  rewrite return_precond.
  unfold eval.
  rewrite eval_precond_correct.
  unfold ">=" in Hfuel.
  do 5 (more_fuel ; simpl).
  destruct input as [[]|am].
  - do 2 (more_fuel ; simpl).
    intuition congruence.
  - do 11 (more_fuel ; simpl).
    rewrite if_false_is_and.
    rewrite (eqb_eq address).
    destruct (contract_ env unit storage_in).
    + split.
      * intros (Hsend, Hops).
        subst storage_in.
        injection Hops; intros; subst; clear Hops.
        do 2 (split; [reflexivity|]).
        exists d; split; reflexivity.
      * intros (Hstorage, (Hsend, (c, (Hcd, Hops)))).
        intuition congruence.
    + split.
      * intuition.
      * intros (_, (_, (c, (Habs, _)))).
        discriminate.
Qed.

End deposit.

