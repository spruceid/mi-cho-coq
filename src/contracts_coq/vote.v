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
Require Import syntax macros semantics comparable util.
Require Import ZArith.
Import error.
Require List.
Require tez.
Require map.

Definition parameter_ty : type := string.
Definition storage_ty := map string int.
Module vote(C:ContractContext).
Module semantics := Semantics C. Import semantics.

Definition vote : full_contract _ parameter_ty None storage_ty :=
  {
    AMOUNT ;
    PUSH mutez (5000000 ~mutez);
    COMPARE; GT;
    IF_TRUE { FAIL } {};
    DUP; DIP1 { CDR; DUP }; CAR; DUP;
    DIP1 {
      (GET (i := get_map string int)); ASSERT_SOME;
      PUSH int (comparable_constant int 1%Z); (ADD (s := add_int_int)); SOME
    };
    (UPDATE (i := Mk_update string (option int) (map string int) (Update_variant_map string int)));
    (NIL operation); PAIR }.

Definition vote_spec
           (env : @proto_env (Some (parameter_ty, None)))
           (storage: data storage_ty)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  (* Preconditions *)
  (Z.ge (tez.to_Z (amount env)) 5000000) /\
  mem _ _ (Mem_variant_map _ int) param storage /\
  (* Postconditions *)
  (forall s, (mem _ _ (Mem_variant_map _ int) s storage) <->
        (mem _ _ (Mem_variant_map _ int) s new_storage)) /\
  returned_operations = nil /\
  (exists tally,
      get _ _ _ (Get_variant_map _ int) param storage = Some tally /\
      get _ _ _ (Get_variant_map _ int) param new_storage = Some (tally + 1)%Z) /\
  (forall s,
      s <> param ->
      get _ _ _ (Get_variant_map _ int) s new_storage =
      get _ _ _ (Get_variant_map _ int) s storage).

Lemma l1 a b : tez.compare a b = Z.compare (tez.to_Z a) (tez.to_Z b).
Proof.
  reflexivity.
Defined.

Opaque Z.add.

Theorem vote_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (storage : data storage_ty)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  fuel >= 42 ->
  eval_seq env vote fuel ((param, storage), tt) = Return ((returned_operations, new_storage), tt)
  <-> vote_spec env storage param new_storage returned_operations.
Proof.
  intro Hfuel. unfold ">=" in Hfuel.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  do 3 (more_fuel; simpl).
  apply and_both_0.
  - change (tez.compare (5000000 ~Mutez) (amount env)) with
        (5000000 ?= (tez.to_Z (amount env)))%Z.
    rewrite Z.compare_antisym.
    unfold ">="%Z.
    destruct (tez.to_Z (amount env) ?= 5000000)%Z; simpl; intuition discriminate.
  - (* Enough tez sent to contract *)
    simpl.
    split.
    + intros (tally, (Ht, H)).
      rewrite Ht.
      injection H; clear H; intros; subst.
      repeat split.
      * apply map.map_getmem with tally; assumption.
      * intro Hstor.
        apply map.map_updatemem.
        assumption.
      * intro Hnstor.
        destruct (string_compare s param) eqn:strcomp.
        rewrite string_compare_Eq_correct in strcomp; subst.
        apply map.map_getmem with tally. assumption.
        eapply map.map_updatemem_rev with (k':= param).
        rewrite <- (compare_diff string). left. eassumption. eassumption.
        eapply map.map_updatemem_rev with (k':= param).
        rewrite <- (compare_diff string). right. eassumption. eassumption.
      * exists tally.
        rewrite map.map_updateeq.
        rewrite Z.add_comm.
        split; reflexivity.
      * intros s Hs.
        rewrite map.map_updateneq; intuition.
    + (* <- *)
      intros (Hmemp, (Hmems, (Hops, ((tally, (Hp, Hpn)), Hs)))).
      exists tally.
      split; [assumption|].
      subst.
      repeat f_equal.
      symmetry.
      rewrite map.map_updateSome_spec.
      rewrite Z.add_comm.
      split; [assumption|].
      intuition.
Qed.

End vote.
