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
Require Import ProofIrrelevanceFacts.
Import syntax.
Import comparable.
Require Import ZArith.
Require Import semantics.
Require Import util.
Import error.
Require List.
Require tez.
Require int64.
Require map.


Definition parameter_ty := string.
Definition storage_ty := map string int.

Module ContractContext <: syntax.ContractContext.
  Axiom get_contract_type : contract_constant -> error.M type.
  Definition self_type := Comparable_type parameter_ty.
End ContractContext.
Module semantics := Semantics ContractContext. Import semantics.

Definition vote : full_contract parameter_ty storage_ty :=
  (
    AMOUNT;;
    PUSH mutez (5000000 ~mutez);;
    COMPARE;; GT;;
    IF ( FAIL ) ( NOOP );;
    DUP;; DIP ( CDR;; DUP );; CAR;; DUP;;
    DIP (
      GET (i := get_map string int);; ASSERT_SOME;;
      PUSH int (Int_constant 1%Z);; ADD (s := add_int_int);; SOME
    );;
    UPDATE (i := Mk_update string (option int) (map string int) (Update_variant_map string int));;
    NIL operation;; PAIR ).

Definition vote_spec
           (storage: data storage_ty)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  (* Preconditions *)
  (Z.ge (tez.to_Z (amount env)) 5000000) /\
  mem parameter_ty _ (Mem_variant_map _ int) param storage /\
  (* Postconditions *)
  (forall s, (mem _ _ (Mem_variant_map _ int) s storage) <->
        (mem _ _ (Mem_variant_map _ int) s new_storage)) /\
  returned_operations = nil /\
  match (get _ _ _ (Get_variant_map _ int) param storage) with
  | Some n1 => match (get _ _ _ (Get_variant_map _ int) param new_storage) with
              | Some n2 => n2 = (BinInt.Z.add n1 1)
              | None => False
              end
  | None => False end /\
  (forall s, s <> param ->
   match (get _ _ _ (Get_variant_map _ int) s storage) with
  | Some n1 => match (get _ _ _ (Get_variant_map _ int) s new_storage) with
              | Some n2 => n2 = n1
              | None => False
              end
  | None => True end).

Theorem vote_correct
      (storage : data storage_ty)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  fuel >= 42 ->
  eval vote fuel ((param, storage), tt) = Return _ ((returned_operations, new_storage), tt)
  <-> vote_spec storage param new_storage returned_operations.
Proof.
  intro Hfuel. unfold ">=" in Hfuel.
  unfold eval.
  rewrite return_precond.
  rewrite eval_precond_correct.
  do 15 (more_fuel; simplify_instruction).

  destruct (BinInt.Z.gtb
      (comparison_to_int
         (tez.compare
            (exist (fun t : int64.int64 => int64.sign t = false)
               (int64.of_Z 5000000) eq_refl) (amount env))) 0) eqn:gtamount.

  - (* Not enough tez sent to contract *)
    split; intros;
      unfold tez.compare, comparison_to_int in gtamount; simpl in gtamount.
    + inversion H.
    + unfold vote_spec in H. destruct H as [gtamountcontra _].
      destruct (int64.compare (int64.of_Z 5000000) (tez.to_int64 (amount env))) eqn:amount;
        try inversion gtamount.
      exfalso. clear gtamount. 
      unfold tez.to_Z in gtamountcontra.
      unfold tez.to_int64 in *. destruct (semantics.amount env) as [t _].
      apply Z.compare_ge_iff in gtamountcontra.
      apply gtamountcontra. clear gtamountcontra.
      unfold int64.compare, int64.of_Z, int64.to_Z at 1 in amount.
      rewrite Zdigits.Z_to_two_compl_to_Z in amount. assumption.
      simpl. omega. reflexivity.
  - (* Enough tez sent to contract *)
    destruct (map.get str Z string_compare param storage) eqn:mapget.
    + (* Key is in the map *)
      more_fuel; simplify_instruction.
      split; intros.
      * (* ->  *)
        unfold vote_spec; repeat split.
        { clear H. clear mapget.
          unfold tez.compare, tez.to_int64 in gtamount.
          unfold tez.to_Z. unfold tez.to_int64.
          destruct (amount env) as [t _].
          destruct (int64.compare (int64.of_Z 5000000) t) eqn:cp;
            unfold int64.compare in cp;
            simpl in gtamount; try inversion gtamount;
          unfold int64.compare, int64.of_Z, int64.to_Z at 1 in cp;
          rewrite Zdigits.Z_to_two_compl_to_Z in cp by (try (simpl; omega); try reflexivity);
          rewrite Z.ge_le_iff; unfold Z.le; rewrite cp; discriminate. }
        unfold get, semantics.get. simpl.
        apply map.map_getmem with z. assumption.
        { inversion H. intro Hstor.
          unfold get, semantics.get. simpl.
          apply map.map_updatemem. assumption. }
        { inversion H. intro Hnstor.
          unfold get, semantics.get in Hnstor. simpl in Hnstor.
          unfold get, semantics.get. simpl.
          destruct (string_compare s param) eqn:strcomp.
          rewrite string_compare_Eq_correct in strcomp; subst.
          apply map.map_getmem with z. assumption.
          eapply map.map_updatemem_rev with (k':= param).
          rewrite <- (compare_diff string). left. eassumption. eassumption.
          eapply map.map_updatemem_rev with (k':= param).
          rewrite <- (compare_diff string). right. eassumption. eassumption. }
        { inversion H. reflexivity. }
        { unfold get, semantics.get. simpl. rewrite mapget.
          inversion H.
          rewrite map.map_updateeq.
          destruct z; try destruct p; reflexivity. }
        { intros s Hneq. unfold get, semantics.get. simpl.
          inversion H.
          destruct (map.get str Z string_compare s storage) eqn:mapget2.
          rewrite map.map_updateneq.
          rewrite mapget2. reflexivity. intro contra. subst; contradiction.
          exact I. }
      * (* <- *)
        destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
        f_equal. f_equal. symmetry. assumption.
        symmetry. rewrite map.map_updateSome_spec. split. 
        clear H6. unfold get, semantics.get in H5; simpl in H5.
        destruct (map.get str Z string_compare param storage);
          destruct (map.get str Z string_compare param new_storage); subst;
            try inversion H5.
        inversion mapget; subst. rewrite BinInt.Z.add_comm. reflexivity.
        clear H5.
        intros s Hdiff. specialize (H6 s).
        assert (s <> param) as Hdiff2 by (intro contra; rewrite contra in Hdiff; contradiction);
        apply H6 in Hdiff2.
        unfold get, semantics.get in Hdiff2. simpl in Hdiff2.
        destruct (map.get str Z string_compare s storage) eqn:get1;
          destruct (map.get str Z string_compare s new_storage) eqn:get2; subst;
            try reflexivity.
        inversion Hdiff2.
        exfalso. clear H6.
        apply map.map_getmem in get2.
        unfold mem, semantics.mem in H3; simpl in H3.
        rewrite <- H3 in get2. apply map.map_memget in get2. destruct get2 as [v get2].
        rewrite get2 in get1. discriminate get1.
    + (* Key is not in the map *)
      more_fuel; simplify_instruction.
      split; intros.
      * (* -> *)
        inversion H.
      * (* <- *)
        destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
        apply map.map_memget in H2. destruct H2 as [v H2].
        simpl in H2. rewrite H2 in mapget. discriminate mapget.
Qed.