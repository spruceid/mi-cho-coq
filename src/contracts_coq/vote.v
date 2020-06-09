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
      PUSH int (Int_constant 1%Z); (ADD (s := add_int_int)); SOME
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

Lemma l1 a b : tez.compare a b = Z.compare (tez.to_Z a) (tez.to_Z b).
Proof.
  reflexivity.
Defined.

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
  unfold eval.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  do 3 (more_fuel; simpl).
  rewrite match_if_exchange.
  rewrite if_false_not.
  apply and_both_0.
  - change (tez.compare (5000000 ~Mutez) (amount env)) with
        (5000000 ?= (tez.to_Z (amount env)))%Z.
    rewrite Z.compare_antisym.
    unfold ">="%Z.
    destruct (tez.to_Z (amount env) ?= 5000000)%Z; simpl; intuition discriminate.
  - (* Enough tez sent to contract *)
    destruct (map.get str Z string_compare param storage) eqn:mapget.
    + (* Key is in the map *)
      split; intros.
      * (* ->  *)
        simpl in *.
        repeat split; inversion H.
        -- apply map.map_getmem with z; assumption.
        -- intro Hstor.
           apply map.map_updatemem.
           assumption.
        -- intro Hnstor.
           destruct (string_compare s param) eqn:strcomp.
           rewrite string_compare_Eq_correct in strcomp; subst.
           apply map.map_getmem with z. assumption.
           eapply map.map_updatemem_rev with (k':= param).
           rewrite <- (compare_diff string). left. eassumption. eassumption.
           eapply map.map_updatemem_rev with (k':= param).
           rewrite <- (compare_diff string). right. eassumption. eassumption.
        -- reflexivity.
        -- rewrite mapget.
           rewrite map.map_updateeq.
           destruct z; try destruct p; reflexivity.
        -- intros s Hneq.
           destruct (map.get str Z string_compare s storage) eqn:mapget2.
           rewrite map.map_updateneq.
           rewrite mapget2. reflexivity. intro contra. subst; contradiction.
           constructor.
      * (* <- *)
        repeat simpl.
        destruct H as [H1 [H2 [H3 [H4 H5]]]].
        repeat f_equal.
        -- symmetry. assumption.
        -- symmetry.
           rewrite map.map_updateSome_spec.
           split.
           ++ unfold get, semantics.get in H5; simpl in H5.
              simpl in *.
              destruct (map.get str Z string_compare param storage); destruct (map.get str Z string_compare param new_storage); subst;
                try inversion H4.
              inversion mapget; subst. rewrite BinInt.Z.add_comm. reflexivity.
           ++ simpl in *.
              clear H4.
              intros s Hdiff. specialize (H5 s).
              assert (s <> param) as Hdiff2 by (intro contra; rewrite contra in Hdiff; contradiction);
                apply H5 in Hdiff2.
              unfold get, semantics.get in Hdiff2. simpl in Hdiff2.
              destruct (map.get str Z string_compare s storage) eqn:get1;
                destruct (map.get str Z string_compare s new_storage) eqn:get2; subst;
                  try reflexivity.
              inversion Hdiff2.
              exfalso. clear H5.
              apply map.map_getmem in get2.
              rewrite <- H2 in get2. apply map.map_memget in get2. destruct get2 as [v get2].
              rewrite get2 in get1. discriminate get1.
  + (* Key is not in the map *)
    do 2 more_fuel; simpl.
               split; intros.
      * (* -> *)
        inversion H.
      * (* <- *)
        destruct H as [H1 [H2 [H3 [H4 H5]]]].
        apply map.map_memget in H1. destruct H1 as [v H1].
        simpl in H1. rewrite H1 in mapget. discriminate mapget.
Qed.

End vote.
