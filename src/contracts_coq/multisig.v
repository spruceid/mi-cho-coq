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

Definition action_ty := or (pair mutez (contract unit)) (or (option key_hash) (pair nat (list key))).

Definition parameter_ty := (pair
             (pair
                nat
                action_ty)
             (list (option signature))).

Definition storage_ty := pair nat (pair nat (list key)).

Module multisig(C:ContractContext).

Module semantics := Semantics C. Import semantics.

Definition ADD_nat {S} : instruction (Some parameter_ty) _ (nat ::: nat ::: S) (nat ::: S) := ADD.

Definition pack_ty := pair (pair chain_id address) (pair nat action_ty).

Definition multisig : full_contract _ parameter_ty storage_ty :=
  (
    UNPAIR ;; SWAP ;; DUP ;; DIP1 SWAP ;;
    DIP1
      (
        UNPAIR ;;
        DUP ;; SELF ;; ADDRESS ;; CHAIN_ID ;; PAIR ;; PAIR ;;
        PACK ;;
        DIP1 ( UNPAIR ;; DIP1 SWAP ) ;; SWAP
      ) ;;

    UNPAIR ;; DIP1 SWAP ;;
    ASSERT_CMPEQ ;;

    DIP1 SWAP ;; UNPAIR ;;
    DIP1
      (
        PUSH nat (nat_constant 0%N) ;; SWAP ;;
        ITER
          (
            DIP1 SWAP ;; SWAP ;;
            IF_CONS
              (
                IF_SOME
                  ( SWAP ;;
                    DIP1
                      (
                        SWAP ;; DIIP ( DIP1 DUP ;; SWAP ) ;;
                        CHECK_SIGNATURE ;; ASSERT ;;
                        PUSH nat (nat_constant 1%N) ;; ADD_nat))
                  ( SWAP ;; DROP1 )
              )
              (
                FAIL
              ) ;;
            SWAP
          )
      ) ;;
    ASSERT_CMPLE ;;
    DROP1 ;; DROP1 ;;

    DIP1 ( UNPAIR ;; PUSH nat (nat_constant 1%N) ;; ADD ;; PAIR ) ;;

    NIL operation ;; SWAP ;;
    IF_LEFT
      ( UNPAIR ;; UNIT ;; TRANSFER_TOKENS ;; CONS )
      ( IF_LEFT (SET_DELEGATE ;; CONS )
                ( DIP1 ( SWAP ;; CAR ) ;; SWAP ;; PAIR ;; SWAP )) ;;
    PAIR ).

Fixpoint check_all_signatures (sigs : Datatypes.list (Datatypes.option (data signature)))
         (keys : Datatypes.list (data key))
         (check_sig : data key -> data signature -> data bool) {struct keys} :=
  match sigs, keys with
  | nil, nil => true
  | nil, cons _ _ => false
  | cons _ _, nil => true
  | cons (Some sig) sigs, cons k keys =>
    andb (check_sig k sig) (check_all_signatures sigs keys check_sig)
  | cons None sigs, cons _ keys =>
    check_all_signatures sigs keys check_sig
  end.

Fixpoint count_signatures (sigs : Datatypes.list (Datatypes.option (data signature))) :=
  match sigs with
  | nil => 0%N
  | cons None sigs => count_signatures sigs
  | cons (Some _) sigs => (count_signatures sigs + 1)%N
  end.


Definition multisig_spec
           (env : @proto_env (Some parameter_ty))
           (counter : N)
           (action : data action_ty)
           (sigs : Datatypes.list (Datatypes.option (data signature)))
           (stored_counter : N)
           (threshold : N)
           (keys : Datatypes.list (data key))
           (new_stored_counter : N)
           (new_threshold : N)
           (new_keys : Datatypes.list (data key))
           (returned_operations : Datatypes.list (data operation)) :=
  let params : data parameter_ty := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  counter = stored_counter /\
  exists first_sigs remaining_sigs,
    sigs = (first_sigs ++ remaining_sigs)%list /\
    length first_sigs = length keys /\
    check_all_signatures
      first_sigs keys
      (fun k sig =>
         check_signature
           env k sig
           (pack env pack_ty ((chain_id_ env, address_ env parameter_ty (self env)),
                             (counter, action)))) /\
    (count_signatures first_sigs >= threshold)%N /\
    new_stored_counter = (1 + stored_counter)%N /\
    match action with
    | inl (amout, contr) =>
      new_threshold = threshold /\
      new_keys = keys /\
      returned_operations = (transfer_tokens env unit tt amout contr :: nil)%list
    | inr (inl kh) =>
      new_threshold = threshold /\
      new_keys = keys /\
      returned_operations = (set_delegate env kh :: nil)%list
    | inr (inr (nt, nks)) =>
      new_threshold = nt /\
      new_keys = nks /\
      returned_operations = nil
    end.

Definition multisig_head (then_ : instruction (Some parameter_ty) Datatypes.false (nat ::: list key ::: list (option signature) ::: bytes ::: action_ty ::: storage_ty ::: nil) (pair (list operation) storage_ty ::: nil)) :
  instruction _ _
              (pair parameter_ty storage_ty ::: nil)
              (pair (list operation) storage_ty ::: nil)
:=
    UNPAIR ;; SWAP ;; DUP ;; DIP1 SWAP ;;
    DIP1
      (
        UNPAIR ;;
        DUP ;; SELF ;; ADDRESS ;; CHAIN_ID ;; PAIR ;; PAIR ;;
        PACK ;;
        DIP1 ( UNPAIR ;; DIP1 SWAP ) ;; SWAP
      ) ;;

    UNPAIR ;; DIP1 SWAP ;;
    ASSERT_CMPEQ ;;

    DIP1 SWAP ;; UNPAIR ;; then_.

Definition multisig_head_spec
           (env : @proto_env (Some parameter_ty))
           (counter : N)
           (action : data action_ty)
           (sigs : Datatypes.list (Datatypes.option (data signature)))
           (stored_counter : N)
           (threshold : N)
           (keys : Datatypes.list (data key))
           (fuel : Datatypes.nat)
           (then_ :
              instruction _ Datatypes.false
                (nat ::: list key ::: list (option signature) ::: bytes :::
                     action_ty ::: storage_ty ::: nil)
                (pair (list operation) storage_ty ::: nil))
           (psi : stack (pair (list operation) storage_ty ::: nil) -> Prop)
  :=
  let params : data parameter_ty := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  counter = stored_counter /\
  precond
    (eval env
       then_ fuel
       (threshold,
        (keys,
         (sigs,
          (pack env pack_ty
                ((chain_id_ env, address_ env parameter_ty (self env)), (counter, action)),
           (action, (storage, tt))))))) psi.

Lemma fold_eval_precond fuel :
  eval_precond_body (@semantics.eval_precond fuel) =
  @semantics.eval_precond (S fuel) (Some parameter_ty).
Proof.
  reflexivity.
Qed.

Lemma multisig_head_correct
      (env : @proto_env (Some parameter_ty))
      (counter : N)
      (action : data action_ty)
      (sigs : Datatypes.list (Datatypes.option (data signature)))
      (stored_counter : N)
      (threshold : N)
      (keys : Datatypes.list (data key))
      (then_ :
         instruction _ _
           (nat ::: list key ::: list (option signature) ::: bytes :::
                action_ty ::: storage_ty ::: nil)
           (pair (list operation) storage_ty ::: nil))
      (psi : stack (pair (list operation) storage_ty ::: nil) -> Prop) :
  let params : data parameter_ty := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  forall fuel, 11 <= fuel ->
    (precond (eval env (multisig_head then_) (10 + fuel) ((params, storage), tt)) psi)
        <->
    multisig_head_spec env counter action sigs stored_counter threshold keys
                       fuel then_ psi.
Proof.
  intros params storage fuel Hfuel.
  rewrite eval_precond_correct.
  unfold multisig_head.
  unfold "+", params, storage, multisig_head_spec.
  rewrite eval_precond_correct.
  repeat (more_fuel; simpl).
  rewrite if_false_is_and.
  rewrite (eqb_eq nat).
  intuition.
Qed.

Definition multisig_iter_body :
  instruction _ _
    (key ::: nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
    (nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
  :=
  (DIP1 SWAP ;; SWAP ;;
       IF_CONS
       (
         IF_SOME
           ( SWAP ;;
                  DIP1
                  (
                    SWAP ;; DIIP ( DIP1 DUP ;; SWAP ) ;;
                         CHECK_SIGNATURE ;; ASSERT ;;
                         PUSH nat (nat_constant 1%N) ;; ADD_nat))
           ( SWAP ;; DROP1 )
       )
       (
         FAIL
       ) ;;
       SWAP).

Lemma multisig_iter_body_correct env k n sigs packed
      (st : stack (action_ty ::: storage_ty ::: nil)) fuel psi :
    14 <= fuel ->
    precond (eval env multisig_iter_body fuel (k, (n, (sigs, (packed, st))))) psi
    <->
    match sigs with
    | nil => false
    | cons None sigs => psi (n, (sigs, (packed, st)))
    | cons (Some sig) sigs =>
      check_signature env k sig packed = true /\
      psi ((1 + n)%N, (sigs, (packed, st)))
    end.
Proof.
  intro Hfuel.
  rewrite eval_precond_correct.
  repeat more_fuel.
  simpl.
  destruct sigs as [|[sig|] sigs].
  - reflexivity.
  - case (check_signature env k sig packed).
    + tauto.
    + split.
      * intro H; inversion H.
      * intros (H, _); discriminate.
  - reflexivity.
Qed.

Definition multisig_iter :
  instruction _ _
    (list key ::: nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
    (nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
  :=
  ITER multisig_iter_body.

(* Executing on stack (keys, n, sigs, packed, st) returns (nb_valid_sigs + n, nb_excess_sigs, packed, st) *)
(* Invariant: all_keys = verified_keys @ remaining *)

Lemma multisig_iter_correct env keys n sigs packed
      (st : stack (action_ty ::: storage_ty ::: nil)) fuel psi :
    length keys * 14 + 1 <= fuel ->
    precond (eval env multisig_iter fuel (keys, (n, (sigs, (packed, st))))) psi <->
    (exists first_sigs remaining_sigs,
        length first_sigs = length keys /\
        sigs = (first_sigs ++ remaining_sigs)%list /\
        check_all_signatures
          first_sigs keys (fun k sig => check_signature env k sig packed) /\
        psi ((count_signatures first_sigs + n)%N, (remaining_sigs, (packed, st)))).
Proof.
  rewrite eval_precond_correct.
  generalize n sigs packed fuel; clear n sigs packed fuel.
  induction keys as [|key keys]; intros n sigs packed fuel Hfuel.
  - simpl in Hfuel.
    more_fuel.
    simpl.
    split.
    + intro H.
      exists nil.
      exists sigs.
      simpl.
      intuition reflexivity.
    + intros (first_sigs, (remaining_sigs, (Hlen, (Happ, (_, H))))).
      simpl in Hlen.
      apply List.length_zero_iff_nil in Hlen.
      subst first_sigs.
      simpl in Happ.
      subst remaining_sigs.
      exact H.
  - simpl in Hfuel.
    more_fuel.
    change (13 + (length keys * 14 + 1) <= fuel) in Hfuel.
    assert (length keys * 14 + 1 <= fuel) as Hfuel2 by (transitivity (13 + (length keys * 14 + 1)); [repeat constructor| apply Hfuel]).
    simpl.
    rewrite <- eval_precond_correct.
    rewrite multisig_iter_body_correct.
    + destruct sigs as [|[sig|] sigs].
      * split; [intro H; inversion H|].
        intros (first_sigs, (remaining_sigs, (Hlen, (Happ, _)))).
        symmetry in Happ.
        apply List.app_eq_nil in Happ.
        destruct Happ as (Hfirst, _).
        subst first_sigs.
        simpl in Hlen.
        discriminate.
      * split.
        -- intros (Hcheck, Hrec).
           specialize (IHkeys (1 + n)%N sigs packed fuel Hfuel2).
           rewrite IHkeys in Hrec.
           destruct Hrec as (first_sigs, (remaining_sigs, (Hlen, (Happ, (Hchecks, H))))).
           exists (Some sig :: first_sigs)%list.
           exists remaining_sigs.
           split ; [simpl; f_equal; assumption|].
           subst sigs.
           split ; [reflexivity|].
           split.
           ++ simpl.
              rewrite Hcheck.
              exact Hchecks.
           ++ rewrite N.add_assoc in H.
              exact H.
        -- intros (first_sigs, (remaining_sigs, (Hlen, (Happ, (Hchecks, H))))).
           destruct first_sigs as [|[first_sig|] first_sigs].
           ++ simpl in Hlen.
              discriminate.
           ++ simpl in Happ.
              injection Happ.
              intro Hsigs; subst sigs.
              intro Hsig; subst first_sig.
              simpl in Hchecks.
              destruct (check_signature env key sig packed).
              ** simpl in Hchecks.
                 split; [reflexivity|].
                 apply (IHkeys _ _ _ _ Hfuel2).
                 exists first_sigs; exists remaining_sigs.
                 simpl in Hlen.
                 apply NPeano.Nat.succ_inj in Hlen.
                 split; [assumption|].
                 split; [reflexivity|].
                 split; [assumption|].
                 simpl in H.
                 rewrite N.add_assoc.
                 exact H.
              ** simpl in Hchecks.
                 inversion Hchecks.
           ++ simpl in Happ.
              discriminate.
      * rewrite (IHkeys _ _ _ _ Hfuel2).
        split;
          intros (first_sigs, (remaining_sigs, (Hlen, (Happ, (Hchecks, H))))).
        -- exists (None :: first_sigs)%list.
           exists remaining_sigs.
           split; [simpl; f_equal; exact Hlen|].
           subst sigs.
           split; [reflexivity|].
           split; [exact Hchecks|].
           exact H.
        -- destruct first_sigs as [|[first_sig|] first_sigs].
           ++ simpl in Hlen; discriminate.
           ++ simpl in Happ; discriminate.
           ++ exists first_sigs.
              exists remaining_sigs.
              simpl in Hlen.
              apply NPeano.Nat.succ_inj in Hlen.
              split; [assumption|].
              simpl in Happ.
              split; [injection Happ; auto|].
              split; [exact Hchecks|].
              exact H.
    + transitivity (13 + (length keys * 14 + 1)).
      * destruct (length keys).
        -- simpl. constructor.
        -- simpl. repeat (apply Le.le_n_S).
           apply le_0_n.
      * assumption.
Qed.

Definition multisig_tail :
  instruction _ _
    (nat ::: nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
    (pair (list operation) storage_ty ::: nil) :=
      ASSERT_CMPLE ;;
    DROP1 ;; DROP1 ;;

    DIP1 ( UNPAIR ;; PUSH nat (nat_constant 1%N) ;; ADD_nat ;; PAIR ) ;;

    NIL operation ;; SWAP ;;
    IF_LEFT
      ( UNPAIR ;; UNIT ;; TRANSFER_TOKENS ;; CONS )
      ( IF_LEFT (SET_DELEGATE ;; CONS )
                ( DIP1 ( SWAP ;; CAR ) ;; SWAP ;; PAIR ;; SWAP )) ;;
    PAIR.

Lemma multisig_split : multisig = multisig_head (DIP1 (PUSH nat (nat_constant 0%N);; SWAP;; multisig_iter);; multisig_tail).
Proof.
  reflexivity.
Qed.

Lemma multisig_tail_correct
      env threshold n sigs packed action counter keys psi fuel :
    13 <= fuel ->
    precond (eval env multisig_tail fuel (threshold, (n, (sigs, (packed, (action, ((counter, (threshold, keys)), tt))))))) psi <->
    ((threshold <= n)%N /\
     match action with
     | inl (amout, contr) =>
       psi (((transfer_tokens env unit tt amout contr :: nil)%list, ((1 + counter)%N, (threshold, keys))), tt)
    | inr (inl kh) =>
      psi (((set_delegate env kh :: nil)%list, ((1 + counter)%N, (threshold, keys))), tt)
    | inr (inr (nt, nks)) =>
      psi (nil, ((1 + counter)%N, (nt, nks)), tt)
    end).
Proof.
  intro Hfuel.
  change (data (list key)) in keys.
  rewrite eval_precond_correct.
  unfold multisig_tail.
  do 6 more_fuel.
  simpl.
  rewrite if_false_is_and.
  rewrite (leb_le nat).
  unfold lt, lt_comp, compare, simple_compare.
  rewrite N.compare_lt_iff.
  rewrite <- N.le_lteq.
  apply and_both.
  repeat more_fuel.
  simpl.
  destruct action as [(amount, contract)|[delegate_key_hash|(new_threshold, new_keys)]];
      reflexivity.
Qed.

Lemma multisig_correct
      (env : @proto_env (Some parameter_ty))
      (counter : N)
      (action : data action_ty)
      (sigs : Datatypes.list (Datatypes.option (data signature)))
      (stored_counter : N)
      (threshold : N)
      (keys : Datatypes.list (data key))
      (new_stored_counter : N)
      (new_threshold : N)
      (new_keys : Datatypes.list (data key))
      (returned_operations : Datatypes.list (data operation))
      (fuel : Datatypes.nat) :
  let params : data parameter_ty := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  let new_storage : data storage_ty := (new_stored_counter, (new_threshold, new_keys)) in
  14 * length keys + 37 <= fuel ->
  eval env multisig fuel ((params, storage), tt) = Return ((returned_operations, new_storage), tt) <->
  multisig_spec env counter action sigs stored_counter threshold keys new_stored_counter new_threshold new_keys returned_operations.
Proof.
  intros params storage new_storage Hfuel.
  rewrite return_precond.
  rewrite multisig_split.
  rewrite PeanoNat.Nat.add_comm in Hfuel.
  do 10 more_fuel.
  change (S (S (S (S (S (S (S (S (S (S fuel)))))))))) with (10 + fuel).
  unfold params, storage.
  rewrite multisig_head_correct.
  - unfold multisig_head_spec, multisig_spec.
    apply and_both_2.
    intro; subst counter.
    clear params.
    unfold eval.
    rewrite eval_precond_correct.
    more_fuel; simpl.
    match goal with
    | |- eval_precond fuel env ?i ?t ?st <-> ?r =>
      pose (t) as then_; change (eval_precond fuel env i then_ st <-> r)
    end.
    more_fuel; simpl.
    more_fuel; simpl.
    more_fuel; simpl.
    simpl.
    match goal with
    | |- eval_precond fuel env ?i ?t ?st <-> ?r =>
      pose (t) as iter; change (eval_precond fuel env i iter st <-> r)
    end.
    more_fuel. simpl.
    subst iter.
    rewrite <- eval_precond_correct.
    rewrite multisig_iter_correct.
    apply forall_ex; intro first_sigs.
    apply forall_ex; intro remaining_sigs.
    rewrite and_comm_3.
    apply and_both.
    apply and_both.
    apply and_both.
    unfold then_.
    rewrite <- eval_precond_correct.
    rewrite multisig_tail_correct.
    rewrite N.add_0_r.
    rewrite N.ge_le_iff.
    apply and_both.
    destruct action as [(amount, contr)|[delegate_key_hash|(new_t, new_k)]].
    + split.
      * intro H.
        injection H.
        intro; subst keys.
        intro; subst threshold.
        intro; subst new_stored_counter.
        intro; subst returned_operations.
        intuition reflexivity.
      * intros (Hcounter, (Hthreshold, (Hkeys, Hoper))).
        subst new_stored_counter; subst keys; subst threshold; subst returned_operations.
        reflexivity.
    + split.
      * intros H.
        injection H.
        intro; subst keys.
        intro; subst threshold.
        intro; subst new_stored_counter.
        intro; subst returned_operations.
        intuition reflexivity.
      * intros (Hcounter, (Hthreshold, (Hkeys, Hoper))).
        subst new_stored_counter; subst keys; subst threshold; subst returned_operations.
        reflexivity.
    + split.
      * intro H.
        injection H.
        intro; subst new_keys.
        intro; subst new_threshold.
        intro; subst new_stored_counter.
        intro; subst returned_operations.
        intuition reflexivity.
      * intros (Hcounter, (Hthreshold, (Hkeys, Hoper))).
        subst new_stored_counter; subst new_keys; subst new_threshold; subst returned_operations.
        reflexivity.
    + repeat apply Le.le_n_S.
      refine (NPeano.Nat.le_trans _ _ _ _ Hfuel).
      repeat apply Le.le_n_S.
      apply le_0_n.
    + rewrite PeanoNat.Nat.add_comm.
      apply Le.le_n_S.
      refine (NPeano.Nat.le_trans _ _ _ _ Hfuel).
      repeat constructor.
      rewrite PeanoNat.Nat.mul_comm.
      constructor.
  - refine (NPeano.Nat.le_trans _ _ _ _ Hfuel).
    repeat apply Le.le_n_S.
    apply le_0_n.
Qed.

End multisig.
