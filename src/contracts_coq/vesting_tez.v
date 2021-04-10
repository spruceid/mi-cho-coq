(* Open Source License *)
(* Copyright (c) 2020 Michael J. Klein, TQ Tezos *)

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

Require Import Coq.Classes.EquivDec.
Require Import Michocoq.macros.
Require Import syntax macros main semantics comparable util.
Require Import ZArith.
Require Import Lia.
Import error.
Require List.
Require tez.
Require map.
Require String.

Require vesting_tez_string.

Module source.
  Definition contract_file_M :=
    main.contract_file_M vesting_tez_string.vesting_tez_s 10.

  Definition contract_file := Eval cbv in (error.extract contract_file_M I).
End source.

Module annots.
  Import String.
  Definition setDelegate : string := "%setDelegate".
  Definition vest : string := "%vest".
End annots.

Definition parameter_ty :=
  (or (option key_hash) (Some annots.setDelegate)
      nat (Some annots.vest)
).

Module vesting_tez(C:ContractContext).

Definition storage_ty :=
  (pair (pair address address)
        (pair nat
              (pair timestamp (pair nat nat)))).

Definition vesting_tez : full_contract _ parameter_ty None storage_ty :=
  Eval cbv in contract_file_code source.contract_file.

Module semantics := Semantics C. Import semantics.

Definition vesting_tez_spec
           (env : @proto_env (Some (parameter_ty, None)))
           (target : data address)
           (delegateAdmin : data address)
           (vested : data nat)
           (epoch : data timestamp)
           (secondsPerTick : data nat)
           (tokensPerTick : data nat)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  let storage : data storage_ty :=
    ((target, delegateAdmin),
    (vested, (epoch, (secondsPerTick, tokensPerTick)))) in

  (* %setDelegate: the admin may set the delegate *)
  match param with
  | inl kh =>
    sender env = delegateAdmin /\
    new_storage = storage /\
    returned_operations = (set_delegate env kh :: nil)%list

  (* %vest: anybody can flush tokens *)
  (* this does not modify the storage and produces a 'transfer_tokens'. *)
  | inr to_flush =>
    secondsPerTick <> 0%N /\
    (Z.of_N (to_flush + vested) <= (now env - epoch) / Z.of_N secondsPerTick)%Z /\
    new_storage =
      ((target, delegateAdmin),
      ((to_flush + vested)%N, (epoch, (secondsPerTick, tokensPerTick)))) /\
    exists target_contract, contract_ None unit target = Some target_contract /\
    let tokens_to_flush := (to_flush * tokensPerTick)%N in
    exists pf,
    let tez_to_flush :=
      tez.of_Z_safe
        (Z.of_N tokens_to_flush)
        pf in
    returned_operations =
      (transfer_tokens env unit tt tez_to_flush target_contract :: nil)%list
  end.

Definition vesting_tez_spec_helper
           (env : @proto_env (Some (parameter_ty, None)))
           (target : data address)
           (delegateAdmin : data address)
           (vested : data nat)
           (epoch : data timestamp)
           (secondsPerTick : data nat)
           (tokensPerTick : data nat)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  let storage : data storage_ty :=
    ((target, delegateAdmin),
    (vested, (epoch, (secondsPerTick, tokensPerTick)))) in

  (* %setDelegate: the admin may set the delegate *)
  match param with
  | inl kh =>
    sender env = delegateAdmin /\
    new_storage = storage /\
    returned_operations = (set_delegate env kh :: nil)%list

  (* %vest: anybody can flush tokens *)
  (* this does not modify the storage and produces a 'transfer_tokens'. *)
  | inr to_flush =>
    let expected_new_storage : data storage_ty :=
      ((target, delegateAdmin),
      ((to_flush + vested)%N, (epoch, (secondsPerTick, tokensPerTick)))) in
    exists target_contract, contract_ None unit target = Some target_contract /\
    secondsPerTick <> N0 /\
    is_true (comparison_to_int (
        to_flush ?= Z.to_N ((now env - epoch) / Z.of_N secondsPerTick - Z.of_N vested)
      )%N <=? 0)%Z /\
    is_true ((now env - epoch) / Z.of_N secondsPerTick - Z.of_N vested >=? 0)%Z /\
    let m_tez_to_flush := tez.of_Z (Z.of_N (to_flush * tokensPerTick)) in
    exists m_tez_to_flush_ok : is_true (success m_tez_to_flush),
    let tez_to_flush := extract m_tez_to_flush m_tez_to_flush_ok in
    new_storage = expected_new_storage /\
    returned_operations =
      (transfer_tokens env unit tt tez_to_flush target_contract :: nil)%list
  end.

Lemma shim_simplify_flush_vested_ineqs (vested : data nat)
                                       (to_flush : data nat)
                                       (z : Z) :
  (to_flush <= Z.to_N (z - Z.of_N vested))%N /\ (0 <= z - Z.of_N vested)%Z <->
  (Z.of_N (to_flush + vested) <= z)%Z.
Proof.
  split; intro H.
  - destruct H as (Hsum & Hpos).
    refine (proj2 (Z2N.inj_le _ _ _ _) _).
    + rewrite <- (N2Z.id to_flush) in Hsum.
      apply (proj2 (Z2N.inj_le _ _ (N2Z.is_nonneg _) Hpos)) in Hsum.
      refine (Z.le_trans _ _ _ (N2Z.is_nonneg _) _).
      refine (proj2 (Z2N.inj_le _ _ (N2Z.is_nonneg _) (N2Z.is_nonneg _)) _).
      do 2 rewrite N2Z.id.
      exact (N.le_add_r _ _).
    + apply Zle_0_minus_le in Hpos.
      exact (Z.le_trans _ _ _ (N2Z.is_nonneg _) Hpos).
    + rewrite N2Z.id.
      rewrite Z2N.inj_sub in Hsum by exact (N2Z.is_nonneg _).
      rewrite N2Z.id in Hsum.
      apply (N.add_le_mono_r _ _ vested) in Hsum.
      rewrite N.sub_add in Hsum.
      * assumption.
      * apply Zle_0_minus_le in Hpos.
        apply (proj1 (Z2N.inj_le _ _
         (N2Z.is_nonneg _)
         (Z.le_trans _ _ _ (N2Z.is_nonneg _) Hpos)
        )) in Hpos.
        rewrite N2Z.id in Hpos.
        rewrite N.sub_add in Hsum; assumption.
  - pose (z_nonneg := Z.le_trans _ _ _ (N2Z.is_nonneg _) H).
    split.
    + pose (H' := H).
      apply (proj1 (Z2N.inj_le _ _ (N2Z.is_nonneg _) z_nonneg)) in H'.
      rewrite N2Z.id in H'.
      rewrite (Z2N.inj_sub _ _ (N2Z.is_nonneg _)).
      rewrite N2Z.id.
      exact (N.le_add_le_sub_r _ _ _ H').
    + refine (Zle_minus_le_0 _ _ _).
      pose (H' := H).
      rewrite N2Z.inj_add in H'.
      rewrite <- (Z.add_0_r z) in H'.
      rewrite <- Z.add_comm in H'.
      refine (Z.le_le_add_le _ _ _ _ (N2Z.is_nonneg _) H').
Qed.

(* In coq 8.11+, the proof of the 'assert' below is just 'lia'. *)
Lemma vesting_tez_spec_helper_flush_helper
      (now_env : data timestamp)
      (vested : data nat)
      (epoch : data timestamp)
      (secondsPerTick : data nat)
      (to_flush : data nat) :
  is_true (comparison_to_int (
      to_flush ?= Z.to_N ((now_env - epoch) / Z.of_N secondsPerTick - Z.of_N vested)
    )%N <=? 0)%Z /\
  is_true ((now_env - epoch) / Z.of_N secondsPerTick - Z.of_N vested >=? 0)%Z <->
  (Z.of_N (to_flush + vested) <= (now_env - epoch) / Z.of_N secondsPerTick)%Z.
Proof.
  rewrite N_comparison_to_int_leb.
  refine (iff_trans (and_both_0 _ _) _).
  - refine (iff_trans (IT_eq_iff _) _);
    exact (N.leb_le _ _).
  - refine (iff_trans (IT_eq_iff _) _);
    exact (Z.geb_le _ _).
  - apply shim_simplify_flush_vested_ineqs.
Qed.

Lemma of_Z_success z : success (tez.of_Z z) <-> Bool.Is_true (tez.in_bound z).
Proof.
  unfold tez.of_Z.
  destruct (tez.in_bound z); simpl; intuition.
Qed.

Lemma return_extract {A} (m : M A) H : Return (extract m H) = m.
Proof.
  destruct m.
  - contradiction.
  - destruct H.
    reflexivity.
Qed.

Lemma return_extract_2 {A} (m : M A) a H : m = Return a -> extract m H = a.
Proof.
  intro; subst; simpl.
  destruct H.
  reflexivity.
Qed.

Lemma vesting_tez_spec_helper_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (target : data address)
      (delegateAdmin : data address)
      (vested : data nat)
      (epoch : data timestamp)
      (secondsPerTick : data nat)
      (tokensPerTick : data nat)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation)) :
  vesting_tez_spec_helper
    env
    target
    delegateAdmin
    vested
    epoch
    secondsPerTick
    tokensPerTick
    param
    new_storage
    returned_operations
  <-> vesting_tez_spec
    env
    target
    delegateAdmin
    vested
    epoch
    secondsPerTick
    tokensPerTick
    param
    new_storage
    returned_operations.
Proof.
  unfold vesting_tez_spec_helper.
  unfold vesting_tez_spec.
  destruct param; (tauto || idtac).
  do 2 refine (iff_trans _ (and_assoc _ _ _)).
  refine (iff_trans _ (iff_sym ex_and_comm)).
  refine (forall_ex _).
  intros ((target_address & target_o) & target_type_eq).
  refine (iff_trans _ (and_comm _ _)).
  refine (iff_trans _ (iff_sym (and_assoc _ _ _))).
  refine (and_both _).
  refine (iff_trans _ (and_comm _ _)).
  do 2 refine (iff_trans _ (iff_sym (and_assoc _ _ _))).
  refine (and_both _).
  refine (iff_trans (iff_sym (and_assoc _ _ _)) _).
  refine (and_both_0 (vesting_tez_spec_helper_flush_helper _ _ _ _ _) _).
  refine (iff_trans (iff_sym ex_and_comm) _).
  refine (and_both _).
  split; intros (pf & Hpf).
  - exists (proj1 (of_Z_success _) pf).
    rewrite Hpf.
    do 3 f_equal.
    apply unreturn.
    rewrite <- tez.of_Z_is_safe.
    apply return_extract.
  - exists (proj2 (of_Z_success _) pf).
    rewrite Hpf.
    do 3 f_equal.
    apply unreturn.
    rewrite <- tez.of_Z_is_safe.
    symmetry.
    apply return_extract.
Qed.

Lemma vesting_tez_helper_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (target : data address)
      (delegateAdmin : data address)
      (vested : data nat)
      (epoch : data timestamp)
      (secondsPerTick : data nat)
      (tokensPerTick : data nat)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  let storage : data storage_ty :=
    ((target, delegateAdmin),
    (vested, (epoch, (secondsPerTick, tokensPerTick)))) in
  eval_seq env vesting_tez (100 + fuel) ((param, storage), tt) = Return ((returned_operations, new_storage), tt)
  <-> vesting_tez_spec_helper
    env
    target
    delegateAdmin
    vested
    epoch
    secondsPerTick
    tokensPerTick
    param
    new_storage
    returned_operations.
Proof.
  intro storage.
  remember (100 + fuel) as fuel2.
  assert (100 <= fuel2) by lia.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  unfold vesting_tez_spec_helper.
  destruct param as [kh | to_flush].
  {
    do 17 (more_fuel; simpl).
    rewrite Z.eqb_eq.
    rewrite comparison_to_int_Eq.
    rewrite (compare_eq_iff address).
    apply and_both.
    unfold storage.
    rewrite and_pair_eq.
    rewrite and_comm.
    apply and_left; [reflexivity|].
    rewrite and_pair_eq.
    intuition.
  }
  {
    do 5 (more_fuel; simpl).
    split.
    - intros ((q, r), (H1, H2)).
      destruct (q - Z.of_N vested >=? 0)%Z eqn:Hdiff.
      + destruct H2 as (y, (Hy, (Hflush, (c, (Hc, Hm))))).
        assert (y = Z.to_N (q - Z.of_N vested)) by congruence.
        subst y.
        clear Hy.
        rewrite precond_exists in Hm.
        destruct Hm as (z, (Hz, H2)).
        rewrite and_pair_eq in H2.
        rewrite and_pair_eq in H2.
        destruct H2 as ((H2, H3), _).
        subst.
        change (tez.of_Z (1%Z * Z.of_N (to_flush * tokensPerTick)) = Return z) in Hz.
        rewrite Z.mul_1_l in Hz.
        rewrite Hz.
        simpl.
        exists c.
        split; [assumption|].
        split; [apply ediv_Z_correct in H1; lia|].
        assert (q = ((now env - epoch) / Z.of_N secondsPerTick)%Z).
        * rewrite ediv_Z_correct in H1.
          destruct H1 as (H1, H2).
          apply (Zdiv_unique _ _ _ (Z.of_N r)); [nia|symmetry; assumption].
        * split; [|split].
          -- subst.
             apply Bool.Is_true_eq_left.
             apply Hflush.
          -- apply Bool.Is_true_eq_left.
             congruence.
          -- exists I; split; reflexivity.
      + destruct H2 as (y, (Habsurd, _)).
        discriminate.
    - intros (target_contract, (Ht, (Hspt, (Hflush, (Hdiff, (Hsuccess, He)))))).
      exists (((now env - epoch) / Z.of_N secondsPerTick), Z.to_N ((now env - epoch) mod Z.of_N secondsPerTick))%Z.
      split.
      + assert (Z.of_N secondsPerTick > 0)%Z as Hpos by lia.
        assert (0 <= ((now env - epoch) mod Z.of_N secondsPerTick))%Z as Hneg
            by (apply Z_mod_lt; assumption).
        assert (Z.of_N (Z.to_N ((now env - epoch) mod Z.of_N secondsPerTick)) = ((now env - epoch) mod Z.of_N secondsPerTick))%Z
          as Hid by (apply Z2N.id; assumption).
        rewrite ediv_Z_correct.
        split.
        * symmetry.
          etransitivity; [apply (Z_div_mod_eq _ _ Hpos)|].
          rewrite Hid.
          reflexivity.
        * rewrite Hid.
          replace (Z.abs (Z.of_N secondsPerTick)) with (Z.of_N secondsPerTick).
          -- apply Z_mod_lt. assumption.
          -- lia.
      + apply Bool.Is_true_eq_true in Hdiff.
        rewrite Hdiff.
        eexists.
        split; [reflexivity|].
        apply Bool.Is_true_eq_true in Hflush.
        split; [assumption|].
        eexists.
        split; [eassumption|].
        destruct (success_eq_return_rev _ _ Hsuccess) as (m, Hm).
        change (tez.to_Z _) with 1%Z.
        rewrite Z.mul_1_l.
        rewrite Hm.
        apply (return_extract_2 _ _ Hsuccess) in Hm.
        simpl.
        destruct He; subst.
        reflexivity.
  }
Qed.

Lemma vesting_tez_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (target : data address)
      (delegateAdmin : data address)
      (vested : data nat)
      (epoch : data timestamp)
      (secondsPerTick : data nat)
      (tokensPerTick : data nat)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  let storage : data storage_ty :=
    ((target, delegateAdmin),
    (vested, (epoch, (secondsPerTick, tokensPerTick)))) in
  eval_seq env vesting_tez (100 + fuel) ((param, storage), tt) = Return ((returned_operations, new_storage), tt)
  <-> vesting_tez_spec
    env
    target
    delegateAdmin
    vested
    epoch
    secondsPerTick
    tokensPerTick
    param
    new_storage
    returned_operations.
Proof.
refine (iff_trans (vesting_tez_helper_correct _ _ _ _ _ _ _ _ _ _ _) _).
exact (vesting_tez_spec_helper_correct _ _ _ _ _ _ _ _ _ _).
Qed.

End vesting_tez.