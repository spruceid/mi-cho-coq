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
    exists pf : (tokens_to_flush < 2 ^ 63)%N,
    let tez_to_flush :=
      extract
        (tez.of_Z (Z.of_N tokens_to_flush))
        (tez.of_Z_of_N_success tokens_to_flush pf) in
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
  - destruct (N.lt_decidable (d * tokensPerTick) (2 ^ 63)) as [Hlt | Hge].
    + exists Hlt.
      rewrite Hpf.
      do 3 f_equal.
      exact (Is_true_UIP _ _ _).
    + refine (False_ind _ (Hge _)).
      unfold tez.of_Z in pf.
      pose (pf' := success_bind_arg _ _ pf).
      unfold int64bv.of_Z in pf'.
      assert (success_if_then_Return_else_Failed : forall
        (A : Type)
        (b : Datatypes.bool)
        (x : A)
        (err : exception),
        success (if b then Return x else Failed _ err) = b
      ) by (destruct b; reflexivity).
      rewrite success_if_then_Return_else_Failed in pf'.
      apply Is_true_and_right in pf'.
      apply IT_eq in pf'.
      apply Z.ltb_lt in pf'.
      refine (proj2 (N2Z.inj_lt _ _) _).
      assert (H_pow_2_63 : two_power_nat 63 = Z.of_N (2 ^ 63)%N).
      {
        rewrite two_power_nat_equiv.
        rewrite N2Z.inj_pow.
        f_equal.
      }
      rewrite <- H_pow_2_63.
      assumption.
  - exists (tez.of_Z_of_N_success _ pf).
    assumption.
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
  intro Hfuel.
  remember (100 + fuel) as fuel2.
  assert (100 <= fuel2) by lia.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  unfold vesting_tez_spec_helper.
  destruct param as [kh | to_flush].
  {
    do 17 (more_fuel; simpl).
    destruct env; simpl.
    destruct sender0 as [sender_addr | sender_addr];
    destruct delegateAdmin as [delegateAdmin_addr | delegateAdmin_addr];
    simpl;
    ((
      destruct sender_addr as [sender_addr];
      destruct delegateAdmin_addr as [delegateAdmin_addr];
      destruct (case_string_compare_Eq sender_addr delegateAdmin_addr) as
        [(str_cmp_eq & str_eq) | (str_cmp_neq & str_neq)];
      ((
        rewrite str_cmp_eq;
        rewrite str_eq;
        simpl;
        split;
        intros (_ & Heq);
        ((inversion Heq; intuition) ||
        ( destruct Heq as (Hstorage & Hops);
          rewrite Hstorage;
          rewrite Hops;
          split; auto; reflexivity))
      ) ||
      (
        pose (cmp := string_compare sender_addr delegateAdmin_addr);
        assert (Hcmp : string_compare sender_addr delegateAdmin_addr = cmp) by reflexivity;
        rewrite Hcmp in str_cmp_neq |- *;
        destruct cmp; (congruence ||
        simpl; split; intro Heq; destruct Heq; congruence)
      ))
    ) ||
    (
      destruct sender_addr as [sender_addr];
      destruct delegateAdmin_addr as [delegateAdmin_addr];
      simpl; split; intro Heq; destruct Heq; congruence
    ));
    rewrite H0; rewrite H1; reflexivity.
  }
  {
    do 5 (more_fuel; simpl).
    destruct secondsPerTick as [ | secondsPerTick].
    {
      split; intro Heq; destruct Heq.
      - destruct H0 as (H0 & _); inversion H0.
      - inversion H0 as (H1 & H2 & H3); congruence.
    }
    {
      simpl.
      unfold ediv_Z at 1.
      simpl.
      refine (iff_trans (ex_eq_some_simpl _ _) _).
      match goal with
      | |- (let (_, _) := if ?x then _ else _ in _) <-> _ =>
        pose (is_vesting := x);
        assert (is_vesting_eq : is_vesting = x) by reflexivity
      end.
      rewrite <- is_vesting_eq.
      destruct is_vesting.
      {
        refine (iff_trans (ex_eq_some_simpl _ _) _).
        match goal with
        | |- ?x = true /\ _ <-> _ =>
            pose (any_to_flush := x);
            assert (any_to_flush_eq : any_to_flush = x) by reflexivity
        end.
        rewrite <- any_to_flush_eq.
        destruct any_to_flush.
        {
          assert (cancel_true_refl : forall T, true = true /\ T <-> T) by tauto.
          refine (iff_trans (cancel_true_refl _) _).
          refine (forall_ex _).
          intros ((target_address & target_o) & target_type_eq).
          refine (and_both _).
          assert (H_id :
            match Z.of_N (to_flush * tokensPerTick) with
            | 0%Z => 0%Z
            | Z.pos y' => Z.pos y'
            | Z.neg y' => Z.neg y'
            end = Z.of_N (to_flush * tokensPerTick)
          ).
          {
            destruct (Z.of_N (to_flush * tokensPerTick));
            reflexivity.
          }
          {
            rewrite H_id.
            pose (m_tez_to_flush := tez.of_Z (Z.of_N (to_flush * tokensPerTick))).
            assert (m_tez_to_flush_eq : m_tez_to_flush =
              tez.of_Z (Z.of_N (to_flush * tokensPerTick))) by reflexivity.
            rewrite <- m_tez_to_flush_eq.
            destruct m_tez_to_flush.
            {
              split; simpl;
              (tauto || intros (_ & _ & _ & Hfalse & _));
              assumption.
            }
            {
              split; simpl; intro Heq; inversion Heq as [Hops].
              {
                split.
                - intro neq; inversion neq.
                - split.
                  + refine (IT_eq_rev _ _).
                    rewrite any_to_flush_eq.
                    reflexivity.
                  + split.
                    * refine (IT_eq_rev _ _);
                      rewrite is_vesting_eq;
                      reflexivity.
                    * refine (@ex_intro _ _ I _); tauto.
              }
              {
                destruct H0 as (_ & _ & x & H_storage & H_operations).
                rewrite H_storage.
                rewrite H_operations.
                destruct x.
                reflexivity.
              }
            }
          }
        }
        {
          split.
          - intuition.
          - intros (target_contract & _ & _ & Hfalse & _).
            apply IT_eq in Hfalse.
            destruct env.
            simpl in any_to_flush_eq, Hfalse.
            rewrite <- any_to_flush_eq in Hfalse.
            inversion Hfalse.
        }
      }
      {
        pattern (((now env - epoch) / Z.pos secondsPerTick - Z.of_N vested >=? 0)%Z).
        rewrite <- is_vesting_eq.
        split; intro HH. destruct HH as (x & HH).
        - destruct HH as (Hfalse & _).
          inversion Hfalse.
        - destruct HH as (_ & _ & _ & _ & Hfalse & _).
          inversion Hfalse.
      }
    }
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
