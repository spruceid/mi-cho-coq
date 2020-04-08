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
Require Import Lia.
Import error.
Require List.

Module annots.
  Import String.
  Definition main : string := "%main".
  Definition operation : string := "%operation".
  Definition change_keys : string := "%change_keys".
End annots.

Definition parameter_ty :=
  (or unit (Some default_entrypoint.default)
      (pair
         (pair nat
               (or
                  (lambda unit (list operation)) (Some annots.operation)
                  (pair nat (list key)) (Some annots.change_keys)))
         (list (option signature)))
  (Some annots.main)).

Module generic_multisig(C:ContractContext).

Definition storage_ty := pair nat (pair nat (list key)).

Module semantics := Semantics C. Import semantics.

Definition ADD_nat {S} : instruction (Some (parameter_ty, None)) _ (nat ::: nat ::: S) (nat ::: S) := ADD.

Definition multisig : full_contract _ parameter_ty None storage_ty :=
  {
    UNPAIR;
    IF_LEFT
      { DROP1; (NIL operation); PAIR }
      { PUSH mutez (0 ~mutez); AMOUNT; ASSERT_CMPEQ;
        SWAP; DUP; DIP1 { SWAP };
        DIP1
          {
            UNPAIR;
            DUP; SELF (self_type := parameter_ty) (self_annot := None) None I;
            ADDRESS; CHAIN_ID;
            PAIR; PAIR;
            PACK;
            DIP1 { UNPAIR; DIP1 { SWAP } }; SWAP
          };

        UNPAIR; DIP1 { SWAP };
        ASSERT_CMPEQ;

        DIP1 { SWAP }; UNPAIR;
        DIP1
          {
            PUSH nat (nat_constant 0); SWAP;
            ITER
              {
                DIP1 { SWAP }; SWAP;
                IF_CONS
                  {
                    IF_SOME
                      { SWAP;
                        DIP1
                          {
                            SWAP; DIIP { DUUP };
                            DUUUP; DIP1 { CHECK_SIGNATURE };
                            SWAP; IF_TRUE { DROP1 } { FAILWITH };
                            PUSH nat (nat_constant 1); ADD_nat }}
                      { SWAP; DROP1 }
                  }
                  {
                    FAIL
                  };
                SWAP
              }
          };
        ASSERT_CMPLE;
        IF_CONS { FAIL } {};
        DROP1;

        DIP1 { UNPAIR; PUSH nat (nat_constant 1); ADD; PAIR };

        IF_LEFT
          { UNIT; EXEC }
          {
            DIP1 { CAR }; SWAP;
            PAIR; (NIL operation)
          };
        PAIR }
  }.

Fixpoint check_all_signatures (sigs : Datatypes.list (Datatypes.option (data signature)))
         (keys : Datatypes.list (data key))
         (check_sig : data key -> data signature -> data bool) {struct keys} :=
  match sigs, keys with
  | nil, nil => true
  | nil, cons _ _ => false
  | cons _ _, nil => false
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

Definition action_ty :=
  (or
     (lambda unit (list operation)) (Some annots.operation)
     (pair nat (list key)) (Some annots.change_keys)).
Definition pack_ty := pair (pair chain_id address) (pair nat action_ty).

Definition multisig_spec
           (env : @proto_env (Some (parameter_ty, None)))
           (parameter : data parameter_ty)
           (stored_counter : N)
           (threshold : N)
           (keys : Datatypes.list (data key))
           (new_stored_counter : N)
           (new_threshold : N)
           (new_keys : Datatypes.list (data key))
           (returned_operations : Datatypes.list (data operation))
           (fuel : Datatypes.nat) :=
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  match parameter with
  | inl tt =>
    new_stored_counter = stored_counter /\
    new_threshold = threshold /\
    new_keys = keys /\
    returned_operations = nil
  | inr ((counter, action), sigs) =>
    amount env = (0 ~Mutez) /\
    counter = stored_counter /\
    length sigs = length keys /\
    check_all_signatures
      sigs keys
      (fun k sig =>
         check_signature
           env k sig
           (pack env pack_ty (chain_id_ env, address_ unit (self env None I),
                              (counter, action)))) /\
    (count_signatures sigs >= threshold)%N /\
    new_stored_counter = (1 + stored_counter)%N /\
    match action with
    | inl (existT _ _ lam) =>
      match (eval_seq (no_self env) lam fuel (tt, tt)) with
      | Return (operations, tt) =>
        new_threshold = threshold /\
        new_keys = keys /\
        returned_operations = operations
      | _ => False
      end
    | inr (nt, nks) =>
      new_threshold = nt /\
      new_keys = nks /\
      returned_operations = nil
    end
  end.

Definition multisig_head :
  instruction_seq (Some (parameter_ty, None)) Datatypes.false (pair (pair nat action_ty) (list (option signature)) ::: pair nat (pair nat (list key)) ::: nil) (nat ::: list key ::: list (option signature) ::: bytes ::: action_ty ::: storage_ty ::: nil)
:=
    {
      PUSH mutez (0 ~mutez); AMOUNT; ASSERT_CMPEQ;
      SWAP; DUP; DIP1 { SWAP };
      DIP1
        {
          UNPAIR;
          DUP; SELF (self_type := parameter_ty) (self_annot := None) None I ;
          ADDRESS; CHAIN_ID;
          PAIR; PAIR;
          PACK;
          DIP1 { UNPAIR; DIP1 { SWAP }}; SWAP
        };

      UNPAIR; DIP1 { SWAP };
      ASSERT_CMPEQ;

      DIP1 { SWAP }; UNPAIR }.

Definition multisig_head_spec
           (env : @proto_env (Some (parameter_ty, None)))
           (counter : N)
           (action : data action_ty)
           (sigs : Datatypes.list (Datatypes.option (data signature)))
           (stored_counter : N)
           (threshold : N)
           (keys : Datatypes.list (data key))
           (fuel : Datatypes.nat)
           (psi : stack (nat ::: list key ::: list (option signature) ::: bytes ::: action_ty ::: storage_ty ::: nil) -> Prop)
  :=
  let params := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  amount env = (0 ~Mutez) /\
  counter = stored_counter /\
  psi (threshold,
       (keys,
        (sigs,
         (pack env pack_ty
               (chain_id_ env, address_ unit (self (self_ty := Some (parameter_ty, None)) env None I), (counter, action)),
          (action, (storage, tt)))))).

Ltac fold_eval_precond :=
  change (@eval_precond_body (@eval_precond ?fuel)) with (@eval_precond (S fuel)).

Lemma multisig_head_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (counter : N)
      (action : data action_ty)
      (sigs : Datatypes.list (Datatypes.option (data signature)))
      (stored_counter : N)
      (threshold : N)
      (keys : Datatypes.list (data key))
      psi :
  let params := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  forall fuel,
    5 <= fuel ->
    (semantics.eval_seq_precond fuel env multisig_head psi (params, (storage, tt)))
        <->
        multisig_head_spec env counter action sigs stored_counter threshold keys fuel psi.
Proof.
  intros params storage fuel Hfuel.
  unfold multisig_head.
  unfold "+", params, storage, multisig_head_spec.
  unfold eval_seq_precond.
  repeat (more_fuel; simpl).
  rewrite match_if_exchange.
  rewrite if_false_is_and.
  rewrite (eqb_eq mutez).
  apply and_both.
  rewrite match_if_exchange.
  rewrite if_false_is_and.
  rewrite (eqb_eq nat).
  rewrite (eq_sym_iff counter stored_counter).
  apply and_both.
  reflexivity.
Qed.

Definition multisig_iter_body :
  instruction_seq _ _
    (key ::: nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
    (nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
  :=
    {
      DIP1 { SWAP }; SWAP;
      IF_CONS
          {
            IF_SOME
              { SWAP;
                DIP1
                  {
                    SWAP; DIIP { DUUP };
                    DUUUP; DIP1 { CHECK_SIGNATURE };
                    SWAP; IF_TRUE { DROP1 } { FAILWITH };
                    PUSH nat (nat_constant 1); ADD_nat }}
              { SWAP; DROP1 }
          }
          {
            FAIL
          };
      SWAP
    }.

Opaque N.add.

Lemma multisig_iter_body_correct env k n sigs packed
      (st : stack (action_ty ::: storage_ty ::: nil)) fuel psi :
    8 <= fuel ->
    semantics.eval_seq_precond fuel env multisig_iter_body psi (k, (n, (sigs, (packed, st))))
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
  unfold eval_seq_precond.
  destruct sigs as [|[sig|] sigs].
  - repeat (more_fuel; simpl).
    reflexivity.
  - repeat (more_fuel; simpl).
    case (check_signature env k sig packed).
    + tauto.
    + split.
      * intro H; inversion H.
      * intros (H, _); discriminate.
  - do 4 (more_fuel; simpl).
    reflexivity.
Qed.

Definition multisig_iter :
  instruction _ _
    (list key ::: nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
    (nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
  :=
  ITER multisig_iter_body.

Lemma fold_eval_seq_precond fuel :
  @eval_seq_precond_body (@semantics.eval_precond fuel) =
  @semantics.eval_seq_precond fuel.
Proof.
  reflexivity.
Qed.

Lemma multisig_iter_correct env keys n sigs packed
      (st : stack (action_ty ::: storage_ty ::: nil)) fuel psi :
    length keys + 8 <= fuel ->
    semantics.eval_precond fuel env multisig_iter psi (keys, (n, (sigs, (packed, st)))) <->
    (exists first_sigs remaining_sigs,
        length first_sigs = length keys /\
        sigs = (first_sigs ++ remaining_sigs)%list /\
        check_all_signatures
          first_sigs keys (fun k sig => check_signature env k sig packed) /\
        psi ((count_signatures first_sigs + n)%N, (remaining_sigs, (packed, st)))).
Proof.
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
    unfold multisig_iter.
    remember multisig_iter_body as mib.
    simpl.
    subst mib.
    rewrite fold_eval_seq_precond.
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
           specialize (IHkeys (1 + n)%N sigs packed fuel Hfuel).
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
                 apply (IHkeys _ _ _ _ Hfuel).
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
      * rewrite (IHkeys _ _ _ _ Hfuel).
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
    + omega.
Qed.

Definition multisig_tail :
  instruction_seq (Some (parameter_ty, None)) _
    (nat ::: nat ::: list (option signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
    (pair (list operation) storage_ty ::: nil) :=
  {
    ASSERT_CMPLE;
    IF_CONS { FAIL } {};
    DROP1;

    DIP1 { UNPAIR; PUSH nat (nat_constant 1); ADD; PAIR };

    IF_LEFT
      { UNIT; EXEC }
      {
        DIP1 { CAR }; SWAP;
        PAIR; (NIL operation)
      };
    PAIR }.

Lemma multisig_split :
  multisig =
  {
    UNPAIR;
    IF_LEFT
      { DROP1; NIL operation; PAIR }
      ( multisig_head ;;;
        DIP1 { PUSH nat (nat_constant 0%N); SWAP; multisig_iter };;
        multisig_tail)
  }%michelson.
Proof.
  reflexivity.
Qed.

Lemma multisig_tail_correct
      env threshold n sigs packed action counter (keys : data (list key)) psi fuel :
  3 <= fuel ->
  precond (semantics.eval_seq env multisig_tail (S (S fuel)) (threshold, (n, (sigs, (packed, (action, ((counter, (threshold, keys)), tt))))))) psi <->
  sigs = nil /\
  ((threshold <= n)%N /\
   match action with
   | inl (existT _ _ lam) =>
     match eval_seq (no_self env) lam fuel (tt, tt) with
     | Return (operations, tt) =>
       psi ((operations, ((1 + counter)%N, (threshold, keys))), tt)
     | _ => False
     end
   | inr (nt, nks) =>
     psi (nil, ((1 + counter)%N, (nt, nks)), tt)
   end).
Proof.
  intro Hfuel.
  rewrite eval_seq_precond_correct.
  unfold multisig_tail.
  unfold eval_seq_precond.
  simpl.
  more_fuel; simpl.
  rewrite match_if_exchange.
  more_fuel; simpl.
  case sigs.
  - case_eq (BinInt.Z.leb (comparison_to_int (threshold ?= n)%N) Z0).
    + intro Hle.
      rewrite (leb_le nat) in Hle.
      unfold lt, lt_comp, compare in Hle.
      rewrite N.compare_lt_iff in Hle.
      rewrite <- N.le_lteq in Hle.
      apply (and_right eq_refl).
      apply (and_right Hle).
      destruct action as [(tff, lam)|(new_threshold, new_keys)].
      * more_fuel; simpl.
        repeat fold_eval_precond.
        rewrite fold_eval_seq_precond.
        rewrite <- eval_seq_precond_correct.
        case (semantics.eval_seq _ lam (S (S (S fuel))) (tt, tt)).
        -- intro; split; intro H; simpl in H; inversion H.
        -- intro s; reflexivity.
      * reflexivity.
    + intro Hle.
      apply (leb_gt nat) in Hle.
      rename Hle into Hgt.
      unfold gt, gt_comp, compare in Hgt.
      rewrite N.compare_gt_iff in Hgt.
      split.
      * more_fuel; intro H; inversion H.
      * intros (_, (Hle, _)).
        apply N.lt_nge in Hgt.
        contradiction.
  - intros d l; split; intro H.
    + more_fuel; destruct (comparison_to_int (threshold ?= n)%N <=? 0)%Z; inversion H.
    + destruct H; discriminate.
Qed.

Lemma multisig_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (params : data parameter_ty)
      (stored_counter : N)
      (threshold : N)
      (keys : Datatypes.list (data key))
      (new_stored_counter : N)
      (new_threshold : N)
      (new_keys : Datatypes.list (data key))
      (returned_operations : Datatypes.list (data operation))
      (fuel : Datatypes.nat) :
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  let new_storage : data storage_ty := (new_stored_counter, (new_threshold, new_keys)) in
  length keys + 7 <= fuel ->
  eval_seq env multisig (3 + fuel) ((params, storage), tt) = Return ((returned_operations, new_storage), tt) <->
  multisig_spec env params stored_counter threshold keys new_stored_counter new_threshold new_keys returned_operations fuel.
Proof.
  intros storage new_storage Hfuel.
  rewrite return_precond.
  rewrite multisig_split.
  rewrite PeanoNat.Nat.add_comm in Hfuel.
  subst storage. subst new_storage.
  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  destruct params as [()| ((counter, action), sigs)].
  - split; simpl.
    + intro H; injection H. intuition.
    + intros (H1, (H2, (H3, H4))). subst.
      reflexivity.
  - remember multisig_head as mh.
    remember multisig_iter as mi.
    simpl.
    repeat fold_eval_precond.
    subst mh.
    repeat fold_eval_precond.
    rewrite fold_eval_seq_precond.
    rewrite eval_seq_assoc.
    rewrite multisig_head_correct; [|omega].
    unfold multisig_head_spec.
    apply and_both.
    apply and_both_2.
    intro; subst counter.
    remember multisig_tail as mt.
    unfold eval_seq_precond.
    simpl.
    repeat fold_eval_precond.
    subst mi.
    rewrite multisig_iter_correct; [| rewrite PeanoNat.Nat.add_comm; apply Peano.le_n_S; assumption].
    split.
    + intros (first_sigs, (remaining_sigs, (Hlen, (Hsigs, (Hcheck, Heval))))).
      subst mt.
      rewrite fold_eval_seq_precond in Heval.
      rewrite <- eval_seq_precond_correct in Heval.
      rewrite multisig_tail_correct in Heval; [|omega].
      destruct Heval as (Hrs, (Hcount, Haction)).
      subst remaining_sigs.
      rewrite List.app_nil_r in Hsigs.
      subst first_sigs.
      split; [assumption|].
      split; [assumption|].
      rewrite N.add_0_r in Hcount.
      apply N.le_ge in Hcount.
      split; [assumption|].
      destruct action as [(tff, lam)|(nt, nks)].
      * destruct (eval_seq _ lam fuel (tt, tt)) as [|(ops, [])].
        -- inversion Haction.
        -- injection Haction; intros; subst. repeat constructor.
      * injection Haction; intros; subst. repeat constructor.
    + intros (Hlen, (Hcheck, (Hcount, Haction))).
      exists sigs.
      exists nil.
      split; [assumption|].
      rewrite List.app_nil_r.
      split; [reflexivity|].
      split; [assumption|].
      rewrite fold_eval_seq_precond.
      rewrite <- eval_seq_precond_correct.
      subst mt.
      rewrite multisig_tail_correct; [|omega].
      split; [reflexivity|].
      rewrite N.add_0_r.
      apply N.ge_le in Hcount.
      split; [assumption|].
      destruct Haction as (Hcounter, Haction).
      destruct action as [(tff, lam)|(nt, nks)].
      * destruct (eval_seq _ lam fuel (tt, tt)) as [|(ops, [])].
        -- inversion Haction.
        -- destruct Haction as (Ht, (Hk, Hops)); subst; reflexivity.
      * destruct Haction as (Ht, (Hk, Hops)); subst; reflexivity.
Qed.

End generic_multisig.
