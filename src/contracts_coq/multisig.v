Add LoadPath "../".
Require Import macros.
Import syntax.
Import comparable.
Require Import NArith.
Require Import semantics.
Import error.
Require List.

Print N.

Section multisig.

Definition action_ty := or (pair mutez (contract unit)) (or (option_ key_hash) (pair nat (list_ key))).

Definition parameter_ty := (pair
             (pair
                nat
                action_ty)
             (list_ (option_ signature))).

Context {get_contract_type : contract_constant -> error.M type} {nd : @node get_contract_type parameter_ty}.

Definition instruction := @syntax.instruction get_contract_type parameter_ty.
Definition data := @semantics.data get_contract_type parameter_ty.
Definition stack := @semantics.stack get_contract_type parameter_ty.
Definition eval {A B : stack_type} := @semantics.eval _ _ nd A B.
Definition eval_precond := @semantics.eval_precond _ _ nd.

Definition ADD_nat {S} : instruction (nat ::: nat ::: S) (nat ::: S) := ADD.

Definition storage_ty := pair nat (pair nat (list_ key)).


Definition pack_ty := pair address (pair nat action_ty).


Definition multisig : full_contract parameter_ty storage_ty :=
  (
    UNPAIR ;; SWAP ;; DUP ;; DIP SWAP ;;
    DIP
      (
        UNPAIR ;;
        DUP ;; @SELF _ parameter_ty _ ;; ADDRESS ;; PAIR ;;
        PACK ;;
        DIP ( UNPAIR ;; DIP SWAP ) ;; SWAP
      ) ;;

    UNPAIR ;; DIP SWAP ;;
    ASSERT_CMPEQ ;;

    DIP SWAP ;; UNPAIR ;;
    DIP
      (
        PUSH nat (nat_constant 0%N) ;; SWAP ;;
        ITER
          (
            DIP SWAP ;; SWAP ;;
            IF_CONS
              (
                IF_SOME
                  ( SWAP ;;
                    DIP
                      (
                        SWAP ;; DIIP ( DIP DUP ;; SWAP ) ;;
                        CHECK_SIGNATURE ;; ASSERT ;;
                        PUSH nat (nat_constant 1%N) ;; ADD_nat))
                  ( SWAP ;; DROP )
              )
              (
                FAIL
              ) ;;
            SWAP
          )
      ) ;;
    ASSERT_CMPLE ;;
    DROP ;; DROP ;;

    DIP ( UNPAIR ;; PUSH nat (nat_constant 1%N) ;; ADD ;; PAIR ) ;;

    NIL operation ;; SWAP ;;
    IF_LEFT
      ( UNPAIR ;; UNIT ;; TRANSFER_TOKENS ;; CONS )
      ( IF_LEFT (SET_DELEGATE ;; CONS )
                ( DIP ( SWAP ;; CAR ) ;; SWAP ;; PAIR ;; SWAP )) ;;
    PAIR ).

Fixpoint check_all_signatures (sigs : list (option (data signature)))
         (keys : list (data key))
         (check_sig : data key -> data signature -> M Datatypes.bool) {struct keys} :=
  match sigs, keys with
  | nil, nil => true
  | nil, cons _ _ => false
  | cons _ _, nil => true
  | cons (Some sig) sigs, cons k keys =>
    match check_sig k sig with
    | Failed _ _ => false
    | Return _ b => andb b (check_all_signatures sigs keys check_sig)
    end
  | cons None sigs, cons _ keys =>
    check_all_signatures sigs keys check_sig
  end.

Fixpoint count_signatures (sigs : list (option (data signature))) :=
  match sigs with
  | nil => 0%N
  | cons None sigs => count_signatures sigs
  | cons (Some _) sigs => (count_signatures sigs + 1)%N
  end.


Definition multisig_spec
           (counter : N)
           (action : data action_ty)
           (sigs : list (option (data signature)))
           (stored_counter : N)
           (threshold : N)
           (keys : list (data key))
           (new_stored_counter : N)
           (new_threshold : N)
           (new_keys : list (data key))
           (returned_operations : list (data operation)) :=
  let params : data parameter_ty := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  exists self_address packed first_sigs remaining_sigs,
    address_ nd parameter_ty (self nd) = Return _ self_address /\
    pack nd pack_ty
         (self_address, (counter, action)) = Return _ packed /\
    counter = stored_counter /\
    sigs = (first_sigs ++ remaining_sigs)%list /\
    length first_sigs = length keys /\
    check_all_signatures first_sigs keys
                         (fun k sig => check_signature nd k sig packed) /\
    (count_signatures first_sigs >= threshold)%N /\
    new_stored_counter = (1 + stored_counter)%N /\
    match action with
    | inl (amout, contr) =>
      exists oper, transfer_tokens nd unit tt amout contr = Return _ oper /\
                   new_threshold = threshold /\
                   new_keys = keys /\
                   returned_operations = (oper :: nil)%list
    | inr (inl kh) => exists oper, set_delegate nd kh = Return _ oper /\
                                   new_threshold = threshold /\
                                   new_keys = keys /\
                                   returned_operations = (oper :: nil)%list
    | inr (inr (nt, nks)) => new_threshold = nt /\
                             new_keys = nks /\
                             returned_operations = nil
    end.


Lemma forall_ex {A : Set} {phi psi : A -> Prop} :
  (forall x, phi x <-> psi x) -> ((exists x, phi x) <-> (exists x, psi x)).
Proof.
  intro Hall.
  split; intros (x, Hx); exists x; specialize (Hall x); intuition.
Qed.

Lemma and_comm_3 {A B C} : A /\ (B /\ C) <-> B /\ (A /\ C).
Proof.
  tauto.
Qed.

Lemma ex_and_comm {A : Set} {P : Prop} {Q : A -> Prop} :
  P /\ (exists x, Q x) <-> (exists x, P /\ Q x).
Proof.
  split.
  - intros (p, (x, q)).
    exists x.
    auto.
  - intros (x, (p, q)).
    split.
    + auto.
    + exists x.
      auto.
Qed.

Lemma ex_and_comm2 {A B : Set} {P : Prop} {Q : A -> B -> Prop} :
  P /\ (exists x y, Q x y) <-> (exists x y, P /\ Q x y).
Proof.
  rewrite ex_and_comm.
  apply forall_ex; intro x.
  apply ex_and_comm.
Qed.

Lemma and_both {P Q R : Prop} : (Q <-> R) -> (P /\ Q <-> P /\ R).
Proof.
  intuition.
Qed.

Lemma ex_and_comm_both {A : Set} {P Q R}:
  (Q <-> exists x : A, R x) ->
  ((P /\ Q) <-> exists x : A, P /\ R x).
Proof.
  intro H.
  transitivity (P /\ exists x, R x).
  - apply and_both; assumption.
  - apply ex_and_comm.
Qed.

Lemma ex_and_comm_both2 {A B : Set} {P Q R}:
  (Q <-> exists (x : A) (y : B), R x y) ->
  ((P /\ Q) <-> exists x y, P /\ R x y).
Proof.
  intro H.
  transitivity (P /\ exists x y, R x y).
  - apply and_both; assumption.
  - apply ex_and_comm2.
Qed.

Lemma and_both_eq {X A B : Set} {P : Prop} {Q : X -> X -> Prop} {R : X -> X -> A -> B -> Prop} {x y : X}:
  (Q x x <-> exists (a : A) (b : B), R x x a b) ->
  ((x = y /\ Q x y) <-> (exists a b, x = y /\ R x y a b)).
Proof.
  intro H1.
  split.
  - intros (He, H2); subst x.
    apply H1 in H2.
    destruct H2 as (a, (b, H2)).
    exists a; exists b.
    split; [reflexivity|exact H2].
  - intros (a, (b, (He, H2))).
    subst x.
    split; [reflexivity|].
    apply H1.
    exists a.
    exists b.
    exact H2.
Qed.

Lemma and_left {P Q R : Prop} : P -> (Q <-> R) -> ((P /\ Q) <-> R).
Proof.
  intuition.
Qed.

Lemma and_right {P Q R : Prop} : P -> (Q <-> R) -> (Q <-> (P /\ R)).
Proof.
  intuition.
Qed.


Lemma eqb_eq a c1 c2 :
  BinInt.Z.eqb (comparison_to_int (compare a c1 c2)) Z0 = true <->
  c1 = c2.
Proof.
  rewrite BinInt.Z.eqb_eq.
  rewrite comparison_to_int_Eq.
  apply comparable.compare_eq_iff.
Qed.

Lemma leb_le a c1 c2 :
  BinInt.Z.leb (comparison_to_int (compare a c1 c2)) Z0 = true <->
  (lt a c1 c2 \/ c1 = c2).
Proof.
  case_eq (compare a c1 c2); intro Hleb.
  - rewrite compare_eq_iff in Hleb.
    simpl.
    generalize (BinInt.Z.leb_refl Z0).
    intuition.
  - simpl.
    rewrite BinInt.Z.leb_le.
    generalize (BinInt.Pos2Z.neg_is_nonpos 1).
    unfold lt.
    intuition.
  - simpl.
    rewrite Zbool.Zone_pos.
    unfold lt.
    split.
    + discriminate.
    + rewrite <- compare_eq_iff.
      intros [|]; congruence.
Qed.

Lemma leb_gt a c1 c2 :
  BinInt.Z.leb (comparison_to_int (compare a c1 c2)) Z0 = false <->
  (gt a c1 c2).
Proof.
  unfold gt.
  case_eq (compare a c1 c2); intro Hleb.
  - simpl.
    rewrite BinInt.Z.leb_refl.
    split; discriminate.
  - simpl.
    assert (BinInt.Z.leb (Zneg 1) Z0 = true) as H.
    + rewrite BinInt.Z.leb_le.
      apply (BinInt.Pos2Z.neg_is_nonpos 1).
    + rewrite H.
      split; discriminate.
  - simpl.
    case_eq (BinInt.Z.leb (Zpos 1) Z0).
    + intro H.
      rewrite BinInt.Z.leb_le in H.
      apply Zorder.Zle_not_lt in H.
      destruct (H BinInt.Z.lt_0_1).
    + intro; split; reflexivity.
Qed.

Definition multisig_head (then_ : instruction (nat ::: list_ key ::: list_ (option_ signature) ::: bytes ::: action_ty ::: storage_ty ::: nil) (pair (list_ operation) storage_ty ::: nil)) :
  instruction (pair parameter_ty storage_ty ::: nil)
              (pair (list_ operation) storage_ty ::: nil)
:=
    UNPAIR ;; SWAP ;; DUP ;; DIP SWAP ;;
    DIP
      (
        UNPAIR ;;
        DUP ;; @SELF _ parameter_ty _ ;; ADDRESS ;; PAIR ;;
        PACK ;;
        DIP ( UNPAIR ;; DIP SWAP ) ;; SWAP
      ) ;;

    UNPAIR ;; DIP SWAP ;;
    ASSERT_CMPEQ ;;

    DIP SWAP ;; UNPAIR ;; then_.

Definition multisig_head_spec
           (counter : N)
           (action : data action_ty)
           (sigs : list (option (data signature)))
           (stored_counter : N)
           (threshold : N)
           (keys : list (data key))
           (fuel : Datatypes.nat)
           (then_ :
              instruction
                (nat ::: list_ key ::: list_ (option_ signature) ::: bytes :::
                     action_ty ::: storage_ty ::: nil)
                (pair (list_ operation) storage_ty ::: nil))
           (psi : stack (pair (list_ operation) storage_ty ::: nil) -> Prop)
  :=
  let params : data parameter_ty := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  exists self_address packed,
    address_ nd parameter_ty (self nd) = Return _ self_address /\
    pack nd pack_ty
         (self_address, (counter, action)) = Return _ packed /\
    counter = stored_counter /\
    precond (eval then_ fuel (threshold, (keys, (sigs, (packed, (action, (storage, tt))))))) psi.

Ltac mysimpl :=
  match goal with
    |- ?g =>
    match g with
    | context c[semantics.eval_precond ?nd (S ?n) ?i ?psi] =>
      is_var i ||
             (let simplified := (eval simpl in (semantics.eval_precond nd (S n) i psi)) in
              let full := context c[simplified] in
              let final := eval cbv beta zeta iota in full in
              change final)
    end
  end.

Lemma fold_eval_precond fuel :
  eval_precond_body nd (@semantics.eval_precond _ _ nd fuel) =
  @semantics.eval_precond _ _ nd (S fuel).
Proof.
  reflexivity.
Qed.

Ltac more_fuel :=
  match goal with
    | Hfuel : (_ <= ?fuel) |- _ =>
      destruct fuel as [|fuel];
      [inversion Hfuel; fail
      | apply le_S_n in Hfuel]
  end.

Lemma multisig_head_correct
      (counter : N)
      (action : data action_ty)
      (sigs : list (option (data signature)))
      (stored_counter : N)
      (threshold : N)
      (keys : list (data key))
      (then_ :
         instruction
           (nat ::: list_ key ::: list_ (option_ signature) ::: bytes :::
                action_ty ::: storage_ty ::: nil)
           (pair (list_ operation) storage_ty ::: nil))
      (psi : stack (pair (list_ operation) storage_ty ::: nil) -> Prop) :
  let params : data parameter_ty := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  forall fuel, 9 <= fuel ->
    (precond (eval (multisig_head then_) (10 + fuel) ((params, storage), tt)) psi)
        <->
    multisig_head_spec counter action sigs stored_counter threshold keys
                       fuel then_ psi.
Proof.
  intros params storage fuel Hfuel.
  unfold eval.
  rewrite eval_precond_correct.
  unfold multisig_head.
  more_fuel.
  unfold "+", params, storage, multisig_head_spec.
  mysimpl.
  apply forall_ex; intro addr.
  rewrite <- ex_and_comm.
  apply and_both.
  do 2 more_fuel; mysimpl.
  apply forall_ex.
  intro packed.
  apply and_both.
  do 6 more_fuel.
  mysimpl.
  case_eq (BinInt.Z.eqb (comparison_to_int (stored_counter ?= counter)%N) Z0).
  - intro Heq.
    apply (eqb_eq nat) in Heq.
    symmetry in Heq.
    apply (and_right Heq).
    do 9 rewrite fold_eval_precond.
    rewrite <- eval_precond_correct.
    unfold eval.
    reflexivity.
  - intro Hneq.
    split.
    + intro H; inversion H.
    + intros (Heq, _).
      symmetry in Heq.
      apply (eqb_eq nat) in Heq.
      simpl in Heq.
      exfalso.
      congruence.
Qed.

Definition multisig_iter_body :
  instruction
    (key ::: nat ::: list_ (option_ signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
    (nat ::: list_ (option_ signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
  :=
  (DIP SWAP ;; SWAP ;;
       IF_CONS
       (
         IF_SOME
           ( SWAP ;;
                  DIP
                  (
                    SWAP ;; DIIP ( DIP DUP ;; SWAP ) ;;
                         CHECK_SIGNATURE ;; ASSERT ;;
                         PUSH nat (nat_constant 1%N) ;; ADD_nat))
           ( SWAP ;; DROP )
       )
       (
         FAIL
       ) ;;
       SWAP).

Lemma multisig_iter_body_correct k n sigs packed
      (st : stack (action_ty ::: storage_ty ::: nil)) fuel psi :
    14 <= fuel ->
    precond (eval multisig_iter_body fuel (k, (n, (sigs, (packed, st))))) psi
    <->
    match sigs with
    | nil => false
    | cons None sigs => psi (n, (sigs, (packed, st)))
    | cons (Some sig) sigs =>
      check_signature nd k sig packed = Return _ true /\
      psi ((1 + n)%N, (sigs, (packed, st)))
    end.
Proof.
  intro Hfuel.
  unfold eval.
  rewrite eval_precond_correct.
  do 14 more_fuel.
  mysimpl.
  destruct sigs as [|[sig|] sigs].
  - reflexivity.
  - split.
    + intros ([|], (Hckeck, H)).
      * split; assumption.
      * inversion H.
    + intros (Hcheck, H).
      exists true.
      split; assumption.
  - reflexivity.
Qed.

Definition multisig_iter :
  instruction
    (list_ key ::: nat ::: list_ (option_ signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
    (nat ::: list_ (option_ signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
  :=
  ITER multisig_iter_body.

(* Apres l'execution sur la pile (keys, n, sigs, packed, st), on renvoie (nb_de_signatures_valides + n, signatures exedentaires, packed, st) *)
(* Invariant: all_keys = verified_keys @ remaining *)

Lemma multisig_iter_correct keys n sigs packed
      (st : stack (action_ty ::: storage_ty ::: nil)) fuel psi :
    length keys * 14 + 1 <= fuel ->
    precond (eval multisig_iter fuel (keys, (n, (sigs, (packed, st))))) psi <->
    (exists first_sigs remaining_sigs,
        length first_sigs = length keys /\
        sigs = (first_sigs ++ remaining_sigs)%list /\
        check_all_signatures
          first_sigs keys (fun k sig => check_signature nd k sig packed) /\
        psi ((count_signatures first_sigs + n)%N, (remaining_sigs, (packed, st)))).
Proof.
  unfold eval.
  rewrite eval_precond_correct.
  generalize n sigs packed fuel; clear n sigs packed fuel.
  induction keys as [|key keys]; intros n sigs packed fuel Hfuel.
  - simpl in Hfuel.
    more_fuel.
    mysimpl.
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
    mysimpl.
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
              destruct (check_signature nd key sig packed) as [|[|]].
              ** inversion Hchecks.
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
              injection Happ.
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
           ++ simpl in Happ; injection Happ; discriminate.
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
        -- simpl. do 14 (apply Le.le_n_S).
           apply le_0_n.
      * assumption.
Qed.

Definition multisig_tail :
  instruction
    (nat ::: nat ::: list_ (option_ signature) ::: bytes ::: action_ty :::
         storage_ty ::: nil)
    (pair (list_ operation) storage_ty ::: nil) :=
      ASSERT_CMPLE ;;
    DROP ;; DROP ;;

    DIP ( UNPAIR ;; PUSH nat (nat_constant 1%N) ;; ADD_nat ;; PAIR ) ;;

    NIL operation ;; SWAP ;;
    IF_LEFT
      ( UNPAIR ;; UNIT ;; TRANSFER_TOKENS ;; CONS )
      ( IF_LEFT (SET_DELEGATE ;; CONS )
                ( DIP ( SWAP ;; CAR ) ;; SWAP ;; PAIR ;; SWAP )) ;;
    PAIR.

Lemma multisig_split : multisig = multisig_head (DIP (PUSH nat (nat_constant 0%N);; SWAP;; multisig_iter);; multisig_tail).
Proof.
  reflexivity.
Qed.

Lemma multisig_tail_correct
      threshold n sigs packed action counter keys psi fuel :
    13 <= fuel ->
    precond (eval multisig_tail fuel (threshold, (n, (sigs, (packed, (action, ((counter, (threshold, keys)), tt))))))) psi <->
    ((threshold <= n)%N /\
     match action with
    | inl (amout, contr) =>
      exists oper, transfer_tokens nd unit tt amout contr = Return _ oper /\
                   psi (((oper :: nil)%list, ((1 + counter)%N, (threshold, keys))), tt)
    | inr (inl kh) =>
      exists oper, set_delegate nd kh = Return _ oper /\
                   psi (((oper :: nil)%list, ((1 + counter)%N, (threshold, keys))), tt)
    | inr (inr (nt, nks)) =>
      psi (nil, ((1 + counter)%N, (nt, nks)), tt)
    end).
Proof.
  intro Hfuel.
  change (data (list_ key)) in keys.
  unfold eval.
  rewrite eval_precond_correct.
  unfold multisig_tail.
  do 4 more_fuel.
  mysimpl.
  case_eq (BinInt.Z.leb (comparison_to_int (threshold ?= n)%N) Z0).
  - intro Hle.
    rewrite (leb_le nat) in Hle.
    unfold lt, compare in Hle.
    rewrite N.compare_lt_iff in Hle.
    rewrite <- N.le_lteq in Hle.
    apply (and_right Hle).
    do 6 more_fuel.
    mysimpl.
    destruct action as [(amount, contract)|[delegate_key_hash|(new_threshold, new_keys)]].
    + do 3 more_fuel.
      reflexivity.
    + more_fuel.
      reflexivity.
    + do 3 more_fuel.
      reflexivity.
  - do 3 more_fuel.
    mysimpl.
    intro Hle.
    apply (leb_gt nat) in Hle.
    rename Hle into Hgt.
    unfold gt, compare in Hgt.
    rewrite N.compare_gt_iff in Hgt.
    split.
    + intro H; inversion H.
    + intros (Hle, _).
      apply N.lt_nge in Hgt.
      contradiction.
Qed.

Lemma multisig_correct
      (counter : N)
      (action : data action_ty)
      (sigs : list (option (data signature)))
      (stored_counter : N)
      (threshold : N)
      (keys : list (data key))
      (new_stored_counter : N)
      (new_threshold : N)
      (new_keys : list (data key))
      (returned_operations : list (data operation))
      (fuel : Datatypes.nat) :
  let params : data parameter_ty := ((counter, action), sigs) in
  let storage : data storage_ty := (stored_counter, (threshold, keys)) in
  let new_storage : data storage_ty := (new_stored_counter, (new_threshold, new_keys)) in
  14 * length keys + 37 <= fuel ->
  eval multisig fuel ((params, storage), tt) = Return _ ((returned_operations, new_storage), tt) <->
  multisig_spec counter action sigs stored_counter threshold keys new_stored_counter new_threshold new_keys returned_operations.
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
    apply forall_ex; intro address.
    apply forall_ex; intro packed.
    apply ex_and_comm_both2.
    apply ex_and_comm_both2.
    apply ex_and_comm_both2.
    clear params counter.
    unfold eval.
    rewrite eval_precond_correct.
    more_fuel; mysimpl.
    match goal with
    | |- semantics.eval_precond nd fuel ?i ?t ?st <-> ?r =>
      pose (t) as then_; change (semantics.eval_precond nd fuel i then_ st <-> r)
    end.
    more_fuel; mysimpl.
    more_fuel; mysimpl.
    more_fuel; mysimpl.
    match goal with
    | |- semantics.eval_precond nd fuel ?i ?t ?st <-> ?r =>
      pose (t) as iter; change (semantics.eval_precond nd fuel i iter st <-> r)
    end.
    more_fuel; mysimpl.
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
    + rewrite ex_and_comm.
      apply forall_ex; intro oper.
      split.
      * intros (Htransfer, H).
        injection H.
        intro; subst keys.
        intro; subst threshold.
        intro; subst new_stored_counter.
        intro; subst returned_operations.
        intuition reflexivity.
      * intros (Hcounter, (Htransfer, (Hthreshold, (Hkeys, Hoper)))).
        subst new_stored_counter; subst keys; subst threshold; subst returned_operations.
        split; [assumption | reflexivity].
    + rewrite ex_and_comm.
      apply forall_ex; intro oper.
      split.
      * intros (Hdelegate, H).
        injection H.
        intro; subst keys.
        intro; subst threshold.
        intro; subst new_stored_counter.
        intro; subst returned_operations.
        intuition reflexivity.
      * intros (Hcounter, (Hdelegat, (Hthreshold, (Hkeys, Hoper)))).
        subst new_stored_counter; subst keys; subst threshold; subst returned_operations.
        split; [assumption | reflexivity].
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
    + do 4 apply Le.le_n_S.
      refine (NPeano.Nat.le_trans _ _ _ _ Hfuel).
      do 9 apply Le.le_n_S.
      apply le_0_n.
    + rewrite PeanoNat.Nat.add_comm.
      apply Le.le_n_S.
      refine (NPeano.Nat.le_trans _ _ _ _ Hfuel).
      do 22 constructor.
      rewrite PeanoNat.Nat.mul_comm.
      constructor.
  - refine (NPeano.Nat.le_trans _ _ _ _ Hfuel).
    do 9 apply Le.le_n_S.
    apply le_0_n.
Qed.
