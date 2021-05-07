Require Import String ZArith.
Require Import syntax macros semantics comparable util entrypoints.
Import error.
Require List.
Require tez.
Require map.

Require List.
Import List.ListNotations.
Open Scope list.

Require Import spending_limit_contract_definition.

Module Spending_limit_contract_verification (C:ContractContext).

Module semantics := Semantics C. Import semantics.


Module Tactics.
  (*
   * Solves some fuel-related goals on the form
   *   Hfuel : Y <= fuel |- X <= fuel by showing X <= Y
   *)
  Hint Rewrite List.rev_length : fuel.

  Ltac simple_fuel :=
    match goal with
    | Hfuel:_ <= ?fuel |- _ =>
      autorewrite with fuel in *;
      apply (le_trans_rev _ _ _ Hfuel); simpl; omega
    end.

  (* Tactics for rewriting under existential binders *)
  Ltac ex_under_aux' tac := etransitivity; [eapply forall_ex; intro; tac; apply iff_refl|].
  Ltac ex_under_aux tac :=  ex_under_aux' tac || (rewrite iff_comm; ex_under_aux' tac; rewrite iff_comm).
  Tactic Notation "ex_under" tactic(T) := ex_under_aux ltac:(T).
  Ltac ex_rewrite rw := ex_under_aux ltac:(rewrite rw).



  Ltac S_fuel_to_add_fuel  :=
    match goal with
    | [ fuel : Datatypes.nat |- _ ] =>
      repeat match goal with
             | [ |- context[S fuel] ] => change (S fuel) with (1 + fuel)
             | [ |- context[S (?n + fuel)] ] => change (S (n + fuel)) with ((S n) + fuel)
             end
    end.

  Ltac simple_fuel_add_n_fuel :=
    match goal with
    | [ fuel : Datatypes.nat |- _ ] =>
      match goal with
      | [ |- ?n <= ?m + fuel ] => apply Nat.le_sub_le_add_l
      end
    end.

  Ltac my_simple_fuel :=
    intros; try S_fuel_to_add_fuel; try simple_fuel_add_n_fuel;
    (omega || simple_fuel).

  Lemma my_simple_fuel_test_1:
    forall (A : type) (xs : Datatypes.list (data A)) (fuel : Datatypes.nat),
      Datatypes.length xs <= fuel ->
      1 + Datatypes.length xs <= S fuel.
  Proof. my_simple_fuel. Qed.

  Lemma my_simple_fuel_test_2:
    forall (fuel : Datatypes.nat) (L : Datatypes.list (comparable_data timestamp * comparable_data mutez)),
      1 + Datatypes.length L <= fuel -> 1 + Datatypes.length L <= fuel.
  Proof.
    intros fuel L H.
    my_simple_fuel.
  Qed.
End Tactics.

Import Tactics.

Fixpoint total_amount_transaction_list1
         (transaction_list : (data (list (pair mutez (contract unit)))))
         (acc : data mutez)
         (result : data mutez) : Prop :=
  match transaction_list with
  | nil => result = acc
  | cons (tz, _) transaction_list =>
    exists new_acc,
    (add _ _ _ Add_variant_tez_tez acc tz) = Return new_acc  /\
    (total_amount_transaction_list1 transaction_list new_acc result)
  end.

Definition total_amount_transaction_list
           (transaction_list : data (list (pair mutez (contract unit))))
           (result : data mutez) :=
  total_amount_transaction_list1 transaction_list (0 ~Mutez) result.

Definition slc_ep_transfer2_transaction_iter_body_spec {A} :
      (stack (list operation ::: mutez ::: A) -> Prop) ->
      (data (pair mutez (contract unit))) ->
      stack (list operation ::: mutez ::: A) -> Prop :=
  fun psi '(transferred_amount, destination) '(oplist, (threshold, st)) =>
    exists new_threshold,
    add _ _ _ Add_variant_tez_tez threshold transferred_amount = Return new_threshold /\
    psi ((transfer_tokens unit I tt transferred_amount destination) :: oplist,
         (new_threshold, st)).

Lemma slc_ep_transfer2_transaction_iter_body_spec_precond_ex A psi transferred_amount destination oplist threshold st :
  slc_ep_transfer2_transaction_iter_body_spec (A := A) psi (transferred_amount, destination) (oplist, (threshold, st)) =
  precond_ex (add _ _ _ Add_variant_tez_tez threshold transferred_amount)
             (fun new_threshold => psi ((transfer_tokens unit I tt transferred_amount destination) :: oplist,
                                        (new_threshold, st))).
Proof.
  reflexivity.
Qed.

Opaque add.
Opaque sub.

Lemma slc_ep_transfer2_transaction_iter_body_correct {A} env fuel :
  forall (psi : stack (list operation ::: mutez ::: A) -> Prop)
         (element : data (pair mutez (contract unit)))
         (st : stack (list operation ::: mutez ::: A)),
  3 <= fuel ->
  eval_seq_precond fuel env slc_ep_transfer2_transaction_iter_body
               psi
               (element, st) <->
  slc_ep_transfer2_transaction_iter_body_spec
    psi element st.
Proof.
  intros psi (transferred_amount, destination) (oplist, (threshold, st)) Hfuel.
  rewrite slc_ep_transfer2_transaction_iter_body_spec_precond_ex.
  rewrite <- precond_exists.
  unfold slc_ep_transfer2_transaction_iter_body.
  unfold eval_seq_precond.
  simpl eval_seq_precond_body.
  more_fuel.
  simpl.
  more_fuel.
  simpl.
  more_fuel.
  simpl.
  reflexivity.
Qed.

Lemma slc_ep_transfer2_transaction_iter_correct
      {A}
      env
      psi
      (transaction_list : data (list (pair mutez (contract unit))))
      (st : stack A) :
  forall
    (oplist : data (list operation))
    fuel
    (threshold : data mutez),
    4 + Datatypes.length transaction_list <= fuel ->
    eval_precond fuel env (ITER (i := iter_list _) slc_ep_transfer2_transaction_iter_body) psi
                 (transaction_list, (oplist, (threshold, st))) <->
    exists final_threshold,
      total_amount_transaction_list1 transaction_list threshold final_threshold /\
      psi
        (List.rev
           (List.map
              (fun '(transfered_amount, destination) =>
                 transfer_tokens unit I tt transfered_amount destination) transaction_list) ++
           oplist,
         (final_threshold, st)).
Proof.

  intros oplist fuel threshold H.
  rewrite <- eval_precond_correct.
  rewrite precond_iter_bounded
          with (body_spec := slc_ep_transfer2_transaction_iter_body_spec)
               (fuel_bound := 3).
  - generalize dependent oplist.
    generalize dependent threshold.
    induction transaction_list as [| (head_mut, ct) transaction_list_tail ]; intros threshold oplist.
    + rewrite iff_comm. apply ex_eq_simpl.
    + simpl.
      rewrite ex_2. rewrite ex_order.
      apply forall_ex.
      intro acc.
      rewrite underex_and_assoc.
      rewrite <- ex_and_comm.
      apply and_both.
      rewrite IHtransaction_list_tail; try my_simple_fuel.
      rewrite <- List.app_assoc.
      reflexivity.

  - intros fuel0 (transferred_amount, destination) (oplist', (threshold', st')) psi0 Hfuel.
    rewrite eval_seq_precond_correct.
    apply slc_ep_transfer2_transaction_iter_body_correct.
    assumption.

  - intros psi1 psi2 (transferred_amount, destination) (oplist', (threshold', st')) Hpsi.
    unfold slc_ep_transfer2_transaction_iter_body_spec.
    apply forall_ex. intro new_threshold. rewrite Hpsi. reflexivity.

  - simple_fuel.
Qed.
Definition reverse {sty A B} :
  instruction
    sty false
    (list A ::: list A ::: B)
    (list A ::: B)
  := ITER (i := iter_list _) { CONS }.


Definition reverse_body_spec
           {A : type} {B : Datatypes.list type}
           (psi : stack (list A ::: B) -> Prop)
           (x : data A)
           (st : stack (list A ::: B)) : Prop :=
  match st with
    (xs, st') => psi (cons x xs, st')
  end.

Lemma reverse_correct
      fuel self_type env (A : type) (B : Datatypes.list type)
      (xs ys : data (list A))
      (st : stack B)
      (psi : stack (list A ::: B) -> Prop) :
    2 + Datatypes.length xs <= fuel ->
    eval_precond (self_type := self_type) fuel env reverse psi (xs, (ys, st))
    <-> psi (List.app (List.rev xs) ys, st).
Proof.
  intros Hfuel.
  extract_fuel (Datatypes.length xs + 1).
  rewrite <- Nat.add_assoc.
  rewrite <- eval_precond_correct.
  unfold reverse.
  rewrite precond_iter_bounded with
      (body_spec := reverse_body_spec)
      (fuel_bound := 1).
  rewrite fold_right_psi_simpl with
      (f := reverse_body_spec)
      (f' := fun x '(ys, st)  => (cons x ys, st)).
  - apply eq_iff_refl.
    f_equal.
    unfold data.
    fold data_aux.
    generalize (@List.rev (data_aux (op (data_aux Empty_set)) A) xs) ys.
    induction l; intro ys'; simpl.
    + reflexivity.
    + now rewrite IHl.
  - destruct st0. reflexivity.
  - intros fuel0 x (xs', st') psi0 H.
    more_fuel. simpl. reflexivity.
  - intros psi1 psi2 x (xs', st') H.
    apply H.
  - omega.
Qed.

Definition slc_ep_transfer_loop_body_spec self_type (env : @proto_env self_type)
           (input : stack (list (pair timestamp mutez) ::: list (pair timestamp mutez) ::: mutez ::: storage_auth_ty ::: nil))
           (*
            * (output : stack (bool ::: list (pair timestamp mutez) ::: list (pair timestamp mutez) ::: mutez ::: storage_auth_ty ::: nil))
            *)
           psi : Prop :=
  let '(q1, (q2, (amount, st))) := input in
  match q1, q2 with
    | hd :: q1', q2 =>
      if ((fst hd) <=? (now env))%Z
      then exists sum, add _ _ _ Add_variant_tez_tez amount (snd hd) = Return sum /\
                       psi (true, (q1', (q2, (sum, st))))
      else psi (false, (q1, (q2, (amount, st))))
    | [], hd :: q2' => psi (true, (List.rev (hd :: q2'), ([], (amount, st))))
    | [], [] => psi (false, ([], ([], (amount, st))))
  end.

Lemma slc_ep_transfer_loop_body_correct env fuel psi (q1 q2 : data (list (pair timestamp mutez))) amount st :
  (* sum (queue) + amount = init_thresh *)
  6 + Datatypes.length q2 <= fuel ->
  eval_precond fuel  env slc_ep_transfer_loop_body psi (q1, (q2, (amount, st)))
  <-> slc_ep_transfer_loop_body_spec _ env (q1, (q2, (amount, st))) psi.
Proof.
  intros Hfuel.
  unfold slc_ep_transfer_loop_body.
  cbn.
  destruct q1.
  - destruct q2.
    + now (do 5 (more_fuel; cbn)).
    + simpl in Hfuel.
      do 3 (more_fuel; cbn).
      destruct q2; [reflexivity|].
      match goal with |- context[eval_precond fuel env (@ITER ?tff ?st ?c ?i ?A ?code) ?psi] =>
                      remember (eval_precond fuel env (@ITER tff st c i A code) psi) as eval_itercode
      end.
      more_fuel.
      cbn.
      subst eval_itercode.
      rewrite reverse_correct; [|my_simple_fuel].
      rewrite <- List.app_assoc.
      reflexivity.
  - destruct d as (ts, tz).
    do 6 (more_fuel; cbn).
    rewrite <- comparison_to_int_leb.
    rewrite <- comparison_to_int_opp.
    destruct (_ >=? _)%Z.
    + rewrite precond_exists. unfold precond_ex.
      apply forall_ex.
      intro x.
      apply and_both_0; [|reflexivity].
      rewrite add_comm; reflexivity.
    + reflexivity.
Qed.

(* Start defining specification *)

Fixpoint allowed_amount l rem now result :=
  match l with
  | nil => result = rem
  | cons (frozen_timestamp, frozen_amount) l =>
    match compare timestamp frozen_timestamp now with
    (* Modified Arvid & Zaynah *)
    (* frozen_timestamp <= now *)
    | Lt | Eq =>
           exists new_rem,
           (* new_rem = rem + frozen_amount *)
           add _ _ _ Add_variant_tez_tez rem frozen_amount = Return new_rem /\
           allowed_amount l new_rem now result
    | Gt => result = rem
    end
  end.

(* true iff exists t1 \in l1, t1 > now *)
Fixpoint queue_cut_before_now (l1 : data (list (pair timestamp mutez))) (now : data timestamp) : Datatypes.bool :=
  match l1 with
  | nil => false
  | cons (t, _) l1 =>
    match compare timestamp t now with
    (* t <= now *)
    | Lt | Eq => queue_cut_before_now l1 now
    | Gt => true
    end
  end.

(* filter (fun ts => ts > now) l *)
Fixpoint remove_past (l : data (list (pair timestamp mutez))) (now : data timestamp) :=
  match l with
  | nil => nil
  | cons (t, m) l =>
    match compare timestamp t now with
    | Lt | Eq => remove_past l now
    | Gt => (t,m)::l
    end
  end.

Definition update_queue
           (l1 l2 : data (list (pair timestamp mutez)))
           (now : data timestamp) :=
  if queue_cut_before_now l1 now then
    (remove_past l1 now, l2)
  else
    (* l1 can be removed completely *)
    (remove_past (List.rev l2) now, nil).

Lemma slc_ep_transfer_loop_correct1
      env
      fuel
      psi
      (q1 q2 : data (list (pair timestamp mutez)))
      (amount : data mutez)
      (st : stack (storage_auth_ty ::: nil)) :
  Datatypes.length q1 + Datatypes.length q2 + 6 <= fuel ->
  queue_cut_before_now q1 (now env) = true ->
  eval_precond  fuel env slc_ep_transfer_loop psi (true, (q1, (q2, (amount, st)))) <->
  (exists amount' ,
      allowed_amount q1 amount (now env) amount' /\
      psi (remove_past q1 (now env), (q2, (amount', st)))).
Proof.
  intros Hfuel Hqueue_cut.

  unfold slc_ep_transfer_loop.

  generalize dependent amount.
  generalize dependent fuel.
  induction q1 as [ | (tz, ts) q1 ]; intros fuel Hfuel amount.

  - inversion Hqueue_cut.
  - rewrite plus_comm in Hfuel.
    more_fuel; simpl.
    rewrite slc_ep_transfer_loop_body_correct by my_simple_fuel.
    unfold slc_ep_transfer_loop_body_spec.
    unfold queue_cut_before_now in Hqueue_cut.
    fold queue_cut_before_now in Hqueue_cut.

    simpl compare in Hqueue_cut.
    rewrite Z.leb_compare.
    simpl fst.

    unfold allowed_amount. simpl compare. fold allowed_amount.
    unfold remove_past. simpl compare. fold remove_past.

    repeat rewrite Z_match_compare_gt in *.

    ex_rewrite Z_match_compare_gt.
    destruct (now env <? tz)%Z eqn:HtzCompNow.

    + more_fuel. simpl. rewrite iff_comm. apply ex_eq_simpl.

    + rewrite ex_2. rewrite ex_order. apply forall_ex. intro sum.
      rewrite underex_and_assoc. rewrite <- ex_and_comm. apply and_both.

      now rewrite IHq1; try assumption; try my_simple_fuel.
Qed.

Lemma queue_cut_before_false_tl:
 forall q a t x,
  queue_cut_before_now ((a,t) :: q) x = false ->
  queue_cut_before_now q x = false /\ (a <=? x)%Z = true.
Proof.
 simpl; intros; simpl in H.
 rewrite  Z.leb_compare.
 (*Set Printing All.*)
 case_eq ((a ?= x)%Z ) ; intros; try rewrite H0 in H; simpl in H; try congruence; intuition.
Qed.

Remark add_mul: forall a b, 2* (S a) + b = a + (S (S a)) + b.
Proof.
  intros;omega.
Qed.

Lemma eval_precond_loop fuel self_ty (env : @proto_env self_ty) A (code : instruction _ false A (bool ::: A)) st psi :
  eval_precond (S fuel) env (LOOP {code})%michelson psi (true, st) =
  eval_precond fuel env code (eval_precond fuel env (LOOP {code})%michelson psi) st.
Proof.
  reflexivity.
Qed.

Lemma slc_ep_transfer_loop_correct2':
  forall
    env
    psi
    (q1 : data (list (pair timestamp mutez)))
    fuel (x: data (pair timestamp mutez))
    (q2 : data (list (pair timestamp mutez)))
    ( Hfuel: 6 + Datatypes.length q2 <= fuel)
    (Hqueue_cut : queue_cut_before_now (x::q1) (now env) = false)
    (amount : data mutez)
    (st : stack (storage_auth_ty ::: nil)),
    eval_precond ((S (Datatypes.length q1)) + fuel) env slc_ep_transfer_loop psi (true, ((x::q1), (q2, (amount, st)))) <->
    exists amount',
      allowed_amount (x::q1) amount (now env) amount' /\
      eval_precond fuel env slc_ep_transfer_loop
                   psi ( true, ([],(q2, (amount',st)))).
Proof.
  intros env psi ; unfold slc_ep_transfer_loop. induction  q1 as [ | (tz, ts) q1 ]; intros.

(* case q1 == nil *)
  - destruct x.
    simpl.
    rewrite slc_ep_transfer_loop_body_correct by my_simple_fuel. simpl.
    simpl in Hqueue_cut.
    case_eq ( (d ?= now env)%Z); intros K; rewrite K in Hqueue_cut; inversion Hqueue_cut.
    +  rewrite Z.leb_compare. rewrite K. intuition.
     *  destruct H as [sum [Heq Prd]].
        exists sum. split;auto.
        exists sum. split;auto.


     *  destruct H as [am [A Prd]].
        destruct A as [sum' [Heq1 Heq2]].
        subst. exists sum'.  split;auto.

    + rewrite Z.leb_compare. rewrite K. intuition.
      * destruct H as [sum [Heq Prd]].

        exists sum. split;auto.
        exists sum. split;auto.

      * destruct H as [am [A Prd]].
        destruct A as [sum' [Heq1 Heq2]].
        subst. exists sum'.  split;auto.

(* case q1 <> nil *)
  - assert (Hqueue_ind: queue_cut_before_now ((tz, ts) :: q1) (now env) = false).
    simpl in Hqueue_cut.
    destruct x. case_eq ((d ?= now env)%Z  ); intro K; rewrite K in Hqueue_cut; inversion Hqueue_cut; auto.
    simpl "+".
    rewrite eval_precond_loop.
     rewrite slc_ep_transfer_loop_body_correct. simpl.
     destruct x. simpl. assert (Cond : (d <=? now env)%Z = true).
     destruct (queue_cut_before_false_tl _ _ _ _ Hqueue_cut) as [A B]. auto.
     rewrite Z.leb_compare. rewrite Z.leb_compare in Cond.
     case_eq ( (d ?= now env)%Z); intros K ; rewrite K in Cond; inversion Cond ; try rewrite K.
    + (* K : (d ?= now env)%Z = Eq *)
      split.
      *
       intros [sum [Heq1 Prd]].
       destruct (IHq1 fuel (tz,ts) q2 Hfuel Hqueue_ind sum st) as [Ia Ib].
       destruct (Ia Prd) as [am [Alw Prd']].
       exists am.  split;intuition. exists sum. split. auto.
       simpl in Alw. auto.

      *
       intros [am [A Prd]]. destruct A as [sum [ Heq  Alw]].
       exists sum. split. auto.
       destruct (IHq1 fuel (tz,ts) q2 Hfuel Hqueue_ind sum st) as [Ia Ib].
       apply Ib. exists am.  split; auto.
    + (*K : (d ?= now env)%Z = Lt*)
      split.
      *
       intros [sum [Heq1 Prd]].
       destruct (IHq1 fuel (tz,ts) q2 Hfuel Hqueue_ind sum st) as [Ia Ib].
       destruct (Ia Prd) as [am [Alw Prd']].
       exists am.  split;intuition. exists sum. split. auto.
       simpl in Alw. auto.
      *
       intros [am [A Prd]]. destruct A as [sum [ Heq  Alw]].
       exists sum. split. auto.
       destruct (IHq1 fuel (tz,ts) q2 Hfuel Hqueue_ind sum st) as [Ia Ib].
       apply Ib. exists am.  split; auto.
    +
   (* fuel bound *)
    omega.
Qed.

(*****************************************************************)

Definition list_empty_b (q2 : data (list (pair timestamp mutez))) : Datatypes.bool :=
  match q2 with nil => true | _ => false end.


(* probably not used *)
Lemma slc_ep_transfer_loop_correct3'
      env
      fuel
      psi
      (q2 : data (list (pair timestamp mutez)))
      (amount : data mutez)
      (st : stack (storage_auth_ty ::: nil)) :
  6 + Datatypes.length q2 <= fuel ->
  (eval_precond (S fuel) env slc_ep_transfer_loop psi (true, ([], (q2, (amount, st)))) <->
   eval_precond fuel env slc_ep_transfer_loop psi (negb (list_empty_b q2), (List.rev q2, ([], (amount, st))))).
Proof.
  intros Hfuel.
  simpl.
  rewrite slc_ep_transfer_loop_body_correct by my_simple_fuel.
  simpl slc_ep_transfer_loop_body_spec.
  unfold slc_ep_transfer_loop.
  destruct q2; reflexivity.
Qed.

Lemma slc_ep_transfer_loop_correct3
      env
      fuel
      psi
      (x : data (pair timestamp mutez))
      (q2 : data (list (pair timestamp mutez)))
      (amount : data mutez)
      (st : stack (storage_auth_ty ::: nil)) :
  7 + Datatypes.length q2 <= fuel ->
  (eval_precond (S fuel) env slc_ep_transfer_loop psi (true, ([], (x :: q2, (amount, st)))) <->
   eval_precond fuel env slc_ep_transfer_loop psi (true, (List.rev (x :: q2), ([], (amount, st))))).
Proof.
  intros Hfuel. simpl.
  rewrite slc_ep_transfer_loop_body_correct by my_simple_fuel.
  reflexivity.
Qed.

Lemma slc_ep_transfer_loop_correct4
      env
      fuel
      psi
      (amount : data mutez)
      (st : stack (storage_auth_ty ::: nil)) :
  1 <= fuel ->
  (eval_precond fuel env slc_ep_transfer_loop psi (false, ([], ([], (amount, st)))) <->
   psi (([], ([], (amount, st))))).
Proof.
  intros Hfuel. do 1 more_fuel. simpl. intuition.
Qed.

Lemma slc_ep_transfer_loop_correct2
      env
      fuel
      psi
      (q1 q2 : data (list (pair timestamp mutez)))
      (amount : data mutez)
      (st : stack (storage_auth_ty ::: nil)) :
      6 + Datatypes.length q1 + Datatypes.length q2 <= fuel ->
      queue_cut_before_now q1 (now env) = false ->
      eval_precond (Datatypes.length q1 + 1 + fuel) env slc_ep_transfer_loop
                   psi (true, (q1, (q2, (amount, st)))) <->
      exists amount',
        allowed_amount q1 amount (now env) amount' /\
        eval_precond fuel env slc_ep_transfer_loop
                     psi (negb (list_empty_b q2), (List.rev q2,([], (amount',st)))).
Proof.
  intros Hfuel Hqueue_cut.
  destruct q1.
  - simpl (Datatypes.length _ + 1 + fuel).
    rewrite slc_ep_transfer_loop_correct3'.
    + simpl.
      rewrite ex_eq_simpl.
      destruct q2; more_fuel; reflexivity.
    + assumption.

  - simpl Datatypes.length.
    rewrite <- Nat.add_assoc.
    replace (2 + fuel) with (S (S fuel)) by omega.
    rewrite slc_ep_transfer_loop_correct2'; try my_simple_fuel; try assumption.
    apply forall_ex. intro amount'.
    now rewrite slc_ep_transfer_loop_correct3' by my_simple_fuel.
Qed.

Lemma queue_cut_before_now_allowed_amount :
  forall (q1 q2 : (data (list (pair timestamp mutez)))) ts tresh1 tresh,
    queue_cut_before_now q1 ts = true ->
    allowed_amount (q1 ++ q2) tresh ts tresh1 <-> allowed_amount q1 tresh ts tresh1.
Proof.
  intros q1 q2 ts tresh1.

  induction q1.
  + now simpl.
  + destruct a as (ts0, tz).
    rewrite <- List.app_comm_cons.
    simpl.

    intros tresh H.
    repeat rewrite Z_match_compare_gt in *.

    destruct ((ts <? ts0)%Z).
    * intuition.
    * apply forall_ex. intro new_rem. now rewrite IHq1.
Qed.

Lemma remove_past_no_now :
  forall q n,
    queue_cut_before_now q n = false ->
    remove_past q n = [].
Proof. simpl. intros.
       induction q. now simpl.
       destruct a.
       simpl in *.
       destruct (d ?= n)%Z; auto.
       inversion H.
Qed.

Lemma update_queue_not_in  :
  forall q1 q2 ts,
    queue_cut_before_now q1 ts = false ->
    update_queue q1 q2 ts =
    update_queue (List.rev q2) [] ts.
Proof.
  simpl. intros q1 q2 ts H. unfold update_queue.
  rewrite H.
  destruct (queue_cut_before_now (List.rev q2) ts) eqn:HqueueCut.
  - simpl comparable_data in HqueueCut.
    rewrite HqueueCut.
    reflexivity.
  - simpl comparable_data in HqueueCut.
    rewrite HqueueCut.
    now rewrite remove_past_no_now.
Qed.

Lemma Hupdate_queue_no_now self_ty (env : @proto_env self_ty):
  forall (q1 q2 : data (list (pair timestamp mutez))),
    queue_cut_before_now q1 (now env) = false ->
    queue_cut_before_now (List.rev q2) (now env) = false ->
    ([], []) = update_queue q1 q2 (now env).
Proof.
  intros q1 q2 Hq1 Hq2.
  unfold update_queue. rewrite Hq1.
  now rewrite remove_past_no_now.
Qed.

Lemma allowed_amount_app1 :
  forall q1 ts0 a a1 a2 q2,
    queue_cut_before_now q1 ts0 = false ->
    allowed_amount q1 a ts0 a1 ->
    allowed_amount q2 a1 ts0 a2 ->
    allowed_amount (q1 ++ q2) a ts0 a2.
Proof.
  simpl. intros q1.
  induction q1 as [|(ts,mt)]; intros ts0 a a1 a2 q2.
  - simpl. intuition congruence.
  - rewrite <- List.app_comm_cons.
    simpl.
    repeat rewrite Z_match_compare_gt.
    destruct ((ts0 <? ts)%Z) eqn:Heq; [intro H; inversion H|].
    intros Hsort [a1' [Hadd1 Hq1']] Hq2.
    exists a1'. intuition.
    apply IHq1 with a1; assumption.
Qed.

Lemma allowed_amount_app2 :
  forall q1 ts0 a a2 q2,
    queue_cut_before_now q1 ts0 = false ->
    allowed_amount (q1 ++ q2) a ts0 a2 ->
    exists a1,
      allowed_amount q1 a ts0 a1 /\
      allowed_amount q2 a1 ts0 a2.
Proof.
  simpl. intros q1.
  induction q1 as [|(ts,mt)].
  - simpl. eauto.
  - simpl.
    intros ts0 a a2 q2.
    repeat rewrite Z_match_compare_gt.
    destruct (ts0 <? ts)%Z eqn:Hts0LtTs; [intro H; inversion H|].
    intros Hqueue_cut [a' [Ha' Hallowed']].
    specialize (IHq1 _ _ _ _ Hqueue_cut Hallowed') as [a1 [Hq1 Hq2]].
    exists a1.
    rewrite Z_match_compare_gt. rewrite Hts0LtTs. eauto.
Qed.

Lemma allowed_amount_app :
  forall q1 ts0 a a2 q2,
    queue_cut_before_now q1 ts0 = false ->
    allowed_amount (q1 ++ q2) a ts0 a2 <->
    exists a1,
      allowed_amount q1 a ts0 a1 /\
      allowed_amount q2 a1 ts0 a2.
Proof.
  simpl. split.
  now apply allowed_amount_app2.
  intros [a1 [Ha1 Ha1']].
  now apply allowed_amount_app1 with a1.
Qed.

Lemma slc_ep_transfer_loop_correct
      env
      fuel
      psi
      (q1 q2 : data (list (pair timestamp mutez)))
      (amount : data mutez)
      (st : stack (storage_auth_ty ::: nil)) :
  2 * Datatypes.length q1 + 2 * Datatypes.length q2 + 8 <= fuel ->
  eval_precond fuel env slc_ep_transfer_loop psi (true, (q1, (q2, (amount, st)))) <->
  (exists (amount' : data mutez),
      let (q1', q2') := update_queue q1 q2 (now env) in
      allowed_amount (q1 ++ List.rev q2) amount (now env) amount' /\
      psi (q1', (q2', (amount', st)))).
Proof.
  intros Hfuel.

  destruct (queue_cut_before_now q1 (now env)) eqn:Hqueue.

  (* If now is in q1 *)
  - rewrite slc_ep_transfer_loop_correct1; [| simple_fuel | assumption].
    unfold update_queue. rewrite Hqueue.
    ex_under (rewrite queue_cut_before_now_allowed_amount at 1 by assumption).
    reflexivity.

  (* If now is not in q1 *)
  - (* extract fuel *)
    fuel_replace
      ((Datatypes.length q1 + 1) +
       (Datatypes.length q1 + 2 * Datatypes.length q2 + 7)).
    more_fuel_add.

    rewrite slc_ep_transfer_loop_correct2; [| simple_fuel | assumption].

    destruct q2.

    (* if q2 is empty *)
    + rewrite update_queue_not_in by apply Hqueue. simpl.
      rewrite List.app_nil_r.

      apply forall_ex. intro amount'.
      apply and_both.
      apply slc_ep_transfer_loop_correct4; try simple_fuel.

    (* if q2 is non-empty *)
    + destruct (update_queue q1 (d :: q2) (now env)) eqn:Heq. simpl in d0.
      ex_under (rewrite allowed_amount_app at 1 by assumption).
      rewrite ex_2. rewrite ex_order. apply forall_ex; intro amount1.
      rewrite underex_and_assoc. rewrite <- ex_and_comm. apply and_both.

      unfold update_queue in Heq. rewrite Hqueue in Heq.
      apply and_pair_eq in Heq as [Heq1 Heq2].
      subst l. subst d0.

      destruct (queue_cut_before_now (List.rev (d :: q2)) (now env)) eqn:HnowInQ2; try assumption.

      (* If now is in (List.rev (d :: q2)) *)
      * rewrite slc_ep_transfer_loop_correct1; [reflexivity| | assumption].
        (* fuel arithmetic *)
        simpl (Datatypes.length []). rewrite List.rev_length. simple_fuel.

      (* If now is not in (List.rev (d :: q2)) *)
      * (* extract fuel *)
        fuel_replace
          ((Datatypes.length (List.rev (d :: q2)) + 1) +
           (Datatypes.length q1 + Datatypes.length (d :: q2) + 6));
          [|rewrite List.rev_length; simpl; omega].
        more_fuel_add.

        rewrite slc_ep_transfer_loop_correct2; [| |assumption].
        -- apply forall_ex; intro amount'.
           rewrite slc_ep_transfer_loop_correct4; [|my_simple_fuel].
           rewrite remove_past_no_now by assumption.
           reflexivity.
        -- rewrite List.rev_length.
           simpl Datatypes.length in *.
           omega.
Qed.

Definition sig_header_ty :=
  (pair
     (contract parameter_ty)
     chain_id).

Definition slc_ep_transfer1_check_signature_spec
    (env : @proto_env (Some (parameter_ty, None)))
    (transactions : data (list (pair mutez (contract unit))))
    (slave_key : data key)
    (slave_signature : data signature)
    (slave_key_hash new_slave_key_hash : data key_hash)
    (time_limit : data int)
    (queue_left queue_right : data (list (pair timestamp mutez)))
    (threshold : data mutez)
    (master_salt slave_salt : data nat)
    (master_key_hash : data key_hash)
    (psi : stack (list (pair mutez (contract unit)) :::
                            list operation ::: mutez ::: key_hash ::: int ::: mutez ::: list (pair timestamp mutez) :::
                            list (pair timestamp mutez) ::: storage_auth_ty ::: nil) -> Prop)
  :=
  hash_key env slave_key = slave_key_hash /\
  check_signature env slave_key slave_signature
                  (pack env (pair (list (pair mutez (contract unit))) key_hash) I (transactions, new_slave_key_hash)
                        ++ pack env sig_header_ty I (self env None I, (chain_id_ env))
                        ++ pack env nat I slave_salt)%string = true /\
  (exists (threshold_gc : data mutez) ,
      let (q1', q2') := update_queue queue_left queue_right (now env) in
      allowed_amount (queue_left ++ List.rev queue_right) threshold (now env) threshold_gc /\
       psi
              (transactions,
               ([],
                (0 ~Mutez,
                 (new_slave_key_hash,
                  (time_limit,
                   (threshold_gc,
                    (q1',
                     (q2', ((master_key_hash, (master_salt, (slave_salt + 2)%N)), tt)))))))))).
Transparent add.
Opaque N.add.
Opaque tez.of_Z.

Lemma slc_ep_transfer1_check_signature_correct
        (env : @proto_env (Some (parameter_ty, None)))
        (transactions : data (list (pair mutez (contract unit))))
        (slave_key : data key)
        (slave_signature : data signature)
        (slave_key_hash new_slave_key_hash : data key_hash)
        (time_limit : data int)
        (queue_left queue_right : data (list (pair timestamp mutez)))
        (threshold : data mutez)
        (master_salt slave_salt : data nat)
        (master_key_hash : data key_hash)
        (psi : stack (list (pair mutez (contract unit)) :::
                         list operation ::: mutez ::: key_hash ::: int ::: mutez ::: list (pair timestamp mutez) :::
                         list (pair timestamp mutez) ::: storage_auth_ty ::: nil) ->
               Prop) :
  forall fuel,
    11 + Datatypes.length queue_left * 2 + Datatypes.length queue_right * 2 <= fuel ->
    let params_transfer : data parameter_transfer_ty := ((transactions, new_slave_key_hash), (slave_key, slave_signature)) in
    let storage_context : data storage_context_ty := (slave_key_hash, ((threshold, time_limit), (queue_left, queue_right))) in
    let storage_auth : data storage_auth_ty := (master_key_hash, (master_salt, slave_salt)) in
    eval_seq_precond fuel env (slc_ep_transfer1_check_signature)
                 psi (params_transfer, (storage_context, (storage_auth, tt)))
    <->
    slc_ep_transfer1_check_signature_spec
      env transactions slave_key slave_signature slave_key_hash new_slave_key_hash
      time_limit queue_left queue_right
      threshold master_salt slave_salt master_key_hash
      psi.
Proof.
  intros fuel Hfuel params_transfer storage_context storage_auth.
  unfold slc_ep_transfer1_check_signature.
  remember slc_ep_transfer_loop as transfer_loop.
  change 11 with (6 + 5) in Hfuel.
  repeat rewrite <- plus_assoc in Hfuel.
  more_fuel_add.
  unfold eval_seq_precond.
  cbn.
  repeat rewrite fold_eval_precond.
  unfold slc_ep_transfer1_check_signature_spec.

  rewrite (eqb_eq key_hash).

  apply and_both_0.
  apply eq_sym_iff.
  apply and_both.

  rewrite Heqtransfer_loop.
  (* todo: rewrite precond (eval ) in lemmes to eval_precond *)
  rewrite slc_ep_transfer_loop_correct.
  - apply forall_ex.
    intro amount'.
    destruct (update_queue queue_left queue_right (now env)) eqn:Hq1q2.
    apply and_both.

    rewrite N.add_comm.
    reflexivity.

  (* fuel stuff *)
  - my_simple_fuel.
Qed.

Lemma slc_ep_transfer3_register_correct
      env
      fuel
      psi
      (transaction_oplist : data (list operation))
      (transaction_list_total : data mutez)
      (new_slave_key_hash : data key_hash)
      (time_limit : data int)
      (threshold : data mutez)
      (q1 q2 : data (list (pair timestamp mutez)))
      (st : data storage_auth_ty) :
  7 <= fuel ->
  eval_precond fuel env slc_ep_transfer3_register
                 psi
                (transaction_oplist,
                 (transaction_list_total,
                  (new_slave_key_hash,
                   (time_limit,
                    (threshold,
                     (q1, (q2, (st, tt)))))))) <->
  exists new_threshold,
    let new_storage_context : data storage_context_ty :=
        (new_slave_key_hash,
         ((new_threshold, time_limit),
          (q1, ((now env + time_limit)%Z, transaction_list_total) :: q2))) in
    sub _ _ _ Sub_variant_tez_tez threshold transaction_list_total = Return new_threshold /\
    psi (transaction_oplist, (new_storage_context, (st, tt))).
Proof.
  intros Hfuel.
  simpl.
  do 7 (more_fuel; simpl eval_precond).
  rewrite precond_exists.
  reflexivity.
Qed.

Open Scope string_scope.

Definition slc_spec (env : @proto_env (Some (parameter_ty, None))) (fuel : Datatypes.nat) (input : data (pair parameter_ty storage_ty)) (output : data (pair (list operation) (storage_ty))) :=
  let '(param, storage) := input in
  let '(storage_context, (master_key_hash, (master_salt, slave_salt))) := storage in
  let '(slave_key_hash, ((threshold, time_limit), (queue_left, queue_right))) := storage_context in
  match param with
  (* Entrypoint: Receive *)
  | inl _ =>
     output = (nil, storage)
  (* Entrypoint:  Master *)
  | (inr (inl ((master_key, master_signature), payload))) =>
    hash_key env master_key = master_key_hash /\
    (* Pre-condition 2: the signature is valid *)
    check_signature env master_key master_signature
                    (pack env payload_ty I payload
                          ++ pack env sig_header_ty I (self env None I, (chain_id_ env))
                          ++ pack env nat I master_salt) = true /\
    match payload with
    | inl (new_storage_context, new_master_key_hash) =>
      (* Install new storage *)
      output = (nil, (new_storage_context, (new_master_key_hash, (master_salt + 2, slave_salt)%N)))
    | inr (build_lam _ _ _ lam, new_master_key_hash) =>
      (* Run lambda *)
      precond (eval_seq (no_self env) lam fuel (tt, tt))
              (fun '(operations, tt) =>
                 output = (operations, (storage_context, (new_master_key_hash, (master_salt + 2, slave_salt)%N))))
    end
  (* Entry point: Transfer *)
  | inr (inr ((transactions, new_slave_key_hash), (slave_key, slave_signature))) =>
    hash_key env slave_key = slave_key_hash /\
    check_signature env slave_key slave_signature
                    (pack env (pair (list (pair mutez (contract unit))) key_hash) I (transactions, new_slave_key_hash)
                          ++ pack env sig_header_ty I (self env None I, (chain_id_ env))
                          ++ pack env nat I slave_salt) = true /\
    (exists spent_amount threshold_gc new_threshold,
      (* sum(transactions) = amount *)
      total_amount_transaction_list transactions spent_amount /\
      (* allowed(queue, threshold, now) = threshold_gc *)
      allowed_amount (List.app queue_left (List.rev queue_right)) threshold (now env) threshold_gc /\
      (* new_threshold = threshold_gc - spent_amount *)
      sub _ _ _ Sub_variant_tez_tez threshold_gc spent_amount = Return new_threshold /\
      let new_operations : data (list operation) :=
          List.rev (List.map
                      (fun '(transfered_amount, destination) => transfer_tokens unit I tt transfered_amount destination)
                      transactions) in
      let new_queue :=
          (let (l1', l2') := update_queue queue_left queue_right (now env) in
           (l1', cons ((now env + time_limit)%Z, spent_amount) l2')) in
      let new_context : data storage_context_ty :=
          (new_slave_key_hash, ((new_threshold, time_limit), new_queue)) in
      output = (new_operations, (new_context, (master_key_hash, (master_salt, (slave_salt + 2)%N)))))
  end.

Definition slc_fuel_bound (input : data (pair parameter_ty storage_ty)) :=
    let '(param, storage) := input in
    let '(storage_context, (master_key_hash, master_salt)) := storage in
    let '(slave_key_hash, ((threshold, time_limit), (queue_left, queue_right))) := storage_context in
    match param with
      (* entry point: receive *)
      | inl _ => 0
      (* entry point: master *)
      | inr (inl _) => 5
      (* entry point: transfer *)
      | inr (inr ((transactions, _), _)) => Datatypes.length transactions + Datatypes.length queue_left * 2 + Datatypes.length queue_right * 2 + 11
    end.


Lemma slc_ep_transfer_correct :
  forall env (p3 : data parameter_transfer_ty) (slave_key_hash : data key_hash) (threshold : data mutez) (time_limit : data int)
         (queue_left queue_right : data (list (pair timestamp mutez))) (master_key_hash : data key_hash) (master_salt slave_salt : data nat)
         (output : data (pair (list operation) storage_ty)) (fuel : Datatypes.nat),
    (let (d, _) := p3 in
     let (transactions, _) := d in Datatypes.length transactions + Datatypes.length queue_left * 2 + Datatypes.length queue_right * 2 + 12) <=
    fuel ->
    eval_seq_precond (4 + fuel) env dsl (fun x : stack [pair (list operation) storage_ty] => x = (output, tt))
                 (inr (inr p3), (slave_key_hash, (threshold, time_limit, (queue_left, queue_right)), (master_key_hash, (master_salt, slave_salt))), tt) <->
    slc_spec env (S fuel)
             (inr (inr p3), (slave_key_hash, (threshold, time_limit, (queue_left, queue_right)), (master_key_hash, (master_salt, slave_salt))))
             output.
Proof.
  intros env p3 slave_key_hash threshold time_limit queue_left queue_right master_key_hash master_salt slave_salt output fuel Hfuel.

  unfold dsl.
  remember slc_ep_transfer as prog.
  destruct p3 as ((transactions, new_slave_key_hash), (slave_key, slave_signature)).
  unfold eval_seq_precond.
  rewrite Nat.add_comm in Hfuel.
  simpl eval_seq_precond_body.
  do 1 more_fuel'; simpl.
  rewrite Nat.add_comm in Hfuel.
  repeat rewrite fold_eval_precond.
  rewrite Heqprog. unfold slc_ep_transfer.

  rewrite Nat.add_comm in Hfuel.
  rewrite fold_eval_seq_precond_aux.
  rewrite eval_seq_assoc.
  rewrite slc_ep_transfer1_check_signature_correct; [| my_simple_fuel].
  unfold slc_ep_transfer1_check_signature_spec.
  unfold slc_spec.
  apply and_both.
  apply and_both.

  destruct (update_queue queue_left queue_right _) eqn:Hupdate_queue. simpl in d.

  rewrite ex_order.
  apply forall_ex; intro threshold_gc.
  unfold seq_aux.
  change (eval_seq_precond ?fuel env (SEQ ?i1 ?i2) ?psi ?st) with (eval_precond fuel env i1 (eval_seq_precond fuel env i2 psi) st).
  unfold slc_ep_transfer2_transaction_iter.
  rewrite (slc_ep_transfer2_transaction_iter_correct env _ _ _ _ (S (S fuel))); [| my_simple_fuel].
  unfold total_amount_transaction_list.
  rewrite iff_comm.

  rewrite <- underex2_and_comm at 1.
  rewrite underex2_and_assoc.

  rewrite <- ex2_and_comm.
  apply and_both.

  apply forall_ex; intro spent_sum.

  rewrite underex_and_comm.
  rewrite <- ex_and_comm at 1.
  apply and_both.

  change (eval_seq_precond ?fuel env (SEQ ?i1 ?i2) ?psi ?st) with (eval_precond fuel env i1 (eval_seq_precond fuel env i2 psi) st).
  rewrite slc_ep_transfer3_register_correct; [| my_simple_fuel].

  apply forall_ex; intro final_threshold.

  apply and_both.
  unfold eval_seq_precond; simpl.
  rewrite and_pair_eq.
  rewrite List.app_nil_r.
  intuition.
Qed.

Lemma slc_ep_master_correct:
  forall env (p2 : data parameter_master_ty) (slave_key_hash : data key_hash) (threshold : data mutez) (time_limit : data int)
         (queue_left queue_right : data (list (pair timestamp mutez))) (master_key_hash : data key_hash) (master_salt slave_salt : data nat)
         (output : data (pair (list operation) storage_ty)) (fuel : Datatypes.nat),
    5 <= fuel ->
    eval_seq_precond (5 + fuel) env dsl (fun x : stack [pair (list operation) storage_ty] => x = (output, tt))
                 (inr (inl p2), (slave_key_hash, (threshold, time_limit, (queue_left, queue_right)), (master_key_hash, (master_salt, slave_salt))), tt) <->
    slc_spec env fuel
             (inr (inl p2), (slave_key_hash, (threshold, time_limit, (queue_left, queue_right)), (master_key_hash, (master_salt, slave_salt))))
             output.
Proof.
  intros env p2 slave_key_hash threshold time_limit queue_left queue_right master_key_hash master_salt slave_salt output fuel Hfuel.
  destruct p2 as ((key, signature), payload).
  unfold eval_seq_precond.
  do 5 (more_fuel; simpl).
  repeat rewrite fold_eval_precond.
  rewrite (eqb_eq key_hash).
  unfold slc_spec. rewrite N.add_comm.

  destruct payload as [ (foo, slave_key_hash') | ((lam_ff, lam), slave_key_hash') ].

  + unfold data. simpl. intuition; congruence.

  + unfold slc_spec.

    apply and_both_0. apply eq_sym_iff.
    apply and_both.

    change (@eval_seq_precond_body (@eval_precond ?fuel)) with (@eval_seq_precond fuel).
    rewrite <- (eval_seq_precond_correct lam).
    apply precond_eqv.
    intros [st1 []].
    intuition.
    inversion H. f_equal.
    rewrite H. reflexivity.
Qed.

Theorem slc_correct env input output :
  forall fuel,
    fuel >= slc_fuel_bound input ->
    eval_seq env dsl (5 + fuel) (input, tt) = Return (output, tt) <->
    slc_spec env fuel input output.
Proof.
  unfold ">=".
  intros fuel Hfuel.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  destruct input as (param,
                     ((slave_key_hash, ((threshold, time_limit), (queue_left, queue_right))),
                        (master_key_hash, (master_salt, slave_salt)))).

  destruct param as [ [] | [ p2 | p3 ] ]; simpl in Hfuel.

  (* Entry point: receive *)
  - unfold eval_seq_precond, data. simpl.
    rewrite pair_equal_spec.
    intuition.
  (* Entry point : master call *)
  - apply slc_ep_master_correct. apply Hfuel.
  (* Entry point : transfer *)
  - apply slc_ep_transfer_correct. destruct p3 as ((transactions, _), _).
    apply le_n_S in Hfuel.
    rewrite <- Nat.add_succ_r in Hfuel.
    assumption.
Qed.

End Spending_limit_contract_verification.
