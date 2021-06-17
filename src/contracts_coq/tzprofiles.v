(* Open Source License *)
(* Copyright (c) 2021 Michael J. Klein, TQ Tezos, Spruce Systems, Inc. *)

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
Require Import entrypoints syntax macros main semantics comparable util.
Require Import ZArith.
Require Import Lia.
Import error.
Require List.
Require tez.
Require map.
Require String.

Require tzprofiles_string.

Module raw.

Require Import String.

(* See micheline2michelson.v +29 *)
(* Cpair only _currently_ allows *)
(* simple_comparable_type's in its first argument *)

(* (set (pair (pair string bytes) string)) *)
(* ==>=>> *)
(* (set (pair string (pair string bytes))) *)
Definition tzprofiles_string_2 : string := "
parameter (pair (set (pair string (pair string bytes))) bool) ;
storage (pair (pair (set %claims (pair string (pair string bytes))) (string %contract_type))
        (pair (big_map %metadata string bytes) (address %owner))) ;
code { UNPAIR ;
       SWAP ;
       DUP ;
       DUG 2 ;
       CDR ;
       CDR ;
       SENDER ;
       COMPARE ;
       NEQ ;
       IF { PUSH string ""Unauthorized."" ; FAILWITH } {} ;
       UNPAIR ;
       DUP 3 ;
       CDR ;
       CDR ;
       DUP 4 ;
       CDR ;
       CAR ;
       PAIR ;
       DUP 4 ;
       CAR ;
       CDR ;
       DIG 4 ;
       CAR ;
       CAR ;
       DIG 3 ;
       ITER { SWAP ; DUP 5 ; DIG 2 ; UPDATE } ;
       DIG 3 ;
       DROP ;
       PAIR ;
       PAIR ;
       NIL operation ;
       PAIR }
".

End raw.

Lemma new_tzprofiles_string : raw.tzprofiles_string_2 <> tzprofiles_string.tzprofiles_string.
Proof. unfold raw.tzprofiles_string_2; unfold tzprofiles_string.tzprofiles_string; congruence. Qed.

Module source.
  Definition contract_file_M :=
    main.contract_file_M raw.tzprofiles_string_2 9.
    (* main.michelson_M raw.tzprofiles_string_2 9. *)
  (* Eval cbv in (main.parsed_M raw.tzprofiles_string_2 9). *)
  (* Eval cbv in (main.michelson_M raw.tzprofiles_string_2 9). *)

  Definition contract_file := Eval cbv in (error.extract contract_file_M I).
End source.

Definition parameter_ty := ep_leaf
  (pair (set (Cpair string (Cpair string bytes))) bool).

Module tzprofiles(C:ContractContext).

(* storage (pair (pair (set %claims (pair (pair string bytes) string)) (string %contract_type)) *)
(*         (pair (big_map %metadata string bytes) (address %owner))) ; *)
Definition storage_ty :=
  (pair (pair (set (Cpair string (Cpair string bytes))) string)
        (pair (big_map string bytes) address)).

Definition tzprofiles : full_contract _ parameter_ty None storage_ty :=
  Eval cbv in contract_file_code source.contract_file.

Import String.

Definition raw_tzprofiles_iter_body :
  instruction_seq
    (Some
       (ep_leaf
          (pair
             (set
                (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
             (Comparable_type bool)), None)) false
    (pair (Comparable_type syntax_type.string)
       (pair (Comparable_type syntax_type.string) (Comparable_type bytes))
     ::: set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
         ::: Comparable_type syntax_type.string
             ::: pair (big_map syntax_type.string (Comparable_type bytes))
                   (Comparable_type address)
                 ::: Comparable_type bool ::: nil)
    (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
     ::: Comparable_type syntax_type.string
         ::: pair (big_map syntax_type.string (Comparable_type bytes))
               (Comparable_type address) ::: Comparable_type bool ::: nil).
Proof.
  pose (H := tzprofiles).
  unfold tzprofiles in H.

  do 25 match goal with
  | _ := SEQ ?x ?y |- _ =>
      (* pose x; *)
      pose (H2 := y);
      clear H;
      rename H2 into H
  end.

  match goal with
  | _ := SEQ ?x ?y |- _ =>
      pose (H2 := x);
      (* pose (H2 := y); *)
      clear H;
      rename H2 into H
  end.

  match goal with
  | _ := ITER ?x |- _ =>
      pose (H2 := x);
      (* pose (H2 := y); *)
      clear H;
      rename H2 into H
  end.

  assumption.
Defined.

Definition tzprofiles_iter_body :
  instruction_seq
    (Some
       (ep_leaf
          (pair
             (set
                (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
             (Comparable_type bool)), None)) false
    (pair (Comparable_type syntax_type.string)
       (pair (Comparable_type syntax_type.string) (Comparable_type bytes))
     ::: set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
         ::: Comparable_type syntax_type.string
             ::: pair (big_map syntax_type.string (Comparable_type bytes))
                   (Comparable_type address)
                 ::: Comparable_type bool ::: nil)
    (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
     ::: Comparable_type syntax_type.string
         ::: pair (big_map syntax_type.string (Comparable_type bytes))
               (Comparable_type address) ::: Comparable_type bool ::: nil) :=
  Eval lazy in raw_tzprofiles_iter_body.

Definition raw_tzprofiles_iter :
 instruction
   (Some
      (ep_leaf
         (pair
            (set
               (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
            (Comparable_type bool)), None)) false
   (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
    ::: set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
        ::: Comparable_type syntax_type.string
            ::: pair (big_map syntax_type.string (Comparable_type bytes))
                  (Comparable_type address)
                ::: Comparable_type bool ::: nil)
   (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
    ::: Comparable_type syntax_type.string
        ::: pair (big_map syntax_type.string (Comparable_type bytes))
              (Comparable_type address) ::: Comparable_type bool ::: nil).
Proof.
  pose (H := tzprofiles).
  unfold tzprofiles in H.

  do 25 match goal with
  | _ := SEQ ?x ?y |- _ =>
      (* pose x; *)
      pose (H2 := y);
      clear H;
      rename H2 into H
  end.

  match goal with
  | _ := SEQ ?x ?y |- _ =>
      pose (H2 := x);
      (* pose (H2 := y); *)
      clear H;
      rename H2 into H
  end.

  assumption.
Defined.

Definition tzprofiles_iter :
 instruction
   (Some
      (ep_leaf
         (pair
            (set
               (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
            (Comparable_type bool)), None)) false
   (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
    ::: set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
        ::: Comparable_type syntax_type.string
            ::: pair (big_map syntax_type.string (Comparable_type bytes))
                  (Comparable_type address)
                ::: Comparable_type bool ::: nil)
   (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
    ::: Comparable_type syntax_type.string
        ::: pair (big_map syntax_type.string (Comparable_type bytes))
              (Comparable_type address) ::: Comparable_type bool ::: nil) :=
  Eval lazy in raw_tzprofiles_iter.

Lemma tzprofiles_iter_to_body_correct :
  tzprofiles_iter = @ITER _ _ _
    (Mk_iter _ _
      (Iter_variant_set (Cpair _ (Cpair _ (Comparable_type_simple _)))))
    _
    tzprofiles_iter_body.
Proof. reflexivity. Qed.



Module semantics := Semantics C. Import semantics.
Export semantics.

(* Check eval_seq. *)

Lemma tzprofiles_iter_body_raw_spec_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (* (x0 : data (pair *)
      (*   (Comparable_type syntax_type.string) *)
      (*   (pair (Comparable_type syntax_type.string) (Comparable_type bytes)))) *)

      (x0_1 : data (Comparable_type syntax_type.string))
      (x0_2 : data (Comparable_type syntax_type.string))
      (x0_3 : data (Comparable_type bytes))

      (x1 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (x2 : data (Comparable_type syntax_type.string))
      (x3 : data (pair
        (big_map syntax_type.string (Comparable_type bytes))
        (Comparable_type address)))
      (x4 : data (Comparable_type bool))

      (y0 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (y1 : data (Comparable_type syntax_type.string))
      (y2 : data (pair (big_map syntax_type.string (Comparable_type bytes))
                 (Comparable_type address)))
      (y3 : data (Comparable_type bool))
      (fuel : Datatypes.nat) :
  eval_seq env tzprofiles_iter_body (6 + fuel)
    ((x0_1, (x0_2, x0_3)), (x1, (x2, (x3, (x4, tt))))) =
    Return (y0, (y1, (y2, (y3, tt))))
  <->
  (update _ _ _ (Update_variant_set (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
    (x0_1, (x0_2, x0_3)) x4 x1,
  (x2, (x3, (x4, tt)))) =
  (y0,
  (y1, (y2, (y3, tt)))).
Proof.
  remember (6 + fuel) as fuel2.
  assert (6 <= fuel2) by lia.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  unfold tzprofiles_iter_body.

  do 6 (more_fuel; simpl).
  reflexivity.
Qed.

(* Lemma tzprofiles_iter_raw_spec_correct *)
(*       (env : @proto_env (Some (parameter_ty, None))) *)

(*       (x0 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes)))) *)
(*       (x1 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes)))) *)
(*       (x2 : data (Comparable_type syntax_type.string)) *)
(*       (x3 : data (pair (big_map syntax_type.string (Comparable_type bytes)) (Comparable_type address))) *)
(*       (x4 : data (Comparable_type bool)) *)

(*       (y0 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes)))) *)
(*       (y1 : data (Comparable_type syntax_type.string)) *)
(*       (y2 : data (pair (big_map syntax_type.string (Comparable_type bytes)) *)
(*                  (Comparable_type address))) *)
(*       (y3 : data (Comparable_type bool)) *)
(*       (fuel : Datatypes.nat) : *)

(*   eval env tzprofiles_iter (6 + fuel) *)
(*     (x0, (x1, (x2, (x3, (x4, tt))))) = *)
(*     Return (y0, (y1, (y2, (y3, tt)))) *)
(*   <-> *)
(*   false. *)
(* Proof. *)
(*   remember (6 + fuel) as fuel2. *)
(*   assert (6 <= fuel2) by lia. *)
(*   rewrite return_precond. *)
(*   (1* rewrite eval_seq_precond_correct. *1) *)
(*   (1* unfold eval_seq_precond. *1) *)
(*   unfold tzprofiles_iter. *)


(*   Check (precond_iter_bounded *)
(*     (@Some (entrypoint_tree * Datatypes.option annotation) (parameter_ty, @None annotation)) *)
(*     false *)
(*     env *)
(*   ). *)

(*   Check set.destruct. *)
(*   Locate set.set. *)
(*   Print set.set. *)
(*   Print data_aux. *)
(*   Print data. *)
(*   Locate "{ _ | _ }". *)
(*   Check proj1_sig. *)
(*   Locate proj1. *)
(*   (1* Search (sig -> _). *1) *)
(*   Check (forall a (xs : set.set (comparable_data a) (compare a)), proj1_sig xs = nil). *)
(*   (1* List.list. *1) *)
(*   (1* Search set.set List.list. *1) *)

(*   Check TODO_prove_precond_ITER_ignores_set_and_treats_it_like_the_list_in_sig. *)

(*   precond (eval env (ITER body) fuel (xs, input_stack)) psi = *)
(*   precond (eval env (ITER body) fuel (proj1_sig xs, input_stack)) psi. *)


(*   Lemma precond_iter_bounded st tff env a (l : data (list a)) A (body : instruction_seq st tff (a ::: A) A) *)
(*         fuel_bound body_spec *)
(*     (Hbody_correct : *)
(*        forall fuel (x : data a) (input_stack : stack A) (psi : stack A -> Prop), *)
(*         fuel_bound <= fuel -> *)
(*         precond (eval_seq env body fuel (x, input_stack)) psi *)
(*         <-> body_spec psi x input_stack) *)
(*     (Hbody_spec_extensional : *)
(*        forall psi1 psi2 x input_stack, *)
(*         (forall x, psi1 x <-> psi2 x) -> *)
(*         body_spec psi1 x input_stack <-> body_spec psi2 x input_stack) : *)



(*   Can't use precond_iter_bounded since it's specialized to lists. *)
(*   It should be possible to replace lists with sets in it somehow. *)

(*   Search ITER. *)
(*   _ *)


(*   rewrite precond_iter_bounded. *)
(*   precond_iter_bounded *)



(*   do 6 (more_fuel; simpl). *)
(*   reflexivity. *)
(* Qed. *)

(* Definition tzprofiles_iter : *)
(*  instruction *)
(*    (Some *)
(*       (ep_leaf *)
(*          (pair *)
(*             (set *)
(*                (Cpair syntax_type.string (Cpair syntax_type.string bytes))) *)
(*             (Comparable_type bool)), None)) false *)
(*    (set (Cpair syntax_type.string (Cpair syntax_type.string bytes)) *)
(*     ::: set (Cpair syntax_type.string (Cpair syntax_type.string bytes)) *)
(*         ::: Comparable_type syntax_type.string *)
(*             ::: pair (big_map syntax_type.string (Comparable_type bytes)) *)
(*                   (Comparable_type address) *)
(*                 ::: Comparable_type bool ::: nil) *)
(*    (set (Cpair syntax_type.string (Cpair syntax_type.string bytes)) *)
(*     ::: Comparable_type syntax_type.string *)
(*         ::: pair (big_map syntax_type.string (Comparable_type bytes)) *)
(*               (Comparable_type address) ::: Comparable_type bool ::: nil) := *)
(*   Eval lazy in raw_tzprofiles_iter. *)


(* Check TODO_apply_tzprofiles_iter_body_to_iter_spec. *)


(* Print tzprofiles_iter_body. *)

(* Lemma ok : Datatypes.unit. *)
(* Proof. *)
(*   pose (H := tzprofiles). *)
(*   unfold tzprofiles in H. *)

(*   Check @SEQ. *)
(*   (1* Set Printing All. *1) *)
(*   do 25 match goal with *)
(*   | _ := SEQ ?x ?y |- _ => *)
(*       (1* pose x; *1) *)
(*       pose (H2 := y); *)
(*       clear H; *)
(*       rename H2 into H *)
(*   end. *)

(*   match goal with *)
(*   | _ := SEQ ?x ?y |- _ => *)
(*       pose (H2 := x); *)
(*       (1* pose (H2 := y); *1) *)
(*       clear H; *)
(*       rename H2 into H *)
(*   end. *)

(*   match goal with *)
(*   | _ := ITER ?x |- _ => *)
(*       pose (H2 := x); *)
(*       (1* pose (H2 := y); *1) *)
(*       clear H; *)
(*       rename H2 into H *)
(*   end. *)


(*   Check SEQ. *)
(*   Search SEQ. *)
(*   Print tzprofiles. *)


(* Definition tzprofiles_spec_helper *)
(*            (env : @proto_env (Some (parameter_ty, None))) *)
(*            (claims : data (set (Cpair string (Cpair string bytes)))) *)
(*            (contract_type : data string) *)
(*            (metadata : data (big_map string bytes)) *)
(*            (owner : data address) *)
(*            (param : data parameter_ty) *)
(*            (new_storage : data storage_ty) *)
(*            (returned_operations : data (list operation)) := *)
(*   let storage : data storage_ty := *)
(*     ((claims, contract_type), *)
(*       (metadata, owner)) in *)

(*   negb (comparison_to_int (address_compare (sender env) owner) =? 0)%Z = false /\ *)
(*   (comparison_to_int (tez.compare (amount env) (0 ~Mutez)) >? 0)%Z = false /\ *)
(*   false. *)

(*   (1* match param with *1) *)
(*   (1* | inl rotateOwner => *1) *)
(*   (1*     (nil, (metadata, rotateOwner, (endpoint, type_, verification_method)), tt) = *1) *)
(*   (1*     (returned_operations, new_storage, tt) *1) *)
(*   (1* | inr (inl rotateAuth) => *1) *)
(*   (1*     (nil, (metadata, owner, (endpoint, type_, rotateAuth)), tt) = *1) *)
(*   (1*     (returned_operations, new_storage, tt) *1) *)
(*   (1* | inr (inr rotateService) => *1) *)
(*   (1*     (nil, (metadata, owner, (rotateService, verification_method)), tt) = *1) *)
(*   (1*     (returned_operations, new_storage, tt) *1) *)
(*   (1* end. *1) *)

(* Lemma tzprofiles_spec_helper_correct *)
(*       (env : @proto_env (Some (parameter_ty, None))) *)
(*       (claims : data (set (Cpair string (Cpair string bytes)))) *)
(*       (contract_type : data string) *)
(*       (metadata : data (big_map string bytes)) *)
(*       (owner : data address) *)
(*       (param : data parameter_ty) *)
(*       (new_storage : data storage_ty) *)
(*       (returned_operations : data (list operation)) *)
(*       (fuel : Datatypes.nat) : *)
(*   let storage : data storage_ty := *)
(*     ((claims, contract_type), *)
(*       (metadata, owner)) in *)
(*   eval_seq env tzprofiles (100 + fuel) ((param, storage), tt) = *)
(*     Return ((returned_operations, new_storage), tt) *)
(*   <-> tzprofiles_spec_helper env claims contract_type metadata owner param *)
(*     new_storage returned_operations. *)
(* Proof. *)
(*   intro Hfuel. *)
(*   remember (100 + fuel) as fuel2. *)
(*   assert (100 <= fuel2) by lia. *)
(*   rewrite return_precond. *)
(*   rewrite eval_seq_precond_correct. *)
(*   unfold eval_seq_precond. *)
(*   unfold tzprofiles_spec_helper. *)

(*   (more_fuel; simpl). *)
(*   (more_fuel; simpl). *)
(*   (more_fuel; simpl). *)

(*   apply and_iff_compat_l. *)

(*   destruct param as (claim_set & add_remove). *)

(*   (more_fuel; simpl). *)
(*   rewrite precond_iter_fun. *)
(*   precond_iter_bounded. *)

(*   Search UPDATE. *)
(*   Check update. *)
(*   Print update_variant. *)

(*   Check (fun a => update _ _ _ (Update_variant_set a)). *)

(*   Check (fun a b => *)
(*     List.fold_left *)
(*       (fun (memo : data (set a)) x => update _ _ _ (Update_variant_set a) x b memo)). *)

(* fun a : comparable_type => update a bool (set a) (Update_variant_set a) *)
(*      : forall a : comparable_type, *)
(*        comparable_data a -> data bool -> data (set a) -> data (set a) *)


(*   Fixpoint fold_left (l:list B) (a0:A) : A := *)
(*     match l with *)
(*       | nil => a0 *)
(*       | cons b t => fold_left t (f a0 b) *)
(*     end. *)


(*   Check TODO_define_update. *)

(*   Definition update a b c (v : update_variant a b c) : *)
(*     comparable_data a -> data b -> data c -> data c := *)
(*     match v with *)
(*     | Update_variant_set a => *)
(*       set.update _ _ (compare_eq_iff a) (lt_trans a) (gt_trans a) *)
(*     | Update_variant_map k v => *)
(*       map.update _ _ _ (compare_eq_iff k) (lt_trans k) (gt_trans k) *)
(*     | Update_variant_bigmap k _ => *)
(*       map.update _ _ _ (compare_eq_iff k) (lt_trans k) (gt_trans k) *)
(*     end. *)


(*   Search update. *)
(*   _ *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)


(*   _ *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)

(*   Search (_ /\ _ <-> _ /\ _). *)

(*   _ *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)
(*   (1* (more_fuel; simpl). *1) *)


(*   (do 3 (more_fuel; simpl); reflexivity). *)
(*   destruct param as [[rotateAuth | rotateOwner] | rotateService]; *)
(*   (do 3 (more_fuel; simpl); reflexivity). *)
(* Qed. *)

(* (1* Definition tzprofiles_spec *1) *)
(* (1*            (env : @proto_env (Some (parameter_ty, None))) *1) *)
(* (1*            (metadata : data (big_map string bytes)) *1) *)
(* (1*            (owner : data address) *1) *)
(* (1*            (endpoint : data string) *1) *)
(* (1*            (type_ : data string) *1) *)
(* (1*            (verification_method : data address) *1) *)
(* (1*            (param : data parameter_ty) *1) *)
(* (1*            (new_storage : data storage_ty) *1) *)
(* (1*            (returned_operations : data (list operation)) := *1) *)
(* (1*   let storage : data storage_ty := *1) *)
(* (1*     ((metadata, owner), *1) *)
(* (1*     ((endpoint, type_), *1) *)
(* (1*       verification_method)) in *1) *)

(* (1*   match new_storage with *1) *)
(* (1*   | ((new_metadata, new_owner), *1) *)
(* (1*     ((new_endpoint, new_type_), *1) *)
(* (1*       new_verification_method)) => *1) *)

(* (1*     sender env = owner /\ *1) *)

(* (1*     (int64bv.to_Z (tez.to_int64 (amount env)) <= 0)%Z /\ *1) *)

(* (1*     returned_operations = nil /\ *1) *)
(* (1*     new_metadata = metadata /\ *1) *)

(* (1*     match param with *1) *)
(* (1*     | inl rotateOwner => *1) *)
(* (1*         new_owner = rotateOwner /\ *1) *)
(* (1*         new_endpoint = endpoint /\ *1) *)
(* (1*         new_type_ = type_ /\ *1) *)
(* (1*         new_verification_method = verification_method *1) *)
(* (1*     | inr (inl rotateAuth) => *1) *)
(* (1*         new_owner = owner /\ *1) *)
(* (1*         new_endpoint = endpoint /\ *1) *)
(* (1*         new_type_ = type_ /\ *1) *)
(* (1*         new_verification_method = rotateAuth *1) *)
(* (1*     | inr (inr (rotateEndpoint, rotateType)) => *1) *)
(* (1*         new_owner = owner /\ *1) *)
(* (1*         new_endpoint = rotateEndpoint /\ *1) *)
(* (1*         new_type_ = rotateType /\ *1) *)
(* (1*         new_verification_method = verification_method *1) *)
(* (1*     end *1) *)
(* (1*   end. *1) *)

(* (1* Lemma tzprofiles_spec_correct *1) *)
(* (1*       (env : @proto_env (Some (parameter_ty, None))) *1) *)
(* (1*       (metadata : data (big_map string bytes)) *1) *)
(* (1*       (owner : data address) *1) *)
(* (1*       (endpoint : data string) *1) *)
(* (1*       (type_ : data string) *1) *)
(* (1*       (verification_method : data address) *1) *)
(* (1*       (param : data parameter_ty) *1) *)
(* (1*       (new_storage : data storage_ty) *1) *)
(* (1*       (returned_operations : data (list operation)) *1) *)
(* (1*       (fuel : Datatypes.nat) : *1) *)
(* (1*   let storage : data storage_ty := *1) *)
(* (1*     ((metadata, owner), *1) *)
(* (1*           ((endpoint, type_), verification_method)) in *1) *)
(* (1*   eval_seq env tzprofiles (100 + fuel) ((param, storage), tt) = *1) *)
(* (1*     Return ((returned_operations, new_storage), tt) *1) *)
(* (1*   <-> tzprofiles_spec env metadata owner endpoint type_ verification_method *1) *)
(* (1*     param new_storage returned_operations. *1) *)
(* (1* Proof. *1) *)
(* (1*   Arguments Nat.add : simpl never. *1) *)
(* (1*   simpl. *1) *)
(* (1*   Arguments Nat.add : simpl nomatch. *1) *)

(* (1*   rewrite tzprofiles_spec_helper_correct. *1) *)
(* (1*   unfold tzprofiles_spec_helper. *1) *)
(* (1*   unfold tzprofiles_spec. *1) *)

(* (1*   rewrite address_compare_iff, tez_not_gt_0. *1) *)

(* (1*   destruct param as [rotateOwner | [rotateAuth | (rotateEndpoint & rotateType)]]. *1) *)

(* (1*   - split; intro H. *1) *)
(* (1*     + repeat match goal with *1) *)
(* (1*       | H : _ /\ _ |- _ => destruct H *1) *)
(* (1*       | H : _ = _ |- _ => inversion H; destruct H *1) *)
(* (1*       | |- (let (x, y) := ?z in _) => destruct z *1) *)
(* (1*       end; *1) *)
(* (1*       tauto. *1) *)
(* (1*     + repeat match goal with *1) *)
(* (1*       | H : (let (x, y) := ?z in _) |- _ => destruct z *1) *)
(* (1*       | H : _ /\ _ |- _ => destruct H *1) *)
(* (1*       end; *1) *)
(* (1*       repeat split; try congruence; *1) *)
(* (1*       repeat f_equal; intuition. *1) *)

(* (1*   - split; intro H. *1) *)
(* (1*     + repeat match goal with *1) *)
(* (1*       | H : _ /\ _ |- _ => destruct H *1) *)
(* (1*       | H : _ = _ |- _ => inversion H; destruct H *1) *)
(* (1*       | |- (let (x, y) := ?z in _) => destruct z *1) *)
(* (1*       end; *1) *)
(* (1*       tauto. *1) *)
(* (1*     + repeat match goal with *1) *)
(* (1*       | H : (let (x, y) := ?z in _) |- _ => destruct z *1) *)
(* (1*       | H : _ /\ _ |- _ => destruct H *1) *)
(* (1*       end; *1) *)
(* (1*       repeat split; try congruence; *1) *)
(* (1*       repeat f_equal; intuition. *1) *)

(* (1*   - split; intro H. *1) *)
(* (1*     + repeat match goal with *1) *)
(* (1*       | H : _ /\ _ |- _ => destruct H *1) *)
(* (1*       | H : _ = _ |- _ => inversion H; destruct H *1) *)
(* (1*       | |- (let (x, y) := ?z in _) => destruct z *1) *)
(* (1*       end; *1) *)
(* (1*       tauto. *1) *)
(* (1*     + repeat match goal with *1) *)
(* (1*       | H : (let (x, y) := ?z in _) |- _ => destruct z *1) *)
(* (1*       | H : _ /\ _ |- _ => destruct H *1) *)
(* (1*       end. *1) *)
(* (1*       repeat split; try congruence; *1) *)
(* (1*       repeat f_equal; intuition. *1) *)
(* (1* Qed. *1) *)

End tzprofiles.

