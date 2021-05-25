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
(* ==>=>> *)
(* (list (pair string (pair string bytes))) *)
Definition tzprofiles_string_2 : string := "
parameter (pair (list (pair string (pair string bytes))) bool) ;
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
  (pair (list (Cpair string (Cpair string bytes))) bool).

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
             (list
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
             (list
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
            (list
               (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
            (Comparable_type bool)), None)) false
   (list (Cpair syntax_type.string (Cpair syntax_type.string bytes))
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
            (list
               (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
            (Comparable_type bool)), None)) false
   (list (Cpair syntax_type.string (Cpair syntax_type.string bytes))
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
      (Iter_variant_list (Cpair _ (Cpair _ (Comparable_type_simple _)))))
    _
    tzprofiles_iter_body.
Proof. reflexivity. Qed.



Module semantics := Semantics C. Import semantics.
Export semantics.

(* Check eval_seq. *)

Definition tzprofiles_iter_body_raw_spec
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
      (y3 : data (Comparable_type bool)) :=
  (update _ _ _ (Update_variant_set (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
    (x0_1, (x0_2, x0_3)) x4 x1,
  (x2, (x3, (x4, tt)))) =
  (y0,
  (y1, (y2, (y3, tt)))).

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
  tzprofiles_iter_body_raw_spec x0_1 x0_2 x0_3 x1 x2 x3 x4 y0 y1 y2 y3.
Proof.
  remember (6 + fuel) as fuel2.
  assert (6 <= fuel2) by lia.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  unfold tzprofiles_iter_body.
  unfold tzprofiles_iter_body_raw_spec.
  do 6 (more_fuel; simpl).
  reflexivity.
Qed.

Definition tzprofiles_iter_body_spec
  (psi : stack
      (set
         (Cpair syntax_type.string
            (Cpair syntax_type.string bytes))
       ::: Comparable_type syntax_type.string
           ::: pair
                 (big_map syntax_type.string
                    (Comparable_type bytes))
                 (Comparable_type address)
               ::: Comparable_type bool ::: nil) -> Prop)
   (param : data (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
   (input_stack : stack
     (set
        (Cpair syntax_type.string
           (Cpair syntax_type.string bytes))
      ::: Comparable_type syntax_type.string
          ::: pair
                (big_map syntax_type.string
                   (Comparable_type bytes))
                (Comparable_type address)
              ::: Comparable_type bool ::: nil)) : Prop.
Proof.
  simpl in input_stack; simpl in psi.
  destruct param as (x0_1 & (x0_2 & x0_3)).
  destruct input_stack as (x1 & (x2 & (x3 & (x4 & tt_)))).

  exact (exists y0 y1 y2 y3,
    tzprofiles_iter_body_raw_spec x0_1 x0_2 x0_3 x1 x2 x3 x4 y0 y1 y2 y3 /\
    psi (y0, (y1, (y2, (y3, tt))))
  ).
Defined.

Lemma tzprofiles_iter_body_spec_correct
  (env : @proto_env (Some (parameter_ty, None)))
  (fuel : Datatypes.nat)
  (param : data (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
  (input_stack : stack
                   (set
                      (Cpair syntax_type.string
                         (Cpair syntax_type.string bytes))
                    ::: Comparable_type syntax_type.string
                        ::: pair
                              (big_map syntax_type.string
                                 (Comparable_type bytes))
                              (Comparable_type address)
                            ::: Comparable_type bool ::: nil))
  (psi : stack
           (set
              (Cpair syntax_type.string
                 (Cpair syntax_type.string bytes))
            ::: Comparable_type syntax_type.string
                ::: pair
                      (big_map syntax_type.string
                         (Comparable_type bytes))
                      (Comparable_type address)
                    ::: Comparable_type bool ::: nil) -> Prop) :
  6 <= fuel ->
  precond (eval_seq env tzprofiles_iter_body fuel (param, input_stack)) psi <->
  tzprofiles_iter_body_spec psi param input_stack.
Proof.
  intro fuel_gt.

  simpl in input_stack; simpl in psi.
  destruct param as (x0_1 & (x0_2 & x0_3)).
  destruct input_stack as (x1 & (x2 & (x3 & (x4 & tt_)))).

  do 6 more_fuel.

  lazymatch goal with
  | |- precond (eval_seq _ _ ?H_fuel _) _ <-> _ =>
      replace H_fuel with (6 + fuel) by reflexivity
  end.

  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  unfold tzprofiles_iter_body.
  unfold tzprofiles_iter_body_spec.

  remember (6 + fuel) as fuel2.
  assert (6 <= fuel2) by lia.
  unfold tzprofiles_iter_body_raw_spec.
  do 6 (more_fuel; simpl).

  destruct tt_.
  split; intro H_iff.
  - match goal with
    | H_iff : psi (?y0, (?y1, (?y2, (?y3, tt)))) |- _ =>
        exists y0;
        exists y1;
        exists y2;
        exists y3
    end.
    auto.

  - destruct H_iff as (y0 & (y1 & (y2 & (y3 & (update_eq & H_psi))))).
    rewrite <- update_eq in H_psi.
    assumption.
Qed.

Lemma tzprofiles_iter_body_spec_ext
  (psi1
   psi2 : stack
            (set
               (Cpair syntax_type.string
                  (Cpair syntax_type.string bytes))
             ::: Comparable_type syntax_type.string
                 ::: pair
                       (big_map syntax_type.string
                          (Comparable_type bytes))
                       (Comparable_type address)
                     ::: Comparable_type bool ::: nil) -> Prop)
  (x : data
         (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
  (input_stack : stack
                   (set
                      (Cpair syntax_type.string
                         (Cpair syntax_type.string bytes))
                    ::: Comparable_type syntax_type.string
                        ::: pair
                              (big_map syntax_type.string
                                 (Comparable_type bytes))
                              (Comparable_type address)
                                ::: Comparable_type bool ::: nil)) :

  (forall
     x0 : stack
            (set
               (Cpair syntax_type.string
                  (Cpair syntax_type.string bytes))
             ::: Comparable_type syntax_type.string
                 ::: pair
                       (big_map syntax_type.string
                          (Comparable_type bytes))
                       (Comparable_type address)
                     ::: Comparable_type bool ::: nil),
   psi1 x0 <-> psi2 x0) ->
  tzprofiles_iter_body_spec psi1 x input_stack <->
  tzprofiles_iter_body_spec psi2 x input_stack.
Proof.
  intro H_psi12.
  destruct x as (x0_1 & (x0_2 & x0_3)).
  destruct input_stack as (x1 & (x2 & (x3 & (x4 & tt_)))).
  unfold tzprofiles_iter_body_spec.
  split; intro H;
  destruct H as (y0 & (y1 & (y2 & (y3 & (update_eq & H_psi)))));
  rewrite <- update_eq in H_psi;
  exists y0;
  exists y1;
  exists y2;
  exists y3;
  split; try assumption;
  apply H_psi12;
  congruence.
Qed.

Definition tzprofiles_iter_raw_spec
      (x0 : data (list (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (x1 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (x2 : data (Comparable_type syntax_type.string))
      (x3 : data (pair (big_map syntax_type.string (Comparable_type bytes)) (Comparable_type address)))
      (x4 : data (Comparable_type bool))

      (y0 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (y1 : data (Comparable_type syntax_type.string))
      (y2 : data (pair (big_map syntax_type.string (Comparable_type bytes))
                 (Comparable_type address)))
      (y3 : data (Comparable_type bool)) :=
  List.fold_right
  (fun (x : data (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
     (psi : stack
              (set
                 (Cpair syntax_type.string (Cpair syntax_type.string bytes))
               ::: Comparable_type syntax_type.string
                   ::: pair
                         (big_map syntax_type.string (Comparable_type bytes))
                         (Comparable_type address)
                       ::: Comparable_type bool ::: nil) -> Prop)
     (st : stack
             (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
              ::: Comparable_type syntax_type.string
                  ::: pair
                        (big_map syntax_type.string (Comparable_type bytes))
                        (Comparable_type address)
                      ::: Comparable_type bool ::: nil)) =>
   tzprofiles_iter_body_spec psi x st)
  (fun
     x : stack
           (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))
            ::: Comparable_type syntax_type.string
                ::: pair (big_map syntax_type.string (Comparable_type bytes))
                      (Comparable_type address)
                    ::: Comparable_type bool ::: nil) =>
   x = (y0, (y1, (y2, (y3, tt))))) x0 (x1, (x2, (x3, (x4, tt)))).

Lemma tzprofiles_iter_raw_spec_correct
      (env : @proto_env (Some (parameter_ty, None)))

      (x0 : data (list (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (x1 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (x2 : data (Comparable_type syntax_type.string))
      (x3 : data (pair (big_map syntax_type.string (Comparable_type bytes)) (Comparable_type address)))
      (x4 : data (Comparable_type bool))

      (y0 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (y1 : data (Comparable_type syntax_type.string))
      (y2 : data (pair (big_map syntax_type.string (Comparable_type bytes))
                 (Comparable_type address)))
      (y3 : data (Comparable_type bool))
      (fuel : Datatypes.nat) :

  eval env tzprofiles_iter (7 + Datatypes.length x0 + fuel)
    (x0, (x1, (x2, (x3, (x4, tt))))) =
    Return (y0, (y1, (y2, (y3, tt))))
  <-> tzprofiles_iter_raw_spec x0 x1 x2 x3 x4 y0 y1 y2 y3.
Proof.
  remember (7 + Datatypes.length x0 + fuel) as fuel2.
  assert (7 + Datatypes.length x0 <= fuel2) by lia.
  rewrite return_precond.
  unfold tzprofiles_iter.
  unfold tzprofiles_iter_raw_spec.
  fold tzprofiles_iter_body.
  rewrite (precond_iter_bounded
    (@Some (entrypoint_tree * Datatypes.option annotation) (parameter_ty, @None annotation))
    false
    env
    (Cpair syntax_type.string (Cpair syntax_type.string bytes))
    x0
    _
    tzprofiles_iter_body
    6
    tzprofiles_iter_body_spec
    (tzprofiles_iter_body_spec_correct env)
    tzprofiles_iter_body_spec_ext
  ); try assumption.
  reflexivity.
Qed.

Lemma tzprofiles_iter_raw_spec_correct_helper
      (env : @proto_env (Some (parameter_ty, None)))

      (x0 : data (list (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (x1 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (x2 : data (Comparable_type syntax_type.string))
      (x3 : data (pair (big_map syntax_type.string (Comparable_type bytes)) (Comparable_type address)))
      (x4 : data (Comparable_type bool))

      (y0 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (y1 : data (Comparable_type syntax_type.string))
      (y2 : data (pair (big_map syntax_type.string (Comparable_type bytes))
                 (Comparable_type address)))
      (y3 : data (Comparable_type bool))
      (fuel : Datatypes.nat) :
  7 + Datatypes.length x0 <= fuel ->
  eval env tzprofiles_iter fuel
    (x0, (x1, (x2, (x3, (x4, tt))))) =
    Return (y0, (y1, (y2, (y3, tt))))
  <-> tzprofiles_iter_raw_spec x0 x1 x2 x3 x4 y0 y1 y2 y3.
Proof.
  intro H.
  replace fuel
     with (7 + Datatypes.length x0 + (fuel - 7 - Datatypes.length x0))
       by lia.
  rewrite tzprofiles_iter_raw_spec_correct.
  reflexivity.
Qed.

Lemma tzprofiles_iter_raw_spec_correct_exists_helper
      (env : @proto_env (Some (parameter_ty, None)))
      (in_stack : _)
      (out_stack : _)
      (fuel : Datatypes.nat) :
  7 + Datatypes.length (fst in_stack) <= fuel ->
  eval env tzprofiles_iter fuel in_stack = Return out_stack
  <-> tzprofiles_iter_raw_spec
    (fst in_stack)
    (fst (snd in_stack))
    (fst (snd (snd in_stack)))
    (fst (snd (snd (snd in_stack))))
    (fst (snd (snd (snd (snd in_stack)))))
    (fst out_stack)
    (fst (snd out_stack))
    (fst (snd (snd out_stack)))
    (fst (snd (snd (snd out_stack)))).
Proof.
  destruct in_stack as (x0 & (x1 & (x2 & (x3 & (x4 & tt_))))).
  destruct tt_.
  destruct out_stack as (y0 & (y1 & (y2 & (y3 & tt_)))).
  destruct tt_.
  simpl snd; simpl fst.
  apply tzprofiles_iter_raw_spec_correct_helper.
Qed.

Definition tzprofiles_iter_spec_exists
  (in_stack : Datatypes.list
                (comparable_data syntax_type.string *
                 (comparable_data syntax_type.string *
                  comparable_data bytes)) *
              (data
                 (set
                    (Cpair syntax_type.string
                       (Cpair syntax_type.string bytes))) *
               (data (Comparable_type syntax_type.string) *
                (data
                   (pair
                      (big_map syntax_type.string
                         (Comparable_type bytes))
                      (Comparable_type address)) *
                 (data (Comparable_type bool) * Datatypes.unit))))) :=
  (List.fold_left (fun memo x =>
    update _ _ _
      (Update_variant_set (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
      x
      (fst (snd (snd (snd (snd in_stack)))))
      memo)
    (fst in_stack)
    (fst (snd in_stack)),
     (fst (snd (snd in_stack)),
     (fst (snd (snd (snd in_stack))),
     (fst (snd (snd (snd (snd in_stack)))), tt)))).



Fixpoint tzprofiles_iter_spec_correct
      (x0 : data (list (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (x1 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (x2 : data (Comparable_type syntax_type.string))
      (x3 : data (pair (big_map syntax_type.string (Comparable_type bytes)) (Comparable_type address)))
      (x4 : data (Comparable_type bool))

      (y0 : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (y1 : data (Comparable_type syntax_type.string))
      (y2 : data (pair (big_map syntax_type.string (Comparable_type bytes))
                 (Comparable_type address)))
      (y3 : data (Comparable_type bool)) :
  tzprofiles_iter_raw_spec x0 x1 x2 x3 x4 y0 y1 y2 y3 <->
  tzprofiles_iter_spec_exists (x0, (x1, (x2, (x3, (x4, tt))))) = (y0, (y1, (y2, (y3, tt)))).
Proof.
  unfold tzprofiles_iter_spec_exists.
  unfold tzprofiles_iter_body_spec.
  unfold tzprofiles_iter_body_raw_spec.

  destruct x0 as [| (x0_1 & (x0_2 & x0_3)) ].
  - reflexivity.

  - unfold tzprofiles_iter_raw_spec.
    simpl.
    assert (H_exists_eq : forall H, (exists y4 y5 y6 y7,
      (update _ _ _
        (Update_variant_set (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
        (x0_1, (x0_2, x0_3)) x4 x1, (x2, (x3, (x4, tt)))) =
      (y4, (y5, (y6, (y7, tt)))) /\ H y4 y5 y6 y7) <->
      H (update _ _ _
        (Update_variant_set (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
        (x0_1, (x0_2, x0_3)) x4 x1) x2 x3 x4).
    {
      intro H.
      split; intro H_iff.

      {
        destruct H_iff as (y4 & (y5 & (y6 & (y_update & (update_eq & H_psi))))).
        congruence.
      }

      {
        match goal with
        | H_iff : H ?y4 ?y5 ?y6 ?y7 |- _ =>
            exists y4;
            exists y5;
            exists y6;
            exists y7;
            split; try assumption
        end.
        reflexivity.
      }
    }

    rewrite H_exists_eq; clear H_exists_eq.
    unfold tzprofiles_iter_raw_spec in tzprofiles_iter_spec_correct.
    rewrite tzprofiles_iter_spec_correct; clear tzprofiles_iter_spec_correct.
    reflexivity.
Qed.

Lemma tzprofiles_iter_spec_exists_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (in_stack : _)
      (fuel : Datatypes.nat) :
  7 + Datatypes.length (fst in_stack) <= fuel ->
  eval env tzprofiles_iter fuel in_stack =
  Return (tzprofiles_iter_spec_exists in_stack).
Proof.
  intro H.
  rewrite (tzprofiles_iter_raw_spec_correct_exists_helper env); try assumption.
  rewrite tzprofiles_iter_spec_correct.
  reflexivity.
Qed.



Definition tzprofiles_spec_helper
           (env : @proto_env (Some (parameter_ty, None)))
           (claims : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
           (contract_type : data syntax_type.string)
           (metadata : data (big_map syntax_type.string bytes))
           (owner : data address)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  let storage : data storage_ty :=
    ((claims, contract_type),
      (metadata, owner)) in

  negb (comparison_to_int (address_compare (sender env) owner) =? 0)%Z = false /\
  (* (comparison_to_int (tez.compare (amount env) (0 ~Mutez)) >? 0)%Z = false /\ *)

  match param with
  | (update_list, add_or_remove) =>
      match new_storage with
      | ((new_claims, new_contract_type), (new_metadata, new_owner)) =>

          (nil,
          (List.fold_left
             (fun
                (memo : data
                          (set
                             (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
                (x : str * (str * str)) =>
              set.update (str * (str * str))
                (lexicographic_comparison string_compare
                   (lexicographic_comparison string_compare string_compare))
                (compare_eq_iff
                   (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
                (comparable.lt_trans
                   (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
                (comparable.gt_trans
                   (Cpair syntax_type.string (Cpair syntax_type.string bytes))) x
                add_or_remove memo) update_list claims, contract_type,
          (metadata, owner)), tt) =
          (returned_operations,
          (new_claims, new_contract_type, (new_metadata, new_owner)), tt)
      end
  end.


Lemma tzprofiles_spec_helper_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (claims : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (contract_type : data syntax_type.string)
      (metadata : data (big_map syntax_type.string bytes))
      (owner : data address)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  let storage : data storage_ty :=
    ((claims, contract_type),
      (metadata, owner)) in
  eval_seq env tzprofiles (100 + Datatypes.length (fst param) + fuel) ((param, storage), tt) =
    Return ((returned_operations, new_storage), tt)
  <-> tzprofiles_spec_helper env claims contract_type metadata owner param
    new_storage returned_operations.
Proof.
  intro Hfuel.
  remember (100 + Datatypes.length (fst param) + fuel) as fuel2.
  assert (100 + Datatypes.length (fst param) <= fuel2) by lia.
  rewrite return_precond.
  rewrite eval_seq_precond_correct.
  unfold eval_seq_precond.
  unfold tzprofiles_spec_helper.

  destruct param as (update_list & add_or_remove).
  destruct new_storage as ((new_claims & new_contract_type) & (new_metadata & new_owner)).
  simpl fst in H, Heqfuel2.

  Arguments eval_seq_precond_body : simpl never.
  simpl.
  Arguments eval_seq_precond_body : simpl nomatch.

  unfold tzprofiles.
  Arguments eval_precond : simpl never.
  simpl.
  Arguments eval_precond : simpl nomatch.

  rewrite <- eval_precond_correct.
  (more_fuel; simpl precond).
  (more_fuel; simpl precond).
  (more_fuel; simpl precond).

  apply and_iff_compat_l.
  rewrite <- eval_precond_correct.
  (more_fuel; simpl precond).

  rewrite <- eval_precond_correct.
  (more_fuel; simpl precond).

  rewrite <- eval_precond_correct.
  fold tzprofiles_iter.


  lazymatch goal with
  | H : ?x <= fuel2 |- _ =>
      replace x with (95 + Datatypes.length update_list) in H by reflexivity
  end.

  lazymatch goal with
  | |- precond (eval _ _ ?x _) _ <-> _ =>
      replace x with (5 + fuel2) in Heqfuel2 |- * by reflexivity
  end.

  rewrite tzprofiles_iter_spec_exists_correct.
  2: {
    rewrite Heqfuel2.
    simpl fst.
    lia.
  }

  simpl precond.
  reflexivity.
Qed.


Definition tzprofiles_spec
           (env : @proto_env (Some (parameter_ty, None)))
           (claims : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
           (contract_type : data syntax_type.string)
           (metadata : data (big_map syntax_type.string bytes))
           (owner : data address)
           (param : data parameter_ty)
           (new_storage : data storage_ty)
           (returned_operations : data (list operation)) :=
  let storage : data storage_ty :=
    ((claims, contract_type),
      (metadata, owner)) in

  negb (comparison_to_int (address_compare (sender env) owner) =? 0)%Z = false /\
  (* (comparison_to_int (tez.compare (amount env) (0 ~Mutez)) >? 0)%Z = false /\ *)

  match param with
  | (update_list, add_or_remove) =>
      match new_storage with
      | ((new_claims, new_contract_type), (new_metadata, new_owner)) =>
          new_claims = List.fold_left (fun memo x =>
            update _ _ _
              (Update_variant_set (Cpair syntax_type.string (Cpair syntax_type.string bytes)))
              x
              add_or_remove
              memo)
            update_list
            claims /\
          new_contract_type = contract_type /\
          new_metadata = metadata /\
          new_owner = owner /\
          returned_operations = nil
      end
  end.


Lemma tzprofiles_spec_correct
      (env : @proto_env (Some (parameter_ty, None)))
      (claims : data (set (Cpair syntax_type.string (Cpair syntax_type.string bytes))))
      (contract_type : data syntax_type.string)
      (metadata : data (big_map syntax_type.string bytes))
      (owner : data address)
      (param : data parameter_ty)
      (new_storage : data storage_ty)
      (returned_operations : data (list operation))
      (fuel : Datatypes.nat) :
  let storage : data storage_ty :=
    ((claims, contract_type),
      (metadata, owner)) in
  eval_seq env tzprofiles (100 + Datatypes.length (fst param) + fuel) ((param, storage), tt) =
    Return ((returned_operations, new_storage), tt)
  <-> tzprofiles_spec env claims contract_type metadata owner param
    new_storage returned_operations.
Proof.
  (* intro Hfuel. *)
  (* remember (100 + Datatypes.length (fst param) + fuel) as fuel2. *)
  (* assert (100 + Datatypes.length (fst param) <= fuel2) by lia. *)
  (* rewrite Heqfuel2. *)

  intro Hfuel; unfold Hfuel.
  rewrite (tzprofiles_spec_helper_correct env claims contract_type metadata owner param
    new_storage returned_operations fuel).

  unfold tzprofiles_spec_helper.
  unfold tzprofiles_spec.

  apply and_iff_compat_l.

  destruct param as (update_list & add_or_remove).
  destruct new_storage as ((new_claims & new_contract_type) & (new_metadata & new_owner)).

  split; intro H.
  - inversion H; clear H.
    intuition.
  - destruct H as (claims_eq & (contract_type_eq & (metadata_eq & (owner_eq & op_eq)))).
    rewrite claims_eq, contract_type_eq, metadata_eq, owner_eq, op_eq.
    reflexivity.
Qed.

End tzprofiles.


