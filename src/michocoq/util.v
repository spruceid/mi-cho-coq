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

Require Import ZArith.
Require Import Michocoq.macros.
Import syntax.
Import comparable.
Require Import semantics.

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

Lemma and_both_2 (P Q R : Prop):
  (P -> (Q <-> R)) ->
  ((P /\ Q) <-> (P /\ R)).
Proof.
  intuition.
Qed.

Lemma and_both_0 {P Q R S : Prop} : (P <-> R) -> (Q <-> S) -> (P /\ Q) <-> (R /\ S).
Proof.
  intuition.
Qed.

Lemma and_left {P Q R : Prop} : P -> (Q <-> R) -> ((P /\ Q) <-> R).
Proof.
  intuition.
Qed.

Lemma and_right {P Q R : Prop} : P -> (Q <-> R) -> (Q <-> (P /\ R)).
Proof.
  intuition.
Qed.

Lemma or_both {P Q R S} : P <-> R -> Q <-> S -> ((P \/ Q) <-> (R \/ S)).
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
  unfold gt, gt_comp.
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

Lemma lt_is_leb a c1 c2 :
  BinInt.Z.gtb (comparison_to_int (compare a c1 c2)) Z0 =
  negb (BinInt.Z.leb (comparison_to_int (compare a c1 c2)) Z0).
Proof.
  generalize (comparison_to_int (compare a c1 c2)).
  intro z.
  rewrite Z.gtb_ltb.
  apply Z.ltb_antisym.
Qed.



Lemma if_false_is_and (b : Datatypes.bool) A : (if b then A else False) <-> (b = true /\ A).
Proof.
  destruct b.
  - apply and_right.
    + reflexivity.
    + intuition.
  - split.
    + intro H; inversion H.
    + intros (H, _); inversion H.
Qed.

Lemma if_false_not (b : Datatypes.bool) A : (if b then False else A) <-> (b = false /\ A).
Proof.
  destruct b.
  - split.
    + intro H; inversion H.
    + intros (H, _); inversion H.
  - apply and_right.
    + reflexivity.
    + intuition.
Qed.

Lemma eq_sym_iff {A : Type} (x y : A) : x = y <-> y = x.
Proof.
  split; apply eq_sym.
Qed.

Lemma destruct_if (b : Datatypes.bool) P Q :
  (if b then P else Q) <-> ((b = true /\ P ) \/ (b = false /\ Q)).
Proof.
  destruct b; intuition discriminate.
Qed.

Lemma bool_not_false b : b = false <-> ~ b = true.
Proof.
  destruct b; intuition congruence.
Qed.

Lemma match_if_exchange A B (b : Datatypes.bool) (P : A -> Prop) (Q : B -> Prop) u v :
  match (if b then inl u else inr v) with
  | inl x => P x
  | inr y => Q y
  end =
  if b then P u else Q v.
Proof.
  destruct b; reflexivity.
Qed.

