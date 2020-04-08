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

(* Michelson comparable types: nat, int, string, timestamp, mutez, bool,
   and key hashes *)

Require Import ZArith.
Require Import Ascii.
Require String.
Require Import ListSet.
Require tez.
Require Relations_1.
Require Import syntax.
Require Import syntax_type.

Definition simple_comparable_data (a : simple_comparable_type) : Set :=
  match a with
  | int => Z
  | nat => N
  | string => str
  | bytes => str
  | timestamp => Z
  | mutez => tez.mutez
  | bool => Datatypes.bool
  | address => address_constant
  | key_hash => key_hash_constant
  end.

Fixpoint comparable_data (a : comparable_type) : Set :=
  match a with
  | Comparable_type_simple a => simple_comparable_data a
  | Cpair a b => simple_comparable_data a * comparable_data b
  end.

Definition comparison_to_int (c : comparison) :=
  match c with
  | Lt => (-1)%Z
  | Gt => 1%Z
  | Eq => 0%Z
  end.

Lemma comparison_to_int_Lt c : comparison_to_int c = (-1)%Z <-> c = Lt.
Proof.
  split.
  - destruct c; simpl.
    + discriminate.
    + reflexivity.
    + discriminate.
  - intro; subst c.
    reflexivity.
Qed.

Lemma comparison_to_int_Gt c : comparison_to_int c = 1%Z <-> c = Gt.
Proof.
  split.
  - destruct c; simpl.
    + discriminate.
    + discriminate.
    + reflexivity.
  - intro; subst c.
    reflexivity.
Qed.

Lemma comparison_to_int_Eq c : comparison_to_int c = 0%Z <-> c = Eq.
Proof.
  split.
  - destruct c; simpl.
    + reflexivity.
    + discriminate.
    + discriminate.
  - intro; subst c.
    reflexivity.
Qed.

Definition bool_compare (b1 b2 : Datatypes.bool) : comparison :=
  match b1, b2 with
  | false, false => Eq
  | false, true => Lt
  | true, false => Gt
  | true, true => Eq
  end.

Definition ascii_compare (a1 a2 : ascii) : comparison :=
  (Ascii.N_of_ascii a1 ?= Ascii.N_of_ascii a2)%N.

Fixpoint string_compare (s1 s2 : str) : comparison :=
  match s1, s2 with
  | String.EmptyString, String.EmptyString => Eq
  | String.EmptyString, _ => Lt
  | _, String.EmptyString => Gt
  | String.String a1 s1, String.String a2 s2 =>
    match ascii_compare a1 a2 with
    | Lt => Lt
    | Gt => Gt
    | Eq => string_compare s1 s2
    end
  end.

Lemma ascii_compare_Eq_correct (a1 a2 : Ascii.ascii) : ascii_compare a1 a2 = Eq <-> a1 = a2.
Proof.
  unfold ascii_compare.
  rewrite N.compare_eq_iff.
  split.
  - intro H.
    apply (f_equal Ascii.ascii_of_N) in H.
    rewrite Ascii.ascii_N_embedding in H.
    rewrite Ascii.ascii_N_embedding in H.
    assumption.
  - apply f_equal.
Qed.

Lemma ascii_compare_Lt_neq (a1 a2 : Ascii.ascii) : ascii_compare a1 a2 = Lt -> a1 <> a2.
Proof.
  intros H He.
  apply ascii_compare_Eq_correct in He.
  congruence.
Qed.

Lemma ascii_compare_Gt_neq (a1 a2 : Ascii.ascii) : ascii_compare a1 a2 = Gt -> a1 <> a2.
Proof.
  intros H He.
  apply ascii_compare_Eq_correct in He.
  congruence.
Qed.

Lemma ascii_compare_Lt_trans (a1 a2 a3 : Ascii.ascii) :
  ascii_compare a1 a2 = Lt ->
  ascii_compare a2 a3 = Lt ->
  ascii_compare a1 a3 = Lt.
Proof.
  apply N.lt_trans.
Qed.

Lemma ascii_compare_Lt_Gt (a1 a2 : Ascii.ascii) : ascii_compare a1 a2 = Gt <-> ascii_compare a2 a1 = Lt.
Proof.
  unfold ascii_compare.
  rewrite N.compare_lt_iff.
  rewrite N.compare_gt_iff.
  intuition.
Qed.

Lemma ascii_compare_Gt_trans (a1 a2 a3 : Ascii.ascii) :
  ascii_compare a1 a2 = Gt ->
  ascii_compare a2 a3 = Gt ->
  ascii_compare a1 a3 = Gt.
Proof.
  rewrite ascii_compare_Lt_Gt.
  rewrite ascii_compare_Lt_Gt.
  rewrite ascii_compare_Lt_Gt.
  intros.
  apply (ascii_compare_Lt_trans _ a2); assumption.
Qed.

Lemma string_compare_Eq_correct (s1 s2 : str) : string_compare s1 s2 = Eq <-> s1 = s2.
Proof.
  generalize s2; clear s2.
  induction s1 as [|a1 s1]; intros [|a2 s2].
  - simpl. intuition.
  - simpl. split; discriminate.
  - simpl. split; discriminate.
  - simpl.
    case_eq (ascii_compare a1 a2).
    + intro H.
      apply (ascii_compare_Eq_correct a1 a2) in H.
      destruct H.
      split.
      * intro H.
        apply IHs1 in H.
        destruct H.
        reflexivity.
      * intro H.
        injection H.
        apply IHs1.
    + intro H.
      apply ascii_compare_Lt_neq in H.
      split; congruence.
    + intro H.
      apply ascii_compare_Gt_neq in H.
      split; congruence.
Qed.

Lemma string_compare_Lt_trans (s1 s2 s3 : str) :
  string_compare s1 s2 = Lt ->
  string_compare s2 s3 = Lt ->
  string_compare s1 s3 = Lt.
Proof.
  generalize s2 s3. clear s2 s3.
  induction s1 as [|ax x] ; simpl; intros [|ay y]; intros [|az z]; simpl; try congruence.
  specialize (IHx y z).
  case_eq (ascii_compare ax ay); case_eq (ascii_compare ay az); case_eq (ascii_compare ax az); try congruence.
  + auto.
  + rewrite ascii_compare_Eq_correct.
    rewrite ascii_compare_Eq_correct.
    intros Hxz Hyz Hxy.
    assert (ax = az) as He by congruence.
    rewrite <- ascii_compare_Eq_correct in He.
    congruence.
  + rewrite ascii_compare_Eq_correct.
    rewrite ascii_compare_Eq_correct.
    intros Hxz Hyz Hxy.
    assert (ay = az) as He by congruence.
    rewrite <- ascii_compare_Eq_correct in He.
    congruence.
  + rewrite ascii_compare_Lt_Gt.
    intros Hxz Hyz Hxy.
    assert (ascii_compare ay ax = Lt) as Hlt by (apply (ascii_compare_Lt_trans _ az _); assumption).
    rewrite <- ascii_compare_Lt_Gt in Hlt.
    congruence.
  + rewrite ascii_compare_Eq_correct.
    rewrite ascii_compare_Eq_correct.
    intros Hxz Hyz Hxy.
    assert (ax = ay) as He by congruence.
    rewrite <- ascii_compare_Eq_correct in He.
    congruence.
  + rewrite ascii_compare_Lt_Gt.
    intros Hxz Hyz Hxy.
    assert (ascii_compare az ay = Lt) as Hlt by (apply (ascii_compare_Lt_trans _ ax _); assumption).
    rewrite <- ascii_compare_Lt_Gt in Hlt.
    congruence.
  + intros Hxz Hyz Hxy.
    assert (ascii_compare ax az = Lt) as Hlt by (apply (ascii_compare_Lt_trans _ ay _); assumption).
    congruence.
  + intros Hxz Hyz Hxy.
    assert (ascii_compare ax az = Lt) as Hlt by (apply (ascii_compare_Lt_trans _ ay _); assumption).
    congruence.
Qed.

Lemma string_compare_Lt_Gt (s1 s2 : str) :
  string_compare s1 s2 = Gt <->
  string_compare s2 s1 = Lt.
Proof.
  generalize s2. clear s2.
  induction s1 as [|a1 s1]; intros [|a2 s2] ; simpl.
  - split; congruence.
  - split; congruence.
  - intuition.
  - specialize (IHs1 s2).
    case_eq (ascii_compare a1 a2); case_eq (ascii_compare a2 a1);
      try (rewrite ascii_compare_Lt_Gt; congruence);
      try (rewrite <- ascii_compare_Lt_Gt; congruence);
      intuition.
Qed.

Lemma string_compare_Gt_trans (s1 s2 s3 : str) :
  string_compare s1 s2 = Gt ->
  string_compare s2 s3 = Gt ->
  string_compare s1 s3 = Gt.
Proof.
  rewrite string_compare_Lt_Gt.
  rewrite string_compare_Lt_Gt.
  rewrite string_compare_Lt_Gt.
  intros.
  apply (string_compare_Lt_trans _ s2); assumption.
Qed.

(* Not documented, see contract_repr.ml in the Tezos protocol  *)
Definition address_compare (a1 a2 : address_constant) : comparison :=
  match a1, a2 with
  | Implicit (Mk_key_hash s1), Implicit (Mk_key_hash s2) => string_compare s1 s2
  | Originated (Mk_smart_contract_address s1), Originated (Mk_smart_contract_address s2) => string_compare s1 s2
  | Implicit _, Originated _ => Lt
  | Originated _, Implicit _ => Gt
  end.

Definition key_hash_compare (h1 h2 : key_hash_constant) : comparison :=
  match h1, h2 with
  | Mk_key_hash s1, Mk_key_hash s2 => string_compare s1 s2
  end.

Definition comprel (A : Set) := A -> A -> comparison.

Definition simple_compare (a : syntax_type.simple_comparable_type) :
  comprel (simple_comparable_data a) :=
  match a with
  | nat => N.compare
  | int => Z.compare
  | bool => bool_compare
  | string => string_compare
  | bytes => string_compare
  | mutez => tez.compare
  | address => address_compare
  | key_hash => key_hash_compare
  | timestamp => Z.compare
  end.

Definition lexicographic_comparison {A B : Set}
           (cA : comprel A) (cB : comprel B) : comprel (A * B) :=
  fun '(x1, y1) '(x2, y2) =>
    match cA x1 x2 with
    | Eq => cB y1 y2
    | c => c
    end.

Fixpoint compare (a : comparable_type) :
  comprel (comparable_data a) :=
  match a with
  | Comparable_type_simple a => simple_compare a
  | Cpair a b => lexicographic_comparison (simple_compare a) (compare b)
  end.

Definition eq_compatible {A : Set} (cA : comprel A) : Prop :=
  forall x y : A, cA x y = Eq <-> x = y.

Lemma lexicographic_comparison_eq_iff {A B} (cA : comprel A) (cB : comprel B) :
  eq_compatible cA -> eq_compatible cB ->
  eq_compatible (lexicographic_comparison cA cB).
Proof.
  intros HA HB (xA, xB) (yA, yB).
  specialize (HA xA yA).
  specialize (HB xB yB).
  simpl.
  split.
  - destruct (cA xA yA); intuition congruence.
  - intro H; injection H.
    intros HBe HAe.
    rewrite <- HA in HAe.
    rewrite HAe.
    intuition.
Qed.

Lemma simple_compare_eq_iff a c1 c2 : simple_compare a c1 c2 = Eq <-> c1 = c2.
Proof.
  destruct a; simpl.
  - apply string_compare_Eq_correct.
  - apply N.compare_eq_iff.
  - apply Z.compare_eq_iff.
  - apply string_compare_Eq_correct.
  - destruct c1; destruct c2; split; simpl; congruence.
  - apply tez.compare_eq_iff.
  - destruct c1 as [[s1]|[s1]]; destruct c2 as [[s2]|[s2]]; simpl;
      try rewrite string_compare_Eq_correct; split; congruence.
  - destruct c1 as [s1]; destruct c2 as [s2]. simpl.
    rewrite string_compare_Eq_correct.
    split; congruence.
  - apply Z.compare_eq_iff.
Qed.

Lemma compare_eq_iff a : forall c1 c2, compare a c1 c2 = Eq <-> c1 = c2.
Proof.
  induction a as [a|a b]; simpl.
  - apply simple_compare_eq_iff.
  - apply lexicographic_comparison_eq_iff.
    + exact (simple_compare_eq_iff _).
    + exact IHb.
Qed.

Definition lt_comp {A : Set} (c : comprel A) (x y : A) : Prop := c x y = Lt.

Definition lt a := lt_comp (compare a).

Lemma lexicographic_comparison_lt_trans {A B} (cA : comprel A) (cB : comprel B) :
  Relations_1.Transitive (lt_comp cA) ->
  Relations_1.Transitive (lt_comp cB) ->
  eq_compatible cA ->
  Relations_1.Transitive (lt_comp (lexicographic_comparison cA cB)).
Proof.
  intros HA HB Hcomp (xA, xB) (yA, yB) (zA, zB) Hxy Hyz.
  unfold lt_comp in *.
  simpl in *.
  case_eq (cA xA yA); intro H1; rewrite H1 in Hxy.
  - rewrite (Hcomp xA yA) in H1.
    rewrite H1.
    destruct (cA yA zA).
    + apply (HB _ yB); assumption.
    + reflexivity.
    + assumption.
  - case_eq (cA yA zA); intro H2; rewrite H2 in Hyz.
    + rewrite (Hcomp yA zA) in H2.
      rewrite <- H2.
      rewrite H1.
      reflexivity.
    + rewrite (HA xA yA zA); assumption.
    + discriminate.
  - discriminate.
Qed.

Lemma lt_trans_simple (a : simple_comparable_type) : Relations_1.Transitive (lt_comp (simple_compare a)).
Proof.
  unfold lt.
  destruct a; simpl; intros x y z.
  - apply string_compare_Lt_trans.
  - apply N.lt_trans.
  - apply Z.lt_trans.
  - apply string_compare_Lt_trans.
  - unfold lt_comp; destruct x; destruct y; destruct z; simpl; congruence.
  - apply Z.lt_trans.
  - unfold lt_comp;
      destruct x as [[x]|[x]];
      destruct y as [[y]|[y]];
      destruct z as [[z]|[z]]; simpl;
        try reflexivity; try discriminate; apply string_compare_Lt_trans.
  - destruct x as [x]; destruct y as [y]; destruct z as [z].
    apply string_compare_Lt_trans.
  - apply Z.lt_trans.
Qed.

Lemma lt_trans (a : comparable_type) : Relations_1.Transitive (lt a).
Proof.
  unfold lt.
  induction a as [a | a b].
  - apply lt_trans_simple.
  - apply lexicographic_comparison_lt_trans.
    + apply lt_trans_simple.
    + exact IHb.
    + exact (simple_compare_eq_iff a).
Qed.

Definition gt_comp {A : Set} (c : comprel A) (x y : A) : Prop := c x y = Gt.
Definition gt a := gt_comp (compare a).

Lemma lexicographic_comparison_gt_trans {A B} (cA : comprel A) (cB : comprel B) :
  Relations_1.Transitive (gt_comp cA) ->
  Relations_1.Transitive (gt_comp cB) ->
  eq_compatible cA ->
  Relations_1.Transitive (gt_comp (lexicographic_comparison cA cB)).
Proof.
  intros HA HB Hcomp (xA, xB) (yA, yB) (zA, zB) Hxy Hyz.
  unfold gt_comp in *.
  simpl in *.
  case_eq (cA xA yA); intro H1; rewrite H1 in Hxy.
  - rewrite (Hcomp xA yA) in H1.
    rewrite H1.
    destruct (cA yA zA).
    + apply (HB _ yB); assumption.
    + assumption.
    + reflexivity.
  - discriminate.
  - case_eq (cA yA zA); intro H2; rewrite H2 in Hyz.
    + rewrite (Hcomp yA zA) in H2.
      rewrite <- H2.
      rewrite H1.
      reflexivity.
    + discriminate.
    + rewrite (HA xA yA zA); assumption.
Qed.

Lemma gt_trans_simple (a : simple_comparable_type) : Relations_1.Transitive (gt_comp (simple_compare a)).
Proof.
  unfold gt.
  destruct a; simpl; intros x y z.
  - apply string_compare_Gt_trans.
  - unfold gt_comp.
    rewrite N.compare_gt_iff.
    rewrite N.compare_gt_iff.
    rewrite N.compare_gt_iff.
    intros.
    transitivity y; assumption.
  - apply Zcompare_Gt_trans.
  - apply string_compare_Gt_trans.
  - unfold gt_comp.
    destruct x; destruct y; destruct z; simpl; congruence.
  - apply Zcompare_Gt_trans.
  - unfold gt_comp;
      destruct x as [[x]|[x]];
      destruct y as [[y]|[y]];
      destruct z as [[z]|[z]]; simpl;
        try reflexivity; try discriminate; apply string_compare_Gt_trans.
  - destruct x as [x]; destruct y as [y]; destruct z as [z].
    apply string_compare_Gt_trans.
  - apply Zcompare_Gt_trans.
Qed.

Lemma gt_trans (a : comparable_type) : Relations_1.Transitive (gt a).
Proof.
  unfold gt.
  induction a as [a | a b].
  - apply gt_trans_simple.
  - apply lexicographic_comparison_gt_trans.
    + apply gt_trans_simple.
    + exact IHb.
    + exact (simple_compare_eq_iff a).
Qed.

Lemma compare_diff (K : comparable_type) (k1 k2 : comparable_data K) :
  compare K k1 k2 = Lt \/ compare K k1 k2 = Gt <-> k1 <> k2.
Proof.
  apply map.compare_diff.
  apply compare_eq_iff.
Qed.
