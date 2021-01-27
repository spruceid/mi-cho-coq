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


(* Signed 64-bits integers: these are used to represent Tez amounts *)

Require Import Bvector.
Require Import ZArith.
Require Import Zdigits.
Require Import Lia.
Require error.

Definition int64 := Bvector 64.

Definition sign : int64 -> bool := Bsign 63.

Definition to_Z : int64 -> Z := two_compl_value 63.

Lemma to_Z_lower_bound : forall b : int64, (- two_power_nat 63 <= to_Z b)%Z.
Proof.
  unfold int64, to_Z.
  generalize 63.
  intros n b.
  refine (@VectorDef.caseS
            _
            (fun n b => - two_power_nat n <= two_compl_value n b)%Z
            _ n b).
  clear n b.
  intros b n t.
  simpl.
  generalize b; clear b.
  induction t.
  + simpl.
    unfold eq_rec_r.
    simpl.
    intro b; destruct b; simpl; omega.
  + simpl two_compl_value.
    unfold eq_rec_r.
    simpl.
    specialize (IHt h).
    generalize IHt; clear IHt.
    destruct (two_compl_value n (h :: t)).
    * destruct b; simpl; nia.
    * destruct b; simpl; nia.
    * generalize (shift_nat n 1); intro p0; simpl.
      destruct b; simpl; try nia.
      apply Pos2Z.neg_le_neg.
      unfold "<="%Z in IHt.
      unfold "?="%Z in IHt.
      rewrite <- Pos.compare_antisym in IHt.
      change (p <= p0)%positive in IHt.
      transitivity (p~0)%positive.
      -- rewrite <- Pos.succ_pred_double.
         lia.
      -- nia.
Qed.

Lemma to_Z_upper_bound : forall b : int64, (to_Z b < two_power_nat 63)%Z.
  unfold int64, to_Z.
  generalize 63.
  intros n b.
  refine (@VectorDef.caseS
            _
            (fun n b => two_compl_value n b < two_power_nat n)%Z
            _ n b).
  clear n b.
  intros b n t.
  generalize b; clear b.
  induction t.
  + unfold two_power_nat.
    simpl.
    unfold eq_rec_r.
    simpl.
    intro b; destruct b; simpl; omega.
  + simpl two_compl_value.
    unfold eq_rec_r.
    simpl.
    specialize (IHt h).
    generalize IHt; clear IHt.
    unfold two_power_nat.
    destruct (two_compl_value n (h :: t)).
    * destruct b; simpl; nia.
    * destruct b; simpl; nia.
    * generalize (shift_nat n 1); intro p0; simpl.
      destruct b; simpl; nia.
Qed.

Definition of_Z_unsafe : Z -> int64 := Z_to_two_compl 63.

Definition of_Z_safe (z : Z) :
  ((z >=? - two_power_nat 63) && (z <? two_power_nat 63))%Z = true -> int64 :=
  fun _ => of_Z_unsafe z.

Definition of_Z (z : Z) : error.M int64 :=
  if ((z >=? - two_power_nat 63) && (z <? two_power_nat 63))%bool%Z
  then
    error.Return (of_Z_unsafe z)
  else
    error.Failed _ error.Overflow.

Lemma of_Z_safe_is_of_Z z H : of_Z z = error.Return (of_Z_safe z H).
Proof.
  unfold of_Z, of_Z_safe.
  rewrite H.
  reflexivity.
Qed.

Definition int64_inversion (b : int64) : exists a v, b = Bcons a 63 v :=
  match b in Vector.t _ (S _) return exists a v, b = Bcons a _ v with
  | Vector.cons _ a _ v => ex_intro _ a (ex_intro _ v eq_refl)
  end.

Lemma of_Z_to_Z_eqv z b : to_Z b = z <-> of_Z z = error.Return b.
Proof.
  unfold of_Z, to_Z.
  split.
  - intro; subst z.
    destruct (int64_inversion b) as (a, (v, H)).
    rewrite H.
    unfold of_Z_unsafe.
    rewrite two_compl_to_Z_to_two_compl.
    rewrite <- H; clear H.
    assert ((two_compl_value 63 b >=? - two_power_nat 63)%Z = true) as Hlow.
    + rewrite Z.geb_le.
      apply to_Z_lower_bound.
    + rewrite Hlow; clear Hlow.
      assert ((two_compl_value 63 b <? two_power_nat 63)%Z = true) as Hhigh.
      * rewrite Z.ltb_lt.
        apply to_Z_upper_bound.
      * rewrite Hhigh; clear Hhigh.
        reflexivity.
  - intro H.
    case_eq ((z >=? - two_power_nat 63) && (z <? two_power_nat 63))%Z.
    + intro Hcond.
      rewrite Hcond in H.
      apply (f_equal (fun o => match o with error.Return x => x | _ => b end)) in H.
      subst b.
      apply andb_prop in Hcond.
      destruct Hcond as (H1, H2).
      apply Z_to_two_compl_to_Z.
      * apply Z.le_ge.
        apply Z.geb_le.
        assumption.
      * apply Z.ltb_lt.
        assumption.
    + intro Hcond.
      rewrite Hcond in H.
      discriminate.
Qed.

Lemma of_Z_to_Z b : of_Z (to_Z b) = error.Return b.
Proof.
  rewrite <- of_Z_to_Z_eqv.
  reflexivity.
Qed.

Lemma of_Z_of_N
      (n : N)
      (H : (n < 2 ^ 63)%N) :
      of_Z (Z.of_N n) = error.Return (of_Z_unsafe (Z.of_N n)).
Proof.
  unfold of_Z.
  pose (lower_bound := (Z.of_N n >=? - two_power_nat 63)%Z).
  assert (lower_bound_eq : (Z.of_N n >=? - two_power_nat 63)%Z = lower_bound) by reflexivity.
  rewrite lower_bound_eq.
  pose (upper_bound := (Z.of_N n <? two_power_nat 63)%Z).
  assert (upper_bound_eq : (Z.of_N n <? two_power_nat 63)%Z = upper_bound) by reflexivity.
  rewrite upper_bound_eq.
  rewrite two_power_nat_equiv in *.
  Ltac lower_bound_false lower_bound_eq :=
  (
    rewrite Z.geb_leb in lower_bound_eq;
    apply (proj1 (Z.leb_nle _ _)) in lower_bound_eq;
    refine (False_ind _ (lower_bound_eq _));
    refine (Z.le_trans _ _ _
      (proj2 (Z.opp_nonpos_nonneg _) (Z.pow_nonneg _ _ _))
      (N2Z.is_nonneg _)
    );
    intuition
  ).
  destruct lower_bound, upper_bound;
  (reflexivity || lower_bound_false lower_bound_eq || idtac).
  apply (proj1 (Z.ltb_nlt _ _)) in upper_bound_eq.
  refine (False_ind _ (upper_bound_eq _)).
  apply (proj1 (N2Z.inj_lt _ _)) in H.
  assert (Z_pow_eq : Z.of_N (2 ^ 63) = (2 ^ Z.of_nat 63)%Z).
  + rewrite N2Z.inj_pow.
    f_equal.
  + rewrite Z_pow_eq in H.
    exact H.
Qed.

(* Returns x / (2 ^ n) where / is integer division:
   see iter_Zdigits_Zmod2_div_pow2. *)
Definition iter_Zdigits_Zmod2 (n : Datatypes.nat) (x : Z) :=
  nat_rec _
    (fun y => y)
    (fun _ f y => f (Zdigits.Zmod2 y))
    n x.

(* The sign bit of the two's complement representation of x in n+1 bits
   (i.e. the (n+1)th or final bit) is set iff (x / (2 ^ n)) is odd *)
Fixpoint iter_Zdigits_Zmod2_correct (n : Datatypes.nat) (x : Z) :
  Bvector.Bsign _ (Zdigits.Z_to_two_compl n x) = Z.odd (iter_Zdigits_Zmod2 n x).
Proof.
  destruct n.
  - reflexivity.
  - simpl.
    rewrite (iter_Zdigits_Zmod2_correct n _).
    reflexivity.
Qed.

Fixpoint iter_Zdigits_Zmod2_upper_bound (n m : Datatypes.nat) (z : Z)
  (H : (z < two_power_nat (n + m))%Z) :
  (iter_Zdigits_Zmod2 n z < two_power_nat m)%Z.
Proof.
  destruct n.
  - assumption.
  - exact (iter_Zdigits_Zmod2_upper_bound n m
      (Zdigits.Zmod2 z)
      (Zdigits.Zlt_two_power_nat_S _ _ H)
    ).
Qed.

Lemma Zdigits_bit_value_bounds (b : Datatypes.bool) :
  (0 <= Zdigits.bit_value b <= 1)%Z.
Proof.
  destruct b; simpl; split; lia.
Qed.

Lemma Zmod2_nonneg (z : Z) :
  (0 <= z)%Z <-> (0 <= Zdigits.Zmod2 z)%Z.
Proof.
  pose (Zdigits_bit_value_bounds (Z.odd z)).
  split; intro H.
  - rewrite (Zdigits.Zmod2_twice z) in H; lia.
  - rewrite (Zdigits.Zmod2_twice z); lia.
Qed.

Fixpoint iter_Zdigits_Zmod2_nonneg (n : Datatypes.nat) (z : Z) :
  forall (H : (0 <= z)%Z),
  (0 <= iter_Zdigits_Zmod2 n z)%Z.
Proof.
  intro H.
  destruct n.
  - assumption.
  - simpl in H |- *.
    exact (iter_Zdigits_Zmod2_nonneg n
      (Zdigits.Zmod2 z)
      (proj1 (Zmod2_nonneg _) H)
    ).
Qed.

Lemma odd_iter_Zdigits_Zmod2
      (n : Datatypes.nat) (z : Z)
      (lb : (0 <= z)%Z)
      (ub : (z < two_power_nat n)%Z) :
  Z.odd (iter_Zdigits_Zmod2 n z) = false.
Proof.
  pose (H_nonneg := iter_Zdigits_Zmod2_nonneg n _ lb).
  rewrite <- (Nat.add_0_r n) in ub.
  pose (H_nonpos := iter_Zdigits_Zmod2_upper_bound n 0%nat z ub).
  pose (z' := iter_Zdigits_Zmod2 n z).
  assert (z_eq' : z' = iter_Zdigits_Zmod2 n z) by reflexivity.
  rewrite <- z_eq' in *.
  destruct z'.
  - auto.
  - destruct (Zlt_not_le _ _ (Pos2Z.pos_is_pos _) (Zlt_succ_le _ 0%Z H_nonpos)).
  - destruct (Zlt_not_le _ _ (Pos2Z.neg_is_neg _) H_nonneg).
Qed.

Lemma sign_of_Z_of_N (n : N) (H : (n < 2 ^ 63)%N) :
  Bool.Is_true (negb (sign (of_Z_unsafe (Z.of_N n)))).
Proof.
  unfold sign.
  unfold of_Z_unsafe.
  rewrite iter_Zdigits_Zmod2_correct.
  refine (error.IT_eq_rev _ _).
  refine (proj2 (Bool.negb_true_iff _) _).
  refine (odd_iter_Zdigits_Zmod2 _ (Z.of_N n) _ _).
  - exact (N2Z.is_nonneg _).
  - assert (H_pow_2_63 : two_power_nat 63 = Z.of_N (2 ^ 63)%N).
    + rewrite two_power_nat_equiv.
      rewrite N2Z.inj_pow.
      f_equal.
    + rewrite H_pow_2_63.
      refine (proj1 (N2Z.inj_lt _ _) _).
      assumption.
Qed.

Definition compare (a b : int64) : comparison :=
  Z.compare (to_Z a) (to_Z b).

(* To avoid a name clash in OCaml extracted code. *)
Definition int64_compare (a b : int64) : comparison := compare a b.

Lemma compare_eq_iff (a b : int64) : compare a b = Eq <-> a = b.
Proof.
  unfold compare.
  rewrite Z.compare_eq_iff.
  split.
  - intro H.
    apply (f_equal of_Z) in H.
    rewrite of_Z_to_Z in H.
    rewrite of_Z_to_Z in H.
    injection H.
    auto.
  - apply f_equal.
Qed.
