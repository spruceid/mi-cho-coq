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
