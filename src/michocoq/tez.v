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


(* Tez amounts implemented by positive signed 64-bits integers *)

Require Int63.
Require error.
Import error.Notations.

Require Import ZArith.

Definition mutez : Set := Int63.int.

Definition to_Z (t : mutez) : Z := Int63.to_Z t.

Definition in_bound (z : Z) : bool :=
  ((0 <=? z) && (z <? Int63.wB))%Z%bool.

Definition of_Z (z : Z) : error.M mutez :=
  if (in_bound z) then error.Return (Int63.of_Z z)
  else error.Failed _ error.Overflow.

Definition of_Z_safe (z : Z) (H : Bool.Is_true (in_bound z)) : mutez :=
  Int63.of_Z z.

Lemma of_Z_is_safe z H :
  of_Z z = error.Return (of_Z_safe z H).
Proof.
  unfold of_Z.
  rewrite (Bool.Is_true_eq_true _ H).
  reflexivity.
Qed.

Lemma to_Z_in_bound (t : mutez) : Bool.Is_true (in_bound (to_Z t)).
Proof.
  generalize (Int63.to_Z_bounded t).
  intros (H1, H2).
  unfold in_bound.
  apply Zle_imp_le_bool in H1.
  rewrite <- Z.ltb_lt in H2.
  apply Bool.Is_true_eq_left in H1.
  apply Bool.Is_true_eq_left in H2.
  apply Bool.andb_prop_intro.
  split; assumption.
Qed.

Lemma of_Z_to_Z_eqv (z : Z) (t : mutez) : to_Z t = z <-> of_Z z = error.Return t.
Proof.
  unfold of_Z.
  split.
  - intro; subst z.
    rewrite (Bool.Is_true_eq_true _ (to_Z_in_bound t)).
    unfold to_Z.
    rewrite Int63.of_to_Z.
    reflexivity.
  - case_eq (in_bound z).
    + intro Hbound.
      intro Ht.
      apply error.unreturn in Ht.
      subst.
      unfold to_Z.
      symmetry.
      apply Int63.is_int.
      unfold in_bound in Hbound.
      apply andb_prop in Hbound.
      destruct Hbound as (H1, H2).
      apply Zle_bool_imp_le in H1.
      rewrite Z.ltb_lt in H2.
      split; assumption.
    + discriminate.
Qed.

Lemma of_Z_to_Z (t : mutez) : of_Z (to_Z t) = error.Return t.
Proof.
  rewrite <- of_Z_to_Z_eqv.
  reflexivity.
Qed.

Lemma to_Z_inj (t1 t2 : mutez) : to_Z t1 = to_Z t2 -> t1 = t2.
Proof.
  intro H.
  rewrite of_Z_to_Z_eqv in H.
  rewrite of_Z_to_Z in H.
  congruence.
Qed.

Definition compare (t1 t2 : mutez) : comparison :=
  Z.compare (to_Z t1) (to_Z t2).

Lemma compare_eq_iff (t1 t2 : mutez) : compare t1 t2 = Eq <-> t1 = t2.
Proof.
  unfold compare.
  rewrite Z.compare_eq_iff.
  split.
  - apply to_Z_inj.
  - apply f_equal.
Qed.
