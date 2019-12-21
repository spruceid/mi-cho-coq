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

Require Import ZArith.
Require int64bv.
Require Eqdep_dec.
Require error.
Import error.Notations.

Definition mutez : Set := {t : int64bv.int64 | int64bv.sign t = false }.

Definition to_int64 (t : mutez) : int64bv.int64 :=
  let (t, _) := t in t.

Definition to_int64_inj (t1 t2 : mutez) :
  to_int64 t1 = to_int64 t2 -> t1 = t2.
Proof.
  intro H.
  destruct t1 as (t1, H1).
  destruct t2 as (t2, H2).
  simpl in H.
  destruct H.
  f_equal.
  apply Eqdep_dec.eq_proofs_unicity.
  intros.
  destruct (Bool.bool_dec x y); tauto.
Qed.

Definition to_Z (t : mutez) : Z := int64bv.to_Z (to_int64 t).

Definition of_int64_aux (t : int64bv.int64) (sign : bool) :
  int64bv.sign t = sign -> error.M mutez :=
  if sign return int64bv.sign t = sign -> error.M mutez
  then fun _ => error.Failed _ error.Overflow
  else fun H => error.Return (exist _ t H).

Definition of_int64 (t : int64bv.int64) : error.M mutez :=
  of_int64_aux t (int64bv.sign t) eq_refl.

Lemma of_int64_return (t : int64bv.int64) (H : int64bv.sign t = false) :
  of_int64 t = error.Return (exist _ t H).
Proof.
  unfold of_int64.
  cut (forall b H', of_int64_aux t b H' = error.Return (exist _ t H)).
  - intro Hl.
    apply Hl.
  - intros b H'.
    unfold of_int64_aux.
    destruct b.
    + congruence.
    + f_equal.
      apply to_int64_inj.
      reflexivity.
Qed.

Lemma of_int64_aux_sign (t : int64bv.int64) sign (e : int64bv.sign t = sign) (b : mutez) :
  of_int64_aux t sign e = error.Return b ->
  sign = false.
Proof.
  unfold of_int64_aux.
  destruct sign.
  - discriminate.
  - reflexivity.
Qed.

Lemma of_int64_sign (t : int64bv.int64) (b : mutez) :
  of_int64 t = error.Return b ->
  int64bv.sign t = false.
Proof.
  destruct b.
  unfold of_int64.
  apply of_int64_aux_sign.
Qed.

Definition of_Z (t : Z) : error.M mutez :=
  let! b := int64bv.of_Z t in
  of_int64 b.

Lemma of_Z_to_Z_eqv (z : Z) (t : mutez) : to_Z t = z <-> of_Z z = error.Return t.
Proof.
  unfold of_Z, to_Z.
  split.
  - intro; subst z.
    rewrite int64bv.of_Z_to_Z.
    destruct t.
    simpl.
    apply of_int64_return.
  - intro H.
    apply (error.bind_eq_return of_int64) in H.
    destruct H as (b, (Hz, Hb)).
    rewrite <- int64bv.of_Z_to_Z_eqv in Hz.
    subst z.
    f_equal.
    destruct t as (b', e').
    simpl.
    assert (int64bv.sign b = false) as e.
    + apply of_int64_sign in Hb.
      assumption.
    + rewrite (of_int64_return _ e) in Hb.
      injection Hb.
      auto.
Qed.

Lemma of_Z_to_Z (t : mutez) : of_Z (to_Z t) = error.Return t.
Proof.
  rewrite <- of_Z_to_Z_eqv.
  reflexivity.
Qed.

Definition compare (t1 t2 : mutez) : comparison :=
  int64bv.int64_compare (to_int64 t1) (to_int64 t2).

Lemma compare_eq_iff (t1 t2 : mutez) : compare t1 t2 = Eq <-> t1 = t2.
Proof.
  unfold compare.
  rewrite int64bv.compare_eq_iff.
  split.
  - apply to_int64_inj.
  - apply f_equal.
Qed.
