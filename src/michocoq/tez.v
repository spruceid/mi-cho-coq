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

Definition mutez : Set := {t : int64bv.int64 | Bool.Is_true (negb (int64bv.sign t)) }.

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
  apply error.Is_true_UIP.
Qed.

Definition to_Z (t : mutez) : Z := int64bv.to_Z (to_int64 t).

Definition of_int64 (t : int64bv.int64) : error.M mutez :=
  let! H :=
     error.dif
       (A := fun b => error.M (Bool.Is_true (negb b)))
       (int64bv.sign t)
       (fun _ => error.Failed _ error.Overflow)
       (fun H => error.Return H)
  in
  @error.Return mutez (exist _ t H).

Lemma of_int64_to_int64_eqv (t : int64bv.int64) (m : mutez) :
  to_int64 m = t <-> of_int64 t = error.Return m.
Proof.
  unfold of_int64, to_int64.
  destruct m as (t', H).
  rewrite error.bind_eq_return.
  split.
  - intro; subst.
    exists H.
    split; [| reflexivity].
    apply (@error.dif_case (fun b => error.M (Bool.Is_true (negb b)))).
    + intro Hn; destruct (int64bv.sign t); contradiction.
    + intro H'; f_equal; apply error.Is_true_UIP.
  - intros (H', (Hd, HR)).
    congruence.
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
    simpl.
    apply of_int64_to_int64_eqv.
    reflexivity.
  - intro H.
    apply (error.bind_eq_return of_int64) in H.
    destruct H as (b, (Hz, Hb)).
    apply of_int64_to_int64_eqv in Hb.
    rewrite <- int64bv.of_Z_to_Z_eqv in Hz.
    congruence.
Qed.

Lemma of_Z_to_Z (t : mutez) : of_Z (to_Z t) = error.Return t.
Proof.
  rewrite <- of_Z_to_Z_eqv.
  reflexivity.
Qed.

Lemma of_Z_of_N_success (n : N) (H : (n < 2 ^ 63)%N) :
  Bool.Is_true (error.success (of_Z (Z.of_N n))).
Proof.
  unfold of_Z.
  rewrite int64bv.of_Z_of_N by assumption.
  simpl error.bind.
  unfold of_int64.
  refine (error.success_bind_rev _ _ _).
  exists (int64bv.sign_of_Z_of_N n H).
  split.
  - exact (@error.dif_is_false _ _ _ _ _).
  - exact I.
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
