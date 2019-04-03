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

Definition int64 := Bvector 64.

Definition sign : int64 -> bool := Bsign 63.

Definition to_Z : int64 -> Z := two_compl_value 63.

Definition of_Z : Z -> int64 := Z_to_two_compl 63.

Definition int64_inversion (b : int64) : exists a v, b = Bcons a 63 v :=
  match b in Vector.t _ (S _) return exists a v, b = Bcons a _ v with
  | Vector.cons _ a _ v => ex_intro _ a (ex_intro _ v eq_refl)
  end.

Lemma of_Z_to_Z b : of_Z (to_Z b) = b.
Proof.
  destruct (int64_inversion b) as (a, (v, H)).
  rewrite H.
  apply two_compl_to_Z_to_two_compl.
Qed.

Definition compare (a b : int64) : comparison :=
  Z.compare (to_Z a) (to_Z b).

Lemma compare_eq_iff (a b : int64) : compare a b = Eq <-> a = b.
Proof.
  unfold compare.
  rewrite Z.compare_eq_iff.
  split.
  - intro H.
    apply (f_equal of_Z) in H.
    rewrite of_Z_to_Z in H.
    rewrite of_Z_to_Z in H.
    assumption.
  - apply f_equal.
Qed.
