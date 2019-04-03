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
Require int64.
Require Eqdep_dec.
Require error.

Definition mutez : Set := {t : int64.int64 | int64.sign t = false }.

Definition to_int64 (t : mutez) : int64.int64 :=
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

Coercion to_int64 : mutez >-> int64.int64.

Definition to_Z (t : mutez) : Z := int64.to_Z t.

Definition of_int64 (t : int64.int64) : error.M mutez :=
  match int64.sign t as b return int64.sign t = b -> error.M mutez with
  | false => fun H => error.Return _ (exist _ t H)
  | true => fun _ => error.Failed _ error.Overflow
  end eq_refl.

Definition of_Z (t : Z) : error.M mutez :=
  of_int64 (int64.of_Z t).

Definition compare (t1 t2 : mutez) : comparison :=
  int64.compare (to_int64 t1) (to_int64 t2).

Lemma compare_eq_iff (t1 t2 : mutez) : compare t1 t2 = Eq <-> t1 = t2.
Proof.
  unfold compare.
  rewrite int64.compare_eq_iff.
  split.
  - apply to_int64_inj.
  - apply f_equal.
Qed.

