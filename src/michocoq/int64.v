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
