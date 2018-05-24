(* Tez amounts implemented by positive signed 64-bits integers *)

Require Import ZArith.
Require int64.
Require Eqdep_dec.

Definition tez : Set := {t : int64.int64 | int64.sign t = false }.

Definition to_int64 (t : tez) : int64.int64 :=
  let (t, _) := t in t.

Definition to_int64_inj (t1 t2 : tez) :
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

Coercion to_int64 : tez >-> int64.int64.

Definition to_Z (t : tez) : Z := int64.to_Z t.

Definition of_int64 (t : int64.int64) : option tez :=
  match int64.sign t as b return int64.sign t = b -> option tez with
  | false => fun H => Some (exist _ t H)
  | true => fun _ => None
  end eq_refl.

Definition of_Z (t : Z) : option tez :=
  of_int64 (int64.of_Z t).

Definition compare (t1 t2 : tez) : comparison :=
  int64.compare (to_int64 t1) (to_int64 t2).

Lemma compare_eq_iff (t1 t2 : tez) : compare t1 t2 = Eq <-> t1 = t2.
Proof.
  unfold compare.
  rewrite int64.compare_eq_iff.
  split.
  - apply to_int64_inj.
  - apply f_equal.
Qed.

