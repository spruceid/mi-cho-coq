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

