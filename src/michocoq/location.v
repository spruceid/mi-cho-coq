Require Import Arith.

Record location := Mk_loc { line : nat; column : nat }.

Lemma location_dec (x y : location) : {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Qed.

Definition location_add (loc : location) (n : nat) : location :=
  {| line := loc.(line); column := n + loc.(column) |}.

Definition location_start : location :=
  {| line := 0; column := 0 |}.

Definition location_incr (loc : location) := location_add loc 1.

Definition location_newline (loc : location) : location :=
  {| line := S (loc.(line)); column := 0 |}.
