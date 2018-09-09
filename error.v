(* The error monad *)

Inductive exception : Prop :=
  Out_of_fuel | Overflow | Assertion_Failure (A : Set) (a : A).

Inductive M (A : Set) : Set :=
| Failed : exception -> M A
| Return : A -> M A.

Definition bind {A B : Set} (f : A -> M B) (m : M A) :=
  match m with
  | Failed _ e => Failed B e
  | Return _ SB => f SB
  end.
