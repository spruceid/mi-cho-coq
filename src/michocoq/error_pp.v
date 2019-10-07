Require Import location error String micheline_pp ZArith.

Open Scope string.

Definition location_pp (l : location) : string :=
  "line " ++ string_of_Z (Z.of_nat l.(line)) ++ " column " ++ string_of_Z (Z.of_nat l.(column)).


Definition exception_pp (e : exception) : string :=
  match e with
  | Out_of_fuel => "Out of execution fuel"
  | Overflow => "Overflow"
  | Assertion_Failure _ _ => "Assertion failure"
  | Lexing l => "Lexing error at " ++ location_pp l
  | Parsing => "Parsing error"
  | Parsing_Out_of_Fuel => "Out of parsing fuel"
  | Expansion b e => "Expansion error between " ++ location_pp b ++ " and " ++ location_pp e
  | Expansion_prim b e s => "Unknown primitive " ++ s ++ " between " ++ location_pp b ++ " and " ++ location_pp e
  | Typing _ _ => "Typing error"
  end.

Definition m_pp {A} (m : M A) : string :=
  match m with
  | Return _ _ => "OK"
  | Failed _ e => exception_pp e
  end.
