Require Import String ZArith.
Require Import syntax macros semantics comparable util.
Import error.
Require tez.
Require map.


Module Contract_components (C : ContractContext).

Module semantics := Semantics C. Import semantics.



End Contract_components.
