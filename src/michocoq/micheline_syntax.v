Require Import String ZArith.

Inductive micheline :=
| SEQ (_ : list micheline)
| PRIM (_ : string) (_ : list micheline)
| STR (_ : string)
| BYTES (_ : string)
| NUMBER (_ : Z).
