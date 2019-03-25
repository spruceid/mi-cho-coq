Require Import String ZArith.
Require Import location.

Inductive micheline : Set :=
| SEQ (_ : list loc_micheline)
| PRIM (_ : location * location * string)
       (_ : list loc_micheline)
| STR (_ : string)
| BYTES (_ : string)
| NUMBER (_ : Z)
with
loc_micheline : Set :=
| Mk_loc_micheline : location * location * micheline -> loc_micheline.

