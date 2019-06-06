Require Import Ascii String ZArith List.
Require Import DecimalString.
Require Import location error.
Require Import micheline_tokens micheline_parser micheline_lexer.
Require Import micheline_syntax.

Definition string_of_Z z := DecimalString.NilZero.string_of_int (Z.to_int z).

Open Scope string_scope.
Fixpoint micheline_pp (mich:loc_micheline) :=
  match mich with
  | Mk_loc_micheline (_, _, NUMBER z) => (string_of_Z z)
  | Mk_loc_micheline (_, _, STR s) => """"++s++""""
  | Mk_loc_micheline (_, _, BYTES s) => "0x"++s
  | Mk_loc_micheline (_, _, SEQ es) => "{ "++(String.concat ";" (map micheline_pp es))++" }"
  | Mk_loc_micheline (_, _, PRIM (_, _, s) nil) => s
  | Mk_loc_micheline (_, _, PRIM (_, _, s) es) => "("++s++" "++(String.concat " " (map micheline_pp es))++")"
  end.