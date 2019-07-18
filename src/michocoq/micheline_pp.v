Require Import Ascii String ZArith List.
Require Import DecimalString.
Require Import location error.
Require Import micheline_tokens micheline_parser micheline_lexer.
Require Import micheline_syntax.

Definition string_of_Z z := DecimalString.NilZero.string_of_int (Z.to_int z).

Fixpoint make_string (a:ascii) (n:nat) :=
  match n with
  | 0 => EmptyString
  | S n' => String a (make_string a n')
  end.

Definition lf := (String "010" EmptyString).

Open Scope string_scope.
Fixpoint micheline_pp (indent:nat) (mich:loc_micheline)  :=
  match mich with
  | Mk_loc_micheline (_, _, NUMBER z) => (string_of_Z z)
  | Mk_loc_micheline (_, _, STR s) => """"++s++""""
  | Mk_loc_micheline (_, _, BYTES s) => "0x"++s
  | Mk_loc_micheline (_, _, SEQ es) => "{"++lf++(make_string " " (indent+2))
                                         ++(String.concat
                                              ((String ";" lf)++(make_string " " (indent+2)))
                                              (map (micheline_pp (indent+2)) es))
                                         ++lf++(make_string " " indent)++"}"
  | Mk_loc_micheline (_, _, PRIM (_, _, s) nil) => s
  | Mk_loc_micheline (_, _, PRIM (_, _, s) es) => "("++s++" "++(String.concat " " (map (micheline_pp (indent+2)) es))++")"
  end.