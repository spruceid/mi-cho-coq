Require Import Ascii String ZArith List Bool.
Require Import DecimalString.
Require Import location error.
Require Import micheline_tokens micheline_parser micheline_lexer michelson2micheline.
Require Import micheline_syntax.

Definition string_of_Z z := DecimalString.NilZero.string_of_int (Z.to_int z).

Fixpoint make_string (a:ascii) (n:nat) :=
  match n with
  | 0 => EmptyString
  | S n' => String a (make_string a n')
  end.

Definition lf := (String "010" EmptyString).

Open Scope string_scope.
Fixpoint micheline_pp (mich:loc_micheline) (indent:nat) (in_seq:bool) (seq_lf:bool) :=
  match mich with
  | Mk_loc_micheline (_, _, NUMBER z) => (string_of_Z z)
  | Mk_loc_micheline (_, _, STR s) => """"++s++""""
  | Mk_loc_micheline (_, _, BYTES s) => "0x"++s
  | Mk_loc_micheline (_, _, SEQ es) => "{ "
                                        ++(String.concat
                                             ((if seq_lf then (String ";" lf)++(make_string " " (indent+2)) else ";"))
                                             (map (fun m => micheline_pp m (indent+2) true seq_lf) es))
                                        ++(if seq_lf then lf else "")++(make_string " " indent)++"}"
  | Mk_loc_micheline (_, _, PRIM (_, _, s) nil) => s
  | Mk_loc_micheline (_, _, PRIM (_, _, s) es) =>
    let newIndent := indent+String.length (s++" ") in
    let separator := if (eqb_string s "IF")
                        || (eqb_string s "IF_NONE")
                        || (eqb_string s "IF_LEFT")
                        || (eqb_string s "IF_RIGHT")
                        || (eqb_string s "IF_CONS")
                     then lf++(make_string " " newIndent) else " " in
    let res := s++" "++(String.concat separator (map (fun m => micheline_pp m newIndent false (negb (eqb_string s "PUSH"))) es)) in
    if (in_seq) then res else "("++res++")"
  end.