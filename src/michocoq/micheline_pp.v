Require Import Ascii String ZArith List Bool.
Require Import DecimalString.
Require Import location error.
Require Import micheline_tokens micheline_parser micheline_lexer michelson2micheline.
Require Import micheline_syntax.

Definition string_of_Z z := DecimalString.NilZero.string_of_int (Z.to_int z).

Fixpoint make_string (a : ascii) (n : nat) :=
  match n with
  | 0 => EmptyString
  | S n' => String a (make_string a n')
  end.

Definition lf := (String "010" EmptyString).

Open Scope string_scope.

(* Length taken by a Micheline expression when printed on a single line *)
(* TODO: avoid computing Z.to_int twice for each number litteral *)
Fixpoint micheline_length (mich : loc_micheline) (in_seq : bool) :=
  let '(Mk_loc_micheline (_, _, m)) := mich in
  match m with
  | NUMBER z => String.length (string_of_Z z)
  | STR s => 2 + String.length s
  | BYTES s => 2 + 2 * String.length s
  | SEQ nil => 2
  | SEQ es => fold_left (fun acc m => 2 + micheline_length m true + acc) es 0
  | PRIM (_, _, s) nil nil => String.length s
  | PRIM (_, _, s) annots es =>
    (if in_seq then 0 else 2) + String.length s +
    fold_left (fun acc m => 1 + micheline_length m false + acc) es 0 +
    fold_left (fun acc '(Mk_annot (_, _, annot)) => 1 + String.length annot + acc) annots 0
  end.

Fixpoint micheline_pp_single_line (mich : loc_micheline) (in_seq : bool) :=
  let '(Mk_loc_micheline (_, _, m)) := mich in
  match m with
  | NUMBER z => string_of_Z z
  | STR s => """" ++ s ++ """"
  | BYTES bs => "0x" ++ (bytes_repr.to_string bs)
  | SEQ es => "{" ++ String.concat "; " (map (fun m => micheline_pp_single_line m true) es) ++ "}"
  | PRIM (_, _, s) nil nil => s
  | PRIM (_, _, s) annots es =>
    let annots_strings := map (fun '(Mk_annot (_, _, annot)) => annot) annots in
    let args_strings := map (fun m => micheline_pp_single_line m false) es in
    let res := s ++ " " ++ String.concat " " (List.app annots_strings args_strings) in
    (if in_seq then res else "(" ++ res ++")")
  end.

Fixpoint micheline_pp (mich : loc_micheline) (indent : nat) (in_seq : bool)
         (seq_lf : bool) :=
  if (micheline_length mich in_seq) + indent <? 80 then
    micheline_pp_single_line mich in_seq
  else
  match mich with
  | Mk_loc_micheline (_, _, NUMBER z) => (string_of_Z z)
  | Mk_loc_micheline (_, _, STR s) => """"++s++""""
  | Mk_loc_micheline (_, _, BYTES bs) => "0x"++bytes_repr.to_string bs
  | Mk_loc_micheline (_, _, SEQ es) =>
    let indent_space := (make_string " " indent) in
    let separator := (";"  ++ lf ++ indent_space ++ "  ") in
    "{ " ++(String.concat separator
                          (map
                             (fun m => micheline_pp m (indent+2) true seq_lf)
                             es))
         ++ lf ++ indent_space ++ "}"
  | Mk_loc_micheline (_, _, PRIM (_, _, s) nil nil) => s
  | Mk_loc_micheline (_, _, PRIM (_, _, s) annots es) =>
    let newIndent := indent + 1 + String.length s in
    let separator := lf++(make_string " " newIndent) in
    let annots_strings := map (fun '(Mk_annot (_, _, annot)) => annot) annots in
    let args_strings := (map
                           (fun m =>
                              micheline_pp m newIndent false
                                           (negb (eqb_string s "PUSH")))
                           es) in
    let res := s++" "++
                (String.concat
                   separator
                   (List.app annots_strings args_strings)) in
    if in_seq then res else "("++res++")"
  end.
