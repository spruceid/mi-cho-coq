Require Import String ZArith.
Require micheline_lexer micheline_parser.
Require micheline2michelson typer.
Require Import syntax.
Require Import syntax_type.
Require dummy_contract_context.
Require error_pp.
Import error.Notations.

Section Main.
  Variable input : String.string.
  Variable fuel : Datatypes.nat.

Definition wrap_parser_result {A} r : error.M A :=
  match r with
  | micheline_parser.MenhirLibParser.Inter.Fail_pr =>
    error.Failed _ error.Parsing
  | micheline_parser.MenhirLibParser.Inter.Timeout_pr =>
    error.Failed _ error.Parsing_Out_of_Fuel
  | micheline_parser.MenhirLibParser.Inter.Parsed_pr m _ =>
    error.Return m
  end.

Definition lexed_M := micheline_lexer.lex_micheline_to_parser input.

Definition parsed_M :=
  let! x := lexed_M in
  wrap_parser_result (micheline_parser.seq_file fuel x).

Definition michelson_M :=
  let! x := parsed_M in
  micheline2michelson.micheline2michelson_file x.

Definition self_type_M :=
  let! a := michelson_M in
  error.Return a.(micheline2michelson.parameter).

Definition storage_type_M :=
  let! a := michelson_M in
  error.Return a.(micheline2michelson.storage).

Definition contract_file_M : error.M syntax.contract_file :=
  let! self_type := self_type_M in
  let! storage_type := storage_type_M in
  let! existT _ tff code :=
    let! a := michelson_M in
    let i := a.(micheline2michelson.code) in
    typer.type_check_instruction_seq typer.type_instruction_seq i _ _ in
  error.Return
    {| contract_file_parameter := self_type;
       contract_file_annotation := None;
       contract_file_storage := storage_type;
       contract_tff := tff;
       contract_file_code := code; |}.

Definition is_lexed := error_pp.m_pp lexed_M.

Definition is_parsed := error_pp.m_pp parsed_M.

Definition is_michelson := error_pp.m_pp michelson_M.

Definition type_check := error_pp.m_pp contract_file_M.

Definition fixed_fuel : Datatypes.nat := 500.

Definition lf := micheline_pp.lf.

Definition print_info :=
  ("Lexing: " ++ is_lexed ++ lf ++
   "Parsing: " ++ is_parsed ++ lf ++
   "Expansion: " ++ is_michelson ++ lf ++
   "Type checking: " ++ type_check ++ lf)%string.

End Main.
