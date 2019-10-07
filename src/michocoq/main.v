Require Import String ZArith.
Require micheline_lexer micheline_parser.
Require micheline2michelson typer.
Require syntax.
Require Import syntax_type.
Require dummy_contract_context.
Require error_pp.

Module syntax := syntax.Syntax(dummy_contract_context).
Module typer := typer.Typer(dummy_contract_context).
Import typer syntax.

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
    error.Return _ m
  end.

Definition lexed_M := micheline_lexer.lex_micheline_to_parser input.

Definition parsed_M :=
  error.bind
    (fun x => wrap_parser_result (micheline_parser.seq_file fuel x))
    lexed_M.

Definition michelson_M :=
  error.bind
    micheline2michelson.micheline2michelson_file
    parsed_M.

Definition self_type_M :=
  error.bind
    (fun a => error.Return _ a.(micheline2michelson.parameter))
    michelson_M.

Definition storage_type_M :=
  error.bind
    (fun a => error.Return _ a.(micheline2michelson.storage))
    michelson_M.

Definition contract_file_M : error.M syntax.contract_file :=
  error.bind
    (fun self_type =>
       error.bind
         (fun storage_type =>
            error.bind
              (fun '(existT _ tff code) =>
                 error.Return
                   _
                   {| contract_file_parameter := self_type;
                      contract_file_storage := storage_type;
                      contract_tff := tff;
                      contract_file_code := code; |})
              (error.bind
                 (fun i =>
                    typer.type_check_instruction typer.type_instruction i _ _)
                 (error.bind
                    (fun a => error.Return _ a.(micheline2michelson.code))
                    michelson_M)))
         storage_type_M)
    self_type_M.

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
