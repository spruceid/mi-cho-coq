Require Import String ZArith.
Require micheline_lexer micheline_parser.
Require untyped_syntax micheline2michelson typer.



Definition get_contract_type (_ : syntax.contract_constant) :=
  error.Failed syntax.type error.Typing.

Definition lex_and_parse_micheline (fuel : nat) (input : string) :
  error.M (micheline_syntax.loc_micheline) :=
  error.bind
    (fun s =>
       match micheline_parser.file fuel s with
       | micheline_parser.Parser.Inter.Fail_pr =>
         error.Failed _ error.Parsing
       | micheline_parser.Parser.Inter.Timeout_pr =>
         error.Failed _ error.Parsing_Out_of_Fuel
       | micheline_parser.Parser.Inter.Parsed_pr m _ =>
         error.Return _ m
       end)
    (micheline_lexer.lex_micheline_to_parser input).

Definition lex_and_parse_and_expand_type (fuel : nat) (input : string)
  : error.M syntax.type :=
  error.bind
    (fun m => micheline2michelson.micheline2michelson_type m)
    (lex_and_parse_micheline fuel input).
