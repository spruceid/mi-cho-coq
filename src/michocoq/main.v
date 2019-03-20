Require Import String ZArith.
Require micheline_lexer micheline_parser.

Definition lex_and_parse_micheline (fuel : nat) (input : string)
  : error.M micheline_syntax.micheline :=
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
