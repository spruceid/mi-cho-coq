Require Import String ZArith.
Require micheline_parser.
(*Import micheline_parser.Aut.GramDefs.*)
Require Import location.

(** Tokens *)
Inductive token :=
| LBRACE
| RBRACE
| SEMICOLON
| LPAREN
| RPAREN
| PRIM : string -> token
| STR : string -> token
| NUMBER : Z -> token
| BYTES : string -> token
| EOF.

Definition parser_token := micheline_parser.Aut.GramDefs.token.

(*Definition token_from_parser (t : parser_token) : (location * location * token) :=
  match t with
  | existT _ LBRACE't (b, e) => (b, e, LBRACE)
  | existT _ RBRACE't (b, e) => (b, e, RBRACE)
  | existT _ SEMICOLON't (b, e) => (b, e, SEMICOLON)
  | existT _ LPAREN't (b, e) => (b, e, LPAREN)
  | existT _ RPAREN't (b, e) => (b, e, RPAREN)
  | existT _ PRIMt't ((b, e), s) => (b, e, PRIMt s)
  | existT _ STRt't ((b, e), s) => (b, e, STRt s)
  | existT _ NUMBERt't ((b, e), n) => (b, e, NUMBERt n)
  | existT _ BYTESt't ((b, e), s) => (b, e, BYTES s)
  | existT _ EOF't (b, e) => (b, e, EOF)
  end.*)

Definition token_to_parser (t : (location * location * token)) : parser_token :=
  let '((b, e), t) := t in
  match t with
  | LBRACE => micheline_parser.LBRACE (b, e)
  | RBRACE => micheline_parser.RBRACE (b, e)
  | SEMICOLON => micheline_parser.SEMICOLON (b, e)
  | LPAREN => micheline_parser.LPAREN (b, e)
  | RPAREN => micheline_parser.RPAREN (b, e)
  | PRIM s => micheline_parser.PRIMt (b, e, s)
  | STR s => micheline_parser.STRt (b, e, s)
  | NUMBER n => micheline_parser.NUMBERt (b, e, n)
  | BYTES s => micheline_parser.BYTESt (b, e, s)
  | EOF => micheline_parser.EOF (b, e)
  end.

(*Lemma token_to_parser_from_parser t : token_to_parser (token_from_parser t) = t.
Proof.
  destruct t as (terminal, semantic).
  destruct terminal; try reflexivity; destruct semantic as ((b, e), v); reflexivity.
Qed.

Lemma token_from_parser_to_parser t : token_from_parser (token_to_parser t) = t.
Proof.
  destruct t as ((b, e), t); destruct t; reflexivity.
Qed.*)
