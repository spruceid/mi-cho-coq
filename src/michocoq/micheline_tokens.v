Require Import String ZArith.
Require micheline_parser.
Import micheline_parser.Aut.GramDefs.

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

Definition token_from_parser (t : parser_token) : token :=
  match t with
  | existT _ LBRACE't tt => LBRACE
  | existT _ RBRACE't tt => RBRACE
  | existT _ SEMICOLON't tt => SEMICOLON
  | existT _ LPAREN't tt => LPAREN
  | existT _ RPAREN't tt => RPAREN
  | existT _ PRIM't s => PRIM s
  | existT _ STR't s => STR s
  | existT _ NUMBER't n => NUMBER n
  | existT _ BYTES't s => BYTES s
  | existT _ EOF't tt => EOF
  end.

Definition token_to_parser (t : token) : parser_token :=
  match t with
  | LBRACE => existT _ LBRACE't tt
  | RBRACE => existT _ RBRACE't tt
  | SEMICOLON => existT _ SEMICOLON't tt
  | LPAREN => existT _ LPAREN't tt
  | RPAREN => existT _ RPAREN't tt
  | PRIM s => existT _ PRIM't s
  | STR s => existT _ STR't s
  | NUMBER n => existT _ NUMBER't n
  | BYTES s => existT _ BYTES't s
  | EOF => existT _ EOF't tt
  end.

Lemma token_to_parser_from_parser t : token_to_parser (token_from_parser t) = t.
Proof.
  destruct t as (terminal, semantic).
  destruct terminal; try reflexivity; destruct semantic; reflexivity.
Qed.

Lemma token_from_parser_to_parser t : token_from_parser (token_to_parser t) = t.
Proof.
  destruct t; reflexivity.
Qed.
