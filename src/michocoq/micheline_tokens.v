Require Import String ZArith.
Require micheline_parser.
Import micheline_parser.Aut.GramDefs.
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

Definition token_from_parser (t : parser_token) : (location * location * token) :=
  match t with
  | existT _ LBRACE't (b, e) => (b, e, LBRACE)
  | existT _ RBRACE't (b, e) => (b, e, RBRACE)
  | existT _ SEMICOLON't (b, e) => (b, e, SEMICOLON)
  | existT _ LPAREN't (b, e) => (b, e, LPAREN)
  | existT _ RPAREN't (b, e) => (b, e, RPAREN)
  | existT _ PRIM't ((b, e), s) => (b, e, PRIM s)
  | existT _ STR't ((b, e), s) => (b, e, STR s)
  | existT _ NUMBER't ((b, e), n) => (b, e, NUMBER n)
  | existT _ BYTES't ((b, e), s) => (b, e, BYTES s)
  | existT _ EOF't (b, e) => (b, e, EOF)
  end.

Definition token_to_parser (t : (location * location * token)) : parser_token :=
  let '((b, e), t) := t in
  match t with
  | LBRACE => existT _ LBRACE't (b, e)
  | RBRACE => existT _ RBRACE't (b, e)
  | SEMICOLON => existT _ SEMICOLON't (b, e)
  | LPAREN => existT _ LPAREN't (b, e)
  | RPAREN => existT _ RPAREN't (b, e)
  | PRIM s => existT _ PRIM't (b, e, s)
  | STR s => existT _ STR't (b, e, s)
  | NUMBER n => existT _ NUMBER't (b, e, n)
  | BYTES s => existT _ BYTES't (b, e, s)
  | EOF => existT _ EOF't (b, e)
  end.

Lemma token_to_parser_from_parser t : token_to_parser (token_from_parser t) = t.
Proof.
  destruct t as (terminal, semantic).
  destruct terminal; try reflexivity; destruct semantic as ((b, e), v); reflexivity.
Qed.

Lemma token_from_parser_to_parser t : token_from_parser (token_to_parser t) = t.
Proof.
  destruct t as ((b, e), t); destruct t; reflexivity.
Qed.
