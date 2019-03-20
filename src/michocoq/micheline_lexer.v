Require Import String.
Require Import Ascii.
Require Import ZArith.
Require error.
Require micheline_parser.
Require Import micheline_tokens.

Definition char_is_num (c : ascii) :=
  match c with
  | "0"%char | "1"%char | "2"%char | "3"%char | "4"%char | "5"%char
  | "6"%char | "7"%char | "8"%char | "9"%char => true
  | _ => false
  end.

Definition char_is_alpha (c : ascii) :=
  let leb a b := (N.leb (N_of_ascii a) (N_of_ascii b)) in
  orb (andb (leb "a"%char c) (leb c "z"%char))
      (andb (leb "A"%char c) (leb c "Z"%char)).

Definition Z_of_char (c : ascii) (acc : Z) : Z :=
  match c with
  | "0"%char => (10 * acc)%Z
  | "1"%char => (10 * acc + 1)%Z
  | "2"%char => (10 * acc + 2)%Z
  | "3"%char => (10 * acc + 3)%Z
  | "4"%char => (10 * acc + 4)%Z
  | "5"%char => (10 * acc + 5)%Z
  | "6"%char => (10 * acc + 6)%Z
  | "7"%char => (10 * acc + 7)%Z
  | "8"%char => (10 * acc + 8)%Z
  | "9"%char => (10 * acc + 9)%Z
  | c => 0%Z
  end.

Definition location_start : error.location :=
  {| error.line := 0; error.column := 0 |}.

Definition location_incr (loc : error.location) : error.location :=
  {| error.line := error.line loc; error.column := S (error.column loc) |}.

Definition location_newline (loc : error.location) : error.location :=
  {| error.line := S (error.line loc); error.column := 0 |}.

Definition string_snoc s c := (s ++ String c "")%string.

Fixpoint lex_micheline (input : string) (loc : error.location) : error.M (list (error.location * token)) :=
  match input with
  | String first_char input =>
    let loc := location_incr loc in
    match first_char with
    | "{"%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, LBRACE) l))
        (lex_micheline input loc)
    | "}"%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, RBRACE) l))
        (lex_micheline input loc)
    | "("%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, LPAREN) l))
        (lex_micheline input loc)
    | ")"%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, RPAREN) l))
        (lex_micheline input loc)
    | ";"%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, SEMICOLON) l))
        (lex_micheline input loc)
    | """"%char =>
      lex_micheline_string input ""%string loc
    | "#"%char =>
      lex_micheline_inline_comment input loc
    | " "%char =>
      lex_micheline input loc
    | "010"%char (* newline *) =>
      lex_micheline input (location_newline loc)
    | "/"%char =>
      match input with
      | String "*"%char s =>
        lex_micheline_multiline_comment s loc
      | _ =>
        error.Failed _ (error.Lexing loc)
      end
    | c =>
      if char_is_num c then
        (fix lex_micheline_number (input : string) (acc : Z) loc :=
           match input with
           | String c s =>
             let loc := location_incr loc in
             if char_is_num c then
               lex_micheline_number s (Z_of_char c acc) loc
             else
               (error.bind (fun l => error.Return _ (cons (loc, NUMBER acc) l))
                           (lex_micheline input loc))
           | s => lex_micheline s loc
           end) input (Z_of_char c 0%Z) loc
      else
        if char_is_alpha c then
          (fix lex_micheline_prim (input : string) (acc : string) loc :=
             match input with
             | String c s =>
               let loc := location_incr loc in
               if char_is_alpha c then
                 lex_micheline_prim s (string_snoc acc c) loc
               else
                 (error.bind (fun l => error.Return _ (cons (loc, PRIM acc) l))
                             (lex_micheline input loc))
             | s => lex_micheline s loc
             end) input (String c ""%string) loc
        else
          error.Failed _ (error.Lexing loc)
    end
  | EmptyString => error.Return _ nil
  end
with
lex_micheline_string (input : string) (acc : string) loc :=
  match input with
  | String """"%char s =>
    let loc := location_incr loc in
    error.bind
      (fun l => error.Return _ (cons (loc, STR acc) l))
      (lex_micheline s loc)
  | String c s =>
    let loc := location_incr loc in
    lex_micheline_string s (string_snoc acc c) loc
  | EmptyString =>
    error.Failed _ (error.Lexing loc)
  end
with
lex_micheline_inline_comment (input : string) loc :=
  match input with
  | String "010"%char (* newline *) s => lex_micheline s (location_newline loc)
  | String _ s =>
    let loc := location_incr loc in
    lex_micheline_inline_comment s loc
  | Empty_string => error.Return _ nil
  end
with
lex_micheline_multiline_comment (input : string) loc :=
  match input with
  | String "*"%char (String "/" s) =>
    let loc := location_incr loc in
    let loc := location_incr loc in
    lex_micheline s loc
  | String _ s =>
    let loc := location_incr loc in
    lex_micheline_multiline_comment s loc
  | Empty_string => error.Failed _ (error.Lexing loc)
  end.


Fixpoint tokens_to_parser (ts : list (error.location * token)) : error.M (Streams.Stream parser_token) :=
  match ts with
  | nil => error.Return _ (Streams.const (token_to_parser EOF))
  | cons (_, t) ts =>
    error.bind
      (fun s => error.Return _ (Streams.Cons (token_to_parser t) s))
      (tokens_to_parser ts)
  end.

Definition lex_micheline_to_parser (input : string)
  : error.M (Streams.Stream parser_token) :=
  error.bind tokens_to_parser (lex_micheline input location_start).
