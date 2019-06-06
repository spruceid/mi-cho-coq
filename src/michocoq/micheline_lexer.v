Require Import String Ascii ZArith.
Require error micheline_parser.
Require Import micheline_tokens location.

Definition char_is_num (c : ascii) :=
  match c with
  | "0"%char | "1"%char | "2"%char | "3"%char | "4"%char | "5"%char
  | "6"%char | "7"%char | "8"%char | "9"%char => true
  | _ => false
  end.

Definition eqb_ascii (a b : ascii) : bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Bool.eqb a0 b0 && Bool.eqb a1 b1 && Bool.eqb a2 b2 && Bool.eqb a3 b3
    && Bool.eqb a4 b4 && Bool.eqb a5 b5 && Bool.eqb a6 b6 && Bool.eqb a7 b7
 end.

Definition char_is_alpha (c : ascii) :=
  let leb a b := (N.leb (N_of_ascii a) (N_of_ascii b)) in
  orb (andb (leb "a"%char c) (leb c "z"%char))
      (orb (andb (leb "A"%char c) (leb c "Z"%char))
           (eqb_ascii "_"%char c)).

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


Definition string_snoc s c := (s ++ String c "")%string.

Fixpoint lex_micheline (input : string) (loc : location) : error.M (list (location.location * location.location * token)) :=
  match input with
  | String first_char input =>
    let nloc := location_incr loc in
    match first_char with
    | "{"%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, nloc, LBRACE) l))
        (lex_micheline input loc)
    | "}"%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, nloc, RBRACE) l))
        (lex_micheline input loc)
    | "("%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, nloc, LPAREN) l))
        (lex_micheline input loc)
    | ")"%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, nloc, RPAREN) l))
        (lex_micheline input loc)
    | ";"%char =>
      error.bind
        (fun l => error.Return _ (cons (loc, nloc, SEMICOLON) l))
        (lex_micheline input loc)
    | """"%char =>
      lex_micheline_string input ""%string loc nloc
    | "#"%char =>
      lex_micheline_inline_comment input nloc
    | " "%char =>
      lex_micheline input nloc
    | "010"%char (* newline *) =>
      lex_micheline input (location_newline loc)
    | "/"%char =>
      match input with
      | String "*"%char s =>
        lex_micheline_multiline_comment s (location_incr nloc)
      | _ =>
        error.Failed _ (error.Lexing loc)
      end
    | c =>
      if char_is_num c then
        (fix lex_micheline_number (input : string) (acc : Z) start loc :=
           match input with
           | String c s =>
             let loc := location_incr loc in
             if char_is_num c then
               lex_micheline_number s (Z_of_char c acc) start loc
             else
               (error.bind (fun l =>
                              error.Return _ (cons (start, loc, NUMBER acc) l))
                           (lex_micheline input loc))
           | s => lex_micheline s loc
           end) input (Z_of_char c 0%Z) loc loc
      else
        if char_is_alpha c then
          (fix lex_micheline_prim (input : string) (acc : string) start loc :=
             match input with
             | String c s =>
               let loc := location_incr loc in
               if char_is_alpha c then
                 lex_micheline_prim s (string_snoc acc c) start loc
               else
                 (error.bind (fun l => error.Return _ (cons (start, loc, PRIM acc) l))
                             (lex_micheline input loc))
             | s => lex_micheline s loc
             end) input (String c ""%string) loc loc
        else
          error.Failed _ (error.Lexing loc)
    end
  | EmptyString => error.Return _ nil
  end
with
lex_micheline_string (input : string) (acc : string) start loc :=
  match input with
  | String """"%char s =>
    let loc := location_incr loc in
    error.bind
      (fun l => error.Return _ (cons (start, loc, STR acc) l))
      (lex_micheline s loc)
  | String c s =>
    let loc := location_incr loc in
    lex_micheline_string s (string_snoc acc c) start loc
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
  | String "010"%char (* newline *) s =>
    let loc := location_newline loc in
    lex_micheline_multiline_comment s loc
  | String _ s =>
    let loc := location_incr loc in
    lex_micheline_multiline_comment s loc
  | Empty_string => error.Failed _ (error.Lexing loc)
  end.


Fixpoint tokens_to_parser (ts : list (location * location * token)) : error.M (Streams.Stream parser_token) :=
  match ts with
  | nil => error.Return _ (Streams.const (token_to_parser (location_start, location_start, EOF)))
  | cons t ts =>
    error.bind
      (fun s => error.Return _ (Streams.Cons (token_to_parser t) s))
      (tokens_to_parser ts)
  end.

Definition lex_micheline_to_parser (input : string)
  : error.M (Streams.Stream parser_token) :=
  error.bind tokens_to_parser (lex_micheline input location_start).