Require Import List String Ascii ZArith.
Require error micheline_parser.
Require Import micheline_tokens location.
Import error.Notations.

Definition char_is_num (c : ascii) :=
  match c with
  | "0"%char | "1"%char | "2"%char | "3"%char | "4"%char | "5"%char
  | "6"%char | "7"%char | "8"%char | "9"%char => true
  | _ => false
  end.

Definition char_is_annot (c : ascii) :=
  match c with
  | "%"%char | "@"%char | ":"%char => true
  | _ => false
  end.

Check (eq_refl : char_is_num "a"%char = false).
Check (eq_refl : char_is_num "z"%char = false).
Check (eq_refl : char_is_num "A"%char = false).
Check (eq_refl : char_is_num "Z"%char = false).
Check (eq_refl : char_is_num "_"%char = false).
Check (eq_refl : char_is_num "0"%char = true).
Check (eq_refl : char_is_num "9"%char = true).

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

Definition char_is_dot (c : ascii) := eqb_ascii "."%char c.

Definition char_is_hex (c : ascii) :=
  let leb a b := (N.leb (N_of_ascii a) (N_of_ascii b)) in
  orb (andb (leb "a"%char c) (leb c "f"%char))
      (orb (andb (leb "A"%char c) (leb c "F"%char))
           (char_is_num c)).

Check (eq_refl : char_is_alpha "a"%char = true).
Check (eq_refl : char_is_alpha "z"%char = true).
Check (eq_refl : char_is_alpha "A"%char = true).
Check (eq_refl : char_is_alpha "Z"%char = true).
Check (eq_refl : char_is_alpha "_"%char = true).
Check (eq_refl : char_is_alpha "0"%char = false).
Check (eq_refl : char_is_alpha "9"%char = false).

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
      let! l := lex_micheline input loc in
      error.Return (cons (loc, nloc, LBRACE) l)
    | "}"%char =>
      let! l := lex_micheline input loc in
      error.Return (cons (loc, nloc, RBRACE) l)
    | "("%char =>
      let! l := lex_micheline input loc in
      error.Return (cons (loc, nloc, LPAREN) l)
    | ")"%char =>
      let! l := lex_micheline input loc in
      error.Return (cons (loc, nloc, RPAREN) l)
    | ";"%char =>
      let! l := lex_micheline input loc in
      error.Return (cons (loc, nloc, SEMICOLON) l)
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
    | "-"%char =>
      let loc := location_incr loc in
      (fix lex_micheline_number (input : string) (acc : Z) start loc :=
         match input with
         | String c s =>
           if char_is_num c then
             let loc := location_incr loc in
             lex_micheline_number s (Z_of_char c acc) start loc
           else
            let! l := lex_micheline input loc in
            error.Return (cons (start, loc, NUMBER (- acc)%Z) l)
         | EmptyString => error.Return (cons (start, loc, NUMBER (- acc)%Z) nil)
         end) input 0%Z loc loc
    | "0"%char =>
      match input with
      | String "x" s =>
        (fix lex_micheline_bytes (input : string) (acc : string) start loc :=
           match input with
           | String c s =>
             if char_is_hex c then
               let loc := location_incr loc in
               lex_micheline_bytes s (string_snoc acc c) start loc
             else
              let! l := lex_micheline input loc in
              error.Return (cons (start, loc, BYTES acc) l)
           | EmptyString => error.Return (cons (start, loc, BYTES acc) nil)
           end) s EmptyString loc (location_incr (location_incr loc))
      | String c s =>
        if char_is_num c then error.Failed _ (error.Lexing loc)
        else
          let! l := lex_micheline input loc in
          error.Return (cons (loc, location_incr loc, NUMBER 0%Z) l)
      | EmptyString => error.Return (cons (loc, location_incr loc, NUMBER 0%Z) nil)
      end
    | c =>
      if char_is_num c then
        (fix lex_micheline_number (input : string) (acc : Z) start loc :=
           match input with
           | String c s =>
             if char_is_num c then
               let loc := location_incr loc in
               lex_micheline_number s (Z_of_char c acc) start loc
             else
              let! l := lex_micheline input loc in
              error.Return (cons (start, loc, NUMBER acc) l)
           | EmptyString => error.Return (cons (start, loc, NUMBER acc) nil)
           end) input (Z_of_char c 0%Z) loc loc
      else
        if char_is_alpha c then
          (fix lex_micheline_prim (input : string) (acc : string) start loc :=
             match input with
             | String c s =>
               if orb (char_is_alpha c) (char_is_num c) then
                 let loc := location_incr loc in
                 lex_micheline_prim s (string_snoc acc c) start loc
               else
                let! l := lex_micheline input loc in
                error.Return (cons (start, loc, PRIM acc) l)
             | EmptyString => error.Return (cons (start, loc, PRIM acc) nil)
             end) input (String c ""%string) loc loc
        else
          if char_is_annot c then (* Annotations are ignored *)
            (fix lex_micheline_annot input loc :=
               match input with
               | String c s =>
                 if (orb (char_is_alpha c)
                         (orb (char_is_num c)
                              (orb (char_is_annot c)
                                   (char_is_dot c)))) then
                   let loc := location_incr loc in
                   lex_micheline_annot s loc
                 else
                   lex_micheline input loc
               | EmptyString => error.Return nil
               end) input loc
          else
            error.Failed _ (error.Lexing loc)
    end
  | EmptyString => error.Return nil
  end
with
lex_micheline_string (input : string) (acc : string) start loc :=
  match input with
  | String """"%char s =>
    let loc := location_incr loc in
    let! l := lex_micheline s loc in
    error.Return (cons (start, loc, STR acc) l)
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
  | Empty_string => error.Return nil
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

CoFixpoint const_buffer (t : micheline_parser.Aut.Gram.token) : micheline_parser.MenhirLibParser.Inter.buffer :=
  micheline_parser.MenhirLibParser.Inter.Buf_cons t (const_buffer t).

Fixpoint tokens_to_parser (ts : list (location * location * token)) : error.M micheline_parser.MenhirLibParser.Inter.buffer :=
  match ts with
  | nil => error.Return (const_buffer (token_to_parser (location_start, location_start, EOF)))
  | cons t ts =>
    let! s := tokens_to_parser ts in
    error.Return (micheline_parser.MenhirLibParser.Inter.Buf_cons (token_to_parser t) s)
  end.

Definition lex_micheline_to_parser (input : string)
  : error.M micheline_parser.MenhirLibParser.Inter.buffer :=
  let! ts := lex_micheline input location_start in
  tokens_to_parser ts.

(* Some interesting lemmas *)

Lemma eqb_ascii_eq n m : (eqb_ascii n m) = true <-> n = m.
Proof.
  split; intros.
  + unfold eqb_ascii in H. destruct n; destruct m.
    repeat rewrite Bool.andb_true_iff in H.
    destruct H as [[[[[[[H H0] H1] H2] H3] H4] H5] H6].
    f_equal; apply Bool.eqb_prop; assumption.
  + rewrite H. unfold eqb_ascii. destruct m.
    destruct b; destruct b0; destruct b1; destruct b2;
      destruct b3; destruct b4; destruct b5; destruct b6; reflexivity.
Qed.

Inductive char_not_in_string : ascii -> string -> Prop :=
| CharNotInEmpty : forall c, char_not_in_string c ""
| CharNotInString : forall c c' s,
    c <> c' ->
    char_not_in_string c s ->
    char_not_in_string c (String c' s).

Lemma lex_string_end : forall s start loc,
    lex_micheline_string """" s start loc =
    error.Return ((start, location_incr loc, (micheline_tokens.STR s))::nil).
Proof.
  intros s start loc.
  reflexivity.
Qed.

Lemma append_empty_right : forall s, (String.append s "") = s.
Proof.
  induction s.
  - reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed.

Lemma append_assoc : forall s1 s2 s3,
    ((s1 ++ s2) ++ s3)%string = (s1 ++ (s2 ++ s3))%string.
Proof.
  induction s1; intros.
  - reflexivity.
  - simpl. rewrite IHs1. reflexivity.
Qed.

Lemma append_string_empty_left : forall a s, (String a "" ++ s)%string = String a s.
Proof. reflexivity. Qed.

Lemma lex_string_aux : forall s2 start loc,
    char_not_in_string """" s2 ->
    forall s1, lex_micheline_string (s2++"""") s1 start loc =
    error.Return ((start, location_add loc ((String.length s2)+1), (micheline_tokens.STR (s1++s2)))::nil).
Proof.
  induction s2; intros.
  - (* Empty string *) simpl. rewrite append_empty_right. reflexivity.
  - (* c::s *)
    simpl. inversion H; subst.
    specialize (IHs2 start (location_incr loc) H4 (string_snoc s1 a)).
    unfold string_snoc in *. rewrite IHs2. simpl.
    unfold string_snoc; simpl.
    rewrite location.location_add_incr_S.
    rewrite append_assoc. rewrite append_string_empty_left.
    case_eq a. intros. case_eq b; case_eq b0; case_eq b1; case_eq b2; case_eq b3; case_eq b4; case_eq b5; case_eq b6; try reflexivity.
    intros. subst b; subst b0; subst b1; subst b2; subst b3; subst b4; subst b5; subst b6. symmetry in H0. contradiction.
Qed.

Corollary lex_string : forall s start,
    char_not_in_string """" s ->
    lex_micheline (""""++s++"""") start =
    error.Return ((start, location_add start ((String.length s)+2), (micheline_tokens.STR s))::nil).
Proof.
  intros. simpl.
  specialize (lex_string_aux s start (location_incr start) H "").
  simpl. intro.
  rewrite <- location.location_add_incr_S in H0.
  assert (S (length s + 1) = (length s + 2)) as Hlen by omega.
  rewrite Hlen in H0. assumption.
Qed.
