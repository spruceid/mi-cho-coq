%{Require Import String ZArith.
Require Import micheline_syntax location.
%}

%token <location * location> LBRACE RBRACE SEMICOLON LPAREN RPAREN EOF
%token <location * location * string> PRIMt STRt BYTESt
%token <location * location * Z> NUMBERt

%start <loc_micheline> file

%type <location * location * list (loc_micheline) > args
%type <list (loc_micheline) > seq
%type <loc_micheline> arg atom app micheline

%%

atom:
    STRt {
      let '((b, e), s) := $1 in
      Mk_loc_micheline (b, e, STR s)
    }
  | BYTESt {
      let '((b, e), s) := $1 in
      Mk_loc_micheline (b, e, BYTES s)
    }
  | NUMBERt {
      let '((b, e), z) := $1 in
      Mk_loc_micheline (b, e, NUMBER z) }
  | LBRACE seq RBRACE {
      let '(b, _) := $1 in
      let '(_, e) := $3 in
      Mk_loc_micheline (b, e, SEQ $2) }
;

arg:
    atom { $1 }
  | LPAREN app RPAREN { $2 }
  | PRIMt {
      let '((b, e), _) := $1 in
      Mk_loc_micheline (b, e, PRIM $1 nil)
    }
;

args:
    arg { let '(Mk_loc_micheline ((b, e), _)) := $1 in (b, e, cons $1 nil) }
  | arg args {
      let '(Mk_loc_micheline ((b, _), _)) := $1 in
      let '((_, e), l) := $2 in
      (b, e, cons $1 l)
    }
;

micheline:
    atom { $1 }
  | PRIMt {
      let '((b, e), _) := $1 in
      Mk_loc_micheline (b, e, PRIM $1 nil)
    }
  | app { $1 }
;

seq:
    { nil }
  | micheline SEMICOLON seq { cons $1 $3 }
;

app:
    PRIMt args {
      let '((b, _), _) := $1 in
      let '((_, e), l) := $2 in
      Mk_loc_micheline (b, e, PRIM $1 l)
    }
;

file: micheline EOF { $1 }
%%
