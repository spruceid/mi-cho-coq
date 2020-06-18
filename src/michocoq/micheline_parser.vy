%{Require Import String ZArith.
Require Import micheline_syntax location.
%}

%token <location * location> LBRACE RBRACE SEMICOLON LPAREN RPAREN EOF
%token <location * location * string> PRIMt STRt BYTESt ANNOTATIONt
%token <location * location * Z> NUMBERt

%start <loc_micheline> file
%start <list (loc_micheline)> seq_file

%type <location * location * list annotation * list loc_micheline > argument
%type <location * location * list annotation * list loc_micheline > arguments
%type <annotation> annotation
%type <list (loc_micheline) > seq
%type <loc_micheline> atom app micheline

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
  | PRIMt {
      let '((b, e), _) := $1 in
      Mk_loc_micheline (b, e, PRIM $1 nil nil)
    }
  | LPAREN PRIMt RPAREN {
      let '((b, e), _) := $2 in
      Mk_loc_micheline (b, e, PRIM $2 nil nil)
    }
  | LPAREN app RPAREN { $2 }
  | LBRACE seq RBRACE {
      let '(b, _) := $1 in
      let '(_, e) := $3 in
      Mk_loc_micheline (b, e, SEQ $2) }
;

app:
    PRIMt arguments {
      let '((b, _), _) := $1 in
      let '((_, e), l1, l2) := $2 in
      Mk_loc_micheline (b, e, PRIM $1 l1 l2)
    }
;

annotation:
    ANNOTATIONt {
      let '((b, e), s) := $1 in
      Mk_annot (b, e, s)
    }
;


argument:
    atom { let '(Mk_loc_micheline ((b, e), n)) := $1 in (b, e, nil, cons $1 nil) }
  | annotation { let '(Mk_annot ((b, e), a)) := $1 in (b, e, cons $1 nil, nil) }
;

arguments:
    argument { $1 }
  | argument arguments {
      let '((b, _), l1, l2) := $1 in
      let '((_, e), l3, l4) := $2 in
      (b, e, List.app l1 l3, List.app l2 l4)
    }
;

micheline:
    atom { $1 }
  | app { $1 }
;

seq:
    { nil }
  | micheline { cons $1 nil }
  | micheline SEMICOLON seq { cons $1 $3 }
;

file: micheline EOF { $1 }
seq_file: seq EOF { $1 }
%%
