%{Require Import String ZArith.
Require Import micheline_syntax.
%}

%token LBRACE RBRACE SEMICOLON LPAREN RPAREN
%token <string> PRIM STR BYTES
%token <Z> NUMBER
%token EOF

%start <micheline> file

%type <list micheline> seq args
%type <micheline> arg atom app micheline

%%

atom:
    STR { STR $1 }
  | BYTES { BYTES $1 }
  | NUMBER { NUMBER $1 }
  | LBRACE seq RBRACE { SEQ $2 }
;

arg:
    atom { $1 }
  | LPAREN app RPAREN { $2 }
  | PRIM { PRIM $1 nil }
;

args:
    arg { cons $1 nil }
  | arg args { cons $1 $2 }
;

micheline:
    atom { $1 }
  | PRIM { PRIM $1 nil }
  | app { $1 }
;

seq:
    { nil }
  | micheline SEMICOLON seq { cons $1 $3 }
;

app:
    PRIM args { PRIM $1 $2 }
;

file: micheline EOF { $1 }
%%
