%{
open Utils
%}

%token <int> NUM

%token TRUE
%token FALSE
%token ADD
%token EQ
%token LPAREN
%token RPAREN

%token EOF

%start <Utils.prog> prog

%%

prog:
  | EOF { Num 0 }

expr:
  | n = NUM { Num n }
  | TRUE {True}
  | FALSE { False}
  | LPAREN; ADD;  e1 = expr; e2 = expr ;RPAREN { Add (e1, e2)}
  | LPAREN; EQ; e1 = expr; e2 = expr ; RPAREN { Eq (e1, e2)}
