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
