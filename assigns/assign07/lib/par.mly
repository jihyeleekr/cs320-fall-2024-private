%{
open Utils (* Import ADT from utils.ml *)
%}

%token IF THEN ELSE LET IN FUN ARROW EQ PLUS MINUS TIMES DIVIDE MOD AND OR LT LTE GT GTE NEQ
%token <int> NUM
%token <string> VAR
%token UNIT TRUE FALSE
%start <prog> main
%type <expr> expr expr2 expr3

%right OR
%right AND
%left LT LTE GT GTE EQ NEQ
%left PLUS MINUS
%left TIMES DIVIDE MOD

%%

main:
  | expr { $1 } (* The main expression is just an <expr> *)

expr:
  | IF expr THEN expr ELSE expr { If ($2, $4, $6) }
  | LET VAR EQ expr IN expr     { Let ($2, $4, $6) }
  | FUN VAR ARROW expr          { Fun ($2, $4) }
  | expr2                       { $1 }

expr2:
  | expr2 bop expr2             { Bop ($2, $1, $3) } (* Binary operations *)
  | expr2 expr3                 { App ($1, $2) } (* Application, left-associative *)
  | expr3                       { $1 }

expr3:
  | UNIT                        { Unit }
  | TRUE                        { True }
  | FALSE                       { False }
  | NUM                         { Num $1 }
  | VAR                         { Var $1 }
  | '(' expr ')'                { $2 }

bop:
  | PLUS   { Add }
  | MINUS  { Sub }
  | TIMES  { Mul }
  | DIVIDE { Div }
  | MOD    { Mod }
  | LT     { Lt }
  | LTE    { Lte }
  | GT     { Gte }
  | GTE    { Gte }
  | EQ     { Eq }
  | NEQ    { Neq }
  | AND    { And }
  | OR     { Or }


