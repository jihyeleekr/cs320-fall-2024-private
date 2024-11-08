%{
open Utils
%}

%token <int> NUM
%token <string> VAR
%token IF THEN ELSE LET IN FUN ARROW
%token REC  
%token PLUS MINUS TIMES DIVIDE MOD LTE LT GTE GT EQ NEQ AND OR
%token TRUE FALSE LPAREN RPAREN EOF UNIT

%right OR
%right AND
%left LT LTE GT GTE EQ NEQ
%left PLUS MINUS
%left TIMES DIVIDE MOD

%start <Utils.prog> prog

%%

prog:
  | e = expr EOF { e }
;

expr:
  | IF cond = expr THEN e1 = expr ELSE e2 = expr { If(cond, e1, e2) }
  | LET var = VAR EQ value = expr IN body = expr { Let(var, value, body) }
  | LET REC var = VAR EQ value = expr IN body = expr { LetRec(var, value, body) }
  | FUN arg = VAR ARROW body = expr { Fun(arg, body) }
  | or_expr { $1 }
;

or_expr:
  | e1 = or_expr OR e2 = and_expr { Bop(Or, e1, e2) }
  | and_expr { $1 }
;

and_expr:
  | e1 = and_expr AND e2 = compare_expr { Bop(And, e1, e2) }
  | compare_expr { $1 }
;

compare_expr:
  | e1 = compare_expr LT e2 = add_expr { Bop(Lt, e1, e2) }
  | e1 = compare_expr LTE e2 = add_expr { Bop(Lte, e1, e2) }
  | e1 = compare_expr GT e2 = add_expr { Bop(Gt, e1, e2) }
  | e1 = compare_expr GTE e2 = add_expr { Bop(Gte, e1, e2) }
  | e1 = compare_expr EQ e2 = add_expr { Bop(Eq, e1, e2) }
  | e1 = compare_expr NEQ e2 = add_expr { Bop(Neq, e1, e2) }
  | add_expr { $1 }
;

add_expr:
  | e1 = add_expr PLUS e2 = mult_expr { Bop(Add, e1, e2) }
  | e1 = add_expr MINUS e2 = mult_expr { Bop(Sub, e1, e2) }
  | mult_expr { $1 }
;

mult_expr:
  | e1 = mult_expr TIMES e2 = app { Bop(Mul, e1, e2) }
  | e1 = mult_expr DIVIDE e2 = app { Bop(Div, e1, e2) }
  | e1 = mult_expr MOD e2 = app { Bop(Mod, e1, e2) }
  | app { $1 }
;

app:
  | e1 = app e2 = simple_expr { App(e1, e2) }
  | simple_expr { $1 }
;

simple_expr:
  | LPAREN e = expr RPAREN { e }
  | n = NUM { Num n }
  | x = VAR { Var x }
  | TRUE { True }
  | FALSE { False }
  | UNIT { Unit }
;
