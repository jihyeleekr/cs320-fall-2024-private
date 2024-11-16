%{
open Utils
%}

%token EOF
%token FUN "fun"
%token ARROW "->"
%token LPAREN "("
%token RPAREN ")"
%token LET "let"
%token REC "rec"
%token EQUALS "="
%token IN "in"
%token ASSERT "assert"
%token IF "if"
%token THEN "then"
%token ELSE "else"
%token PLUS "+"
%token MINUS "-"
%token TIMES "*"
%token SLASH "/"
%token MOD "mod"
%token LT "<"
%token LTE "<="
%token GT ">"
%token GTE ">="
%token EQ "="
%token NEQ "<>"
%token AND "&&"
%token OR "||"
%token COLON ":"
%token COMMA ","
%token TRUE "true"
%token FALSE "false"
%token UNIT "()"
%token <string> VAR
%token <int> NUM
%token INT "int"
%token BOOL "bool"

%right ARROW
%left OR
%left AND
%nonassoc LT LTE GT GTE EQ NEQ
%left PLUS MINUS
%left TIMES SLASH MOD
%left APP

%start <Utils.prog> main

%%

main:
  | program = program EOF { program }

program:
  | toplist = toplist { List.rev toplist }

toplist:
  | toplist = toplist toplet = toplet { toplet :: toplist }
  | /* empty */ { [] }

toplet:
  | "let" x = VAR args_opt = args_opt ":" ty = ty "=" e = expr
    { { is_rec = false; name = x; args = args_opt; ty; value = e } }
  | "let" "rec" x = VAR args_opt = args_opt ":" ty = ty "=" e = expr
    { { is_rec = true; name = x; args = args_opt; ty; value = e } }

args_opt:
  | /* empty */ { [] }
  | args = args { args }

args:
  | arg = arg args = args { arg :: args }
  | arg = arg { [arg] }

arg:
  | "(" x = VAR ":" ty = ty ")" { (x, ty) }

ty:
  | "int" { IntTy }
  | "bool" { BoolTy }
  | "unit" { UnitTy }
  | t1 = ty "->" t2 = ty { FunTy(t1, t2) }
  | "(" ty = ty ")" { ty }

expr:
  | let_expr = let_expr { let_expr }
  | if_expr = if_expr { if_expr }
  | fun_expr = fun_expr { fun_expr }
  | e = expr2 { e }

let_expr:
  | "let" x = VAR args_opt = args_opt ":" ty = ty "=" e1 = expr "in" e2 = expr
    { SLet { is_rec = false; name = x; args = args_opt; ty; value = e1; body = e2 } }
  | "let" "rec" x = VAR args_opt = args_opt ":" ty = ty "=" e1 = expr "in" e2 = expr
    { SLet { is_rec = true; name = x; args = args_opt; ty; value = e1; body = e2 } }

if_expr:
  | "if" e1 = expr "then" e2 = expr "else" e3 = expr { SIf(e1, e2, e3) }

fun_expr:
  | "fun" arg = arg args = args "->" e = expr { SFun { arg; args; body = e } }

expr2:
  | e1 = expr2 bop = bop e2 = expr2 { SBop(bop, e1, e2) }
  | "assert" e = expr3 { SAssert e }
  | e = expr3 { e }

expr3:
  | "()" { SUnit }
  | "true" { STrue }
  | "false" { SFalse }
  | n = NUM { SNum n }
  | x = VAR { SVar x }
  | "(" e = expr ")" { e }

bop:
  | "+" { Add }
  | "-" { Sub }
  | "*" { Mul }
  | "/" { Div }
  | "mod" { Mod }
  | "<" { Lt }
  | "<=" { Lte }
  | ">" { Gt }
  | ">=" { Gte }
  | "=" { Eq }
  | "<>" { Neq }
  | "&&" { And }
  | "||" { Or }
