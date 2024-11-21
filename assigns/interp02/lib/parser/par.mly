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
%token EQ "="
%token DIV "/"
%token MOD "mod"
%token LT "<"
%token LTE "<="
%token GT ">"
%token GTE ">="
%token NEQ "<>"
%token AND "&&"
%token OR "||"
%token IN "in"
%token <string> VAR
%token <int> NUM
%token IF "if"
%token THEN "then"
%token ELSE "else"
%token PLUS "+"
%token TIMES "*"
%token MINUS "-"
%token TRUE "true"
%token FALSE "false"
%token ASSERT "assert"

%token INTTY "int"
%token BOOLTY "bool"
%token COLON ":"

%token UNIT "()"
%token UNITTY "unit"

%right ARROW
%right OR AND
%left LT LTE GT GTE EQ
%left PLUS MINUS
%left TIMES DIV MOD

%start <Utils.prog> prog

%%

prog:
  | ls = toplet * EOF { ls }

toplet:
  | "let" x = VAR args = arg* ":" ty = ty "=" e = expr
    { { is_rec = false; name = x; args = args; ty; value = e } }
  | "let" "rec" x = VAR args = arg* ":" ty = ty "=" e = expr
    { { is_rec = true; name = x; args = args; ty; value = e } }

arg:
  | "(" x = VAR ":" ty = ty ")" { (x, ty) }

ty:
  | "int" { IntTy }
  | "bool" { BoolTy }
  | "unit" { UnitTy }
  | "(" t = ty ")" { t }
  | t1 = ty "->" t2 = ty { FunTy(t1, t2) }

expr:
  | "let" x = VAR args = arg* ":" ty = ty "=" e1 = expr "in" e2 = expr
    { SLet { is_rec = false; name = x; args = args; ty; value = e1; body = e2 } }
  | "let" "rec" x = VAR args = arg* ":" ty = ty "=" e1 = expr "in" e2 = expr
    { SLet { is_rec = true; name = x; args = args; ty; value = e1; body = e2 } }
  | "if" e1 = expr "then" e2 = expr "else" e3 = expr
      { SIf(e1, e2, e3) }
  | "fun" arg=arg ; args=arg* "->" e = expr
      { SFun { arg = arg; args = args; body = e } }
  | e = expr2 { e }

expr2:
  | e1 = expr2 bop = bop e2 = expr2
      { SBop(bop, e1, e2) }
  | "assert" e = expr3
      { SAssert e }
  | e = expr3 es = expr3*
      { List.fold_left (fun e1 e2 -> SApp (e1, e2)) e es }


expr3:
  | UNIT { SUnit }
  | TRUE { STrue }
  | FALSE { SFalse }
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