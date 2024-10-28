{
open Parser (* For referring to token types in par.mly *)
}

rule token = parse
  | "if"         { IF }
  | "then"       { THEN }
  | "else"       { ELSE }
  | "let"        { LET }
  | "in"         { IN }
  | "fun"        { FUN }
  | "->"         { ARROW }
  | "="          { EQ }
  | "+"          { PLUS }
  | "-"          { MINUS }
  | "*"          { TIMES }
  | "/"          { DIVIDE }
  | "mod"        { MOD }
  | "&&"         { AND }
  | "||"         { OR }
  | "<"          { LT }
  | "<="         { LTE }
  | ">"          { GT }
  | ">="         { GTE }
  | "<>"         { NEQ }
  | ['0'-'9']+ as num { NUM (int_of_string num) }
  | ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']* as var { VAR var }
  | _            { failwith "Unrecognized token" }
