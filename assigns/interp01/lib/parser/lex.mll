{
open Par
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule read =
  parse
  | "if"          { IF }
  | "then"        { THEN }
  | "else"        { ELSE }
  | "let"         { LET }
  | "in"          { IN }
  | "fun"         { FUN }
  | "->"          { ARROW }
  | "="           { EQ }
  | "+"           { PLUS }
  | "-"           { MINUS }
  | "*"           { TIMES }
  | "/"           { DIVIDE }
  | "mod"         { MOD }
  | "&&"          { AND }
  | "||"          { OR }
  | "<"           { LT }
  | "<="          { LTE }
  | ">"           { GT }
  | ">="          { GTE }
  | "<>"          { NEQ }
  | "("           { LPAREN }
  | ")"           { RPAREN }
  | "true"        { TRUE }
  | "false"       { FALSE }
  | "()"          { UNIT }  
  | num           { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | var           { VAR (Lexing.lexeme lexbuf) }
  | whitespace    { read lexbuf }  
  | eof           { EOF }    

