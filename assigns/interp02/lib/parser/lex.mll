{
open Par
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule read = parse
| '(' { LPAREN }
| ')' { RPAREN }
| ':' { COLON }
| "->" { ARROW }
| "let" { LET }
| "rec" { REC }
| "in" { IN }
| "if" { IF }
| "then" { THEN }
| "else" { ELSE }
| "fun" { FUN }
| "true" { TRUE }
| "false" { FALSE }
| "assert" { ASSERT }
| '+' { PLUS }
| '-' { MINUS }
| '*' { TIMES }
| '/' { DIV }
| "mod" { MOD }
| '<' { LT }
| "<=" { LTE }
| '>' { GT }
| ">=" { GTE }
| '=' { EQUALS }
| "<>" { NEQ }
| "&&" { AND }
| "||" { OR }
| num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
| var { VAR (Lexing.lexeme lexbuf) }
| whitespace { read lexbuf }
| eof { EOF }
