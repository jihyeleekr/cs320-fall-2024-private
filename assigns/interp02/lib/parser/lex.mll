{
open Par

let whitespace = [' ' '\t' '\n' '\r']+
let num = ['-']? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*
}

rule tokenize = parse
| whitespace { tokenize lexbuf } 
| '(' { LPAREN }
| ')' { RPAREN }
| ':' { COLON }
| "->" { ARROW }
| ',' { COMMA }
| "let" { LET }
| "rec" { REC }
| "in" { IN }
| "if" { IF }
| "then" { THEN }
| "else" { ELSE }
| "fun" { FUN }
| "true" { TRUE }
| "false" { FALSE }
| "()" { UNIT }
| "assert" { ASSERT }
| '+' { PLUS }
| '-' { MINUS }
| '*' { STAR }
| '/' { SLASH }
| "mod" { MOD }
| '<' { LT }
| "<=" { LTE }
| '>' { GT }
| ">=" { GTE }
| '=' { EQ }
| "<>" { NEQ }
| "&&" { AND }
| "||" { OR }
| num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
| var { VAR (Lexing.lexeme lexbuf) }
| eof { EOF }
| _ { failwith ("Unexpected character: " ^ Lexing.lexeme lexbuf) }
