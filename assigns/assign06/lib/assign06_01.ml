
open Utils
let lex (s: string) : tok list option = 
  let words = split s in
  let rec aux words =
    match words with
    | [] -> Some []
    | word :: rest ->
      (match tok_of_string_opt word with
       | None -> None
       | Some token ->
         (match aux rest with
          | None -> None
          | Some tokens -> Some (token :: tokens)))
  in
  aux words