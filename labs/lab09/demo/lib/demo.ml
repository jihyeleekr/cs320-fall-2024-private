open Utils
include My_parser

let rec interp (e : expr) : expr option = 
  match e with
  | Num n  -> Some (Num n)
  | True -> Some (True)
  | False -> Some (False)
  | Add (Num n, Num m) -> Some (Num (n + m))
  | Add (e1, e2) -> 
let doParse x = parse x
