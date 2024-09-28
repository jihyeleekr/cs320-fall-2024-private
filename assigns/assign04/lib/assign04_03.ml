open Assign04_02
type value = 
| VNum of int
| VBool of bool

let rec eval (e : expr) : value = 
  match e with
  | True -> VBool true
  | False -> VBool false
  | Num a -> VNum a
  | Or (a, b) -> (
    match eval a, eval b with
    | VBool false, VBool false -> VBool false
    | _ -> VBool true
  )
  | Add (a, b) -> (
    match eval a, eval b with
    | VNum a, VNum b -> VNum(a + b)
    | _ -> VNum 0
  )
  | IfThenElse (a, b, c) -> (
    match eval a, eval b, eval c with
    | cond, v_then, _ when cond = VBool true -> v_then
    | cond, _, v_else when cond = VBool false -> v_else
    | _ -> VNum 0
  )
  