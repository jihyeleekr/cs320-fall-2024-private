
type expr = 
| True
| False
| Num of int
| Or of expr * expr
| Add of expr * expr
| IfThenElse of expr * expr * expr

type ty = 
| Int
| Bool

let rec type_of (e : expr) : ty option = 
  match e with
  | True -> Some Bool
  | False -> Some Bool
  | Num _ ->  Some Int
  | Or (a, b) ->
    (match type_of a, type_of b with
    | Some Bool, Some Bool -> Some Bool
    | _ -> None)
  | Add (a, b) -> 
    (match type_of a, type_of b with
    | Some Int, Some Int -> Some Int
    | _ -> None)
  | IfThenElse (a, b, c) -> 
    (match type_of a, type_of b, type_of c with
    | Some Bool, Some t1, Some t2 when t1 = t2 -> Some t1
    | _ -> None)