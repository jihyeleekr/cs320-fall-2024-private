
type ident = string

type expr' = 
| True
| False
| Num of int
| Var of ident
| Let of ident * expr' * expr'
| Add of expr' * expr'
| Or of expr' * expr'
| IfThenElse of expr' * expr' * expr'

type ty' = 
| Int
| Bool

type context = (ident * ty') list

let rec type_of' (ctxt : context) (exp : expr') : ty' option =
  match exp with
  | True -> Some Bool
  | False -> Some Bool
  | Num _ -> Some Int
  | Var v -> (
    match ctxt with 
    | []  -> None
    | (id, ty)::rest -> if id = v then Some ty
    else type_of' rest exp
  )
  | Let (id, e1, e2) ->  
    (match type_of' ctxt e1 with
  | Some ty1 ->  
      let new_ctxt = (id, ty1) :: ctxt in
      (match type_of' new_ctxt e2 with
      | Some ty2 -> Some ty2  
      | _ -> None  
      )
  | _ -> None  
)
  | Add (a, b) -> (
    match type_of' ctxt a, type_of' ctxt b with
    | Some Int, Some Int -> Some Int
    | _ -> None
  )
  | Or (a, b) -> (
    match type_of' ctxt a, type_of' ctxt b with
    | Some Bool, Some Bool -> Some Bool
    | _ -> None
  )

  | IfThenElse (con, e1, e2) -> (
    match type_of' ctxt con, type_of' ctxt e1, type_of' ctxt e2 with
    | Some Bool, Some t1, Some t2 when t1 = t2 -> Some t1
    | _ -> None)
