open Utils

let parse = My_parser.parse

let value_to_expr = function
  | VNum n -> Num n
  | VBool b -> if b then True else False
  | VUnit -> Unit
  | VFun (arg, body) -> Fun (arg, body)

let rec subst (v : value) (x : string) (e : expr) : expr =
  match e with
  | Num _ | True | False | Unit -> e
  | Var y -> if y = x then value_to_expr v else e
  | If (cond, e1, e2) -> If (subst v x cond, subst v x e1, subst v x e2)
  | Let (y, e1, e2) ->
      if y = x then Let (y, subst v x e1, e2) 
      else Let (y, subst v x e1, subst v x e2)
  | Fun (y, body) ->
      if y = x then e 
      else Fun (y, subst v x body)
  | App (e1, e2) -> App (subst v x e1, subst v x e2)
  | Bop (op, e1, e2) -> Bop (op, subst v x e1, subst v x e2)

let eval_bop op v1 v2 =
  match op, v1, v2 with
  | Add, VNum n1, VNum n2 -> Ok (VNum (n1 + n2))
  | Sub, VNum n1, VNum n2 -> Ok (VNum (n1 - n2))
  | Mul, VNum n1, VNum n2 -> Ok (VNum (n1 * n2))
  | Div, VNum n1, VNum n2 -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 / n2))
  | Mod, VNum n1, VNum n2 -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 mod n2))
  | Lt, VNum n1, VNum n2 -> Ok (VBool (n1 < n2))
  | Lte, VNum n1, VNum n2 -> Ok (VBool (n1 <= n2))
  | Gt, VNum n1, VNum n2 -> Ok (VBool (n1 > n2))
  | Gte, VNum n1, VNum n2 -> Ok (VBool (n1 >= n2))
  | Eq, VNum n1, VNum n2 -> Ok (VBool (n1 = n2))
  | Neq, VNum n1, VNum n2 -> Ok (VBool (n1 <> n2))
  | And, VBool b1, VBool b2 -> Ok (VBool (b1 && b2))
  | Or, VBool b1, VBool b2 -> Ok (VBool (b1 || b2))
  | _ -> Error (InvalidArgs op)

let rec eval (e : expr) : (value, error) result =
  match e with
  | Num n -> Ok (VNum n)
  | True -> Ok (VBool true)
  | False -> Ok (VBool false)
  | Unit -> Ok VUnit
  | Var x -> Error (UnknownVar x)
  | Bop (And, e1, e2) -> (
      match eval e1 with
      | Ok (VBool false) -> Ok (VBool false)  
      | Ok (VBool true) -> eval e2
      | _ -> Error InvalidIfCond)
  | Bop (Or, e1, e2) -> (
      match eval e1 with
      | Ok (VBool true) -> Ok (VBool true)  
      | Ok (VBool false) -> eval e2
      | _ -> Error InvalidIfCond)
  | If (cond, e1, e2) -> (
      match eval cond with
      | Ok (VBool true) -> eval e1
      | Ok (VBool false) -> eval e2
      | _ -> Error InvalidIfCond)
  | Let (x, e1, e2) -> (
      match eval e1 with
      | Ok v -> eval (subst v x e2)
      | Error err -> Error err)
  | Fun (arg, body) -> Ok (VFun (arg, body))
  | App (e1, e2) -> (
      match eval e1 with
      | Ok (VFun (arg, body)) -> (
          match eval e2 with
          | Ok v -> eval (subst v arg body)
          | Error err -> Error err)
      | Ok _ -> Error InvalidApp
      | Error err -> Error err)
  | Bop (op, e1, e2) -> (
      match eval e1 with
      | Ok v1 -> (
          match eval e2 with
          | Ok v2 -> eval_bop op v1 v2
          | Error err -> Error err)
      | Error err -> Error err)

let interp (input : string) : (value, error) result =
  match parse input with
  | Some prog -> eval prog
  | None -> Error ParseFail
