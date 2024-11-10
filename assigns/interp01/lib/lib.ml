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

let rec eval (e : expr) : (value, error) result =
  match e with
  | Num n -> Ok (VNum n)
  | True -> Ok (VBool true)
  | False -> Ok (VBool false)
  | Unit -> Ok VUnit
  | Var x -> Error (UnknownVar x)
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
  | Bop (op, e1, e2) -> eval_bop op e1 e2

and eval_bop op e1 e2 =
  match op with
  | And -> (
      match eval e1 with
      | Ok (VBool false) -> Ok (VBool false)
      | Ok (VBool true) -> eval e2
      | _ -> Error (InvalidArgs And))
  | Or -> (
      match eval e1 with
      | Ok (VBool true) -> Ok (VBool true)
      | Ok (VBool false) -> eval e2
      | _ -> Error (InvalidArgs Or))
  | _ -> 
      match eval e1, eval e2 with
      | Error err, _ -> Error err
      | _, Error err -> Error err
      | Ok (VNum v1), Ok (VNum v2) -> (match op with
          | Add -> Ok (VNum (v1 + v2))
          | Sub -> Ok (VNum (v1 - v2))
          | Mul -> Ok (VNum (v1 * v2))
          | Div -> if v2 = 0 then Error DivByZero else Ok (VNum (v1 / v2))
          | Mod -> if v2 = 0 then Error DivByZero else Ok (VNum (v1 mod v2))
          | Lt -> Ok (VBool (v1 < v2))
          | Lte -> Ok (VBool (v1 <= v2))
          | Gt -> Ok (VBool (v1 > v2))
          | Gte -> Ok (VBool (v1 >= v2))
          | _ -> Error (InvalidArgs op))
      | _ -> Error (InvalidArgs op)

let interp (input : string) : (value, error) result =
  match parse input with
  | Some prog -> eval prog
  | None -> Error ParseFail
