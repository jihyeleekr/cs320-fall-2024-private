open Utils
<<<<<<< HEAD
let parse = My_parser.parse
=======
>>>>>>> upstream/main

let parse = My_parser.parse

let desugar =
  let rec go = function
  | [] -> Fun("x", Var "x")
  | [_, e] -> e
  | (x, e) :: ls -> Let (x, e, go ls)
  in go

<<<<<<< HEAD
e1 \|/ fun x -> e      e2 \|/ v2      [v2 / x] e \|/ v
------------------------------------------------------
              e1 e2 \|/ v
*)

let rec eval e = 
   match e with
   | Var _ -> None
   | Fun (x, e) -> Some (VFun (x, e))
   | App (e1, e2) -> (
	match eval e1 with
	| VFun (x, e) -> (
		match eval e2 with
		| Some v2 -> eval (substs v2 x e)
		| _ -> None
	)
	| _ -> None
)

(* 
 
[v / x] y = if x = y then v else x
=======
let expr_of_val (VFun (x, e)) = Fun (x, e)

let replace_var x y =
  let rec go = function
    | Var z -> if z = y then Var x else Var z
    | App (e1, e2) -> App (go e1, go e2)
    | Fun (z, e) -> if z = y then Fun (z, e) else Fun (z, go e)
    | Let (z, e1, e2) -> if z = y then Let (z, go e1, e2) else Let(z, go e1, go e2)
  in go
>>>>>>> upstream/main

let subst v x =
  let rec go = function
    | Var y -> if x = y then expr_of_val v else Var y
    | App (e1, e2) -> App (go e1, go e2)
    | Fun (y, e) ->
      if x = y
      then Fun (y, e)
      else
        let z = gensym () in
        Fun (z, go (replace_var z y e))
    | Let (y, e1, e2) ->
      if x = y
      then Let (y, go e1, e2)
      else
        let z = gensym () in
        Let (z, go e1, go (replace_var z y e2))
  in go

<<<<<<< HEAD
[v / x] (fun y -> e) =
  if x = y then
    fun y -> x
  else
    fun z -> [v / x] ([x / y] e)

*)
let expr_of_val v = 
 match v with
 | VFun (x, e) -> Fun(x, e)

let rec replace_var x y e = 
 match e with
 | Var z -> if z = y then Var x else Var z
 | App (e1, e2) -> App (replace_var x y e1, replace_var x y e2)
 | Fun (z, e) -> Fun (z, replace x y e)

let rec subst v x e =
	match e with 
	| Var y -> if x = y then expr_of_val v else Var x
	| App (e1, e2) -> App (subst v x e1, subst v x e2)
	| Fun (y, e) -> if x = y then VFun (y, e) else 
        		let z = gensym() in 
  			VFun (Z, subst v x (replace_var z y e))
let _ = ignore (Var "x")
=======
let ( let* ) = Option.bind

let string_of_expr =
  let rec go = function
  | Var x -> x
  | App (e1, e2) -> "(" ^ go e1 ^ " " ^ go e2 ^ ")"
  | Fun (x, e) -> "(fun " ^ x ^ " -> " ^ go e ^ ")"
  | Let (x, e1, e2) -> "(let " ^ x ^ " = " ^ go e1 ^ " in " ^ go e2 ^ ")"
 in go

let eval =
  let rec go = function
    | Var _ -> None
    | Fun (x, e) -> Some (VFun (x, e))
    | App (e1, e2) ->
      let* (VFun (x, e)) = go e1 in
      let* v2 = go e2 in
      go (subst v2 x e)
    | Let (x, e1, e2) ->
      let* v = go e1 in
      go (subst v x e2)
  in go

let interp str =
  let* prog = parse str in
  let expr = desugar prog in
  eval expr

let interp' str =
  match interp str with
  | Some v -> string_of_expr (expr_of_val v)
  | None -> "ERROR"
>>>>>>> upstream/main
