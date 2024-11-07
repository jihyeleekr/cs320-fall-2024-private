open Utils
let parse = My_parser.parse

(*

--------------------------
fun x -> e \|/ fun x -> e

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

[v / x] (e1 e2) = ([v / x] e1) ([v / x] e2)

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
