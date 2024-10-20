
open Utils

type value = 
| VNum of int
| VBool of bool
let rec eval expr =
  match expr with
  | Num n -> VNum n
  | Add (e1, e2) ->
    (match eval e1, eval e2 with
     | VNum n1, VNum n2 -> VNum (n1 + n2)
     | _ -> failwith "Undefined behavior")
  | Lt (e1, e2) ->
    (match eval e1, eval e2 with
     | VNum n1, VNum n2 -> VBool (n1 < n2)
     | _ -> failwith "Undefined behavior")
  | Ite (e1, e2, e3) ->
    (match eval e1 with
     | VBool true -> eval e2
     | VBool false -> eval e3
     | _ -> failwith "Undefined behavior")
