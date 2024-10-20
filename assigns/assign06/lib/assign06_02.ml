
open Utils

let parse toks =
  let rec aux toks stack =
    match toks with
    | [] -> 
      (match stack with
       | [e] -> Some e
       | _ -> None)
    | TNum n :: rest -> aux rest (Num n :: stack)
    | TAdd :: rest ->
      (match stack with
       | e2 :: e1 :: stack_tail -> aux rest (Add (e1, e2) :: stack_tail)
       | _ -> None)
    | TLt :: rest ->
      (match stack with
       | e2 :: e1 :: stack_tail -> aux rest (Lt (e1, e2) :: stack_tail)
       | _ -> None)
    | TIte :: rest ->
      (match stack with
       | e3 :: e2 :: e1 :: stack_tail -> aux rest (Ite (e1, e2, e3) :: stack_tail)
       | _ -> None)
  in
  aux toks []
