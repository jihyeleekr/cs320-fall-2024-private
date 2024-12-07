(* list filtering *)
let filter f =
  let rec go l =
    match l with
    | x :: l ->
      if f x
      then x :: go l
      else go l
    | [] -> []
  in go

let _ = assert (filter (fun x -> x > 0) [-1;2;0;34;2] = [2;34;2])