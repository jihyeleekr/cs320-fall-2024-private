open Assign01_02

let nth (s: int) (i : int) : int =
  let x = nth_prime i in
  let rec is_div (s : int) (x : int) (c : int) : int = 
    if s mod x <> 0 then c
    else is_div (s / x)  x (c + 1)
  in
  if s < 0 then failwith "Invalid input for s"
  else is_div s x 0
