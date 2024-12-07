(* sum of squares function *)
(* let sum_of_squares x y = 
  let x_squared = x * x in
  let y_squared = y * y in
  x_squared + y_squared
  let _ = assert ( sum_of_squares 3 ( -5) = 34)  *)

(* let x: int = 3 *)
(* let test : unit = assert (b) *)
(* let _ =
  let u : unit = () in
  assert (u = ())  *)

  let _ =
    let l = [] in
    let l = [1;2;3] in
    let l : bool list = true :: false :: true :: [] in
    assert (l = true :: false :: true :: [])