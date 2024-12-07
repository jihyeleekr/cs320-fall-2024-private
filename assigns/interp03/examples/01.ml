let abs n = if n < 0 then 0 - n else n
let abs_float n = if n < 0. then 0. -. n else n

(* Newton's method a la SICP *)
let newtons_method g =
  let tolerance = 0.00001 in
  let close_enough v1 v2 = abs_float (v1 -. v2) < tolerance in
  let fixed_point f =
    let rec go guess =
      let next = f guess in
      if close_enough guess next
      then next
      else go next
    in go
  in
  let dx = 0.00001 in
  let deriv g x = (g (x +. dx) -. g x) /. dx in
  let newton_transform g x = x -. (g x /. deriv g x) in
  fixed_point (newton_transform g)

let sqrt n = newtons_method (fun y -> y *. y -. n) 1.

let _ = assert (abs_float (sqrt 4. -. 2.) < 0.0001)
let _ = assert (abs_float (sqrt 2. -. 1.414213) < 0.0001)
