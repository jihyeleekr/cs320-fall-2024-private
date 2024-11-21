
let sum_of_squares (x : int) (y : int) : int =
  let x_squared : int = x * x in
  let y_squared : int = y * y in
  x_squared + y_squared
let _ : unit = assert (sum_of_squares 3 (-5) = 34)
