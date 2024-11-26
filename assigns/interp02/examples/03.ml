
let apply_twice (f : int -> int) (x : int) : int =
  f (f x)

let increment (x : int) : int = x + 1
let test : unit = assert (apply_twice increment 5 = 7)
