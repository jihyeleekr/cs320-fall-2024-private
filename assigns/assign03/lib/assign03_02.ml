let gen_fib (l : int list) (k : int) : int = 
  match l with
  |[] -> 0
  | _::_ -> k
