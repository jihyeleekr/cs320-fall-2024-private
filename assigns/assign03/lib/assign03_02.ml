let gen_fib (l : int list) (n : int) : int =
  let k = List.length l in
  if k = 0 || n < 0 then failwith "Invalid Inputs.";
  let rec accum (lst : int list) (k : int) : int = 
    match lst, k with
    | [], _ -> 0
    | _, 0 -> 0
    | h::t, k -> h + (accum t (k - 1))
  in

  let rec fib (lst : int list) (i : int) : int = 
    match lst with
    | [] -> failwith "Invalid input for l"
    | h::_ when i = n -> h
    | _ ->
      let next_val = accum lst k in
      fib (next_val::lst) (i + 1)
    in
    fib (List.rev l) k                            