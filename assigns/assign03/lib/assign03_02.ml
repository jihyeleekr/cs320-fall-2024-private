
let gen_fib (l : int list) (n : int) : int =
  let k = List.length l in

  let rec sum (lst : int list) (k : int) (acc : int) : int =
    match lst, k with
    | [], _ -> acc
    | _, 0 -> acc
    | h :: t, k -> sum t (k - 1) (acc + h)
  in

  let rec fib (lst : int list) (idx : int) : int =
    match idx with
    | _ when idx < n -> 
      let next_val = sum lst k 0 in
      fib (next_val :: lst) (idx + 1)
    | _ ->  List.nth (List.rev lst) n
  in

  fib (List.rev l) (k - 1)


