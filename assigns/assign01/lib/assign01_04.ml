open Assign01_03
let to_string (n : int) : string =
  let s = [] @ [string_of_int (nth n 2)] in
  let list_to_string lst = 
    let rec aux lst = 
      match lst with 
      | [] -> ""
      | [x] -> x
      | x :: xs -> x ^";" ^ aux xs
    in
    "[" ^ aux lst ^ "]"
  in
  if n < 0 then failwith "Invalid input for n"
  else list_to_string s