open Assign01_03
let to_string (s : int) : string =
  let rec generate_sequence (s : int) (i : int) (seq : int list) : int list = (* Return the number sequences in list form: contains int*)
    let count = nth s i in 
    if count = 0 then List.rev seq (* Reverse the list *)
    else generate_sequence s (i + 1) (count :: seq)
  in 
  let seq_list = generate_sequence s 0 [] in
  
  let list_to_string (lst : int list) : string = 
    let rec aux lst = (* Take the list elements and convert it into string *)
      match lst with
      | [] -> ""
      | [x] -> string_of_int x (* Convert the int element to String *)
      | x :: xs -> string_of_int x ^ "; " ^ aux xs
    in
    "[" ^ aux lst ^ "]" (* Add list brackets *)
  in
  if s < 0 then failwith "Invalid input for n"
  else list_to_string seq_list
