let group l =
  let rec validate_and_group acc current_sign current_group = function
    | [] -> 
        (* End of the list, return the accumulated groups *)
        if current_group = [] then Some (List.rev acc)
        else Some (List.rev (List.rev current_group :: acc))
    
    | 0 :: xs -> 
        (* Check if the current group is empty (invalid) or has the same sign *)
        if current_group = [] then None
        else 
          let next_sign = (match xs with | y :: _ -> if y > 0 then 1 else if y < 0 then -1 else 0 | [] -> 0) in
          (* A 0 is valid only if it's surrounded by opposite sign elements *)
          if current_sign <> 0 && next_sign <> 0 && current_sign <> next_sign then
            validate_and_group (List.rev current_group :: acc) 0 [] xs
          else None
    
    | x :: xs when x > 0 ->
        (* Continue grouping positive numbers *)
        if current_sign = 0 || current_sign = 1 then 
          validate_and_group acc 1 (x :: current_group) xs
        else None (* Invalid if switching from negative directly to positive without a 0 *)

    | x :: xs when x < 0 ->
        (* Continue grouping negative numbers *)
        if current_sign = 0 || current_sign = -1 then 
          validate_and_group acc (-1) (x :: current_group) xs
        else None (* Invalid if switching from positive directly to negative without a 0 *)

    | _ -> None
  in
  validate_and_group [] 0 [] l
