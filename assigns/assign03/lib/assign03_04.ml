let group l =
  let rec group_maker acc sign current_group = function
    | [] -> 
        if current_group = [] then Some (List.rev acc)
        else Some (List.rev (List.rev current_group :: acc))
    
    | 0 :: xs -> 
        if current_group = [] then None
        else 
          let next_sign = (match xs with | y :: _ -> if y > 0 then 1 else if y < 0 then -1 else 0 | [] -> 0) in
          if sign <> 0 && next_sign <> 0 && sign <> next_sign then
            group_maker (List.rev current_group :: acc) 0 [] xs
          else None
    
    | x :: xs when x > 0 ->
        if sign = 0 || sign = 1 then 
          group_maker acc 1 (x :: current_group) xs
        else None 

    | x :: xs when x < 0 ->
        if sign = 0 || sign = -1 then 
          group_maker acc (-1) (x :: current_group) xs
        else None 

    | _ -> None
  in
  group_maker [] 0 [] l