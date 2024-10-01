let large_value = max_int

let rec lifespan (f : 'a -> 'a) (s : 'a) (p: ('a -> bool)) (k : int) : int option =
  if k > 1000000 then Some large_value  
  else if p (f s) then Some k
  else lifespan f (f s) p (k + 1)

let calculate_lifespan f s p =
  let rec aux current_s count =
    if p current_s then Some count  
    else if count > 1000000 then Some large_value
    else aux (f current_s) (count + 1)  
  in
  aux s 0

let last_function_standing funcs start pred =
  let rec max_lifespan_finder funcs max_f max_lifespan =
    match funcs with
    | [] -> max_f  
    | f :: rest ->
      match calculate_lifespan f start pred with
      | None -> max_lifespan_finder rest max_f max_lifespan  (* Skip failed lifespans *)
      | Some l ->
        if l = large_value then
          (* Count the number of functions with infinite lifespan *)
          let rec count_infinite rest =
            match rest with
            | [] -> 0
            | f' :: rest' ->
              match calculate_lifespan f' start pred with
              | Some l' when l' = large_value -> 1 + count_infinite rest'
              | _ -> count_infinite rest'
          in
          let count = count_infinite rest in
          if count > 0 then None  (* Multiple infinite lifespan functions found *)
          else max_lifespan_finder rest (Some f) max_lifespan  (* Continue checking *)
        else if l > max_lifespan then
          max_lifespan_finder rest (Some f) l
        else if l = max_lifespan then
          None  (* Found a tie *)
        else
          max_lifespan_finder rest max_f max_lifespan  
  in
  max_lifespan_finder funcs None 0
