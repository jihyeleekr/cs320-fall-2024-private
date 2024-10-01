let large_value = max_int

let calculate_lifespan f s p =
  let rec aux current_s count =
    if p current_s then count  
    else if count > 1000000 then large_value
    else aux (f current_s) (count + 1)  
  in
  aux s 0

let last_function_standing funcs start pred =
  let rec max_lifespan_finder funcs max_f max_lifespan max_count =
    match funcs with
    | [] -> 
      if max_count > 1 then None  
      else max_f  
    | f :: rest ->
      let l = calculate_lifespan f start pred in
      if l = large_value then
        max_lifespan_finder rest (Some f) max_lifespan max_count  
      else if l > max_lifespan then
        max_lifespan_finder rest (Some f) l 1  
      else if l = max_lifespan then
        max_lifespan_finder rest max_f max_lifespan (max_count + 1)  
      else
        max_lifespan_finder rest max_f max_lifespan max_count  
  in
  max_lifespan_finder funcs None 0 0
