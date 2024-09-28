
let large_value = max_int
let rec lifespan (f : 'a -> 'a) (s : 'a) (p: ('a -> bool)) (k : int) : int = 
  if p(f s) then k
  else lifespan f (f s) p k + 1

  let calculate_lifespan f s p =
    let rec aux current_s count =
      if p current_s then count  
      else if count > 1000000 then large_value
      else aux (f current_s) (count + 1)  
    in
    aux s 0
  
  let last_function_standing fs s p =
    let rec max_lifespan_finder fs max_f max_lifespan =
      match fs with
      | [] -> max_f  
      | f :: rest ->
        let l = calculate_lifespan f s p in
        if l = large_value then Some f  
        else if l > max_lifespan then max_lifespan_finder rest (Some f) l  
        else if l = max_lifespan then None  
        else max_lifespan_finder rest max_f max_lifespan  
    in
    max_lifespan_finder fs None 0