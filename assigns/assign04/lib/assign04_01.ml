
let calculate_lifespan f s p =
  let rec aux current_s count =
    if p current_s then count  
    else aux (f current_s) (count + 1)  
  in
  aux s 0  

let last_function_standing funcs start pred =
  let rec find_max_lifespan funcs current_max_f current_max_lifespan tied_count =
    match funcs with
    | [] -> 
      if tied_count > 1 then None  
      else current_max_f  
    | f :: rest ->
      let lifespan = calculate_lifespan f start pred in  
      if lifespan > current_max_lifespan then
        find_max_lifespan rest (Some f) lifespan 1
      else if lifespan = current_max_lifespan then
        find_max_lifespan rest current_max_f current_max_lifespan (tied_count + 1)
      else
        find_max_lifespan rest current_max_f current_max_lifespan tied_count
  in
  find_max_lifespan funcs None (-1) 0  


