

let rec lifespan (f : 'a -> 'a) (s : 'a) (p: ('a -> bool)) (k : int) : int= 
  if p(f s) then k
  else lifespan f (f s) p k + 1

let last_function_standing (f : ('a -> 'a) list)  (s : 'a) (p : ('a -> bool)) : ('a -> 'a) option =
  let rec max_lifespan_finder fs max_f max_lifespan =
    match fs with
    | [] -> max_f  
    | f :: rest ->
      let l = lifespan f s p 0 in
      if l > max_lifespan then max_lifespan_finder rest (Some f) l
      else if l = max_lifespan then None  
      else max_lifespan_finder rest max_f max_lifespan
  in
  max_lifespan_finder f None (-1)