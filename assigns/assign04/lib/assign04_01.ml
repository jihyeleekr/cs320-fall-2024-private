let large_value = max_int

let rec lifespan (f : 'a -> 'a) (s : 'a) (p : ('a -> bool)) (k : int) : int option =
  if k > 1000000 then Some large_value  
  else if p (f s) then Some k
  else lifespan f (f s) p (k + 1)

let rec infinite_lifespan_check funcs start pred =
  match funcs with
  | [] -> 0  
  | f :: rest ->
    match lifespan f start pred 0 with
    | Some l when l = large_value -> 1 + infinite_lifespan_check rest start pred  
    | _ -> infinite_lifespan_check rest start pred  

let last_function_standing funcs start pred =
  match funcs with
  | [] -> None  
  | [f] -> Some f  
  | _ ->
    let rec max_lifespan_finder funcs max_f max_lifespan =
      match funcs with
      | [] -> max_f  
      | f :: rest ->
        match lifespan f start pred 0 with
        | None -> max_lifespan_finder rest max_f max_lifespan  
        | Some l ->
          if l = large_value then
            let infinite_count = infinite_lifespan_check rest start pred in
            if infinite_count > 0 then None  
            else max_lifespan_finder rest (Some f) max_lifespan 
          else if l > max_lifespan then
            max_lifespan_finder rest (Some f) l
          else if l = max_lifespan then
            None  
          else
            max_lifespan_finder rest max_f max_lifespan  
    in
    max_lifespan_finder funcs None 0