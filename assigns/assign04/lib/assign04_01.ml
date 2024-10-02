
let last_function_standing funcs start pred =
  let rec eliminate funcs longest_f longest_survivor step_count =
    match funcs with
    | [] ->
      if step_count = 1 then longest_f  
      else None  
    | f :: rest ->
      let rec step_function f current_state steps =
        if pred current_state then steps  
        else step_function f (f current_state) (steps + 1)
      in
      let steps = step_function f start 0 in
      if steps > longest_survivor then
        eliminate rest (Some f) steps 1
      else if steps = longest_survivor then
        eliminate rest longest_f longest_survivor (step_count + 1)
      else
        eliminate rest longest_f longest_survivor step_count
  in
  eliminate funcs None (-1) 0  






