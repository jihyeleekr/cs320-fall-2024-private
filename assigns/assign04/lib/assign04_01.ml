
let last_function_standing funcs start pred =
  let rec compare_funcs funcs max_f current_s max_count =
    match funcs with
    | [] -> 
      if max_count > 1 then None
      else max_f
    | f :: rest ->
      let rec step f current_s step_count =
        if pred current_s then step_count
        else step f (f current_s) (step_count + 1)
      in
      let f_steps = step f start 0 in
      match max_f with
      | None -> 
        compare_funcs rest (Some f) start 1
      | Some max_f' ->
        let max_steps = step max_f' start 0 in
        if f_steps > max_steps then
          compare_funcs rest (Some f) start 1
        else if f_steps = max_steps then
          compare_funcs rest max_f current_s (max_count + 1)
        else
          compare_funcs rest max_f current_s max_count
  in
  compare_funcs funcs None start 0
