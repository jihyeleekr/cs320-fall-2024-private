let last_function_standing funcs start pred =
  let rec step funcs states =
    match funcs with
    | [] -> None
    | [f] -> Some f
    | _ ->
      let rec process_funcs funcs states survivors new_states =
        match funcs, states with
        | [], [] -> (survivors, new_states)
        | f :: fs_rest, state :: st_rest ->
          let new_state = f state in
          if pred new_state then
            process_funcs fs_rest st_rest survivors new_states
          else
            process_funcs fs_rest st_rest (f :: survivors) (new_state :: new_states)
        | _ -> (survivors, new_states)
      in
      let (survivors, new_states) = process_funcs funcs states [] [] in
      match survivors with
      | [] -> None
      | [f] -> Some f
      | _ ->
        let rec reverse lst acc =
          match lst with
          | [] -> acc
          | h :: t -> reverse t (h :: acc)
        in
        step (reverse survivors []) (reverse new_states [])
  in
  let rec initialize_states funcs start acc =
    match funcs with
    | [] -> acc
    | _ :: rest -> initialize_states rest start (start :: acc)
  in
  step funcs (initialize_states funcs start [])