type tree = 
  | Leaf of int
  | Node of tree list

let rec collapse h t =
  let rec collapse_children h children =
    match children with
    | [] -> []
    | c :: rest ->
      let collapsed_child =
        match c with
        | Leaf _ -> c
        | Node [] -> if h <= 0 then Node [] else c
        | _ -> collapse (h - 1) c
      in collapsed_child :: collapse_children h rest
  in
  match t with
  | Leaf _ -> t
  | Node [] -> if h <= 0 then Node [] else t
  | Node children ->
    if h <= 1 then
      let rec terminal_children children =
        match children with
        | [] -> []
        | Leaf _ as l :: rest -> l :: terminal_children rest
        | Node [] as n :: rest -> n :: terminal_children rest
        | Node subchildren :: rest ->
          terminal_children subchildren @ terminal_children rest
      in Node (terminal_children children)
    else
      Node (collapse_children h children)

