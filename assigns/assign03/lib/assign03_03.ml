type tree = 
  | Leaf of int
  | Node of tree list
let rec connect lsts =
  match lsts with
  | [] -> []
  | l :: ls -> l @ connect ls
let rec height t =
  match t with
  | Leaf _ -> 0
  | Node cs ->
    let rec max_depth cs =
      match cs with
      | [] -> -1
      | c :: cs -> max (height c) (max_depth cs)
    in 1 + max_depth cs

let rec terminal_elements t =
  match t with
  | Leaf _ -> [t]
  | Node [] -> [t]
  | Node children -> connect (List.map terminal_elements children)

let rec collapse h t =
  if h = 0 then t
  else match t with
  | Leaf _ -> t
  | Node children ->
    if h = 1 then
      Node (connect (List.map terminal_elements children))
    else
      (* Recursively collapse each child node *)
      Node (List.map (collapse (h - 1)) children)