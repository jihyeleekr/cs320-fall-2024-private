type tree = 
  | Leaf of int
  | Node of tree list

(* Helper function to concatenate a list of lists *)
let rec concat_lists lsts =
  match lsts with
  | [] -> []
  | l :: ls -> l @ concat_lists ls

(* Helper function to compute the height of the tree *)
let rec height t =
  match t with
  | Leaf _ -> 0
  | Node cs ->
    let rec max_depth cs =
      match cs with
      | [] -> -1
      | c :: cs -> max (height c) (max_depth cs)
    in 1 + max_depth cs

(* Helper function to collect all terminal elements from a tree *)
let rec terminal_elements t =
  match t with
  | Leaf _ -> [t]
  | Node [] -> [t]
  | Node children -> concat_lists (List.map terminal_elements children)

(* Main collapse function *)
let rec collapse h t =
  if h = 0 then t
  else match t with
  | Leaf _ -> t
  | Node children ->
    if h = 1 then
      (* Collapse the children to terminal elements *)
      Node (concat_lists (List.map terminal_elements children))
    else
      (* Recursively collapse each child node *)
      Node (List.map (collapse (h - 1)) children)

