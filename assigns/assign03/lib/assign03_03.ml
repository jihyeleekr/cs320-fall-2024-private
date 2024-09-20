type tree = 
| Leaf of int
| Node of tree list

let collapse (h : int) (t : tree) : tree = 
  match t with
  | Leaf value -> Leaf (value + h)  (* Increase the leaf value by h *)
  | Node _ -> Node []
