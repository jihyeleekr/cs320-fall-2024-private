let mk_unique_keys (alst : (string * int) list) : (string * int) list = 
  let rec lookup k sum = function
| [] -> [(k, sum)]
| (k',v) :: t -> if k = k' then lookup k (sum + v) t else lookup k sum t
in 

let rec update_alst alst acc = 
  match alst with
  | [] -> acc
  | (k, _) :: t ->let add_sum = lookup k 0 alst in
 let new_alst = List.filter (fun (k', _) -> k <> k') t in update_alst new_alst (add_sum @ acc)
in 
update_alst alst []
