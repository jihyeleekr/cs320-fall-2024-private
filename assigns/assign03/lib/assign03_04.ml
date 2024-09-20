let group (l : int list) : int list list option = 
  match l with 
  | [] -> Some [[]] 
  | _::_ -> Some [l]