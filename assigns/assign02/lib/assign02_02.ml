type matrix = {
entries : float list list;
rows : int;
cols : int;
}

let mk_matrix (entry : float list) ((r, c) : int * int) : matrix = 
  let rec dividor n lst =
    match lst with
    | [] -> []
    | _ ->
        let row = List.take n lst in
        row :: dividor n (List.drop n lst)
    in
    { entries = dividor c entry; rows = r; cols = c }
