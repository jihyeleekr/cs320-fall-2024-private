
type set_info = {
ind : int -> bool;
mn : int;
mx : int;
}

module ListSet = struct
  type t = int list
  let rec mem x s =
    match s with
    | [] -> false
    | h :: t -> if h = x then true else mem x t
  let empty = []
  let singleton x = [x]
  let card s = List.length s
  let rec union s1 s2 =
    match s1, s2 with
    | [], s | s, [] -> s
    | h1 :: t1, h2 :: t2 ->
      if h1 = h2 then h1 :: union t1 t2
      else if h1 < h2 then h1 :: union t1 s2
      else h2 :: union s1 t2
end

module FuncSet = struct
  type t = set_info
  let mem x s = s.ind x
  let empty = 
    { ind = (fun _ -> false)
    ; mn = 1
    ; mx = 0 
    }
  let singleton x =
    { ind = (fun y -> y = x)
    ; mn = x
    ; mx = x
    }
  let card s =
    let rec count acc x =
      if x > s.mx then acc
      else if s.ind x then count (acc + 1) (x + 1)
      else count acc (x + 1)
    in count 0 s.mn
  let union s1 s2 =
    let new_ind x = s1.ind x || s2.ind x in
    let new_mn = min s1.mn s2.mn in
    let new_mx = max s1.mx s2.mx in
    { ind = new_ind
    ; mn = new_mn
    ; mx = new_mx
    }
end


