type piece = 
| X
| O

type pos = 
| Piece of piece
| Blank

type board = (pos * pos * pos) * (pos * pos * pos) * (pos * pos * pos)

type row_index = 
| Top
| Middle
| Bottom

type col_index = 
| Left
| Middle 
| Right

type pos_index = row_index * col_index

let get_pos (b : board) (p : pos_index) : pos = 
  let (row_index, col_index) = p in
  let row = match row_index with
  | Top -> let(r,_,_) = b in r
  | Middle -> let(_,r,_) = b in r
  | Bottom -> let(_,_,r) = b in r

in 
match col_index with
| Left -> let (c, _, _) = row in c
| Middle -> let (_, c, _) = row in c
| Right -> let (_, _, c) = row in c

let winner (b : board) : bool = 
  let check_winner = function (* https://ocaml.org/manual/5.2/patterns.html *)
    | (Piece X, Piece X, Piece X) -> true
    | (Piece O, Piece O, Piece O) -> true
    | _ -> false
  in
  let (r1, r2, r3) = b in
  (* Row match*)
  let row_match = check_winner r1 || check_winner r2 || check_winner r3 in

  (* Colmun match *)
  let col_match = 
    let c1 = (get_pos b (Top, Left), get_pos b (Middle,Left), get_pos b (Bottom, Left)) in
    let c2 = (get_pos b (Top, Middle), get_pos b (Middle,Middle), get_pos b (Bottom, Middle)) in
    let c3 = (get_pos b (Top, Right), get_pos b (Middle,Right), get_pos b (Bottom, Right)) in

    check_winner c1 ||  check_winner c2 ||  check_winner c3
  in

  (* Diagonal match *)

  let diag_match = 
    let left_diag = (get_pos b (Top, Left), get_pos b (Middle, Middle), get_pos b (Bottom, Right)) in
    let rigth_diag = (get_pos b (Top, Right), get_pos b (Middle, Middle), get_pos b (Bottom, Left)) in
    
    check_winner left_diag || check_winner rigth_diag
  in
  row_match || col_match || diag_match