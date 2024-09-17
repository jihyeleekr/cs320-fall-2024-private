type dir = 
| North
| South
| East
| West

type path = dir list

let dist (dirs : path) : float = 
  let rec final_point (x,y) = function
  | [] -> (x, y)
  | North :: rest -> final_point(x , y +. 1.) rest
  | South :: rest  -> final_point(x, y -. 1.) rest
  | East :: rest -> final_point(x +. 1., y) rest
  | West :: rest -> final_point(x -. 1., y) rest
in
let (x, y) = final_point(0., 0.) dirs in
let dist_form = sqrt ( (x ** 2.) +. (y ** 2.))
in
dist_form
