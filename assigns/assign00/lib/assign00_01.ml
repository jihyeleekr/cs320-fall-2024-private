let sqrt n = 
  let rec find_sqrt k =
    if n <= k * k
      then k
  else
    find_sqrt(k + 1)
  in 
if n < 0
  then failwith "Invalid Input" (*From Chapter 3.10*)
else
  find_sqrt 0