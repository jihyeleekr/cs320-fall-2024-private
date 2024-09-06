let rec pow (n : int) (k : int) : int = 
  if k < 0 then failwith "Invalid input for k"
  else if k = 0 then 1
  else n * (pow n (k - 1));;

