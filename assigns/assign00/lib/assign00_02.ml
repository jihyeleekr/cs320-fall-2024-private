let is_prime n =
  let rec prime_checker k =
    if k = n
    then true
    else if n mod k = 0
    then false
    else prime_checker (k + 1)
  in
  if n < 2
  then false
  else prime_checker 2