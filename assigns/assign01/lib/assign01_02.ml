let nth_prime (n : int) : int = 
  let rec is_prime (n : int) (k : int) : int = 
      let rec prime_checker (k : int) (p : int) =
      if p = k then true
      else if k mod p = 0 then false
      else prime_checker k (p + 1)
    in 
    if n = 0 then k
    else if prime_checker (k + 1) 2 then is_prime (n - 1) (k + 1)
    else is_prime n (k + 1)
  in 
  if n < 0 then failwith "Invalid input for n"
  else is_prime n 2


