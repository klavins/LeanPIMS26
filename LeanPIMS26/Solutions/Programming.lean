def fib n :=
  let rec aux (n a b : Nat) : Nat :=
    match n with
    | 0 => a
    | 1 => b
    | k+1 => aux k b (a+b)
  aux n 1 1

#eval (List.range 10).map fib
