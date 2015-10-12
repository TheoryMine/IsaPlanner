header{* Peano Arithmetic *}

theory BMark_N_fib
imports BMark_N
begin

consts fib :: "N \<Rightarrow> N"
recdef fib "measure size"
  fib_0[wrule]        :  "fib 0 = (0 :: N)"
  fib_suc_0[wrule]    :  "fib (suc 0) = (suc 0)"
  fib_suc_suc[wrule]  :  "fib (suc (suc n)) = (fib (suc n)) + (fib n)"

end;