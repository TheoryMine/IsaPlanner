header{* Peano Arithmetic - Mult 1 *}

theory BMark_N_m1
imports BMark_N
begin

primrec 
  mult_0[wrule]    :  "(x * 0) = (0 :: N)"
  mult_suc[wrule]  :  "x * (suc y) = x + (x * y)"

end;