header{* Peano Arithmetic - Mult 2 *}

theory BMark_N_m2
imports BMark_N
begin

primrec 
  mult_0[wrule]    :  "(x * 0) = (0 :: N)"
  mult_suc[wrule]  :  "x * (suc y) = (x * y) + x"

end;