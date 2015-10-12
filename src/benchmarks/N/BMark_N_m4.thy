header{* Peano Arithmetic - Mult 4 *}

theory BMark_N_m4
imports BMark_N
begin

primrec 
  mult_0[wrule]    :  "(0 * y) = (0 :: N)"
  mult_suc[wrule]  :  "(suc x) * y = (x * y) + y"

end;