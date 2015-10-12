header{* Peano Arithmetic - Mult 3 *}

theory BMark_N_m3
imports BMark_N
begin

primrec 
  mult_0[wrule]    :  "(0 * y) = (0 :: N)"
  mult_suc[wrule]  :  "(suc x) * y = y + (x * y)"

end;