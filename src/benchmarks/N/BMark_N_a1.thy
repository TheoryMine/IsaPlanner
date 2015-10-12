header{* Peano Arithmetic - Addition 1 *}

theory BMark_N_a1
imports BMark_N
begin

primrec 
  add_0[wrule]    :  "(0 + y) = (y :: N)"
  add_suc[wrule]  :  "suc x + y = suc (x + y)"

end;