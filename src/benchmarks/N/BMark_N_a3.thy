header{* Peano Arithmetic - Addition 3 *}

theory BMark_N_a3
imports BMark_N
begin

primrec 
  add_0[wrule]    :  "0 + y = (y :: N)"
  add_suc[wrule]  :  "suc x + y =  x + (suc y)"

end;