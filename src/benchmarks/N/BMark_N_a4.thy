header{* Peano Arithmetic - Addition 3 *}

theory BMark_N_a4
imports BMark_N
begin

primrec 
  add_0[wrule]    :  "x + 0 = (x :: N)"
  add_suc[wrule]  :  "x + (suc y) =  (suc x) + y"

end;