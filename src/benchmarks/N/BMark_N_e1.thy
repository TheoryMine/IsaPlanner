header{* Peano Arithmetic - Exp 1 *}

theory BMark_N_e1
imports BMark_N
begin

consts exp :: "[N, N] => N"            (infixr "exp" 80)
translations "op ^" == "op exp"
primrec
  exp_0[wrule]   : "x ^ 0 = suc 0"
  exp_suc[wrule] : "x ^ (suc y) = x * (x ^ y)"

end;