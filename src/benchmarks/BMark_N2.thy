header{* Peano Arithmetic 2 *}

theory BMark_N2 = Main + IsaP:

text {* In this theory we define Peano aithmetic recursivly on the
second argument. This is not standard but leads to improved
automation. *}

datatype N = zero  ("zero")
           | suc N ("suc _" [100] 100)

instance N :: one ..
instance N :: ord ..
instance N :: plus ..
instance N :: times ..

translations "0" == "zero"

defs (overloaded) one_def: "1 == suc 0"

primrec 
  add_0[wrule]    :  "(y + 0) = (y :: N)"
  add_suc[wrule]  :  "y + (suc x) = suc (y + x)"

primrec 
  mult_0[wrule]    :  "(y * 0) = (0 :: N)"
  mult_suc[wrule]  :  "y * (suc x) = (y * x) + y"

consts exp :: "[N, N] => N"            (infixr "exp" 80)
translations "op ^" == "op exp"
primrec
  exp_0[wrule]   : "x ^ 0 = suc 0"
  exp_suc[wrule] : "x ^ (suc y) = (x ^ y) * x"

primrec
  less_0[wrule]   : "x < (0 :: N) = False"
  less_Suc[wrule] : "x < (suc y) = (case x of 0 => True | suc z => z < y)"

declare N.inject[impwrule]

end;
