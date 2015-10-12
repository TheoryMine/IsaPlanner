header{* Peano Arithmetic 1 *}

theory BMark_N1 = Main + IsaP:

text {* The standard definitions for Peano aithmetic (recursivly on
the first argument, except for exponentiation and less than). *}

datatype N = zero  ("zero")
           | suc N ("suc _" [100] 100)

instance N :: one ..
instance N :: ord ..
instance N :: plus ..
instance N :: times ..

translations "0" == "zero"

defs (overloaded) one_def: "1 == suc 0"

primrec 
  add_0[wrule]    :  "(0 + y) = (y :: N)"
  add_suc[wrule]  :  "suc x + y = suc (x + y)"

primrec 
  mult_0[wrule]    :  "(0 * y) = (0 :: N)"
  mult_suc[wrule]  :  "(suc x) * y = y + (x * y)"

consts exp :: "[N, N] => N"            (infixr "exp" 80)
translations "op ^" == "op exp"
primrec
  exp_0[wrule]   : "x ^ 0 = suc 0"
  exp_suc[wrule] : "x ^ (suc y) = x * (x ^ y)"

primrec
  less_0[wrule]   : "x < (0 :: N) = False"
  less_Suc[wrule] : "x < (suc y) = (case x of 0 => True | suc z => z < y)"

declare N.inject[impwrule]

end;
