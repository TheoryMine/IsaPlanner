header{* Test Synthesis on +, * and exp.*}

theory N_plus_mult_exp 

imports ATP_Linkup IsaP
begin

datatype N = zero  ("0\<^isub>N")
           | suc N ("suc\<^isub>N _" [500] 500)
syntax
  "_suc"     :: "N => N" ("suc _" [500] 500)
translations
  "0" == "0\<^isub>N"
  "suc x" == "suc\<^isub>N x"

declare N.inject[impwrule]

consts add :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "+\<^isub>N" 509)
translations "x + y" == "x +\<^isub>N y" 
primrec 
  add_0[wrule]    :  "(0 + y) = y"
  add_suc[wrule]  :  "suc x + y = suc (x + y)"

consts mult :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "*\<^isub>N" 509)
translations "x * y" == "x *\<^isub>N y" 
primrec 
  mult_0[wrule]    :  "(0 * y) = 0"
  mult_suc[wrule]  :  "(suc x) * y = y + (x * y)"


consts exp :: "[N, N] => N"            (infixr "exp" 515)
translations "op ^" == "op exp"
primrec
  exp_0[wrule]   : "x ^ 0 = suc 0"
  exp_suc[wrule] : "x ^ (suc y) = x * (x ^ y)"



end