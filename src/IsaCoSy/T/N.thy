theory N
imports IsaP

begin
datatype N = zero  ("0\<^isub>N")
           | suc N ("suc\<^isub>N _" [500] 500)
syntax
  "_suc"     :: "N => N" ("suc _" [500] 500)
translations
  "0" == "0\<^isub>N"
  "suc x" == "suc\<^isub>N x"
declare N.inject[impwrule]

primrec plus_N :: "N \<Rightarrow> N \<Rightarrow> N" (infix "+" 509)
where
  add_0[wrule]:  "0 + y = y"
| add_suc[wrule]:"(suc x) + y = suc (x + y)"

primrec mult_N :: "N \<Rightarrow> N \<Rightarrow> N" (infix "*" 509)
where
  mult_0[wrule]:  "0 * y = 0"
| mult_suc[wrule]:"(suc x) * y = y + (x * y)"




end
