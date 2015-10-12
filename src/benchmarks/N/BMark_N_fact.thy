header{* Peano Arithmetic *}

theory BMark_N_fact
imports BMark_N_m1
begin

consts fact :: "N \<Rightarrow> N"
recdef fact "measure size"
  fact_0[wrule]        :  "fact 0 = 0"
  fact_suc_0[wrule]    :  "fact (suc n) = (suc n) * (fact n)"

end;