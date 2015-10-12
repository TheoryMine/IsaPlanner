theory CaseAnalysis
imports IsaP
begin

declare nat.inject[wrule]
declare Nat.add_0[wrule]
declare Nat.add_Suc[wrule]
declare Nat.mult_0[wrule]
declare Nat.mult_Suc[wrule]

fun minus :: "nat => nat => nat" (infix "minus" 520)
where
  minus_0:     "0 minus m = 0"
  | minus_suc: "(Suc m) minus n = (case n of 0 => (Suc m) | Suc k => m minus k)"
declare minus_0[wrule]
declare minus_suc[wrule]

fun less :: "nat => nat => bool" (infix "less" 520)
where
  less_0  : "(x :: nat) less 0 = False" |
  less_Suc : "x less (Suc y) = (case x of 0 => True | Suc z => (z less y))"
declare less_0[wrule]
declare less_Suc[wrule]

fun less_eq :: "nat => nat => bool" (infix "leq" 520)
where
  less_eq_0: "(0::nat) leq y = True" |
  less_eq_Suc:  "(Suc x) leq y = (case y of 0 => False | Suc z => (x leq z))"
declare less_eq_0[wrule]
declare less_eq_Suc[wrule]

 fun max :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
    max_0: "max 0 y = y"
  | max_Suc: "max (Suc x) y = (case y of 0 => (Suc x) | Suc z => Suc(max x z))"
declare max_0[wrule]
declare max_Suc[wrule]

fun min :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
    min_0: "min 0 y = 0"
  | min_Suc: "min (Suc x) y = (case y of 0 => y | Suc z => Suc(min x z))"
declare min_0[wrule]
declare min_Suc[wrule]

end
