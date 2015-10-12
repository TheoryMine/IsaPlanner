header{* Inequalities *}

theory Ineq
imports Main IsaP
begin

declare Nat.add_0[wrule]
declare Nat.add_Suc[wrule]
declare Nat.inject[wrule]

fun less_eq :: "nat => nat => bool" (infix "leq" 520)
where
  less_eq_0: "(0::nat) leq y = True" |
  less_eq_Suc:  "(Suc x) leq y = (case y of 0 => False | Suc z => (x leq z))"
declare less_eq_0[wrule]
declare less_eq_Suc[wrule]

fun count :: "'a => 'a list => nat"
where
		count_nil[simp]: "count x [] = 0" |
		count_cons[simp]: "count x (y#ys) = (if (x=y) then (1 + (count x ys)) else (count x ys))"
declare count_nil[wrule]
declare count_cons[wrule]

end;
