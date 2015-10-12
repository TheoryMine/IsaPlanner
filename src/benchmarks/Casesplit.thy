header{* teasting case-splitting critic *}

theory Casesplit 
imports ATP_Linkup IsaP
begin

text {* The standard definitions for Peano aithmetic (recursivly on
the first argument, except for exponentiation and less than). *}

datatype N = zero  ("zero")
           | suc N ("suc _" [100] 100)
translations "0" == "zero"
instance N :: one ..
instance N :: ord ..
instance N :: plus ..
instance N :: times ..
thm N.split
primrec
  less_0[wrule]   : "x < (0 :: N) = False"
  less_Suc[wrule] : "x < (suc y) = (case x of 0 => True | suc z => z < y)"

lemma "0_less":"0 < (suc x) = True"
apply simp
done
lemma "less_suc":"((suc x) < (suc y)) = (x < y)"
apply simp
done
section{* Lists *}

datatype 'a List = nil ("[]") 
                 | cons "'a" "'a List"      (infixr "#" 490)
syntax
  "@list"     :: "args => 'a List"                          ("[(_)]")
translations
	"[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

consts len :: "'a List \<Rightarrow> N"   ("len _" [500] 500)
primrec 
  len_nil[wrule]:     "len [] = 0"
  len_cons[wrule]:    "len (h # t) = suc (len t)"

consts append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" (infixl "@" 501)
primrec 
  append_0[wrule]      : "[] @ l = l"
  append_cons[wrule]   : "(h # t) @ l = h # (t @ l)"

consts mem :: "['a, 'a List] => bool" (infixl 55)
primrec
  mem_Nil[wrule]:  "x mem []     = False"
  mem_Cons[wrule]: "x mem (y#ys) = (if y=x then True else x mem ys)"

lemma mem_cons_suc_eq: "x =y ==> x mem (y#ys) = True" by simp
lemma mem_cons_suc_neq: "\<not>(x=y) ==> x mem (y#ys) = x mem ys" by simp

consts ins :: "N * (N List)=> (N List)" ("ins _" [500] 500)
recdef ins "measure (size o snd)"
	insert_nil[wrule]: "ins (n, []) = [n]"
	insert_cons[wrule]: "ins (n, (h#t)) = (if n<h then n#h#t else ins(n, t))"

consts ins_set :: "'a * ('a List)=> ('a List)" ("insset _" [500] 500)
recdef ins_set "measure (size o snd)"
	ins_set_nil[wrule]: "ins_set (n, []) = [n]"
	ins_set_cons[wrule]: "ins_set (n, (h#t)) = (if h=n then (n#t) else h#ins_set(n, t))"

lemma "(x=y) --> (x mem (ins_set (y,l)) = True)"
apply (induct l)
apply simp
apply (subst ins_set_cons)
apply (split split_if, rule conjI, rule impI)
apply (subst mem_Cons)
apply (split split_if, rule conjI, rule impI)
apply simp
apply simp
apply (subst mem_Cons)
apply (split split_if, rule conjI, rule impI)
apply simp
apply (rule impI, rule impI)
apply assumption
done

theorem "IsaP_split_if": "\<lbrakk> Q \<Longrightarrow> P(x); ~Q \<Longrightarrow> P(y) \<rbrakk> \<Longrightarrow> P (if Q then x else y)"
apply simp
done


end
