theory Ireland
imports ATP_Linkup IsaP
begin

datatype N = zero  ("0\<^isub>N")
           | suc N ("suc\<^isub>N _" [500] 500)
syntax
  "_suc"     :: "N => N" ("suc _" [500] 500)
translations
  "0" == "0\<^isub>N"
  "suc x" == "suc\<^isub>N x"

declare N.inject[wrule]

consts add :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "+\<^isub>N" 509)
translations "x + y" == "x +\<^isub>N y" 
primrec 
  add_0[wrule]    :  "(0 + y) = y"
  add_suc[wrule]  :  "suc x + y = suc (x + y)"


section{* Lists *}
datatype 'a List = Nil ("[]") 
                 | Cons "'a" "'a List"      (infixr "#" 65)

declare list.inject[wrule]

syntax
  "_list"     :: "args => 'a list"                          ("[(_)]")

(*translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"
*)
consts len :: "'a List \<Rightarrow> N"   ("len _" [500] 500)
primrec 
  len_nil[wrule]:     "len [] = 0"
  len_cons[wrule]:    "len (h # t) = suc (len t)"

consts append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" (infixl "@" 501)
primrec 
  append_0[wrule]      : "[] @ l = l"
  append_cons[wrule]   : "(h # t) @ l = h # (t @ l)"

consts rev :: "'a List \<Rightarrow> 'a List"   ("rev _" [511] 511)
primrec 
  rev_nil[wrule]: "rev [] = []"
  rev_cons[wrule]: "rev (h # t) = rev t @ (h#[])"

consts rotate :: "N \<Rightarrow> 'a List => 'a List"
primrec
  rot_zero[wrule]:  "rotate 0 l = l"
  rot_suc[wrule]:   "rotate (suc n) l = (case l of (h#t) => rotate n (t@(h#[]))
                                                  | [] => [])" 

text{* Even  *}

consts even :: "N \<Rightarrow> bool" ("even _" [520] 520)
recdef even "measure size"
  even_0[wrule]:"even 0 = True"
  even_not_S_0[wrule]: "even (suc 0) = False"
  even_S_S[wrule]:     "even (suc (suc n)) = even n"


end;
