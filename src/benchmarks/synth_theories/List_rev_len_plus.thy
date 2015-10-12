header{* Benchmark synthesis on Lists with @, rev, len *}

theory List_rev_len_plus
imports ATP_Linkup IsaP
begin

(* Lists *)
datatype 'a List = Nil ("[]") 
                 | cons "'a" "'a List"      (infixr "#" 490)
syntax
  "@list"     :: "args => 'a List"                          ("[(_)]")
translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

(* Nural numbers *)
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

consts append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" (infixl "@" 501)
primrec 
  append_nil[wrule]      : "[] @ l = l"
  append_cons[wrule]   : "(h # t) @ l = h # (t @ l)"


consts rev :: "'a List \<Rightarrow> 'a List"   ("rev _" [511] 511)
primrec 
  rev_Nil[wrule]: "rev [] = []"
  rev_cons[wrule]: "rev (h # t) = rev t @ [h]"


consts len :: "'a List \<Rightarrow> N"
primrec
  len_nil[wrule]: "len [] = 0"
  len_cons[wrule]: "len (h#t) = suc(len t)"

end