header{* Test Synthesis on lists *}

theory SynthL
imports ATP_Linkup IsaP
begin

datatype 'a List = Nil ("[]") 
                 | cons "'a" "'a List"      (infixr "#" 490)
syntax
  "@list"     :: "args => 'a List"                          ("[(_)]")
translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

consts append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" (infixl "@" 501)
primrec 
  append_nil[wrule]      : "[] @ l = l"
  append_cons[wrule]   : "(h # t) @ l = h # (t @ l)"


consts rev :: "'a List \<Rightarrow> 'a List"   ("rev _" [511] 511)
primrec 
  rev_Nil[wrule]: "rev [] = []"
  rev_cons[wrule]: "rev (h # t) = rev t @ [h]"

consts qrev :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" ("qrev _ _" [512,512] 512)
primrec 
  qrev_Nil[wrule]:  "qrev [] l = l"
  qrev_cons[wrule]: "qrev (h # t) l = qrev t (h # l)"

lemma List_distinct1: "(h#t = []) = False"
by simp
end
