header{* Benchmark Synthesis on lists with @, rev, qrev. *}

theory List_rev_qrev
imports ATP_Linkup IsaP
begin

(* remove old list syntax - make sure we are starting from a fresh theory *)
no_translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"
no_syntax
 "@list" :: "args => 'a list"    ("[(_)]")
no_notation Nil ("[]")
no_notation Cons (infixr "#" 65)
no_notation append (infixr "@" 65)

hide (open) const Nil Cons length map append rev rotate
hide (open) type list

datatype 'a list = Nil ("[]") 
                 | Cons "'a" "'a list"      (infixr "#" 65)
declare list.inject[wrule]
syntax
  -- {* list Enumeration *}
  "@list" :: "args => 'a list"    ("[(_)]")
translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"


consts append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "@" 65)
primrec 
  append_nil[wrule]      : "[] @ l = l"
  append_cons[wrule]   : "(h # t) @ l = h # (t @ l)"


consts rev :: "'a list \<Rightarrow> 'a list"   ("rev _" [511] 511)
primrec 
  rev_Nil[wrule]: "rev [] = []"
  rev_cons[wrule]: "rev (h # t) = rev t @ [h]"

consts qrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" ("qrev _ _" [512,512] 512)
primrec 
  qrev_Nil[wrule]:  "qrev [] l = l"
  qrev_cons[wrule]: "qrev (h # t) l = qrev t (h # l)"

end