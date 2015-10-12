header{* Benchmark synthesis on Lists with @, rev, len *}

theory List_rev_len
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

(* Tests to make sure we successfully hid the intended syntax/constants *) 
(* term "P []" *)
(* term "P [a,b]" *)
(* term "P (b#bs)" *)
(* term "a @ b" *)

datatype 'a list = Nil ("[]") 
                 | Cons "'a" "'a list"      (infixr "#" 65)
declare list.inject[wrule]
syntax
  -- {* list Enumeration *}
  "@list" :: "args => 'a list"    ("[(_)]")
translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

(* Add some common rules for Naturual numbers as wrules.*)
declare Nat.add_0[wrule]
declare Nat.add_Suc[wrule]
declare Nat.add_0_right[wrule]
declare Nat.add_Suc_right[wrule]
declare Nat.nat_add_assoc[wrule]

consts append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "@" 501)
primrec 
  append_nil[wrule]      : "[] @ l = l"
  append_cons[wrule]   : "(h # t) @ l = h # (t @ l)"


consts rev :: "'a list \<Rightarrow> 'a list"   ("rev _" [511] 511)
primrec 
  rev_Nil[wrule]: "rev [] = []"
  rev_cons[wrule]: "rev (h # t) = rev t @ [h]"


consts len :: "'a list \<Rightarrow> nat"
primrec
  len_nil[wrule]: "len [] = 0"
  len_cons[wrule]: "len (h#t) = Suc(len t)"

end