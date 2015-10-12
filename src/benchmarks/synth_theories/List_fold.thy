header{* Benchmark synthesis on Lists with @, rev, map *}

theory List_fold
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
  append_nil[wrule]      : "([] @ l) = l"
  append_cons[wrule]   : "((h # t) @ l) = (h # (t @ l))"

consts foldl :: "('b => 'a => 'b) => 'b => 'a list => 'b"
primrec
  foldl_Nil[wrule]:"foldl f a [] = a"
  foldl_Cons[wrule]: "foldl f a (x#xs) = foldl f (f a x) xs"

consts foldr :: "('a => 'b => 'b) => 'a list => 'b => 'b"
primrec
  foldr_nil[wrule]:  "foldr f [] a = a"
  foldr_cons[wrule]: "foldr f (x#xs) a = f x (foldr f xs a)"


(*consts map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a List \<Rightarrow> 'b List)"  ("map _ _" [510] 510)
primrec
  map_Nil[wrule]:  "map f []     = []"
  map_cons[wrule]: "map f (x#xs) = f(x)#map f xs"
*)


end