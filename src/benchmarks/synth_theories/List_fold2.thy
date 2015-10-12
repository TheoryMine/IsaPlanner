header{* Benchmark synthesis on Lists with @, rev, map *}

theory List_fold2
imports ATP_Linkup IsaP
begin

datatype List = Nil ("[]") 
                 | cons "nat" "List"      (infixr "#" 490)
syntax
  "@list"     :: "args => List"                          ("[(_)]")
translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

consts append :: "List => List => List" (infixl "@" 501)
primrec 
  append_nil[wrule]      : "[] @ l = l"
  append_cons[wrule]   : "(h # t) @ l = h # (t @ l)"

consts foldl :: "(nat => nat => nat) => nat => List => nat"
primrec
  foldl_Nil[wrule]:"foldl f a [] = a"
  foldl_Cons[wrule]: "foldl f a (x#xs) = foldl f (f a x) xs"


consts foldr :: "(nat => nat => nat) => List => nat => nat"
primrec
  foldr_nil[wrule]:  "foldr f [] a = a"
  foldr_cons[wrule]: "foldr f (x#xs) a = f x (foldr f xs a)"


end