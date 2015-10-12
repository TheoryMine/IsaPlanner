theory L 
imports (*ATP_Linkup*) IsaP
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

hide_const (open) Nil Cons length map append rev rotate
hide_type (open) list

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

consts length :: "'a list => nat"
primrec
  length_Nil[wrule]:  "length([])   = 0"
  length_Cons[wrule]: "length(x#xs) = Suc (length xs)"


consts map :: "('a=>'b) => ('a list => 'b list)"
primrec
  map_Nil[wrule]:  "map f []     = []"
  map_Cons[wrule]: "map f (x#xs) = f(x)#map f xs"

consts append :: "'a list => 'a list => 'a list" (infixr "@" 65) 
primrec 
  append_Nil[wrule]:  "[] @ ys = ys" 
  append_Cons[wrule]: "(x # xs) @ ys = x # (xs @ ys)"

consts rev :: "'a list => 'a list" 
primrec 
  rev_Nil[wrule]:  "rev [] = []" 
  rev_Cons[wrule]: "rev (x # xs) = (rev xs) @ [x]"


consts qrev :: "'a list => 'a list => 'a list" 
primrec 
  qrev_Nil[wrule]:  "qrev [] l = l" 
  qrev_Cons[wrule]: "qrev (x # xs) l = qrev xs (x # l)"

consts rot :: "(nat \<times> 'a list) => 'a list" 
recdef rot "measure (fst)"
  rot_0[wrule]:  "rot (0, x) = x" 
  rot_Nil[wrule]: "rot (n, []) = []"
  rot_SucCons[wrule]: "rot ((Suc n), (h # t)) = (rot (n, t @ [h]))"

(*
WRONG but interesting mistake: 
consts rot :: "(nat \<times> nat list) => nat list" 
axioms 
  rot_0:  "rot (0, x) = x" 
  rot_Nil: "rot (n, []) = []"
  rot_SucCons: "rot ((Suc n), (h # t)) = (rot (n, t)) @ [h]"

consts rot :: "(nat \<times> nat list) => nat list" 
recdef rot "measure (size o fst)"
  rot_0:  "rot ((0 :: nat), x) = x" 

thm 
consts
  rot_Nil[wrule]: "rot n [] = []"
  rot_SucCons[wrule]: "rot (Suc n) (h # t) = (rot n t) @ [h]"
*)

end;
