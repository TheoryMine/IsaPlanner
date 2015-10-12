theory ITPSynth
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
  add_suc[wrule]  :  "(suc x) + y = suc (x + y)"

fun less_eq :: "N => N => bool" (infix "leq" 520)
where
  less_eq_0: "(0::N) leq y = True" |
  less_eq_Suc:  "(suc x) leq y = (case y of 0 => False | suc z => (x leq z))"
declare less_eq_0[wrule]
declare less_eq_Suc[wrule]

section{* Lists *}
(* Lists *)
datatype 'a List = Nil ("[]") 
                 | Cons "'a" "'a List"      (infixr "#" 65)

declare list.inject[wrule]

syntax
  "_list"     :: "args => 'a list"                          ("[(_)]")

(*translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"
*)
consts len :: "'a List => N"
primrec
  len_nil[wrule]: "len [] = 0"
  len_cons[wrule]: "len (h#t) = suc(len t)"

consts append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" (infixl "@" 501)
primrec 
  append_0[wrule]      : "[] @ l = l"
  append_cons[wrule]   : "(h # t) @ l = h # (t @ l)"

consts rev :: "'a List \<Rightarrow> 'a List"   ("rev _" [511] 511)
primrec 
  rev_nil[wrule]: "rev [] = []"
  rev_cons[wrule]: "rev (h # t) = rev t @ (h# [])"

consts map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a List \<Rightarrow> 'b List)"  ("map _ _" [510] 510)
primrec
  map_Nil[wrule]:  "map f []     = []"
  map_cons[wrule]: "map f (x#xs) = f(x)#map f xs"

consts maps :: "('a => 'b List) => 'a List => 'b List"
primrec
  maps_nil[wrule]: "maps f [] = []" 
  maps_cons[wrule]: "maps f (h#t) = (f h) @ (maps f t)"

consts rotate :: "N \<Rightarrow> 'a List => 'a List"
primrec
  rot_zero[wrule]:  "rotate 0 l = l"
  rot_suc[wrule]:   "rotate (suc n) l = (case l of (h#t) => rotate n (t@[h])
                                                  | [] => [])" 

consts concat :: "'a List List => 'a List"
primrec
  concat_nil[wrule]: "concat [] = []" 
  concat_cons[wrule]: "concat (h#t) = h @ (concat t)"

text{* Even  *}

consts NevenR :: "N \<Rightarrow> bool" ("evenR _" [520] 520)
recdef NevenR "measure size"
  NevenR_0[wrule]:"evenR 0 = True"
  NevenR_not_S_0[wrule]: "evenR (suc 0) = False"
  NevenR_S_S[wrule]:     "evenR (suc (suc n)) = evenR n"


end;
