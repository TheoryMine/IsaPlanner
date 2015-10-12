header{* Peano Arithmetic and Lists *}

theory BMark_NL = PreList + IsaP:

section{* Peano Arithmetic *}

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

consts mult :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "*\<^isub>N" 509)
translations "x * y" == "x *\<^isub>N y" 
primrec 
  mult_0[wrule]    :  "(0 * y) = 0"
  mult_suc[wrule]  :  "(suc x) * y = y + (x * y)"

consts exp :: "[N, N] => N"            (infixr "exp" 515)
translations "op ^" == "op exp"
primrec
  exp_0[wrule]   : "x ^ 0 = suc 0"
  exp_suc[wrule] : "x ^ (suc y) = x * (x ^ y)"

consts less :: "[N, N] => bool"            (infix "less" 520)
translations "op <" == "op less"
primrec
  less_0[wrule]   : "x < 0 = False"
  less_suc[wrule] : "x < (suc y) = (case x of 0 => True | suc z => z < y)"

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

consts map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a List \<Rightarrow> 'b List)"  ("map _ _" [510] 510)
primrec
  map_nil[wrule]:  "map f []     = []"
  map_cons[wrule]: "map f (x#xs) = f(x)#map f xs"

consts rev :: "'a List \<Rightarrow> 'a List"   ("rev _" [511] 511)
primrec 
  rev_nil[wrule]: "rev [] = []"
  rev_cons[wrule]: "rev (h # t) = rev t @ [h]"

consts qrev :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" ("qrev _ _" [512,512] 512)
primrec 
  qrev_nil[wrule]:  "qrev [] l = l"
  qrev_cons[wrule]: "qrev (h # t) l = qrev t (h # l)"

consts rot :: "N \<times> 'a List \<Rightarrow> 'a List"   ("rot _" [505] 505)
recdef rot "measure (size o fst)"
  rot_0[wrule]:   "rot (0, l) = l"
  rot_nil[wrule]: "rot (n, []) = []"
  rot_suc[wrule]:   "rot (suc n, h # t) = rot (n, t @ [h])"

consts zip :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List"   ("zip _ _" [506] 506)
primrec
  zip_nil[wrule]:  "zip [] ys = ys"
  zip_cons[wrule]: "zip (x # xs) ys = 
    (case ys of [] \<Rightarrow> x # xs | (y # ys) \<Rightarrow> x # y # (zip xs ys))"

consts zip2 :: "'a List \<times> 'a List \<Rightarrow> 'a List"   ("zip2 _" [507] 507)
recdef zip2 "measure (size o fst)"
  zip2_nil1: "zip2 ([], ys) = ys"
  zip2_nil2[wrule]: "zip2 (xs, []) = xs"
  zip2_cons[wrule]: "zip2 (x#xs, y#ys) = x # y # (zip2(xs,ys))"

end;
