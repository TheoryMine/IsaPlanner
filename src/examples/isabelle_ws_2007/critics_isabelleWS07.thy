theory critics_isabelleWS07
imports IsaP
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
                 | Cons "'a" "'a List"      (infixr "#" 490)
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

consts rev :: "'a List \<Rightarrow> 'a List"   ("rev _" [511] 511)
primrec 
  rev_nil[wrule]: "rev [] = []"
  rev_cons[wrule]: "rev (h # t) = rev t @ [h]"
(*
consts mem :: "'a \<Rightarrow> 'a List => bool" 
primrec
  mem_Nil[wrule]:  " mem x []     = False"
  mem_Cons[wrule]: "mem x (y#ys) = (if y=x then True else mem x ys)"
*)
consts rotate :: "N \<Rightarrow> 'a List => 'a List"
primrec
  rot_zero[wrule]:  "rotate 0 l = l"
  rot_suc[wrule]:   "rotate (suc n) l = (case l of (h#t) => rotate n (t@[h])
                                                  | [] => [])" 
fun maps :: "('a \<Rightarrow> 'a List) \<Rightarrow> 'a List \<Rightarrow> 'a List"
where
  maps_nil:   "maps f [] = []" |
  maps_cons:  "maps f (h#t) = (f h) @ (maps f t)"
declare maps_nil[wrule]
declare maps_cons[wrule]

fun concat :: " 'a List List  \<Rightarrow> 'a List"
where
  concat_nil: "concat [] = []" |
  (*_nil2: "concat [[]] = []" | *)
  concat_cons: "concat (ls#ts) = ls @ (concat ts)"
declare concat_nil[wrule]
(*declare concat_nil2[wrule] *)
declare concat_cons[wrule]

text{* Even and odd (recursive and mutually recursive) *}

consts NevenR :: "N \<Rightarrow> bool" ("evenR _" [520] 520)
recdef NevenR "measure size"
  NevenR_0[wrule]:"evenR 0 = True"
  NevenR_not_S_0[wrule]: "evenR (suc 0) = False"
  NevenR_S_S[wrule]:     "evenR (suc (suc n)) = evenR n"

consts NoddR :: "N \<Rightarrow> bool" ("oddR _" [520] 520)
recdef NoddR "measure size"
  NoddR_0[wrule]:"oddR 0 = False"
  NoddR_not_S_0[wrule]: "oddR (suc 0) = True"
  NoddR_S_S[wrule]:     "oddR (suc (suc n)) = oddR n"

(*consts NevenM :: "N \<Rightarrow> bool" ("evenM _" [520] 520)
consts NoddM :: "N \<Rightarrow> bool" ("oddM _" [520] 520)

axioms
 NevenM_suc[simp]: "evenM (suc n) = oddM n"
 NoddM_suc[simp]: "oddM (suc n) = evenM n"
 NevenM_0[simp]: "evenM 0 = True"
 NoddM_0[simp]: "oddM 0 = False"

declare NevenM_suc[wrule]
declare NoddM_suc[wrule]
declare NevenM_0[wrule]
declare NoddM_0[wrule] 
*)
text{* Some induction schemes *}
axioms 
two_step_ind: "\<lbrakk>P 0; P (suc 0);\<And>m. P m \<Longrightarrow> P
(suc (suc m))\<rbrakk> \<Longrightarrow> P n"

end;
