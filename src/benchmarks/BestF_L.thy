header{* Peano Arithmetic and Lists for Best_first*}

theory BestF_L 
imports ATP_Linkup IsaP
begin
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

(*consts less :: "[N, N] => bool"            (infix "less" 520)
translations "op <" == "op less"
primrec
  less_0[wrule]   : "x < 0 = False"
  less_suc[wrule] : "x < (suc y) = (case x of 0 => True | suc z => z < y)"
*)
consts double	:: "N => N"
primrec
	double_0[wrule]	: "double 0 = 0"
	double_suc[wrule]	: "double (suc n) = suc(suc(double n)) "

consts half 	:: "N => N"
recdef half "measure size"
	half_0[wrule]	: "half 0 = 0"
	half_1[wrule]	: "half (suc 0) = 0"
 	half_suc[wrule]: "half (suc n) = suc (half (n::N))"
consts binom :: "N * N => N" ("binom _" [500] 500)

consts pre :: "N \<Rightarrow> N"
primrec
presuc[wrule]: "pre (suc n::N) = n"
pre0[wrule]: "pre 0 = 0"

lemma presucP[wrule]: "P (pre (suc (n::N))) = P n" by simp
(*declare presucP[simp]*)



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

consts tail :: "'a List \<Rightarrow> 'a List"
primrec
	tail_nil[wrule]: "tail [] = []"
	tail_cons[wrule]:	"tail (h#t) = t"

consts head :: "'a List \<Rightarrow> 'a"
primrec
	head_cons[wrule]:	"head (h#t) = h"
(*declare head_cons[wrule]*)

(*lemma len_tail[wrule]: "l ~= [] \<Longrightarrow> suc(len(tail l)) = (len l)"
apply (induct l)
apply simp
apply simp
done
*)
consts zip :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List"   ("zip _ _" [506] 506)
primrec
  zip_nil[wrule]:  "zip [] ys = ys"
  zip_cons[wrule]: "zip (x # xs) ys = (case ys of [] \<Rightarrow> x # xs | (y # ys) \<Rightarrow> x # y # (zip xs ys))"

consts mem :: "['a, 'a List] => bool" (infixl 55)
primrec
  mem_Nil[wrule]:  "x mem []     = False"
  mem_Cons[wrule]: "x mem (y#ys) = (if y=x then True else x mem ys)"

(*lemma mem_c1 [wrule]: "x=y \<Longrightarrow> x mem (y#ys) = True"
apply simp
done
lemma mem_c2[wrule]: "x ~= y \<Longrightarrow> x mem (y#ys) = x mem ys"
apply simp
done
*)
consts pairify :: "'a List => 'a List"
primrec
	pairify_nil[wrule]: "pairify [] = []"
	pairify_cons[wrule]: "pairify (h#t) = h#h#(pairify t)"

consts up_to :: "N => N List"
consts upto_aux :: "N => N List => N List"
consts down_to :: "N => N List"
consts downto_aux :: "N => N List => N List"

axioms
up_to_0[simp] : "up_to 0 = []"
up_to_suc[simp] : "up_to (suc n) = upto_aux (suc n) (up_to n)"
upto_aux[simp] : "upto_aux n l = l@(n#[])"
down_to_0[simp] : "down_to 0 = []"
down_to_suc[simp] : "down_to (suc n) = downto_aux (suc n) (down_to n)"
downto_aux[simp] : "downto_aux n l = n#l"

declare up_to_0[impwrule]
declare up_to_suc[wrule]
declare upto_aux[impwrule]
declare down_to_0[impwrule]
declare down_to_suc[wrule]
declare downto_aux[impwrule]


text{* Even and odd stuff *}

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

consts NevenM :: "N \<Rightarrow> bool" ("evenM _" [520] 520)
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

(*lemma wave_if[impwrule]: "\<lbrakk> C \<Longrightarrow> (P A); \<not> C \<Longrightarrow> (P B) \<rbrakk> \<Longrightarrow> P (if C then A else B)" apply auto done *)
(*declare if_P[wrule]
declare if_not_P[wrule]
*)
end;
