header{* Peano Arithmetic and Lists for Best_first*}

theory BestF_Lists = PreList + IsaP:

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

recdef binom "measure (size o fst)"
	binom_0[wrule]:	"binom (x, 0) = suc 0"
	binom_02[wrule]: "binom (0, x) = 0"
  binom_S[wrule]:	"binom( (suc x), (suc(y :: N) ) ) = binom (x, (suc y)) + (binom (x, y))"

consts Minus2 :: "N \<Rightarrow> N \<Rightarrow> N"	(infixr "Minus2" 80)
translations "op -" == "op Minus2"
primrec
	Minus2_0[wrule]		: "(y - 0) = (y :: N)"
	Minus2_suc	:	"y - (suc x) = (case y of 0 \<Rightarrow> 0 | (suc y2) \<Rightarrow> (y2 - x))"

lemma Minus2_suc_suc[wrule]: "(suc y) - (suc x) = (y - x)"
apply simp
done

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


consts zip :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List"   ("zip _ _" [506] 506)
primrec
  zip_nil[wrule]:  "zip [] ys = ys"
  zip_cons[wrule]: "zip (x # xs) ys = (case ys of [] \<Rightarrow> x # xs | (y # ys) \<Rightarrow> x # y # (zip xs ys))"

consts mem :: "['a, 'a List] => bool" (infixl 55)
primrec
  mem_Nil:  "x mem []     = False"
  mem_Cons: "x mem (y#ys) = (if y=x then True else x mem ys)"

text{*


*}
consts drop :: "[N, 'a List] => 'a List"
primrec
  drop_Nil[wrule]:  "drop n [] = []"
  drop_Cons[wrule]: "drop n (x#xs) = (case n of 0 => x#xs | suc(m) => drop m xs)"
consts pairify :: "'a List => 'a List"
primrec
	pairify_nil[wrule]: "pairify [] = []"
	pairify_cons[wrule]: "pairify (h#t) = h#h#(pairify t)"

text{*These functions computes a list of all numbers upto its argument
and appends the reverse of the list to the end. One function for decreasing
and one in increasing order 
consts palin_incr :: "N => N List"
consts palin_decr :: "N => N List"
consts palin_i_aux :: "N => N List => N List => N List"
consts palin_d_aux :: "N => N List => N List => N List"
axioms
palin_incr_0[simp]: "palin_incr 0 = []"
palin_incr_suc[simp]: "palin_incr (suc n) = palin_i_aux (suc n) (palin_incr n) (palin_decr n)"
palin_decr_0[simp]: "palin_decr 0 = []"
palin_decr_suc[simp]: "palin_decr (suc n) = palin_d_aux (suc n) (palin_incr n) (palin_decr n)"
palin_i_aux_[simp]: "palin_i_aux n l1 l2 =  n#(l1 @ l2)"
palin_d_aux_[simp]: "palin_d_aux n l1 l2 = rev(n#(l1 @ l2))"

declare palin_incr_0[impwrule]
declare palin_incr_suc[wrule]
declare palin_decr_0[impwrule]
declare palin_decr_suc[wrule]
declare palin_i_aux_[wrule]
declare palin_d_aux_[wrule]

*}
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


text{* Trees 
datatype 'a Tree = Leaf 'a | Node 'a "'a Tree" "'a Tree" 

consts size_of	:: "'a Tree => N"
primrec
	size_leaf[wrule]:	"size_of (Leaf a) = suc 0"
	size_node[wrule]:	"size_of (Node n l r) = suc ((size_of l) + (size_of r))"

consts flatten :: "'a Tree => 'a List"
primrec
	flatten_leaf[wrule]:	"flatten (Leaf a) = [a]"
	flatten_node[wrule]:  "flatten (Node n l r) = n # (flatten l)@(flatten r)"

consts mirror :: "'a Tree => 'a Tree"
primrec
	mirror_leaf[wrule]:	"mirror (Leaf l) = (Leaf l)"
	mirror_node[wrule]:	"mirror (Node (c#cs)) = (Node ((map mirror cs)@[(mirror c)]))"

consts flatten :: "'a Tree => 'a List"
primrec
	flatten_leaf[wrule]:	"flatten (Leaf a) = [a]"
	flatten_node[wrule]:  "flatten (Node (n,l,r) = n # (flatten l)@(flatten r)"
*}

text{* Cheeky induction stuff 
consts id :: "'a List \<Rightarrow> 'a List"
axioms 
	id_nil[simp]: "id []  = []"
	id_cons[simp]: "id l  = (head l) # (tail l)"
 
declare id_nil[wrule]
declare	id_cons[wrule]
}
text{* Some induction schemes *}

axioms 
two_step_ind: "\<lbrakk>P 0; P (suc 0);\<And>m. P m \<Longrightarrow> P
(suc (suc m))\<rbrakk> \<Longrightarrow> P n"

destr_list: "\<lbrakk>P []; \<And>m. P (tail m) \<Longrightarrow> P (id m) \<rbrakk> \<Longrightarrow> P n"

two_step_list: "\<lbrakk>P []; P (h1#[]); \<And>m. P m \<Longrightarrow> P (h1#h2#m) \<rbrakk> \<Longrightarrow> P n"
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

consts EvenList :: "N List \<Rightarrow> N List"
primrec
  EvenList_nil[wrule]: "EvenList [] = []"
  EvenList_cons[wrule]: "EvenList (h # t) = (if evenR(h) then h#(EvenList t)  else EvenList t)"


end;