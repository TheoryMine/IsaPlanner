header{* Peano Arithmetic for best-first problems *}

theory BestF_N 
imports Main IsaP
begin

text {* The standard definitions for Peano aithmetic (recursivly on
the first argument, except for exponentiation and less than). *}

datatype N = zero  ("zero")
           | suc N ("suc _" [100] 100)

instance N :: one ..
instance N :: ord ..
instance N :: plus ..
instance N :: times ..

translations "0" == "zero"

defs (overloaded) one_def: "1 == suc 0"

primrec 
  add_0[wrule]    :  "(0 + y) = (y :: N)"
  add_suc[wrule]  :  "suc x + y = suc (x + y)"

primrec 
  mult_0[wrule]    :  "(0 * y) = (0 :: N)"
  mult_suc[wrule]  :  "(suc x) * y = y + (x * y)"

consts exp :: "[N, N] => N"            (infixr "exp" 80)
translations "op ^" == "op exp"
primrec
  exp_0[wrule]   : "x ^ 0 = suc 0"
  exp_suc[wrule] : "x ^ (suc y) = x * (x ^ y)"

primrec
  less_0[wrule]   : "x < (0 :: N) = False"
  less_Suc[wrule] : "x < (suc y) = (case x of 0 => True | suc z => z < y)"

declare N.inject[impwrule]

consts sum	:: "N => N"
primrec 
	sum_0[wrule]		:	"sum 0 = 0"
	sum_suc[wrule]	:	"sum (suc n) = (sum n) + (suc (n::N))"

consts half 	:: "N => N"
recdef half "measure size"
	half_0[wrule]	: "half 0 = 0"
	half_1[wrule]	: "half (suc 0) = 0"
 	half_suc[wrule]: "half (suc n) = suc (half (n::N))"

consts double	:: "N => N"
primrec
	double_0[wrule]	: "double 0 = 0"
	double_suc[wrule]	: "double (suc n) = suc(suc(double n)) "

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

text {* Mod stuff *}

consts ZMT	:: "N \<Rightarrow> bool"	("ZMT _" [500] 500)
consts OMT	:: "N \<Rightarrow> bool"	("OMT _" [500] 500)
consts TMT	:: "N \<Rightarrow> bool"	("TMT _" [500] 500)

axioms
	Zero_M_Three_zero[simp]: "ZMT 0 = True"
	Zero_M_Three_suc[simp]: "ZMT (suc x) = TMT x"

  One_M_Three_zero[simp]: "OMT 0 = False"	
	One_M_Three_suc[simp]: "OMT (suc x) = ZMT x"

	Two_M_Three_zero[simp]: "TMT 0 = False"
	Two_M_Three_suc[simp]: "TMT (suc x) = OMT x"

declare Zero_M_Three_zero[wrule]
declare One_M_Three_zero[wrule]
declare Two_M_Three_zero[wrule]
declare Zero_M_Three_suc[wrule]
declare One_M_Three_suc[wrule]
declare Two_M_Three_suc[wrule]

consts pre :: "N \<Rightarrow> N"
primrec
presuc[wrule]: "pre (suc n::N) = n"
pre0[wrule]: "pre 0 = 0"

lemma presucP[wrule]: "P (pre (suc (n::N))) = P n" by simp

axioms 
two_step: "\<lbrakk>P 0; P (suc 0);\<And>m. P m \<Longrightarrow> P
(suc (suc m))\<rbrakk> \<Longrightarrow> P n"

three_step: "\<lbrakk>P 0; P (suc 0); P (suc(suc 0)); \<And>m. P m \<Longrightarrow> P
(suc(suc (suc m))) \<rbrakk> \<Longrightarrow> P n"

end;
