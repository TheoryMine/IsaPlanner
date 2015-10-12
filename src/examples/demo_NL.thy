header{* Peano Arithmetic and Lists *}

theory demo_NL 
imports PreList IsaP
begin

ML {* set quick_and_dirty; *}

section{* Peano Arithmetic *}

datatype N = zero  ("zeroN")
           | suc N ("sucN _" [500] 500)
syntax
  "_suc"     :: "N => N" ("suc _" [500] 500)
translations
  "0" == "zeroN"
  "suc x" == "sucN x"

thm N.inject
thm N.size
thm N.recs
thm N.split
thm N.recs
thm N.cases
thm N.simps

declare N.inject[wrule]
declare N.cases[wrule]
declare N.size[wrule]

section{* Left-recrusive definitions of addition and multiplication *}

consts add :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "plusN" 509)
translations "x + y" == "x plusN y" 
primrec 
  add_0    [wrule]:  "(0 + y) = y"
  add_suc  [wrule]:  "suc x + y = suc (x + y)"

consts mult :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "multN" 509)
translations "x * y" == "x multN y" 
primrec 
  mult_0    [wrule]:  "(0 * y) = 0"
  mult_suc  [wrule]:  "(suc x) * y = y + (x * y)"

section{* Right-recrusive definitions of exponentiation. *}
consts exp :: "[N, N] => N"            (infixr "expN" 515)
translations "op ^" == "op expN"
primrec
  exp_0   [wrule]: "x ^ 0 = suc 0"
  exp_suc [wrule]: "x ^ (suc y) = x * (x ^ y)"


theorem mult_suc_right[wrule]: "x * (suc y) = x + (x * y)"; pp ri; qed


theorem "(a ^ b) ^ c = a ^ (b * c)"; ipp ri; qed

theorem "(a + b) = (b + a)"; pp ri; qed
theorem "(a + b) + c = a + (b + c)"; pp ri; qed
theorem "(a * b) * c = a * (b * c)"; pp ri; qed

section{* Right-recursive defined additiona and multiplication. *}

consts add2 :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "plusN2" 509)
translations "x + y" == "x plusN2 y" 
primrec 
  add2_0    [wrule]:  "y + 0 = y"
  add2_suc  [wrule]:  "x + (suc y) = suc (x + y)"

consts mult2 :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "multN2" 509)
translations "x * y" == "x multN2 y" 
primrec 
  mult2_0    [wrule]:  "(y * 0) = 0"
  mult2_suc  [wrule]:  "x * (suc y) = (x * y) + x"

section{* Right-recrusive definitions of exponentiation. *}
consts exp2 :: "[N, N] => N"            (infixr "expN2" 515)
translations "op ^" == "op expN2"
primrec
  exp2_0   [wrule]: "x ^ 0 = suc 0"
  exp2_suc [wrule]: "x ^ (suc y) = x * (x ^ y)"

theorem "(a ^ b) ^ c = a ^ (b * c)"; pp ri; qed


section{* more explicit definition of exponentiation. *}
consts exp3 :: "N * N => N"
term "exp3 (x,y)"
recdef exp3 "measure (size o snd)"
  exp3_0       [wrule]: "exp3 (0, y) = 0"
  exp3_suc_0   [wrule]: "exp3 (suc x, 0) = suc 0"
  exp3_suc_suc [wrule]: "exp3 (suc x, suc y) = (suc x) * exp3(suc x, y)"

theorem x: "exp3 (exp3 (a, b), c) = exp3 (a, b * c)" oops 
(* by (pp ri) -- fails because it needs to case split on the second
argument *)

section{* Less than *}

consts less :: "[N, N] => bool"            (infix "less" 520)
translations "op <" == "op less"
primrec
  less_0   [wrule]: "x < 0 = False"
  less_suc [wrule]: "x < (suc y) = (case x of 0 => True | suc z => z < y)"

lemma "a < b \<Longrightarrow> a < (b + c)" oops 
(* by (ipp ri) -- fails as we need to carry hypothesis over, and also
we need to be more careful about when we do rippling! i.e. not just
when we have assumptions *)

lemma "a < b --> a < (b + c)"  oops 
(* by (ipp ri) -- leads to a huge search space! *)

consts less2 :: "N \<times> N => bool"
recdef less2 "measure (size o snd)"
  less2_0       [wrule]: "less2(x, 0) = False"
  less2_0_suc   [wrule]: "less2(0, suc y) = True"
  less2_suc_suc [wrule]: "less2(suc x, suc y) = less2(x, y)"

lemma "less2(a,b) \<longrightarrow> less2(a, b + c)" oops 
(* by (ipp ri) -- fails quickly - needs to case split on second argument *)


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

lemma "rev (x @ y) = (rev y) @ (rev x)"; pp ri; qed

end;
