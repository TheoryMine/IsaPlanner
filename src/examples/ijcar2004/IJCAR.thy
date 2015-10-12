(*<*)theory IJCAR = PreList + HOL_IsaP :(*>*)
section {* The Datatype Definitions *}

text {* We use Isabelle's recursive datatype package to define natural
numbers and lists.  *}

datatype N = NZero  ("0\<^isub>N")
           | NSuc N ("S\<^isub>N _" [500] 500)
syntax
  "_S"     :: "N => N" ("S _" [500] 500)
translations
  "0" == "0\<^isub>N"
  "S x" == "S\<^isub>N x"

declare N.inject[wrule]

text {* These syntax translation allow the use of @{text "0"} and
@{text "S"} while avoiding conflicts with Isabelle's internal theory of
natural numbers. *}

datatype 'a List = Nil ("[]") 
                 | Cons "'a" "'a List"      (infixr "#" 490)
syntax
  "@list"     :: "args => 'a List"                          ("[(_)]")
translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

(* declare List.inject[wrule] *)

text {* The above syntax translation(s) for lists allows us to use @{text
"#"} as an infix symbol for @{text "Cons"} and to abbreviate @{text "x
# y # z # []))"} as @{text "[x,y,z]"}. *}


section {* Functions Definitions *}

text {* Given these definitions we can now define the usual functions. *}

consts NAdd :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "+\<^isub>N" 510)
translations "x + y" == "x +\<^isub>N y" 
primrec 
  NAdd_0[wrule]: "0 + n = n"
  NAdd_S[wrule]: "S m + n = S (m + n)"

consts NMult :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "*\<^isub>N" 510)
translations "x * y" == "x *\<^isub>N y" 
primrec 
  NMult_0[wrule]: "0 * n = 0"
  NMult_S[wrule]: "S m * n = n + (m * n)"

consts NEven :: "N \<Rightarrow> bool" ("even _" [520] 520)
recdef NEven "measure size"
  NEven_0[wrule]:       "even 0 = True"
  NEven_not_S_0[wrule]: "even (S 0) = False"
  NEven_S_S[wrule]:     "even (S S n) = even n"

consts len :: "'a List \<Rightarrow> N"   ("len _" [500] 500)
primrec 
  len_Nil[wrule]:     "len [] = 0"
  len_Cons[wrule]:    "len (h # t) = S (len t)"

consts append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" (infixl "@" 500)
primrec 
  append_0[wrule]      : "[] @ l = l"
  append_Cons[wrule]   : "(h # t) @ l = h # (t @ l)"

consts rev :: "'a List \<Rightarrow> 'a List"   ("rev _" [510] 510)
primrec 
  rev_Nil[wrule]: "rev [] = []"
  rev_Cons[wrule]: "rev (h # t) = rev t @ [h]"

consts qrev :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" ("qrev _ _" [510,510] 510)
primrec 
  qrev_Nil[wrule]:  "qrev [] l = l"
  qrev_Cons[wrule]: "qrev (h # t) l = qrev t (h # l)"

consts rot :: "N \<times> 'a List \<Rightarrow> 'a List"   ("rot _" [505] 505)
recdef rot "measure (size o fst)"
  rot_0[wrule]:   "rot (0, l) = l"
  rot_Nil[wrule]: "rot (n, []) = []"
  rot_S[wrule]:   "rot (S n, h # t) = rot (n, t @ [h])"


consts zip :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List"   ("zip _ _" [505] 505)
primrec
  zip_Nil[wrule]:  "zip [] ys = ys"
  zip_Cons[wrule]: "zip (x # xs) ys = 
    (case ys of [] \<Rightarrow> x # xs | (y # ys) \<Rightarrow> x # y # (zip xs ys))"

consts zip2 :: "'a List \<times> 'a List \<Rightarrow> 'a List"   ("zip2 _" [505] 505)
recdef zip2 "measure (size o fst)"
  zip2_Nil1[wrule]: "zip2 ([], ys) = ys"
  zip2_Nil2[wrule]: "zip2 (xs, []) = xs"
  zip2_Cons[wrule]: "zip2 (x#xs, y#ys) = x # y # (zip2(xs,ys))"


section {* Induction Rules *}

text {* Isabelle automatically generates induction rules for recursive
  datatypes and recursive functions.  The name of the induction rule
  is the datatype/function name concatenated onto ``.induct''. For
  example, the following induction rules have been automatically
  derived from the above definitions:

\subsubsection*{@{text "N.induct"}}
@{thm [display] N.induct}

\subsubsection*{@{text "List.induct"}}
@{thm [display] List.induct}

\subsubsection*{@{text "rot.induct"}}
@{thm [display] rot.induct}

\subsubsection*{@{text "NEven.induct"}}
@{thm [display] NEven.induct}

The default rule used by Isabelle's induction tactic is the one
associated with the definition of the data type.
*}
(*<*)
end;(*>*)

