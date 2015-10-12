theory IJCAR2008
imports Main
begin


section {* PROBLEM 1: distributivity of union over intersection. *}

text {* Signatures for basic set theory predicates and functions. *}

consts "iin" :: "'i => ('i => bool) => bool"
consts "intersection" :: "('i => bool) => ('i => bool) => ('i => bool)"
consts "union" :: "('i => bool) => ('i => bool) => ('i => bool)"

defs iin_def: "iin == % X S. S X"
defs intersection_def: "intersection == % S1 S2 U. (iin U S1) & (iin U S2)"
defs union_def: "union == % S1 S2 U. (iin U S1) | (iin U S2)"

text {* Distributivity of union over intersection *}

theorem distr: "union A (intersection B C) = 
  intersection (union A B) (union A C)"
(* apply (simp add: iin_def intersection_def union_def mem_def) *)
(* apply (metis iin_def intersection_def union_def) *)
apply (auto simp add: iin_def intersection_def union_def mem_def)
done

text {* More set examples... *}

theorem union_assoc: "union A (union B C) = 
  union (union A B) C"
apply (auto simp add: iin_def intersection_def union_def mem_def)
done

theorem intersection_assoc: "intersection A (intersection B C) = 
  intersection (intersection A B) C"
apply (auto simp add: iin_def intersection_def union_def mem_def)
done


section {* PROBLEM 2: Puzzle *}

definition
  xor :: "bool => bool => bool" (infix "xor" 30) where
  "P xor Q == P & ~Q | ~P & Q"

lemma xorI1[intro]: "P ==> (Q ==> False) ==> P xor Q"
  by (auto simp add: xor_def)

lemma xorI2[intro]: "(P ==> False) ==> Q ==> P xor Q"
  by (auto simp add: xor_def)

lemma xorE[elim]: "P xor Q ==> (P ==> (Q ==> False) ==> R) ==> ((P ==> False) ==> Q ==> R) ==> R"
  by (auto simp add: xor_def)

typedecl person 
typedecl kind
consts islander :: "person"
consts is_a :: "person => kind => bool"
consts knight :: "kind"
consts knave :: "kind"
consts zoey :: "person"
consts mel :: "person"
consts says :: "person => bool => bool"

lemma natural_puzzle:
  assumes kk_6_1: "ALL X. (is_a X knight) xor (is_a X knave)"
  and kk_6_2: "ALL X. is_a X knight --> (ALL A. says X A --> A)"
  and kk_6_3: "ALL X. is_a X knave --> (ALL A. says X A --> ~ A)"
  and kk_6_5: "says zoey (is_a mel knave)"
  and kk_6_6: "says mel (~ (is_a zoey knave | is_a mel knave))"
  shows "EX Y Z. is_a mel Y & is_a zoey Z"
  using kk_6_1 kk_6_2 kk_6_3 kk_6_5 kk_6_6 xor_def
  term says
  term is_a
  term knight
  term zoey
  by metis

text {* Sujective Cantor Theorem *}

lemma surjectiveCantor: "~ (EX G :: 'a => 'a => bool. ALL F. EX X. G X = F)"
  by best

lemma surjectiveCantor: "~ (EX G :: 'a => 'a => bool. ALL F. EX X. G X = F)"
apply auto
oops

lemma surjectiveCantor: "~ (EX G :: 'a => 'a => bool. ALL F. EX X. G X = F)"
apply simp
oops

lemma surjectiveCantor: "~ (EX G :: 'a => 'a => bool. ALL F. EX X. G X = F)"
(* apply metis -- metis quickly fails: *** Metis: No first-order proof with the lemmas supplied *)
oops

lemma surjectiveCantor: "~ (EX G :: 'a => 'a => bool. ALL F. EX X. G X = F)"
(* apply blast -- I give up after a few 10 seconds *)
oops




end
