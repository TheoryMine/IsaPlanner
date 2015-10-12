header{* Some wave-rules for testing out theorems that require 
         splitting on if- or case-statements. *}

theory CaseAnalysis
imports Main IsaP
begin



(* allows new names to clobber old ones and avoid Isabelle 
   printing long names for our locally defined names *)
ML {* NameSpace.unique_names := false; *}

ML {* set quick_and_dirty; *}

(* -----------------------------*)
(* Natural Numbers              *)
(* -----------------------------*)


declare Nat.add_0[wrule]
declare Nat.add_Suc[wrule]
declare Nat.add_Suc_right[wrule]

declare Nat.mult_0[wrule]
declare Nat.mult_Suc[wrule]
declare Nat.mult_Suc_right[wrule]

lemmas nat_wrules[wrule] = Nat.diff_add_inverse
  Nat.diff_add_inverse2
  Nat.diff_cancel
  Nat.diff_cancel2
  Nat.diff_add_0
  Nat.add_is_1
  Nat.nat_add_assoc
  Nat.nat_add_left_cancel
  Nat.nat_add_left_commute
  Nat.nat_add_right_cancel
  Nat.nat_distrib


fun minus :: "nat => nat => nat" (infix "minus" 520)
where
  minus_0:     "0 minus m = 0"
  | minus_Suc: "(Suc m) minus n = (case n of 0 => (Suc m) | Suc k => m minus k)"
declare minus_0[wrule]
declare minus_Suc[wrule]

fun less :: "nat => nat => bool" (infix "less" 520)
where
  less_0  : "(x :: nat) less 0 = False" |
  less_Suc : "x less (Suc y) = (case x of 0 => True | Suc z => (z less y))"
declare less_0[wrule]
declare less_Suc[wrule]

lemma less_implies_ne[simp]: "a less b ==> b ~= a"
sorry

lemma less_implies_ne2[simp]: "a less b ==> a ~= b"
apply (induct b)
apply (simp+)
apply (cases "a")
apply (simp+)
sorry
(* FIXME: write in real proof *)

fun less_eq :: "nat => nat => bool" (infix "leq" 520)
where
  less_eq_0: "(0::nat) leq y = True" |
  less_eq_Suc:  "(Suc x) leq y = (case y of 0 => False | Suc z => (x leq z))"
declare less_eq_0[wrule]
declare less_eq_Suc[wrule]

 fun max :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
    max_0: "max 0 y = y"
  | max_suc: "max (Suc x) y = (case y of 0 => (Suc x) | Suc z => Suc(max x z))"
declare max_0[wrule]
declare max_suc[wrule]



fun min :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
    min_0: "min 0 y = 0"
  | min_suc: "min (Suc x) y = (case y of 0 => y | Suc z => Suc(min x z))"
declare min_0[wrule]
declare min_suc[wrule]

(*
subsubsection {* Difference *}

lemma diff_self_eq_0 [simp]: "(m::nat) - m = 0"
  by (induct m) simp_all

lemma diff_diff_left: "(i::nat) - j - k = i - (j + k)"
  by (induct i j rule: diff_induct) simp_all

lemma Suc_diff_diff [simp]: "(Suc m - n) - Suc k = m - n - k"
  by (simp add: diff_diff_left)

lemma diff_commute: "(i::nat) - j - k = i - k - j"
  by (simp add: diff_diff_left add_commute)

lemma diff_add_inverse: "(n + m) - n = (m::nat)"
  by (induct n) simp_all

lemma diff_add_inverse2: "(m + n) - n = (m::nat)"
  by (simp add: diff_add_inverse add_commute [of m n])

lemma diff_cancel: "(k + m) - (k + n) = m - (n::nat)"
  by (induct k) simp_all

lemma diff_cancel2: "(m + k) - (n + k) = m - (n::nat)"
  by (simp add: diff_cancel add_commute)

lemma diff_add_0: "n - (n + m) = (0::nat)"
  by (induct n) simp_all

text {* Difference distributes over multiplication *}

lemma diff_mult_distrib: "((m::nat) - n) * k = (m * k) - (n * k)"
by (induct m n rule: diff_induct) (simp_all add: diff_cancel)

lemma diff_mult_distrib2: "k * ((m::nat) - n) = (k * m) - (k * n)"
by (simp add: diff_mult_distrib mult_commute [of k])
  -- {* NOT added as rewrites, since sometimes they are used from right-to-left *}

*)
end
