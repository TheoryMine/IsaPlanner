theory test 
imports Main  
begin

ML {* set quick_and_dirty; *}

consts morel :: "nat => nat list => nat list"
primrec 
morel_Nil:  "morel n [] = []"
morel_Cons: "morel n (h # t) = (if n < h then (h # (morel n t))
                                 else morel n t)"

consts lessl :: "nat => nat list => nat list"
primrec
lessl_Nil:  "lessl n [] = []"
lessl_Cons: "lessl n (h # t) = (if n < h then (lessl n t)
                                 else  (h # (lessl n t)))"

lemma leq_trans: "[| x <= (y :: nat); y <= z |] ==> x <= z"
sorry;
(* SetInterval.greaterThan_subset_iff[symmetric]) *)

lemma le_leq: "x < y ==> x <= (y :: nat)"
sorry;

lemma le_leq_trans: "[| x < y; y <= z  |] ==> x < (z :: nat)"
sorry;



lemma lengthmorel[simp]: "length (morel h t) < Suc (length t)"
sorry

lemma lengthlessl[simp]: "length (lessl h t) < Suc (length t)"
sorry

consts smallest :: "nat => nat list => nat"
primrec 
smallest_nil:  "smallest n [] = n"
smallest_cons: "smallest n (h # t) = 
    (if h < n then smallest h t else smallest n t)"

lemma smallest_leq[simp]: "smallest n t <= n"
sorry

lemma smallest_swap: "smallest n (h # t) = smallest h (n # t)"
sorry 

lemma smallest_swap_cons: "smallest n (h # h2 # t) = smallest n (h2 # h # t)"
sorry 

lemma smallest_cons_leq: "smallest n (h # t) <= h"
sorry

lemma smallest_cons_same[simp]: "smallest n (n # t) = smallest n t"
sorry

lemma smallest_sametl: "a <= b ==> smallest a t <= smallest b t"
sorry

lemma smallest_le_cons: "smallest n (h # t) <= smallest n t"
sorry

lemma smallest_insert: "a <= b ==> smallest a t = smallest a (b # t)"
sorry

lemma leq_smallest_eq: "a <= smallest h t ==> (smallest a (h#t) = a)"
sorry




consts biggest :: "nat => nat list => nat"
primrec 
biggest_nil:  "biggest n [] = n"
biggest_cons: "biggest n (h # t) = 
    (if n < h then biggest h t else biggest n t)"


consts all_less :: "(nat list \<times> nat list) => bool"
recdef all_less "(measure size)"
all_less_nil1: "all_less ([], l2) = True"
all_less_nil2: "all_less (l1, []) = True"
all_less_cons: "all_less (h#t, h2#t2) = ((biggest h t) < (smallest h2 t2))"

consts all_lesseq :: "(nat list \<times> nat list) => bool"
recdef all_lesseq "(measure size)"
all_lesseq_nil1: "all_lesseq ([], l2) = True"
all_lesseq_nil2: "all_lesseq (l1, []) = True"
all_lesseq_cons: "all_lesseq (h#t, h2#t2) = ((biggest h t) <= (smallest h2 t2))"

consts ord :: "nat list => bool"
recdef ord "measure size"
ord_nil: "ord [] = True"
ord_one: "ord [h] = True"
ord_cons: "ord (h1#h2#t) = ((h1 <= h2) \<and> ord (h2 # t))"

lemma ord_cons_le: "ord (h1#h2#t) ==> (h1 <= h2)"
sorry

lemma ord_cons_cons: "ord (h1#h2#t) ==> ord (h2 # t)"
sorry

lemma ord_tlord: "ord (h#t) ==> ord t"
sorry

lemma all_lesseq_hd_smallest[simp]: 
  "all_lesseq ([a], x # xs) = (a <= smallest x xs)"
sorry

lemma allesseq_as_smallest: "all_lesseq ([aa], xs) = (smallest aa xs = aa)"
sorry

lemma ord_imp_lesseq: "ord (a # xs) ==> all_lesseq ([a], xs)"
sorry

lemma "[| smallest a ys = a; ord ys  |] ==> ord (a # ys)"
sorry

lemma "all_lesseq (a # xs, ys) = (all_lesseq([a], ys) & all_lesseq(xs, ys))" 
oops

lemma ord_append: "[| ord xs; ord ys; all_lesseq (xs, ys)  |] ==>
  ord (xs @ ys)"
sorry

lemma ord_append_cons: 
  assumes ord_xs: "ord xs" 
  and ord_ys: "ord ys"
  and le1: "all_lesseq ([h], ys)" 
  and le2: "all_lesseq (xs, h#ys)"
  shows "ord (xs @ (h#ys))"
sorry

lemma ord_append_rule: "ord (xs @ ys) = (ord xs \<and> ord ys \<and> all_lesseq (xs, ys))"
sorry

consts ord2 :: "nat list => bool"
primrec
ord2_nil: "ord2 [] = True"
ord2_one: "ord2 (h#t) = 
  (case t of [] => True 
           | h2 # t2 => ((h < h2) \<and> ord2 t))"


consts remove :: "nat => nat list => nat list"
primrec 
  remove_nil: "remove x [] = []"
  remove_cons: "remove x (h # t) = (if x = h then t else h # (remove x t))"


consts perm :: "nat list => nat list => bool"
primrec 
perm_nil:   "perm [] l = (l = [])"
perm_cons:  "perm (h#t) l = perm t (remove h l)"

constdefs sorts :: "(nat list => nat list) => bool"
sorts_def: "sorts f == (ALL l. ord (f l) \<and> perm (f l) l)"

consts qsort :: "nat list => nat list"

ML {* set show_types *}
ML {* reset show_types *}

end;