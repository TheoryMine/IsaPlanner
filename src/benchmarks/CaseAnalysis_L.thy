header{* Some wave-rules for testing out theorems that require 
         splitting on if- or case-statements. *}

theory CaseAnalysis_L
imports Main IsaP CaseAnalysis
begin

declare List.append_Nil[wrule]
declare List.append_Cons[wrule]
declare List.rev.simps[wrule]
declare List.map.simps[wrule]

(* Can't have as wrule, don't think good in r-to-l order. *)
(* declare o_def[wrule] *)

(* Uses if *)
declare List.member.simps[wrule]
declare List.last.simps[wrule]
declare List.butlast.simps[wrule]

declare List.filter.simps[wrule]

declare List.takeWhile.simps[wrule]
declare List.dropWhile.simps[wrule]


fun delete :: "'a => 'a list => 'a list"
where
	  del_nil: "delete x [] = []"
	| del_cons: "delete x (y#ys) = (if (x=y) then (delete x ys) else y#(delete x ys))"
declare del_nil[wrule]
declare del_cons[wrule]
	
(* Would need own def, with our leq 
declare List.upt_0[wrule]
declare List.upt_Suc[wrule]
*)

(* Uses case *)
fun drop :: "nat => 'a list => 'a list" 
where
	drop_Nil:"drop n [] = []"
	|	drop_Cons: "drop n (x#xs) = (case n of 0 => x#xs | Suc(m) => drop m xs)"
declare drop_Nil[wrule]
declare drop_Cons[wrule]

fun take :: "nat => 'a list => 'a list"
where
 	take_Nil:"take n [] = []"
  | take_Cons: "take n (x#xs) = (case n of 0 => [] | Suc(m) => x # take m xs)"
declare take_Nil[wrule]
declare take_Cons[wrule]

(*fun nth :: "nat => 'a list => 'a"
where
  nth_Cons:"nth n (x#xs) = (case n of 0 => x | (Suc k) => nth k xs)"
declare nth_Cons[wrule]
*)
fun zip :: "'a list => 'a list => ('a * 'a) list"
where
	zip_nil: "zip xs [] = []"
  | zip_Cons: "zip xs (y#ys) = (case xs of [] => [] | z#zs => (z,y)#zip zs ys)"
declare zip_nil[wrule]
declare zip_Cons[wrule]

fun len :: "'a list => nat"   ("len _" [500] 500)
where
  len_nil:     "len [] = 0" |
  len_cons:    "len (h # t) = Suc (len t)"
declare len_nil[wrule]
declare len_cons[wrule]

fun ins :: "nat => (nat list) => (nat list)" 
where	
	insert_nil: "ins n [] = [n]" |
	insert_cons: "ins n (h#t) = (if (n less h) then n#h#t else h#(ins n t))"
declare insert_nil[wrule]
declare insert_cons[wrule]

(* Like insertion in set, only allows one of each element *)
fun ins_1 :: "'a => ('a list) => ('a list)" 
where
	ins_1_nil: "ins_1 n [] = [n]" |
	ins_1_cons: "ins_1 n (h#t) = (if n=h then (n#t) else h#(ins_1 n t))"
declare ins_1_nil[wrule]
declare ins_1_cons[wrule]

fun count :: "'a => 'a list => nat"
where
		count_nil[simp]: "count x [] = 0" |
		count_cons[simp]: "count x (y#ys) = (if (x=y) then (Suc(count x ys)) else (count x ys))"
declare count_nil[wrule]
declare count_cons[wrule]

(* 
fun sorted :: "nat list => bool" 
where
		sorted_nil: "sorted [] <-> True" |
		sorted_single: "sorted [x] <-> True" |
		sorted_cons: "sorted (x#y#zs) <-> (x leq y) & sorted (y#zs)"
*)

fun sorted :: "nat list => bool" 
where
		sorted_nil: "sorted [] = True" |
		sorted_cons: "sorted (x#xs) = 
      (case xs of [] => True 
       | (y#ys) => (x leq y) & sorted (y#ys))"

fun insort :: "nat => nat list => nat list" where
		insort_nil: "insort x [] = [x]" |
		insort_cons: "insort x (y#ys) = (if (x leq y) then (x#y#ys) else y#(insort x ys))"

fun sort :: "nat list => nat list" where
		sort_nil: "sort [] = []" |
		sort_cons: "sort (x#xs) = insort x (sort xs)"
declare sorted_nil[wrule]
(* declare sorted_single[wrule] *)
declare sorted_cons[wrule]
declare insort_nil[wrule]
declare insort_cons[wrule]
declare sort_nil[wrule]
declare sort_cons[wrule]



end
