theory sorting
imports Main IsaP
begin 
section {* Insertion Sorting  *}

text {* Insert-Sort Algorithm *}

fun ins where 
  ins_nil: "ins x [] = [x]"
| ins_cons: "ins x (y#ys) = (if x <= y then (x#y#ys) else y#(ins x ys))"

lemmas ins_defs[wrule] = ins_nil ins_cons

fun insort where
  insort_nil: "insort [] = []"
| insort_cons: "insort (x#xs) = ins x (insort xs)"

lemmas insort_defs[wrule] = insort_nil insort_cons

subsection {* Definition of sorted *} 

fun sorted:: "nat list => bool" where
  sorted_nil: "sorted [] = True"
| sorted_cons: 
   "sorted (x#xs) = 
    ((case xs of [] => True 
              | x2#x2s => (x <= x2)) & (sorted xs))"
;
lemmas sorted_defs[wrule] = sorted_nil sorted_cons

(* Minor varient...
fun sorted2:: "nat list => bool" where
  sorted2_nil: "sorted2 [] = True"
| sorted2_cons: 
   "sorted2 (x#xs) = 
    (case xs of [] => True 
          | x2#x2s => ((x <= x2) & (sorted (x2#x2s))))"
;
lemmas sorted2_defs[wrule] = sorted2_nil sorted2_cons
*)


text {* Testing: *}

lemma "sorted [0, 1, (2::nat)] = True"
by simp;

lemma "sorted [0, 2, (1::nat)] = False"
by simp;

text {* Proofs that insort results in a sorted list *}

(* IMPROVE: change wrule flag to do all wave rule kinds:
currently: below can be impwrule, but not wrule. *)
lemma sorted_ins [simp]: "sorted l ==> sorted (ins a l)"
apply (induct l)
apply simp
apply (case_tac "l")
apply simp+
done

theorem sorted_insort: "sorted (insort l)"
apply (induct l)
apply simp
apply simp -- "may add: l1 "
done

text {* proof 2: *}

lemma l2: "sorted (a#l) ==> (ins a l) = a#l"
apply (induct l) 
apply simp
apply (case_tac "l")
apply simp+
done

theorem t2: "sorted l ==> (insort l) = l"
apply (induct l)
apply simp
apply (simp add: l2)
done

(* 
theorem insert_insort [simp]: "insort (insort l) = (insort l)"
apply (simp add: t1 t2)
done
*)

fun memb where 
  memb: "memb x [] = False"
| memb_cons: "memb x (h#t) = ((x = h) | memb x t)"

fun perm where 
  perm: "perm l1 l2 = (ALL x. (memb x l1 = memb x l2))"

lemma "perm l1 l2 = (insort l1 = insort l2)"
sorry 

lemma "perm l (insort l)"
sorry

end