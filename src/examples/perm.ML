(* INCOMPLETE/TEMPORARY *)

subsection {* Definition of Permutation *} 

text {* Note, it's handy to add permutation definition to our simpset *}

consts
  perm:: "nat list => nat list => bool"
defs 
  perm_def: "perm l1 l2 == insort l1 = insort l2"

text {* testing: *}

lemma "perm [0, 1, (2::nat)] [0, 2, (1::nat)] = True" by (simp add: perm_def);
lemma "perm [0, (0::nat)] [0, 2, (1::nat)] = False" by (simp add: perm_def);

subsection {* Proofs for permutation: *} 

theorem perm_commut: "perm l2 l1 = perm l1 l2"
apply (auto simp add: perm_def)
done

theorem perm_trans: "perm l1 l2 & perm l2 l3 ==> perm l1 l3"
apply (simp add: perm_def)
done

lemma perm_append_order: "ins b (ins a l) = ins a (ins b l)"
apply (induct l)
apply auto
done

lemma perm_append_lemma1:
  "(insort (bs @ a # as)) = ins a (insort (bs @ as))"
apply (induct bs)
apply (auto simp add: perm_append_order)
done

theorem perm_append: "ALL l2. perm (l1 @ l2) (l2 @ l1)"
apply (simp add: perm_def)
apply (induct l1)
apply (auto simp add: perm_append_lemma1)
done


theorem perm_sorted: "perm (insort l) l"
apply (simp add: perm_def t1 t2)
done

theorem perm_is_sort_eq: "perm l1 l2 = (insort l1 = insort l2)"
apply (simp add: perm_def)
done

subsection {* Definition of Merge f Function *}

text {* A less computationally efficient version of merge, but which
is easier prove properties for. *}

consts
  merge2 :: "nat list => nat list => nat list"
primrec
  "merge2 [] l = l"
  "merge2 (a#as) l = merge2 as (ins a l)"


text {* testing: *}

lemma "merge2 [(0::nat), 3, 5] [1,2,(9::nat)] = 
  [(0::nat), 1, 2, 3, 5 ,(9::nat)]"
by simp;

subsection {* Proofs for the merge function *}

theorem merge_keeps_sorted: 
  "ALL bl. sorted al & sorted bl ==> sorted (merge2 al bl)"
apply (induct al)
apply auto
done

lemma insort_merge_lemma [simp]: "sorted (merge2 (insort al) (insort bl))"
apply (simp add: merge_keeps_sorted t1)
done

lemma listlem1: "l1 @ (a # l) = (l1 @ [a]) @ l"
by auto

lemma perm_merge_append_l2: 
  "insort (l1 @ a # aa # list) = insort (l1 @ aa # a # list)"
apply (induct l1)
apply (auto simp add: perm_append_order)
done

lemma perm_merge_append_l1: 
  "ALL l1. insort (l1 @ (ins a l2)) = insort (l1 @ (a # l2) )"
apply (induct "l2")
apply auto
apply (rule perm_merge_append_l2[THEN subst])
apply (rule listlem1[THEN ssubst])
apply (rule_tac "l1" = "ins a list" in listlem1[THEN ssubst])
apply (auto simp del: append_assoc)
done

lemma perm_merge_append: "ALL l2. perm (merge2 l1 l2) (l1 @ l2)"
apply (simp add: perm_def)
apply (induct "l1")
apply simp
apply (rule allI)
apply (simp add: perm_merge_append_l1 perm_append_lemma1)
done

lemma insort_ins_append2 [simp]: 
  "insort ((ins a al) @ bl) = insort ((a # al) @ bl)"
apply (induct "al")
apply simp
apply (simp add: perm_append_order)
done

lemma insert_append_lemma [simp]: 
  "insort ((insort al) @ (insort bl)) = insort (al @ bl)"
apply (induct al)
apply (simp add: t1 t2)
apply (simp add: t1 t2 perm_merge_append_l1)
done

(* same as perm equilalent proved above *)
lemma merge_insert_rel_lem1 [simp]: 
  "\<forall> l2. insort (merge2 l1 l2) = insort (l1 @ l2)"
apply (induct "l1")
apply simp
apply (rule allI)
apply (simp add: perm_merge_append_l1 perm_append_lemma1)
done

lemma sorted_imp_eq_insort [simp]: "sorted l ==> insort l = l"
apply (simp add: t2)
done

lemma perm_and_sorted_imp_insort_eq: 
  "[| perm (insort l2) l1; sorted l1 |] ==> l1 = (insort l2)"
apply (simp add: perm_def t1 t2)
done

theorem merge_insert_rel: "merge2 (insort al) (insort bl) = insort (al @ bl)"
apply (rule perm_and_sorted_imp_insort_eq)
apply (simp add: perm_def t1 t2)
apply (simp add: insort_merge_lemma)
done

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


section {* Part 3 : sequences and subsequences *}

consts subseqnow :: "nat list => nat list => bool"
primrec
  subseqnow_Nil:  "subseqnow [] l = True"
  subseqnow_Cons: "subseqnow (h#t) l = (if l = [] 
    then False 
    else ((h = hd l) & (subseqnow t (tl l))))"

consts subseq :: "nat list => nat list => bool" 
primrec
  subseq_Nil:  "subseq l [] = (if l = [] then True else False)"
  subseq_Cons: "subseq l (h#t) = (subseqnow l (h#t) | (subseq l t))"

lemma subseqnow_nil2 [simp]: "(subseqnow l []) = (l = [])"
apply (induct l)
apply auto
done

lemma subseqnow_id [simp]: "(subseqnow l l)"
apply (induct l)
apply auto
done


lemma subseqnow_imp_eq1: "ALL b. subseqnow a b & subseqnow b a ==> (a = b)"
apply (induct "a")
apply simp
apply clarify
apply (case_tac "b")
apply simp
apply simp
done

lemma [simp]: "ALL b. (subseqnow a b & subseqnow b a) = (a = b)"
apply (induct "a")
apply (simp, blast)
apply clarify
apply (case_tac "b")
apply simp
apply simp
apply clarify
apply blast
done


lemma subseqnow_eq [simp]: "(subseqnow a b & subseqnow b a) = (a = b)"
apply simp
done

(* 
lemma [simp]: "ALL b. length a = length b & subseqnow a b ==> (a = b)"
apply (induct "a")
apply simp
apply (rule allI)
apply (case_tac "b")
apply simp
oops
*)

lemma subseqnow_len1: "ALL b. ((length b) < (length a)) ==> (~ (subseqnow a b))"
apply (induct "a")
apply simp
apply (rule allI)
apply (case_tac "b")
apply simp
apply simp
done

(*
lemma subseqnow_len2: "ALL b. (subseqnow a b) ==> (~ (length b) < (length a))"
apply (induct "a")
apply simp
apply (rule allI)
apply simp
apply (case_tac "b")
apply simp
apply simp
done
*)
 
(* casn use earlier result as below , or prove the whole thing as above*)
lemma subseqnow_len2: "(subseqnow a b) ==> (~ (length b) < (length a))"
apply clarify
apply (cut_tac subseqnow_len1)
apply blast
done



lemma subseq_len1: "ALL a. (length b) < (length a) ==> ~ (subseq a b)"
apply (induct "b")
apply simp
apply (rule allI)
apply clarify
apply (simp add: subseqnow_len1)
done

(*lemma subseq_len2: "(length b) < (length a) ==> ~ (subseq a b)"
apply (simp add: subseq_len1)
done
*)

(* instead of rerunning the proof, as we did above we can use the previosu proof *)
lemma subseq_len2: "(subseq a b) ==> (~ (length b) < (length a))"
apply clarify
apply (cut_tac subseq_len1)
apply blast
done


lemma "(a = b) ==> (subseq a b & subseq b a)"
apply (induct "a")
apply auto
done



lemma my_re_fiddle_lemma: 
  "((a & b & d) | (a & b & e) | (c & a & d) | (c & e)) =
   ((a & b | c) & (a & d | e))" by blast

lemma my_or_split_lemma: "[| (P a); (P b) |] ==> (P (a | b))"
apply (case_tac "b")
apply auto
done


lemma my_re_fiddle_lemma2: 
  "[| ((c & e) = False); ((c & a & d) = False); ((a & b & e) = False) |] ==> 
  (a & b & d) = ((a & b & d) | (a & b & e) | (c & a & d) | (c & e))" 
by blast


theorem "ALL b. (subseq a b & subseq b a) = (a = b)"
apply (induct "a")
apply (simp, blast)
apply clarify
apply (case_tac "b")
apply simp
apply clarify
apply simp
apply (rule_tac x1=aa in eq_sym_conv[THEN ssubst])
apply (rule my_re_fiddle_lemma[THEN subst])
apply (rule my_re_fiddle_lemma2[THEN subst])
apply (cut_tac a="aa # lista" and b="list" in subseq_len2)
apply (cut_tac a="a # list" and b="lista" in subseq_len2)
apply (rule iffI)
apply simp
apply simp
apply (cut_tac a=lista and b=list in subseqnow_len2)
apply (cut_tac a="a # list" and b=lista in subseq_len2)
apply (rule iffI)
apply clarify
apply simp
apply clarify
apply (cut_tac a=list and b=lista in subseqnow_len2)
apply (cut_tac b="list" and a="aa # lista" in subseq_len2)
apply (rule iffI)
apply clarify
apply simp
apply clarify
apply simp
done
