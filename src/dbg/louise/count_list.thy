theory count_list
imports Main IsaP
begin

consts
  count_list :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
                                                                           
      
primrec
  count_list_nil [wrule] : "count_list a [] = 0"
  count_list_cons [wrule]: "count_list a (h#xs) = (if a=h then (Suc (count_list a xs)) else (count_list a 
xs))" 

(* theorem not_mem_cons_list [fwd_impwrule]: "~ (x mem (h # t)) ==> ~ (x mem t)"
by (cases "x = h", simp_all) *)


theorem not_eq_or_mem_cons_list [fwd_impwrule]: "~ (x mem (h # t)) ==> ~(x = h) & ~ (x mem t)"
by (cases "x = h", simp_all)

theorem drop_and_l [fwd_impwrule]: "A & B ==> A" by blast

theorem drop_and_r [fwd_impwrule]: "A & B ==> B" by blast

theorem app_nil [wrule]: "[] @ l = l" by simp

theorem app_cons [wrule]: "((h#t) @ l) = (h#(t @ l))" by simp

consts 
  sub_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"

primrec 
   sub_list_nil: "sub_list l [] = (if (l = []) then True else False)"
   sub_list_cons: "sub_list l (h#t) = (case l of
	[] => True 
	| (h1#t1) => (if (h1 = h) then (sub_list t1 t) else (sub_list l t)))"

theorem tl_cons [wrule]: "(tl (h # t)) = t" by simp

theorem sub_list_list[simp]: "sub_list list list" by (induct list, simp_all)


(*
theorem sub_list_tl[simp]: "sub_list (tl list) list" 
proof (induct list, simp_all)
fix a list
  assume ih: "sub_list (tl list) list"
  from this show "case list of [] => True
           | h1 # t1 =>
               (h1 = a --> sub_list t1 list) &
               (h1 ~= a --> sub_list list list)"
		proof (cases list, simp_all)
			fix aa lista
      assume ih2: "case lista of [] => True
          | h1 # t1 =>
              if h1 = aa then sub_list t1 lista else sub_list lista lista"
			from this show "(aa = a) -->
           (case lista of [] => True
            | h1 # t1 =>
                ((h1 = a) --> sub_list t1 lista) &
                (h1 ~= a --> sub_list lista lista))"
				proof (rule impI)

by (induct_tac list, simp_all)


theorem sub_list_nil[simp]: "(sub_list l []) = (l = [])" by (cases "l = []", simp_all)

theorem sub_list_nil2[simp]: "(sub_list [] l)" by (induct_tac l, simp_all)
*)
(*
theorem sub_list_tlb: "sub_list l1 l2 ==> sub_list l1 (l2@l3)"
proof (induct l2, simp_all)
assume bhyp: "if l1 = [] then True else False"
from this show "sub_list l1 l3" by (cases "l1 = []", simp_all)
next
	fix a l2


*)
end