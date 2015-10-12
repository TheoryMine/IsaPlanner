(*<*)theory IJCAR_proofs = IJCAR :(*>*)

section {* Proofs *}

subsection {* @{term "rev rev x = x"} *}

(*
ML {* RippleTac.print_wrules_of_theory (the_context()); *}
ML {* trace_rippling := true; *}
ML {* set show_types; *}
*)

declare arg_cong[impwrule]

thm Nat.induct


lemma append_Nil2: "Q"
proof - 
  {
    assume "P"
    have "k @ [] = k"
    proof (ipp ri) qed

proof (induct l)
  show "[] @ [] = []" by simp
next
  fix a l
  assume indhyp: "l @ [] = l"
  thus "(a # l) @ [] = a # l" by (rippling)
qed

lemma rev_app_single: "rev (l @ [a]) = a # rev l" 
proof (induct l)
  show "rev ([] @ [a]) = a # rev []" by simp
next
  fix b l 
  assume a: "rev (l @ [a]) = a # rev l"
  thus "rev ((b # l) @ [a]) = a # rev (b # l)" by simp
qed

theorem revrev: "rev rev x = x"
proof (induct x)
  show "rev rev [] = []" by simp
next 
  fix a l
  assume indhyp: "rev rev l = l"
  show "rev rev (a # l) = a # l" 
    by (simp add: rev_app_single)
qed



subsection {* Nats *}

theorem N_add0_right: "x + 0 = x" by (induct "x", simp_all)
theorem N_addS_right: "x + (S y) = S(x + y)" by (induct "x", simp_all)

subsection {* Length *}

theorem [rule_format]: "ALL y. len (zip x y) = len x + len y"
apply (induct x)
apply simp
apply simp
apply clarify
apply (case_tac "y")
apply (simp add: N_add0_right)
apply (simp add: N_addS_right)
done

theorem "len x = 0 \<Longrightarrow> x = []"
apply (cases "x")
apply simp
apply simp
done

subsection {* Zip and Length *}

theorem "ALL b x y. ((len x = len a) & (len y = len b) --> 
         (zip (a @ b) (x @ y)) = ((zip a x) @ (zip b y)))"
apply (induct a)
(* base case *)
  apply clarify
  apply simp
  apply (case_tac "x")
  apply simp
  apply simp
(* step case *)
  apply clarify
  apply (case_tac "x")
  apply simp
  apply simp
done

theorem "((len x = len a) & (len y = len b) --> 
         (zip (a @ b) (x @ y)) = ((zip a x) @ (zip b y)))"
apply (induct "x" "a" rule: zip2.induct)
apply (clarify, simp)+
done

(*
subsection {* Rotate and Length *}

theorem rot_len: "rot(len l, l) = l"
proof(rule N.induct[of _ "len l"])
oops

subsection {* Zip2 and Length *}

theorem "\<lbrakk>len a = len x; len b = len y\<rbrakk> 
     \<Longrightarrow> zip2 (a @ b, x @ y) = (zip2 (a, x)) @ (zip2 (b,y))"
proof (rule zip2.induct)
sorry
*)

end;