theory T_6
imports IsaP 
uses "../myrippling.ML"
begin

datatype "T_6" =  "C_12" "T_6" "HOL.bool"  | "C_11" "HOL.bool" "HOL.bool"  
declare nat.inject[wrule]

fun f_0 :: "T_6 => nat => nat" where
  "f_0 (C_11 a b) c = c"
| "f_0 (C_12 a b) c = Suc (f_0 a c)"

fun f_1 :: "T_6 => nat => nat" where
  "f_1 (C_11 a b) c = Suc c"
| "f_1 (C_12 a b) c = Suc (Suc (f_1 a (Suc c)))"

fun f_2 :: "T_6 => nat => nat" where
  "f_2 (C_11 a b) c = Suc (Suc c)"
| "f_2 (C_12 a b) c = Suc (f_2 a (Suc (f_2 a c)))"

fun f_3 :: "T_6 => nat => nat" where
  "f_3 (C_11 a b) c = Suc (Suc (Suc c))"
| "f_3 (C_12 a b) c = Suc (Suc (f_3 a (f_3 a (Suc c))))"

fun f_4 :: "T_6 => nat => nat" where
  "f_4 (C_11 a b) c = Suc (Suc (Suc (Suc (Suc c))))"
| "f_4 (C_12 a b) c = f_4 a (f_4 a (Suc c))"

fun f_5 :: "T_6 => nat => nat" where
  "f_5 (C_11 a b) c = Suc (Suc (Suc (Suc (Suc (Suc c)))))"
| "f_5 (C_12 a b) c = f_5 a (Suc (Suc (f_5 a (Suc c))))"

fun f_6 :: "T_6 => nat => nat" where
  "f_6 (C_11 a b) c = Suc (Suc (Suc (Suc (Suc (Suc (Suc c))))))"
| "f_6 (C_12 a b) c = Suc (f_6 a (Suc c))"

declare f_0.simps[wrule]
declare f_1.simps[wrule]
declare f_2.simps[wrule]
declare f_3.simps[wrule]
declare f_4.simps[wrule]
declare f_5.simps[wrule]
declare f_6.simps[wrule]

ML{* my_rippling @{context} ["Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))"]*}

ML{* my_rippling @{context} ["f_5 c (f_5 a b) = f_5 a (f_5 c b)"] *}
(*


 (* theorems proven for function: f_0*)
lemma [wrule]: "f_0 a (f_0 b c) = f_0 b (f_0 a c)"
sorry

lemma [wrule]: "f_0 a (Suc b) = Suc (f_0 a b)"
sorry

lemma [wrule]: "Suc (f_0 a b) = f_0 a (Suc b)"
sorry



 (* theorems proven for function: f_1*)
lemma [wrule]: "f_1 a (Suc b) = Suc (f_1 a b)"
sorry

lemma [wrule]: "Suc (f_1 a b) = f_1 a (Suc b)"
sorry



 (* theorems proven for function: f_2*)


 (* theorems proven for function: f_3*)


 (* theorems proven for function: f_4*)


 (* theorems proven for function: f_5*)


 (* theorems proven for function: f_6*)
lemma [wrule]: "f_6 a (Suc b) = Suc (f_6 a b)"
sorry

lemma [wrule]: "Suc (f_6 a b) = f_6 a (Suc b)"
sorry

*)


ML{* val rsts = a_rippling_one_goal_timout @{context} "f_3 a (Suc b) = Suc (f_3 a b)" *}(*mult fert; breadth first needed to prevent inf lemma conj*)

ML{* 
 val (rst_list,lem) = rsts;
 val rst = (fst o the) rst_list;
 RState.print rst ;
 val thethm = SynthPrfTools.name_thrm_from_rst "g1" rst;
 val myctx = RState.get_ctxt rst;
 val newctx = SynthPrfTools.add_to_wrules thethm myctx;
*}



ML{* my_rippling @{context} ["f_6 a (f_6 b c) = f_6 b (f_6 a c)"] *}

 (* open conjectures for function: f_0*)
(*

 (* open conjectures for function: f_1*)
ML{* i_rippling @{context} ["f_1 a (f_1 b c) = f_1 b (f_1 a c)"] *}(*lemma spec; again, the lemma needed is "f_1 a (Suc b) = Suc (f_1 a b)", which is actually proved*)
ML{* i_rippling @{context} ["f_1 a (f_1 b 0) = f_1 b (f_1 a 0)"] *}(*doesn't ripple*)
ML{* i_rippling @{context} ["f_1 a (Suc 0) = Suc (f_1 a 0)"] *}(*doesn't ripple; this is a particular case of a proved lemma*)


 (* open conjectures for function: f_2*)
ML{* i_rippling @{context} ["f_2 a (f_2 b c) = f_2 b (f_2 a c)"] *}(*mult fert*)
ML{* i_rippling @{context} ["f_2 a (f_2 b 0) = f_2 b (f_2 a 0)"] *}(*gen; success will lead to mult fert*)
ML{* i_rippling @{context} ["Suc (f_2 a (Suc b)) = f_2 a (Suc (Suc b))"] *}(*mult fert; breadth first needed to prevent inf lemma conj*)
ML{* i_rippling @{context} ["Suc (f_2 a (Suc 0)) = f_2 a (Suc (Suc 0))"] *}(*gen; success will lead to mult fert. Another path leads to a failure to fertilise*)
ML{* i_rippling @{context} ["Suc (Suc (f_2 a b)) = f_2 a (Suc (Suc b))"] *}(*mult fert*)
ML{* i_rippling @{context} ["Suc (Suc (f_2 a 0)) = f_2 a (Suc (Suc 0))"] *}(*gen; success leads to mult fert. Another path leads to mult fert; this means that breadth first might be helpful*)
ML{* i_rippling @{context} ["f_2 a (Suc b) = Suc (f_2 a b)"] *}(*failure to fertilise; success will lead to mult fert*)
ML{* i_rippling @{context} ["f_2 a (Suc 0) = Suc (f_2 a 0)"] *}(*failure to fertilise; success will lead to mult fert*)
*)

 (* open conjectures for function: f_3*)
ML{* i_rippling @{context} ["f_3 a (f_3 b c) = f_3 b (f_3 a c)"] *}(*mult fert*)
ML{* i_rippling @{context} ["f_3 a (f_3 b 0) = f_3 b (f_3 a 0)"] *}(*doesn't ripple*)
ML{* i_rippling @{context} ["Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))"] *}(*case in which a 'borrowing fertilisation' (multiple) would solve the problem; otherwise it leads to inf lemma calc *) 
ML{* i_rippling @{context} ["Suc (f_3 a (Suc 0)) = f_3 a (Suc (Suc 0))"] *}(*doesn't ripple*)
ML{* i_rippling @{context} ["Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))"] *}(*mult fert*)
ML{* i_rippling @{context} ["Suc (Suc (f_3 a 0)) = f_3 a (Suc (Suc 0))"] *}(*doesn't ripple*)
ML{* i_rippling @{context} ["f_3 a (Suc b) = Suc (f_3 a b)"] *}(*mult fert*)
ML{* i_rippling @{context} ["f_3 a (Suc 0) = Suc (f_3 a 0)"] *}(*doesn't ripple*)


 (* open conjectures for function: f_4*)
ML{* i_rippling @{context} ["f_4 a (f_4 b c) = f_4 b (f_4 a c)"] *}(*mult fert*)
ML{* i_rippling @{context} ["f_4 a (f_4 b 0) = f_4 b (f_4 a 0)"] *}(*gen; success will lead to mult fert*)
ML{* i_rippling @{context} ["Suc (f_4 a (Suc b)) = f_4 a (Suc (Suc b))"] *}(*mult fert*)
ML{* i_rippling @{context} ["Suc (f_4 a (Suc 0)) = f_4 a (Suc (Suc 0))"] *}(*gen; success will lead to mult fert*)
ML{* i_rippling @{context} ["Suc (Suc (f_4 a b)) = f_4 a (Suc (Suc b))"] *}(*mult fert*)
ML{* i_rippling @{context} ["Suc (Suc (f_4 a 0)) = f_4 a (Suc (Suc 0))"] *}(*gen; success will lead to mult fert*)
ML{* i_rippling @{context} ["f_4 a (Suc b) = Suc (f_4 a b)"] *}(*mult fert*)
ML{* i_rippling @{context} ["f_4 a (Suc 0) = Suc (f_4 a 0)"] *}(*gen; success will lead to mult fert*)


 (* open conjectures for function: f_5*)
ML{* i_rippling @{context} ["f_5 a (f_5 b c) = f_5 b (f_5 a c)"] *}(*mult fert*)
ML{* i_rippling @{context} ["f_5 a (f_5 b 0) = f_5 b (f_5 a 0)"] *}(*gen; success will lead to mult fert*)
ML{* i_rippling @{context} ["Suc (f_5 a (Suc b)) = f_5 a (Suc (Suc b))"] *}(*fails to fertilise; success would lead to mult fert*)
ML{* i_rippling @{context} ["Suc (f_5 a (Suc 0)) = f_5 a (Suc (Suc 0))"] *}(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
ML{* i_rippling @{context} ["Suc (Suc (f_5 a b)) = f_5 a (Suc (Suc b))"] *}(*fails to fertilise; success would lead to mult fert*)
ML{* i_rippling @{context} ["Suc (Suc (f_5 a 0)) = f_5 a (Suc (Suc 0))"] *}(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
ML{* i_rippling @{context} ["f_5 a (Suc b) = Suc (f_5 a b)"] *}(*fails to fertilise; success would lead to mult fert*)
ML{* i_rippling @{context} ["f_5 a (Suc 0) = Suc (f_5 a 0)"] *}(*gen; success will lead to failure to fertilise, which will lead to mult fert*)


 (* open conjectures for function: f_6*)
ML{* i_rippling @{context} ["f_6 a (f_6 b c) = f_6 b (f_6 a c)"] *}(*lemma spec. We are trying to prove "Suc (f_6 d (Suc (f_6 e f))) = f_6 e (Suc (f_6 d (Suc f)))" and the usual rule would be helpful, and it is actually proved*)
ML{* i_rippling @{context} ["f_6 a (f_6 b 0) = f_6 b (f_6 a 0)"] *}(*fails to ripple*)
ML{* i_rippling @{context} ["f_6 a (Suc 0) = Suc (f_6 a 0)"] *}(*fails to ripple, but is a particular case of the usual rule*)
(*all in all, it is clear that some more simplification should happen at the beginning and in steps (like before a lemma calculation), using already proved lemmas, and stuff like that*)

end