theory T_2
imports IsaP 
uses "../myrippling.ML"
begin

datatype "T_2" =  "C_4" "T_2" "HOL.bool"  | "C_3" "Nat.nat" "Nat.nat" 
declare nat.inject[wrule]

fun f_0 :: "T_2 => nat => nat" where
  "f_0 (C_3 a b) c = c"
| "f_0 (C_4 a b) c = Suc (f_0 a (Suc (f_0 a (Suc c))))"

fun f_1 :: "T_2 => nat => nat" where
  "f_1 (C_3 a b) c = Suc c"
| "f_1 (C_4 a b) c = Suc (f_1 a (f_1 a (Suc (Suc c))))"

fun f_2 :: "T_2 => nat => nat" where
  "f_2 (C_3 a b) c = Suc (Suc c)"
| "f_2 (C_4 a b) c = f_2 a (f_2 a (Suc (Suc c)))"

fun f_3 :: "T_2 => nat => nat" where
  "f_3 (C_3 a b) c = Suc (Suc (Suc c))"
| "f_3 (C_4 a b) c = Suc (f_3 a (f_3 a c))"

fun f_4 :: "T_2 => nat => nat" where
  "f_4 (C_3 a b) c = Suc (Suc (Suc (Suc c)))"
| "f_4 (C_4 a b) c = Suc (f_4 a (Suc (Suc (f_4 a c))))"

fun f_5 :: "T_2 => nat => nat" where
  "f_5 (C_3 a b) c = Suc (Suc (Suc (Suc (Suc c))))"
| "f_5 (C_4 a b) c = f_5 a (Suc (Suc (f_5 a c)))"

fun f_6 :: "T_2 => nat => nat" where
  "f_6 (C_3 a b) c = Suc (Suc (Suc (Suc (Suc (Suc c)))))"
| "f_6 (C_4 a b) c = Suc (Suc (f_6 a (Suc c)))"

fun f_7 :: "T_2 => nat => nat" where
  "f_7 (C_3 a b) c = Suc (Suc (Suc (Suc (Suc (Suc (Suc c))))))"
| "f_7 (C_4 a b) c = Suc (Suc (f_7 a (f_7 a (Suc c))))"

declare f_0.simps[wrule]
declare f_1.simps[wrule]
declare f_2.simps[wrule]
declare f_3.simps[wrule]
declare f_4.simps[wrule]
declare f_5.simps[wrule]
declare f_6.simps[wrule]
declare f_7.simps[wrule]
ML{* my_rippling @{context} ["f_0 a (Suc b) = Suc (f_0 a b)"] *}
ML{* my_rippling @{context} ["f_3 a (Suc b) = Suc (f_3 a b)"] *}


(*


 (* theorems proven for function: f_0*)


 (* theorems proven for function: f_1*)


 (* theorems proven for function: f_2*)


 (* theorems proven for function: f_3*)


 (* theorems proven for function: f_4*)


 (* theorems proven for function: f_5*)


 (* theorems proven for function: f_6*)
lemma [wrule]: "f_6 a (Suc b) = Suc (f_6 a b)"
sorry

lemma [wrule]: "Suc (f_6 a b) = f_6 a (Suc b)"
sorry


 (* theorems proven for function: f_7*)

*)

(*
 (* open conjectures for function: f_0*)
ML{* i_rippling @{context} ["f_0 a (f_0 b c) = f_0 b (f_0 a c)"] *}(*mult fert; failure leads to inf lemma calc*)
ML{* my_rippling @{context} ["f_0 a (f_0 b 0) = f_0 b (f_0 a 0)"] *}(*gen; success leads to mult fer*)
*)
ML{* my_rippling @{context} ["Suc (f_0 a (Suc b)) = f_0 a (Suc (Suc b))"] *}(*mult fert; should do breadth first because one fertilisation solves the problem while the other leads to a lemma calculation*)
ML{* my_rippling @{context} ["Suc (f_0 a (Suc 0)) = f_0 a (Suc (Suc 0))"] *}(*gen; success leads to mult fert*)
ML{* my_rippling @{context} ["Suc (Suc (f_0 a b)) = f_0 a (Suc (Suc b))"] *}(*mult fert*)(*solved with two ferts*)
ML{* my_rippling @{context} ["Suc (Suc (f_0 a 0)) = f_0 a (Suc (Suc 0))"] *}(*gen; success leads to mult fert*)
ML{* my_rippling @{context} ["f_0 a (Suc b) = Suc (f_0 a b)"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["f_0 a (Suc 0) = Suc (f_0 a 0)"] *}(*gen; success will lead to failure in fertilisation and to mult fert problem*)


 (* open conjectures for function: f_1*)
ML{* my_rippling @{context} ["f_1 a (f_1 b c) = f_1 b (f_1 a c)"] *}(*mult fert; failure leads to infinite lemma calc*)
ML{* my_rippling @{context} ["f_1 a (f_1 b 0) = f_1 b (f_1 a 0)"] *}(*gen; success will lead to mult fert*)
ML{* my_rippling @{context} ["Suc (f_1 a (Suc b)) = f_1 a (Suc (Suc b))"] *}(*mult fert*)
ML{* my_rippling @{context} ["Suc (f_1 a (Suc 0)) = f_1 a (Suc (Suc 0))"] *}(*no rippling; maybe sinks can only be variables and that's why rippling doesn't happen in these cases*)
ML{* my_rippling @{context} ["Suc (Suc (f_1 a b)) = f_1 a (Suc (Suc b))"] *}(*mult fert*)
ML{* my_rippling @{context} ["Suc (Suc (f_1 a 0)) = f_1 a (Suc (Suc 0))"] *}(*no rippling; same as above*)
ML{* my_rippling @{context} ["f_1 a (Suc b) = Suc (f_1 a b)"] *}(*mult fert; failure leads to inf lemma calc*)
ML{* my_rippling @{context} ["f_1 a (Suc 0) = Suc (f_1 a 0)"] *}(*no rippling; same as above*)


 (* open conjectures for function: f_2*)
ML{* my_rippling @{context} ["f_2 a (f_2 b c) = f_2 b (f_2 a c)"] *}(*mult fert*)
ML{* my_rippling @{context} ["f_2 a (f_2 b 0) = f_2 b (f_2 a 0)"] *}(*gen; success will lead to mult fert*)
ML{* my_rippling @{context} ["Suc (f_2 a (Suc b)) = f_2 a (Suc (Suc b))"] *}(*mult fert*)
ML{* my_rippling @{context} ["Suc (f_2 a (Suc 0)) = f_2 a (Suc (Suc 0))"] *}(*gen; success will lead to mult fert*)
ML{* my_rippling @{context} ["Suc (Suc (f_2 a b)) = f_2 a (Suc (Suc b))"] *}(*mult fert*)
ML{* my_rippling @{context} ["Suc (Suc (f_2 a 0)) = f_2 a (Suc (Suc 0))"] *}(*gen; success will lead to mult fert*)
ML{* my_rippling @{context} ["f_2 a (Suc b) = Suc (f_2 a b)"] *}(*mult fert; failure leads to inf lemma calc*)
ML{* my_rippling @{context} ["f_2 a (Suc 0) = Suc (f_2 a 0)"] *}(*gen; success will lead to mult fert*)


 (* open conjectures for function: f_3*)
ML{* my_rippling @{context} ["f_3 a (f_3 b c) = f_3 b (f_3 a c)"] *}(*mult fert*)
ML{* my_rippling @{context} ["f_3 a (f_3 b 0) = f_3 b (f_3 a 0)"] *}(*gen; success will lead to mult fert*)
ML{* my_rippling @{context} ["Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))"] *}(*mult fert*)
ML{* my_rippling @{context} ["Suc (f_3 a (Suc 0)) = f_3 a (Suc (Suc 0))"] *}(*gen*)
ML{* my_rippling @{context} ["Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))"] *}(*mult fert*)
ML{* my_rippling @{context} ["Suc (Suc (f_3 a 0)) = f_3 a (Suc (Suc 0))"] *}(*gen*)
ML{* my_rippling @{context} ["f_3 a (Suc b) = Suc (f_3 a b)"] *}(*mult fert; failure leads to inf lemma calc*)
ML{* my_rippling @{context} ["f_3 a (Suc 0) = Suc (f_3 a 0)"] *}(*just simplification; a lot of cases are like this one but I haven't reported on it*)


 (* open conjectures for function: f_4*)
ML{* my_rippling @{context} ["f_4 a (f_4 b c) = f_4 b (f_4 a c)"] *}(*mult fert*)
ML{* my_rippling @{context} ["f_4 a (f_4 b 0) = f_4 b (f_4 a 0)"] *}(*mult fert; failure leads to inf lemma calc*)
ML{* my_rippling @{context} ["Suc (f_4 a (Suc b)) = f_4 a (Suc (Suc b))"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["Suc (f_4 a (Suc 0)) = f_4 a (Suc (Suc 0))"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["Suc (Suc (f_4 a b)) = f_4 a (Suc (Suc b))"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["Suc (Suc (f_4 a 0)) = f_4 a (Suc (Suc 0))"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["f_4 a (Suc b) = Suc (f_4 a b)"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["f_4 a (Suc 0) = Suc (f_4 a 0)"] *}(*fails to fertilise; success would lead to mult fert problem. Comment: lemma calculation should simplify, otherwise having a Suc in the inductive assumption can be a problem when trying to fertilise*)


 (* open conjectures for function: f_5*)
ML{* my_rippling @{context} ["f_5 a (f_5 b c) = f_5 b (f_5 a c)"] *}(*mult fert*)
ML{* my_rippling @{context} ["f_5 a (f_5 b 0) = f_5 b (f_5 a 0)"] *}(*mult fert*)
ML{* my_rippling @{context} ["Suc (f_5 a (Suc b)) = f_5 a (Suc (Suc b))"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["Suc (f_5 a (Suc 0)) = f_5 a (Suc (Suc 0))"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["Suc (Suc (f_5 a b)) = f_5 a (Suc (Suc b))"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["Suc (Suc (f_5 a 0)) = f_5 a (Suc (Suc 0))"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["f_5 a (Suc b) = Suc (f_5 a b)"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* my_rippling @{context} ["f_5 a (Suc 0) = Suc (f_5 a 0)"] *}(*fails to fertilise; success would lead to mult fert problem*)


 (* open conjectures for function: f_6*)
ML{* my_rippling @{context} ["f_6 a (f_6 b c) = f_6 b (f_6 a c)"] *}(*after rippling it doesn't need to fertilise; this means that induction is not required. However, there are no branches, as apparently it is trying to fertilise and it doesn't check is has finished*)
ML{* my_rippling @{context} ["f_6 a (f_6 b 0) = f_6 b (f_6 a 0)"] *}(*doesn't ripple; this case has been reported above. It has something to do with 0 instead of a variable*)
ML{* my_rippling @{context} ["f_6 a (Suc 0) = Suc (f_6 a 0)"] *}(*this is a particular case of a lemma that's already proven by IsaPlanner. The particular failure happens because there is just no rippling*)


 (* open conjectures for function: f_7*)
ML{* my_rippling @{context} ["f_7 a (f_7 b c) = f_7 b (f_7 a c)"] *}(*mult fert*)
ML{* my_rippling @{context} ["f_7 a (f_7 b 0) = f_7 b (f_7 a 0)"] *}(*doesn't ripple*)
ML{* my_rippling @{context} ["Suc (f_7 a (Suc b)) = f_7 a (Suc (Suc b))"] *}(*mult fert; failure leads to inf lemma calc*)
ML{* my_rippling @{context} ["Suc (f_7 a (Suc 0)) = f_7 a (Suc (Suc 0))"] *}(*doesn't ripple*)
ML{* my_rippling @{context} ["Suc (Suc (f_7 a b)) = f_7 a (Suc (Suc b))"] *}(*mult fert; failure leads to inf lemma calc*)
ML{* my_rippling @{context} ["Suc (Suc (f_7 a 0)) = f_7 a (Suc (Suc 0))"] *}(*doesn't ripple*)
ML{* my_rippling @{context} ["f_7 a (Suc b) = Suc (f_7 a b)"] *}(*mult fert; failure leads to inf lemma calc*)
ML{* my_rippling @{context} ["f_7 a (Suc 0) = Suc (f_7 a 0)"] *}(*doesn't ripple*)


end