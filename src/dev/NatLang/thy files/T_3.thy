theory T_3
imports IsaP 
uses "../myrippling.ML"
begin

datatype "T_3" =  "C_6" "T_3" "Nat.nat"  | "C_5" "HOL.bool" "Nat.nat"  
declare nat.inject[wrule]

fun f_0 :: "T_3 => nat => nat" where
  "f_0 (C_5 a b) c = c"
| "f_0 (C_6 a b) c = f_0 a (Suc (f_0 a (Suc (Suc b))))"

fun f_1 :: "T_3 => nat => nat" where
  "f_1 (C_5 a b) c = Suc c"
| "f_1 (C_6 a b) c = Suc (Suc (Suc (f_1 a b)))"

fun f_2 :: "T_3 => nat => nat" where
  "f_2 (C_5 a b) c = Suc (Suc c)"
| "f_2 (C_6 a b) c = f_2 a (f_2 a (Suc (f_2 a 0)))"

fun f_3 :: "T_3 => nat => nat" where
  "f_3 (C_5 a b) c = Suc (Suc (Suc c))"
| "f_3 (C_6 a b) c = f_3 a (Suc (Suc (f_3 a (Suc c))))"

fun f_4 :: "T_3 => nat => nat" where
  "f_4 (C_5 a b) c = Suc (Suc (Suc (Suc c)))"
| "f_4 (C_6 a b) c = f_4 a (Suc (f_4 a (Suc b)))"

fun f_5 :: "T_3 => nat => nat" where
  "f_5 (C_5 a b) c = Suc (Suc (Suc (Suc c)))"
| "f_5 (C_6 a b) c = Suc (f_5 a (Suc (Suc (f_5 a 0))))"

fun f_6 :: "T_3 => nat => nat" where
  "f_6 (C_5 a b) c = Suc (Suc (Suc (Suc (Suc c))))"
| "f_6 (C_6 a b) c = f_6 a (Suc (Suc (Suc 0)))"

fun f_7 :: "T_3 => nat => nat" where
  "f_7 (C_5 a b) c = Suc (Suc (Suc (Suc (Suc c))))"
| "f_7 (C_6 a b) c = Suc (Suc (f_7 a (Suc (Suc (Suc c)))))"

fun f_8 :: "T_3 => nat => nat" where
  "f_8 (C_5 a b) c = Suc (Suc (Suc (Suc (Suc (Suc c)))))"
| "f_8 (C_6 a b) c = f_8 a c"

fun f_9 :: "T_3 => nat => nat" where
  "f_9 (C_5 a b) c = Suc (Suc (Suc (Suc (Suc (Suc c)))))"
| "f_9 (C_6 a b) c = Suc (f_9 a (f_9 a (Suc b)))"

fun f_10 :: "T_3 => nat => nat" where
  "f_10 (C_5 a b) c = Suc (Suc (Suc (Suc (Suc (Suc (Suc c))))))"
| "f_10 (C_6 a b) c = Suc (Suc (Suc (f_10 a (Suc 0))))"

declare f_0.simps[wrule]
declare f_1.simps[wrule] 
declare f_2.simps[wrule]
declare f_3.simps[wrule] 
declare f_4.simps[wrule]
declare f_5.simps[wrule] 
declare f_6.simps[wrule]
declare f_7.simps[wrule]
declare f_8.simps[wrule]
declare f_9.simps[wrule] 
declare f_10.simps[wrule]

ML{* my_rippling @{context} ["Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))"] *}
(*


 (* theorems proven for function: f_0*)


 (* theorems proven for function: f_1*)


 (* theorems proven for function: f_2*)


 (* theorems proven for function: f_3*)


 (* theorems proven for function: f_4*)


 (* theorems proven for function: f_5*)


 (* theorems proven for function: f_6*)


 (* theorems proven for function: f_7*)
lemma [wrule]: "f_7 a (Suc b) = Suc (f_7 a b)"
sorry

lemma [wrule]: "Suc (f_7 a b) = f_7 a (Suc b)"
sorry


 (* theorems proven for function: f_8*)
lemma [wrule]: "f_8 a (f_8 b c) = f_8 b (f_8 b c)"
sorry

lemma [wrule]: "f_8 a (f_8 b c) = f_8 b (f_8 a c)"
sorry

lemma [wrule]: "f_8 a (f_8 b c) = f_8 a (f_8 a c)"
sorry

lemma [wrule]: "f_8 t (Suc (Suc (Suc (Suc (Suc (Suc n)))))) =
Suc (Suc (Suc (Suc (Suc (Suc (f_8 t n))))))"
sorry

lemma [wrule]: "f_8 a (Suc b) = Suc (f_8 a b)"
sorry

lemma [wrule]: "Suc (f_8 a b) = f_8 a (Suc b)"
sorry

lemma [wrule]: "Suc (Suc (Suc (Suc (Suc (Suc n))))) = f_8 t n"
sorry



 (* theorems proven for function: f_9*)


 (* theorems proven for function: f_10*)

*)
ML{* i_rippling @{context} ["f_7 a (f_7 b c) = f_7 b (f_7 a c)"] *}

(*

 (* open conjectures for function: f_0*)
ML{* i_rippling @{context} ["f_0 a (f_0 a (f_0 a b)) = f_0 a b"] *}(*fails to ripple completely; success will lead to multiple fert problem*)
ML{* i_rippling @{context} ["f_0 a (f_0 a (f_0 a 0)) = f_0 a 0"] *}(*fails to ripple at all*)
ML{* i_rippling @{context} ["f_0 a (f_0 a (Suc b)) = f_0 a (Suc b)"] *}(*without fertilising it has already proved the goal (rippling works as a case split technique. In the lemma it tries: doesn't need induction. After rippling it has proved the goals but it doesn't realise it*)
ML{* i_rippling @{context} ["f_0 a (f_0 a (Suc 0)) = f_0 a (Suc 0)"] *}(*fails to ripple at all*)
ML{* i_rippling @{context} ["f_0 a (Suc (f_0 a b)) = f_0 a (Suc b)"] *}(*without fertilising it has already proved the goal (rippling works as a case split technique*)
ML{* i_rippling @{context} ["f_0 a (Suc (f_0 a 0)) = f_0 a (Suc 0)"] *}(*fails to ripple at all*)
ML{* i_rippling @{context} ["f_0 a (f_0 a b) = f_0 a b"] *}(*without fertilising it has already proved the goal (rippling works as a case split technique). It doesn't realise it has finished. In the lemma it tries it is exactly the same.*)
ML{* i_rippling @{context} ["f_0 a (f_0 a 0) = f_0 a 0"] *}(*fails to ripple at all*)


 (* open conjectures for function: f_1*)
ML{* i_rippling @{context} ["f_1 a (f_1 a (Suc b)) = f_1 a (Suc (Suc b))"] *}(*fails to ripple at all*)
ML{* i_rippling @{context} ["f_1 a (f_1 a (Suc 0)) = f_1 a (Suc (Suc 0))"] *}(*fails to ripple at all*)
ML{* i_rippling @{context} ["f_1 a (Suc (f_1 a b)) = f_1 a (Suc (Suc b))"] *}(*starts ripple but fails to continue with it*)
ML{* i_rippling @{context} ["f_1 a (Suc (f_1 a 0)) = f_1 a (Suc (Suc 0))"] *}(*fails to ripple at all*)
ML{* i_rippling @{context} ["f_1 a (f_1 a b) = f_1 a (Suc b)"] *}(*starts ripple but fails to continue with it*)
ML{* i_rippling @{context} ["f_1 a (f_1 a 0) = f_1 a (Suc 0)"] *}(*fails to ripple at all*)


 (* open conjectures for function: f_2*)
ML{* i_rippling @{context} ["f_2 a (f_2 a b) = f_2 a (Suc (Suc b))"] *}(*fails to ripple completely*)
ML{* i_rippling @{context} ["f_2 a (f_2 a 0) = f_2 a (Suc (Suc 0))"] *}(*fails to ripple at all*)


 (* open conjectures for function: f_3*)
ML{* i_rippling @{context} ["f_3 a (f_3 b c) = f_3 b (f_3 a c)"] *}(*mult fert; failure to do so leads to inf lemma caalc*)
ML{* i_rippling @{context} ["f_3 a (f_3 b 0) = f_3 b (f_3 a 0)"] *}(*gen*)(*success will lead to mult fert problem*)
ML{* i_rippling @{context} ["Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))"] *}(*fails to fertilise; success would lead to mult fert problem*)
ML{* i_rippling @{context} ["Suc (f_3 a (Suc 0)) = f_3 a (Suc (Suc 0))"] *}(*gen; success will lead to mult fert problem*)
ML{* i_rippling @{context} ["Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))"] *}(*fails to fertilise; success would lead to failure to fertilise*)
ML{* i_rippling @{context} ["Suc (Suc (f_3 a 0)) = f_3 a (Suc (Suc 0))"] *}(*gen; success will lead to failure to fertilise*)
ML{* i_rippling @{context} ["f_3 a (Suc b) = Suc (f_3 a b)"] *}(*fails to fertilise; success would lead to failure to fertilise*)
ML{* i_rippling @{context} ["f_3 a (Suc 0) = Suc (f_3 a 0)"] *}(*gen; success will lead to failure to fertilise*)

 (* open conjectures for function: f_4*)


 (* open conjectures for function: f_5*)


 (* open conjectures for function: f_6*)
*)

 (* open conjectures for function: f_7*)
ML{* i_rippling @{context} ["f_7 a (f_7 b c) = f_7 b (f_7 a c)"] *}(*lemma spec; actually, f(a,sb) = sf(a,b), which is poven, helps, but when I try running it with that wave rule rippling doesn't seem to terminate*)(*the goal is: "Suc (Suc (f_7 d (Suc (Suc (Suc (f_7 e f)))))) = f_7 e (Suc (Suc (f_7 d (Suc (Suc (Suc f))))))"*)
ML{* i_rippling @{context} ["f_7 a (f_7 b 0) = f_7 b (f_7 a 0)"] *}(*fails to ripple*)
ML{* i_rippling @{context} ["f_7 a (Suc 0) = Suc (f_7 a 0)"] *}(*fails to ripple, but actually the lemma "f_7 a (Suc b) = Suc (f_7 a b)" is proved, and this is just a particular case of that one*)


 (* open conjectures for function: f_8*)


 (* open conjectures for function: f_9*)


 (* open conjectures for function: f_10*)


end