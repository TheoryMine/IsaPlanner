theory T_6
imports IsaP 
uses "failure_capture.ML"
begin

datatype "T_6" =  "C_12" "T_6" "HOL.bool"  | "C_11" "HOL.bool" "HOL.bool"  


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


 (* open conjectures for function: f_0*)


 (* open conjectures for function: f_1*)
ML{* prove_and_capture @{context} ["f_1 a (f_1 b 0) = f_1 b (f_1 a 0)"] *}
ML{* prove_and_capture @{context} ["f_1 a (f_1 b c) = f_1 b (f_1 a c)"] *}
ML{* prove_and_capture @{context} ["f_1 a (Suc 0) = Suc (f_1 a 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_1 a 0) = f_1 a (Suc 0)"] *}


 (* open conjectures for function: f_2*)
ML{* prove_and_capture @{context} ["f_2 a (f_2 b 0) = f_2 b (f_2 a 0)"] *}
ML{* prove_and_capture @{context} ["f_2 a (f_2 b c) = f_2 b (f_2 a c)"] *}
ML{* prove_and_capture @{context} ["f_2 a (Suc (Suc 0)) = Suc (f_2 a (Suc 0))"] *}
ML{* prove_and_capture @{context} ["f_2 a (Suc (Suc 0)) = Suc (Suc (f_2 a 0))"] *}
ML{* prove_and_capture @{context} ["f_2 a (Suc (Suc b)) = Suc (f_2 a (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_2 a (Suc (Suc b)) = Suc (Suc (f_2 a b))"] *}
ML{* prove_and_capture @{context} ["Suc (f_2 a (Suc 0)) = f_2 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (f_2 a (Suc b)) = f_2 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_2 a 0)) = f_2 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_2 a b)) = f_2 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_2 a (Suc 0) = Suc (f_2 a 0)"] *}
ML{* prove_and_capture @{context} ["f_2 a (Suc b) = Suc (f_2 a b)"] *}
ML{* prove_and_capture @{context} ["Suc (f_2 a 0) = f_2 a (Suc 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_2 a b) = f_2 a (Suc b)"] *}


 (* open conjectures for function: f_3*)
ML{* prove_and_capture @{context} ["f_3 a (f_3 b 0) = f_3 b (f_3 a 0)"] *}
ML{* prove_and_capture @{context} ["f_3 a (f_3 b c) = f_3 b (f_3 a c)"] *}
ML{* prove_and_capture @{context} ["f_3 a (Suc (Suc 0)) = Suc (f_3 a (Suc 0))"] *}
ML{* prove_and_capture @{context} ["f_3 a (Suc (Suc 0)) = Suc (Suc (f_3 a 0))"] *}
ML{* prove_and_capture @{context} ["f_3 a (Suc (Suc b)) = Suc (f_3 a (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_3 a (Suc (Suc b)) = Suc (Suc (f_3 a b))"] *}
ML{* prove_and_capture @{context} ["Suc (f_3 a (Suc 0)) = f_3 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_3 a 0)) = f_3 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_3 a (Suc 0) = Suc (f_3 a 0)"] *}
ML{* prove_and_capture @{context} ["f_3 a (Suc b) = Suc (f_3 a b)"] *}
ML{* prove_and_capture @{context} ["Suc (f_3 a 0) = f_3 a (Suc 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_3 a b) = f_3 a (Suc b)"] *}


 (* open conjectures for function: f_4*)
ML{* prove_and_capture @{context} ["f_4 a (f_4 b 0) = f_4 b (f_4 a 0)"] *}
ML{* prove_and_capture @{context} ["f_4 a (f_4 b c) = f_4 b (f_4 a c)"] *}
ML{* prove_and_capture @{context} ["f_4 a (Suc (Suc 0)) = Suc (f_4 a (Suc 0))"] *}
ML{* prove_and_capture @{context} ["f_4 a (Suc (Suc 0)) = Suc (Suc (f_4 a 0))"] *}
ML{* prove_and_capture @{context} ["f_4 a (Suc (Suc b)) = Suc (f_4 a (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_4 a (Suc (Suc b)) = Suc (Suc (f_4 a b))"] *}
ML{* prove_and_capture @{context} ["Suc (f_4 a (Suc 0)) = f_4 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (f_4 a (Suc b)) = f_4 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_4 a 0)) = f_4 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_4 a b)) = f_4 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_4 a (Suc 0) = Suc (f_4 a 0)"] *}
ML{* prove_and_capture @{context} ["f_4 a (Suc b) = Suc (f_4 a b)"] *}
ML{* prove_and_capture @{context} ["Suc (f_4 a 0) = f_4 a (Suc 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_4 a b) = f_4 a (Suc b)"] *}


 (* open conjectures for function: f_5*)
ML{* prove_and_capture @{context} ["f_5 a (f_5 b 0) = f_5 b (f_5 a 0)"] *}
ML{* prove_and_capture @{context} ["f_5 a (f_5 b c) = f_5 b (f_5 a c)"] *}
ML{* prove_and_capture @{context} ["f_5 a (Suc (Suc 0)) = Suc (f_5 a (Suc 0))"] *}
ML{* prove_and_capture @{context} ["f_5 a (Suc (Suc 0)) = Suc (Suc (f_5 a 0))"] *}
ML{* prove_and_capture @{context} ["f_5 a (Suc (Suc b)) = Suc (f_5 a (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_5 a (Suc (Suc b)) = Suc (Suc (f_5 a b))"] *}
ML{* prove_and_capture @{context} ["Suc (f_5 a (Suc 0)) = f_5 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (f_5 a (Suc b)) = f_5 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_5 a 0)) = f_5 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_5 a b)) = f_5 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_5 a (Suc 0) = Suc (f_5 a 0)"] *}
ML{* prove_and_capture @{context} ["f_5 a (Suc b) = Suc (f_5 a b)"] *}
ML{* prove_and_capture @{context} ["Suc (f_5 a 0) = f_5 a (Suc 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_5 a b) = f_5 a (Suc b)"] *}


 (* open conjectures for function: f_6*)
ML{* prove_and_capture @{context} ["f_6 a (f_6 b 0) = f_6 b (f_6 a 0)"] *}
ML{* prove_and_capture @{context} ["f_6 a (f_6 b c) = f_6 b (f_6 a c)"] *}
ML{* prove_and_capture @{context} ["f_6 a (Suc 0) = Suc (f_6 a 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_6 a 0) = f_6 a (Suc 0)"] *}


end