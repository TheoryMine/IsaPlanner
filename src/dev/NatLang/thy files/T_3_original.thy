theory T_3
imports IsaP 
uses "failure_capture.ML"
begin

datatype "T_3" =  "C_6" "T_3" "Nat.nat"  | "C_5" "HOL.bool" "Nat.nat"  


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


 (* open conjectures for function: f_0*)
ML{* prove_and_capture @{context} ["f_0 a (f_0 a (f_0 a 0)) = f_0 a 0"] *}
ML{* prove_and_capture @{context} ["f_0 a (f_0 a (f_0 a b)) = f_0 a b"] *}
ML{* prove_and_capture @{context} ["f_0 a (f_0 a (Suc 0)) = f_0 a (Suc 0)"] *}
ML{* prove_and_capture @{context} ["f_0 a (f_0 a (Suc b)) = f_0 a (Suc b)"] *}
ML{* prove_and_capture @{context} ["f_0 a (Suc (f_0 a 0)) = f_0 a (Suc 0)"] *}
ML{* prove_and_capture @{context} ["f_0 a (Suc (f_0 a b)) = f_0 a (Suc b)"] *}
ML{* prove_and_capture @{context} ["f_0 a (f_0 a 0) = f_0 a 0"] *}
ML{* prove_and_capture @{context} ["f_0 a (f_0 a b) = f_0 a b"] *}


 (* open conjectures for function: f_1*)
ML{* prove_and_capture @{context} ["f_1 a (f_1 a (Suc 0)) = f_1 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["f_1 a (f_1 a (Suc b)) = f_1 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_1 a (Suc (f_1 a 0)) = f_1 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["f_1 a (Suc (f_1 a b)) = f_1 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_1 a (f_1 a 0) = f_1 a (Suc 0)"] *}
ML{* prove_and_capture @{context} ["f_1 a (f_1 a b) = f_1 a (Suc b)"] *}


 (* open conjectures for function: f_2*)
ML{* prove_and_capture @{context} ["f_2 a (f_2 a 0) = f_2 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["f_2 a (f_2 a b) = f_2 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_2 a (Suc (Suc 0)) = f_2 a (f_2 a 0)"] *}
ML{* prove_and_capture @{context} ["f_2 a (Suc (Suc b)) = f_2 a (f_2 a b)"] *}


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


 (* open conjectures for function: f_5*)


 (* open conjectures for function: f_6*)


 (* open conjectures for function: f_7*)
ML{* prove_and_capture @{context} ["f_7 a (f_7 b 0) = f_7 b (f_7 a 0)"] *}
ML{* prove_and_capture @{context} ["f_7 a (f_7 b c) = f_7 b (f_7 a c)"] *}
ML{* prove_and_capture @{context} ["f_7 a (Suc 0) = Suc (f_7 a 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_7 a 0) = f_7 a (Suc 0)"] *}


 (* open conjectures for function: f_8*)


 (* open conjectures for function: f_9*)


 (* open conjectures for function: f_10*)


end