theory T_12
imports IsaP 
uses "failure_capture.ML" "myrippling.ML"
begin

datatype "T_12" =  "C_24" "Nat.nat"  | "C_23" "T_12" "HOL.bool"  
declare nat.inject[wrule]
declare T_12.inject[wrule]
declare nat.simps[wrule]
declare T_12.simps[wrule]

fun f_0 :: "T_12 => nat => nat" where
  "f_0 (C_24 a) b = b"
| "f_0 (C_23 a b) c = Suc (f_0 a (Suc (f_0 a c)))"

fun f_1 :: "T_12 => nat => nat" where
  "f_1 (C_24 a) b = Suc b"
| "f_1 (C_23 a b) c = Suc (Suc (f_1 a (f_1 a (Suc c))))"

fun f_2 :: "T_12 => nat => nat" where
  "f_2 (C_24 a) b = Suc (Suc b)"
| "f_2 (C_23 a b) c = f_2 a (Suc (Suc c))"

fun f_3 :: "T_12 => nat => nat" where
  "f_3 (C_24 a) b = Suc (Suc (Suc b))"
| "f_3 (C_23 a b) c = f_3 a (Suc (Suc (f_3 a (Suc c))))"

fun f_4 :: "T_12 => nat => nat" where
  "f_4 (C_24 a) b = Suc (Suc (Suc (Suc b)))"
| "f_4 (C_23 a b) c = Suc (f_4 a (f_4 a c))"

fun f_5 :: "T_12 => nat => nat" where
  "f_5 (C_24 a) b = Suc (Suc (Suc (Suc (Suc b))))"
| "f_5 (C_23 a b) c = Suc (Suc (f_5 a (Suc (Suc (Suc c)))))"

fun f_6 :: "T_12 => nat => nat" where
  "f_6 (C_24 a) b = Suc (Suc (Suc (Suc (Suc (Suc b)))))"
| "f_6 (C_23 a b) c = f_6 a c"

fun f_7 :: "T_12 => nat => nat" where
  "f_7 (C_24 a) b = Suc (Suc (Suc (Suc (Suc (Suc (Suc b))))))"
| "f_7 (C_23 a b) c = f_7 a (Suc (Suc (Suc (Suc (Suc c)))))"

declare f_0.simps[wrule]
declare f_1.simps[wrule]
declare f_2.simps[wrule]
declare f_3.simps[wrule]
declare f_4.simps[wrule]
declare f_5.simps[wrule]
declare f_6.simps[wrule]
declare f_7.simps[wrule]


(*


 (* theorems proven for function: f_0*)


 (* theorems proven for function: f_1*)


 (* theorems proven for function: f_2*)
lemma [wrule]: "f_2 a (Suc b) = Suc (f_2 a b)"
sorry

lemma [wrule]: "Suc (f_2 a b) = f_2 a (Suc b)"
sorry



 (* theorems proven for function: f_3*)


 (* theorems proven for function: f_4*)


 (* theorems proven for function: f_5*)
lemma [wrule]: "f_5 a (Suc b) = Suc (f_5 a b)"
sorry

lemma [wrule]: "Suc (f_5 a b) = f_5 a (Suc b)"
sorry



 (* theorems proven for function: f_6*)
lemma [wrule]: "f_6 a (f_6 b c) = f_6 b (f_6 b c)"
sorry

lemma [wrule]: "f_6 a (f_6 b c) = f_6 b (f_6 a c)"
sorry

lemma [wrule]: "f_6 a (f_6 b c) = f_6 a (f_6 a c)"
sorry

lemma [wrule]: "f_6 t (Suc (Suc (Suc (Suc (Suc (Suc n)))))) =
Suc (Suc (Suc (Suc (Suc (Suc (f_6 t n))))))"
sorry

lemma [wrule]: "f_6 a (Suc b) = Suc (f_6 a b)"
sorry

lemma [wrule]: "Suc (f_6 a b) = f_6 a (Suc b)"
sorry

lemma [wrule]: "Suc (Suc (Suc (Suc (Suc (Suc n))))) = f_6 t n"
sorry



 (* theorems proven for function: f_7*)
lemma [wrule]: "f_7 a (Suc b) = Suc (f_7 a b)"
sorry

lemma [wrule]: "Suc (f_7 a b) = f_7 a (Suc b)"
sorry


*)(*

 (* open conjectures for function: f_1*)
ML{* my_rippling @{context} ["f_1 a (f_1 b 0) = f_1 b (f_1 a 0)"] *}
ML{* my_rippling @{context} ["f_1 a (f_1 b c) = f_1 b (f_1 a c)"] *}
ML{* my_rippling @{context} ["f_1 a (Suc (Suc 0)) = Suc (f_1 a (Suc 0))"] *}
ML{* my_rippling @{context} ["f_1 a (Suc (Suc 0)) = Suc (Suc (f_1 a 0))"] *}
ML{* my_rippling @{context} ["f_1 a (Suc (Suc b)) = Suc (f_1 a (Suc b))"] *}
ML{* my_rippling @{context} ["f_1 a (Suc (Suc b)) = Suc (Suc (f_1 a b))"] *}
ML{* my_rippling @{context} ["Suc (f_1 a (Suc 0)) = f_1 a (Suc (Suc 0))"] *}
ML{* my_rippling @{context} ["Suc (f_1 a (Suc b)) = f_1 a (Suc (Suc b))"] *}
ML{* my_rippling @{context} ["Suc (Suc (f_1 a 0)) = f_1 a (Suc (Suc 0))"] *}
ML{* my_rippling @{context} ["Suc (Suc (f_1 a b)) = f_1 a (Suc (Suc b))"] *}
ML{* my_rippling @{context} ["f_1 a (Suc 0) = Suc (f_1 a 0)"] *}
ML{* my_rippling @{context} ["f_1 a (Suc b) = Suc (f_1 a b)"] *}
ML{* my_rippling @{context} ["Suc (f_1 a 0) = f_1 a (Suc 0)"] *}
ML{* my_rippling @{context} ["Suc (f_1 a b) = f_1 a (Suc b)"] *}


 (* open conjectures for function: f_2*)
ML{* my_rippling @{context} ["f_2 a (f_2 b 0) = f_2 b (f_2 a 0)"] *}
ML{* my_rippling @{context} ["f_2 a (f_2 b c) = f_2 b (f_2 a c)"] *}
ML{* my_rippling @{context} ["f_2 a (Suc 0) = Suc (f_2 a 0)"] *}
ML{* my_rippling @{context} ["Suc (f_2 a 0) = f_2 a (Suc 0)"] *}
*)

ML{* my_rippling @{context} ["f_3 a (f_3 b c) = f_3 b (f_3 a c)"] *}

 (* open conjectures for function: f_3*)
ML{* my_rippling @{context} ["f_3 a (f_3 b 0) = f_3 b (f_3 a 0)"] *}
ML{* my_rippling @{context} ["f_3 a (f_3 b c) = f_3 b (f_3 a c)"] *}
ML{* my_rippling @{context} ["f_3 a (Suc (Suc 0)) = Suc (f_3 a (Suc 0))"] *}
ML{* my_rippling @{context} ["f_3 a (Suc (Suc 0)) = Suc (Suc (f_3 a 0))"] *}
ML{* my_rippling @{context} ["f_3 a (Suc (Suc b)) = Suc (f_3 a (Suc b))"] *}
ML{* my_rippling @{context} ["f_3 a (Suc (Suc b)) = Suc (Suc (f_3 a b))"] *}
ML{* my_rippling @{context} ["Suc (f_3 a (Suc 0)) = f_3 a (Suc (Suc 0))"] *}
ML{* my_rippling @{context} ["Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))"] *}
ML{* my_rippling @{context} ["Suc (Suc (f_3 a 0)) = f_3 a (Suc (Suc 0))"] *}
ML{* my_rippling @{context} ["Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))"] *}
ML{* my_rippling @{context} ["f_3 a (Suc 0) = Suc (f_3 a 0)"] *}
ML{* my_rippling @{context} ["f_3 a (Suc b) = Suc (f_3 a b)"] *}
ML{* my_rippling @{context} ["Suc (f_3 a 0) = f_3 a (Suc 0)"] *}
ML{* my_rippling @{context} ["Suc (f_3 a b) = f_3 a (Suc b)"] *}


 (* open conjectures for function: f_4*)
ML{* my_rippling @{context} ["f_4 a (f_4 b 0) = f_4 b (f_4 a 0)"] *}
ML{* my_rippling @{context} ["f_4 a (f_4 b c) = f_4 b (f_4 a c)"] *}
ML{* my_rippling @{context} ["f_4 a (Suc (Suc 0)) = Suc (f_4 a (Suc 0))"] *}
ML{* my_rippling @{context} ["f_4 a (Suc (Suc 0)) = Suc (Suc (f_4 a 0))"] *}
ML{* my_rippling @{context} ["f_4 a (Suc (Suc b)) = Suc (f_4 a (Suc b))"] *}
ML{* my_rippling @{context} ["f_4 a (Suc (Suc b)) = Suc (Suc (f_4 a b))"] *}
ML{* my_rippling @{context} ["Suc (f_4 a (Suc 0)) = f_4 a (Suc (Suc 0))"] *}
ML{* my_rippling @{context} ["Suc (f_4 a (Suc b)) = f_4 a (Suc (Suc b))"] *}
ML{* my_rippling @{context} ["Suc (Suc (f_4 a 0)) = f_4 a (Suc (Suc 0))"] *}
ML{* my_rippling @{context} ["Suc (Suc (f_4 a b)) = f_4 a (Suc (Suc b))"] *}
ML{* my_rippling @{context} ["f_4 a (Suc 0) = Suc (f_4 a 0)"] *}
ML{* my_rippling @{context} ["f_4 a (Suc b) = Suc (f_4 a b)"] *}
ML{* my_rippling @{context} ["Suc (f_4 a 0) = f_4 a (Suc 0)"] *}
ML{* my_rippling @{context} ["Suc (f_4 a b) = f_4 a (Suc b)"] *}


 (* open conjectures for function: f_5*)
ML{* my_rippling @{context} ["f_5 a (f_5 b 0) = f_5 b (f_5 a 0)"] *}
ML{* my_rippling @{context} ["f_5 a (f_5 b c) = f_5 b (f_5 a c)"] *}
ML{* my_rippling @{context} ["f_5 a (Suc 0) = Suc (f_5 a 0)"] *}
ML{* my_rippling @{context} ["Suc (f_5 a 0) = f_5 a (Suc 0)"] *}


 (* open conjectures for function: f_6*)


 (* open conjectures for function: f_7*)
ML{* my_rippling @{context} ["f_7 a (f_7 b 0) = f_7 b (f_7 a 0)"] *}
ML{* my_rippling @{context} ["f_7 a (f_7 b c) = f_7 b (f_7 a c)"] *}
ML{* my_rippling @{context} ["f_7 a (Suc 0) = Suc (f_7 a 0)"] *}
ML{* my_rippling @{context} ["Suc (f_7 a 0) = f_7 a (Suc 0)"] *}


end