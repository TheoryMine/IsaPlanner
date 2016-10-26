theory T_12
imports IsaP 
uses "../myrippling.ML"
begin

datatype "T_12" =  "C_24" "Nat.nat"  | "C_23" "T_12" "HOL.bool"

declare nat.inject[wrule]
declare T_12.inject[wrule]

fun f_7 :: "T_12 => nat => nat" where
"f_7 (C_24 a) b = Suc (Suc (Suc (Suc (Suc (Suc (Suc b))))))"
|"f_7 (C_23 a b) c = f_7 a (Suc (Suc (Suc (Suc (Suc c)))))"

fun f_6 :: "T_12 => nat => nat" where
"f_6 (C_24 a) b = Suc (Suc (Suc (Suc (Suc (Suc b)))))"
|"f_6 (C_23 a b) c = f_6 a c"

fun f_5 :: "T_12 => nat => nat" where
"f_5 (C_24 a) b = Suc (Suc (Suc (Suc (Suc b))))"
|"f_5 (C_23 a b) c = Suc (Suc (f_5 a (Suc (Suc (Suc c)))))"

fun f_4 :: "T_12 => nat => nat" where
"f_4 (C_24 a) b = Suc (Suc (Suc (Suc b)))"
|"f_4 (C_23 a b) c = Suc (f_4 a (f_4 a c))"

fun f_3 :: "T_12 => nat => nat" where
"f_3 (C_24 a) b = Suc (Suc (Suc b))"
|"f_3 (C_23 a b) c = f_3 a (Suc (Suc (f_3 a (Suc c))))"

fun f_2 :: "T_12 => nat => nat" where
"f_2 (C_24 a) b = Suc (Suc b)"
|"f_2 (C_23 a b) c = f_2 a (Suc (Suc c))"

fun f_1 :: "T_12 => nat => nat" where
"f_1 (C_24 a) b = Suc b"
|"f_1 (C_23 a b) c = Suc (Suc (f_1 a (f_1 a (Suc c))))"

fun f_0 :: "T_12 => nat => nat" where
"f_0 (C_24 a) b = b"
|"f_0 (C_23 a b) c = Suc (f_0 a (Suc (f_0 a c)))"

declare f_0.simps[wrule]
declare f_1.simps[wrule]
declare f_2.simps[wrule]
declare f_3.simps[wrule]
declare f_4.simps[wrule]
declare f_5.simps[wrule]
declare f_6.simps[wrule]
declare f_7.simps[wrule]
ML{* my_rippling @{context} ["Suc (Suc (f_0 a b)) = f_0 a (Suc (Suc b))"] *}
ML{*
val openconjs = [
(*"f_0 a (f_0 b 0) = f_0 b (f_0 a 0)",
"f_0 a (f_0 b c) = f_0 b (f_0 a c)",
"f_0 a (Suc (Suc 0)) = Suc (f_0 a (Suc 0))",
"f_0 a (Suc (Suc 0)) = Suc (Suc (f_0 a 0))",
"f_0 a (Suc (Suc b)) = Suc (f_0 a (Suc b))",
"f_0 a (Suc (Suc b)) = Suc (Suc (f_0 a b))",
"Suc (f_0 a (Suc 0)) = f_0 a (Suc (Suc 0))",
"Suc (f_0 a (Suc b)) = f_0 a (Suc (Suc b))",
"Suc (Suc (f_0 a 0)) = f_0 a (Suc (Suc 0))",
"Suc (Suc (f_0 a b)) = f_0 a (Suc (Suc b))",
"f_0 a (Suc 0) = Suc (f_0 a 0)",
"f_0 a (Suc b) = Suc (f_0 a b)",
"Suc (f_0 a 0) = f_0 a (Suc 0)",
"Suc (f_0 a b) = f_0 a (Suc b)"
]
val newopenconjs = top_level_updt_ctx_end @{context} openconjs
*}

ML{* my_rippling @{context} ["Suc (f_1 a (Suc b)) = f_1 a (Suc (Suc b))"]*}

 (* open conjectures for function: f_7*)
ML{* prove_and_capture @{context} ["f_7 a (f_7 b 0) = f_7 b (f_7 a 0)"] *}
ML{* prove_and_capture @{context} ["f_7 a (f_7 b c) = f_7 b (f_7 a c)"] *}
ML{* prove_and_capture @{context} ["f_7 a (Suc 0) = Suc (f_7 a 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_7 a 0) = f_7 a (Suc 0)"] *}


 (* open conjectures for function: f_6*)


 (* open conjectures for function: f_5*)

ML{* FC.filter_print_all_failures () *}

ML{* prove_and_capture @{context} ["f_5 a (f_5 b 0) = f_5 b (f_5 a 0)"] *}
ML{* prove_and_capture @{context} ["f_5 a (f_5 b c) = f_5 b (f_5 a c)"] *}
ML{* prove_and_capture @{context} ["f_5 a (Suc 0) = Suc (f_5 a 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_5 a 0) = f_5 a (Suc 0)"] *}


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


 (* open conjectures for function: f_2*)
ML{* prove_and_capture @{context} ["f_2 a (f_2 b 0) = f_2 b (f_2 a 0)"] *}
ML{* prove_and_capture @{context} ["f_2 a (f_2 b c) = f_2 b (f_2 a c)"] *}
ML{* prove_and_capture @{context} ["f_2 a (Suc 0) = Suc (f_2 a 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_2 a 0) = f_2 a (Suc 0)"] *}


 (* open conjectures for function: f_1*)
ML{* prove_and_capture @{context} ["f_1 a (f_1 b 0) = f_1 b (f_1 a 0)"] *}
ML{* prove_and_capture @{context} ["f_1 a (f_1 b c) = f_1 b (f_1 a c)"] *}
ML{* prove_and_capture @{context} ["f_1 a (Suc (Suc 0)) = Suc (f_1 a (Suc 0))"] *}
ML{* prove_and_capture @{context} ["f_1 a (Suc (Suc 0)) = Suc (Suc (f_1 a 0))"] *}
ML{* prove_and_capture @{context} ["f_1 a (Suc (Suc b)) = Suc (f_1 a (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_1 a (Suc (Suc b)) = Suc (Suc (f_1 a b))"] *}
ML{* prove_and_capture @{context} ["Suc (f_1 a (Suc 0)) = f_1 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (f_1 a (Suc b)) = f_1 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_1 a 0)) = f_1 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_1 a b)) = f_1 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_1 a (Suc 0) = Suc (f_1 a 0)"] *}
ML{* prove_and_capture @{context} ["f_1 a (Suc b) = Suc (f_1 a b)"] *}
ML{* prove_and_capture @{context} ["Suc (f_1 a 0) = f_1 a (Suc 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_1 a b) = f_1 a (Suc b)"] *}


 (* open conjectures for function: f_0*)
ML{* prove_and_capture @{context} ["f_0 a (f_0 b 0) = f_0 b (f_0 a 0)"] *}
ML{* prove_and_capture @{context} ["f_0 a (f_0 b c) = f_0 b (f_0 a c)"] *}
ML{* prove_and_capture @{context} ["f_0 a (Suc (Suc 0)) = Suc (f_0 a (Suc 0))"] *}
ML{* prove_and_capture @{context} ["f_0 a (Suc (Suc 0)) = Suc (Suc (f_0 a 0))"] *}
ML{* prove_and_capture @{context} ["f_0 a (Suc (Suc b)) = Suc (f_0 a (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_0 a (Suc (Suc b)) = Suc (Suc (f_0 a b))"] *}
ML{* prove_and_capture @{context} ["Suc (f_0 a (Suc 0)) = f_0 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (f_0 a (Suc b)) = f_0 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_0 a 0)) = f_0 a (Suc (Suc 0))"] *}
ML{* prove_and_capture @{context} ["Suc (Suc (f_0 a b)) = f_0 a (Suc (Suc b))"] *}
ML{* prove_and_capture @{context} ["f_0 a (Suc 0) = Suc (f_0 a 0)"] *}
ML{* prove_and_capture @{context} ["f_0 a (Suc b) = Suc (f_0 a b)"] *}
ML{* prove_and_capture @{context} ["Suc (f_0 a 0) = f_0 a (Suc 0)"] *}
ML{* prove_and_capture @{context} ["Suc (f_0 a b) = f_0 a (Suc b)"] *}


end