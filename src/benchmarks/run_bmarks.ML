(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      benchmarks/run_bmarks.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    4 Oct 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    An ML file that when used will run through the benchmarks. 
*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* use "benchmarks/run_bmarks.ML"; *)

(*
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*   quick test                                                        *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
use_thy "benchmarks/BMark_N1";
val N_quicktest = [
("add_assoc", "b + c + a = b + (c + (a :: N))"),
("add_commute", "a + b = b + (a :: N)"),
("SP_add_0_a_right", "a + 0 + a = (a :: N) + a"),
("NT_add_suc_suc_right", "a + (suc b) = suc (suc a + b)")
];
val _ = BMarkTimeOut.benchmark 
          PPInterface.depth_fs
          RippleRTechn.induct_ripple_conj
          "RippleRTechn.induct_ripple_conj"
          "BMark_N1"
          N_quicktest;
*)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*   PEANO ARITHMETIC THEORIES                                         *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* The different Basic definitions of Peano arithmetic *)
use_thy "benchmarks/N/BMark_N";
use_thy "benchmarks/N/BMark_N_a1";        
use_thy "benchmarks/N/BMark_N_a2";        
use_thy "benchmarks/N/BMark_N_a3";        
use_thy "benchmarks/N/BMark_N_a4";
use_thy "benchmarks/N/BMark_N_e1";
use_thy "benchmarks/N/BMark_N_e2";
use_thy "benchmarks/N/BMark_N_m1";
use_thy "benchmarks/N/BMark_N_m2";
use_thy "benchmarks/N/BMark_N_m3";
use_thy "benchmarks/N/BMark_N_m4";

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* different theories *)
val theory_names = 
["BMark_N_a1_m1_e1",
"BMark_N_a2_m4_e2",
"BMark_N_a4_m3_e2",
"BMark_N_a1_m1_e2",  
"BMark_N_a4_m4_e1",
"BMark_N_a1_m2_e1",  
"BMark_N_a3_m1_e1",  
"BMark_N_a4_m4_e2",
"BMark_N_a1_m2_e2",  
"BMark_N_a3_m1_e2",  
"BMark_N_a1_m3_e1",  
"BMark_N_a3_m2_e1",  
"BMark_N_a1_m3_e2",  
"BMark_N_a3_m2_e2",  
"BMark_N_a1_m4_e1",  
"BMark_N_a3_m3_e1",  
"BMark_N_a1_m4_e2",  
"BMark_N_a3_m3_e2",  
"BMark_N_a3_m4_e1",  
"BMark_N_a2_m1_e1",  
"BMark_N_a3_m4_e2",  
"BMark_N_a2_m1_e2",  
"BMark_N_a2_m2_e1",  
"BMark_N_a4_m1_e1",  
"BMark_N_a2_m2_e2",  
"BMark_N_a4_m1_e2",  
"BMark_N_a2_m3_e1",  
"BMark_N_a4_m2_e1",  
"BMark_N_a2_m3_e2",  
"BMark_N_a4_m2_e2",
"BMark_N_a2_m4_e1",  
"BMark_N_a4_m3_e1"];

(* load them all *)
map (fn s => use_thy ("benchmarks/N/"^s)) theory_names;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Different versions of rippling *)
val techniques = 
[
("rtechn_dsum",RippleRTechn_dsum.induct_ripple_conj),
(* ("wdsum",RippleRTechn_wdsum.induct_ripple_conj), *)
("rtechn_compound_sinkr_flat",RippleRTechn_compound_sinkr_flat.induct_ripple_conj),
("rtechn_compound_sinkr_ho",RippleRTechn_compound_sinkr_ho.induct_ripple_conj),
("rtechn_compound_unrest_flat",RippleRTechn_compound_unrest_flat.induct_ripple_conj),
("rtechn_compound_unrest_ho",RippleRTechn_compound_unrest_ho.induct_ripple_conj),
("rtechn_maxsplit_sinkr_flat",RippleRTechn_maxsplit_sinkr_flat.induct_ripple_conj),
("rtechn_maxsplit_sinkr_ho",RippleRTechn_maxsplit_sinkr_ho.induct_ripple_conj),
("rtechn_maxsplit_unrest_flat",RippleRTechn_maxsplit_unrest_flat.induct_ripple_conj),
("rtechn_maxsplit_unrest_ho",RippleRTechn_maxsplit_unrest_ho.induct_ripple_conj)
];

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Peano Arithmetic Theorems *)
val N_theorems = [
("add_0_left", "0 + a = (a :: N)"),
("add_0_right", "a + 0 = (a :: N)"),
("add_suc_right", "a + (suc b) = suc (a + b)"),
("add_commute", "a + b = b + (a :: N)"),
("add_assoc", "b + c + a = b + (c + (a :: N))"),
("add_left_commute", "a + (b + c) = b + (a + (c :: N))"),
("add_right_commute", "(a + b) + c = (a + c) + (b :: N)"),
("add_left_cancel", "(k + m = k + n) = (m = (n :: N))"),
("add_right_cancel", "(m + k = n + k) = (m = (n :: N))"),
("mult_0_left", "0 * (m::N)= 0"),
("mult_0_right", "(m::N) * 0 = 0"),
("mult_suc_left", "suc m * b = b + (m * b)"),
("mult_suc_right", "m * suc b = m + (m * b)"),
("mult_1_left", "(suc 0) * n = n"),
("mult_1_right", "n * (suc 0) = n"),
("mult_commute", "m * n = n * (m::N)"),
("add_mult_distrib", "(m + n) * k = (m * k) + ((n * k)::N)"),
("add_mult_distrib2", "k * (m + n) = (k * m) + ((k * n)::N)"),
("mult_assoc", "(m * n) * k = m * ((n * k)::N)"),
("mult_left_commute", "x * (y * z) = y * ((x * z)::N)"),
("mult_right_commute", "(x * y) * z = (x * z) * (y::N)"),
("power_squared", "x ^ (suc (suc 0)) = x * x"),
("power_1", "x ^ (suc 0) = x"),
("power_add", "i ^ (j + k) = i ^ j * i ^ (k ::N)"),
("power_mult", "i ^ (j * k) = (i ^ j) ^ (k ::N)")
]; (* 25 theorems *)


val N_specialised_theorems = [
("SP_add_0_0_left", "0 + 0 + a = (a :: N)"),
("SP_add_0_a_right", "a + 0 + a = (a :: N) + a"),
("SP_add_suc_suc_right", "suc a + (suc b) = suc suc (a + b)"),
("SP_add_a_a_commute", "a + a + b = b + ((a :: N) + a)"),
("SP_add_assoc", "d + b + c + a = b + (c + ((a :: N) + d))"),
("SP_add_left_cancel", "(suc 0 + m = suc 0 + n) = (m = (n :: N))"),
("SP_add_right_cancel", "(m + suc 0 = n + suc 0) = (m = (n :: N))"),
("SP_mult_0_left_n_plus_m", "0 * (n + m::N)= 0"),
("SP_mult_0_left_m_k", "0 * (m::N) * k = 0"),
("SP_mult_0_right_n_plus_m", "(n + m::N) * 0 = 0"),
("SP_mult_suc_right_and_distr_mult", "(m * suc b) * k = m * k + (m * b) * k"),
("SP_power_add_add", "i ^ (j + k + l) = i ^ j * i ^ (k ::N) * i ^ (l ::N)")
]; (* 12 specialised theorems *)


val N_nontheorems = [
("NT_add_0_left", "0 + a = (0 :: N)"),
("NT_add_0_right", "a + 0 = (0 :: N)"),
("NT_add_commute", "a + b = a + (a :: N)"), 
("NT_add_suc_suc_right", "a + (suc b) = suc (suc a + b)"),
("NT_add_assoc1", "b + c + a = b + (c + (c :: N))"),
("NT_add_assoc2", "b + c + a = b + (c + (b :: N))"),
("NT_add_assoc3", "b + c + a = c + (c + (a :: N))"),
("NT_add_left_cancel", "(k + m = k + n) = (k = (n :: N))"), 
("NT_add_right_cancel", "(m + k = n + k) = (k = (n :: N))"), 
("NT_mult_0_left", "0 * (m::N)= m"),
("NT_mult_0_right", "(m::N) * 0 = m"),
("NT_mult_suc_right1", "m * suc b = b + (m * b)"),
("NT_mult_suc_right2", "m * suc b = m * (m + b)"),
("NT_mult_suc_right3", "m * suc b = b * (m + b)"),
("NT_mult_1_left1", "(suc 0) * n = suc 0"),
("NT_mult_1_left2", "(suc 0) * n = 0"),
("NT_mult_1_left3", "(suc 0) * n = n + n"),
("NT_mult_1_right1", "n * (suc 0) = suc 0"),
("NT_mult_1_right2", "n * (suc 0) = 0"),
("NT_mult_1_right3", "n * (suc 0) = n + n"),
("NT_mult_commute1", "m * n = m * (m::N)"),
("NT_mult_commute2", "m * n = n + (m::N)"),
("NT_add_mult_distrib1", "(m + n) * k = (m * k) * ((n * k)::N)"),
("NT_add_mult_distrib2", "(m + n) * k = (m + k) + ((n * k)::N)"),
("NT_add_mult_distrib3", "(m + n) * k = (m * k) + ((n + k)::N)"),
("NT_add_mult_distrib4", "(m + n) * k = (m * n) + ((n * k)::N)"),
("NT_add_mult_distrib5", "(m + n) * k = (m + k) * ((n + k)::N)"),
("NT_add_mult_distrib2_1", "k * (m + n) = (k * m) * ((k * n)::N)"),
("NT_add_mult_distrib2_2", "k * (m + n) = (k + m) + ((k * n)::N)"),
("NT_add_mult_distrib2_3", "k * (m + n) = (k * m) + ((k + n)::N)"),
("NT_add_mult_distrib2_4", "k * (m + n) = (k * n) + ((k * n)::N)"),
("NT_add_mult_distrib2_5", "k * (m + n) = (k + m) * ((k + n)::N)"),
("NT_mult_assoc2", "(m * n) * k = m + ((n + k)::N)"),
("NT_mult_assoc3", "(m * n) * k = m * ((m * k)::N)"),
("NT_mult_assoc4", "(m * n) * k = m + ((n * k)::N)"),
("NT_mult_left_commute1", "x * (y * z) = y * ((y * z)::N)"),
("NT_mult_left_commute2", "x * (y * z) = z * ((x * z)::N)"),
("NT_mult_right_commute1", "(x * y) * z = (x * y) * (y::N)"),
("NT_mult_right_commute2", "(x * y) * z = (y * z) * (y::N)"),
("NT_power_squared1", "x ^ (suc  0) = x * x"),
("NT_power_squared2", "x ^ (suc (suc 0)) = x + x"),
("NT_power_squared3", "x ^ (suc (suc 0)) = x * (suc x)"),
("NT_power_1_1", "x ^ (suc 0) = 0"),
("NT_power_1_2", "x ^ (suc 0) = suc 0"),
("NT_power_1_3", "x ^ 0 = x"),
("NT_power_add1", "i ^ (j + k) = i ^ j + i ^ (k ::N)"),
("NT_power_add2", "i ^ (j + k) = i ^ (j ^ (k ::N))"),
("NT_power_add3", "i ^ (j + k) = i ^ j * j ^ (k ::N)"),
("NT_power_add4", "i ^ (j + k) = j ^ k * i ^ (k ::N)"),
("NT_power_add5", "i ^ (j + k) = (i ^ j) ^ (k ::N)"),
("NT_power_mult1", "i ^ (j * k) = (i * j) ^ (k ::N)"),
("NT_power_mult2", "i ^ (j * k) = (i ^ j) * (k ::N)"),
("NT_power_mult3", "i ^ (j * k) = (i + j) ^ (k ::N)"),
("NT_power_mult4", "i ^ (j * k) = (i + j) * (k ::N)")
]; (* 55 non-theorems *)


(* 92 problems *)
val all_PA_problems = N_theorems @ N_specialised_theorems @ N_nontheorems;

fun bmarkit srchf problems (thry,(technname,techn)) = 
    IsaPBenchmarksSql.benchmark_problems 
      (Time.fromSeconds 5) srchf (technname,techn) 
      (IsaPBenchmarksSql.mk_problems (theory thry) problems);

(* now run benchmarks on all combinations of theories and techniques *)
map 
  (bmarkit 
     PPInterface.depth_fs
     all_PA_problems)
  (IsaPLib.all_pairs theory_names techniques);


exit 0;

(* 

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Peano Arith and Lists *)
val NL_problem_names = [
("append_assoc", "(x @ y) @ z = x @ (y @ z)"),
("append_nil2", "l = l @ []"),
("len_append", "len (x @ y) = (len x) + (len y)"),
("map_append", "map f (x @ y) = (map f x) @ (map f y)"),
("rev_rev", "rev (rev x) = x"),
("rev_rev_append", "rev (rev t @ l) = rev l @ t"),
("rev_append_distr", "rev (a @ b) = rev b @ rev a"),
("rev_map", "rev (map f x) = map f (rev x)"),
("rev_qrev", "rev x = qrev x []"),
("rev_qrev_gen", "(qrev x y)= (rev x) @ y"),
("qrev_qrev", "qrev (qrev x []) [] = x"),
("qrev_qrev_gen", "qrev (qrev xs ys) zs = xs @ qrev ys zs"),
("len_qrev", "len (qrev x []) = len x"),
("qrev_map", "qrev (map f x) [] = map f (qrev x [])"),
("len_rev", "len (rev x) = len x"),
("len_map", "len (map f x) = len x"),
("rot_append", "rot (len l, l @ k) = k @ l"),
("rot_len", "rot (len l, l) = l")
];

(* use_thy "theories/BMark_NL"; *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Orinal Arithmetic *)

val O_problem_names = [
("assoc_add", "(x + y) + z = (x + y) + (z :: Ord)"),
("distr_mult_add", "x * (y + z) = (x * y) + (x * (z :: Ord))"),
("assoc_mult", "a * b * c = a * (b * c :: Ord)"),
("exp_add", "x ^ (y + z) = (x ^ y :: Ord) * (x ^ z)"),
("exp_mult", "x ^ (y * z) = (x ^ y :: Ord) ^ z"),
("add_Zero_left", "Zero + x = x"),
("mult_Zero_left", "Zero * x = Zero"),
("exp_of_one", "(Sc Zero) ^ x = (Sc Zero)")
];

(* use_thy "theories/BMark_O"; *)


*)
