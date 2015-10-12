(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      benchmarks/run_quick_bmarks.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    12 Sep 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Quick test of benchmarking, few theories, few problems, small timeout. 
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* The different Basic definitions of Peano arithmetic *)
use_thy "benchmarks/N/BMark_N";
use_thy "benchmarks/N/BMark_N_a1";        
use_thy "benchmarks/N/BMark_N_a2";        

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* different theories *)
val theory_names = 
["BMark_N_a1_m1_e1", "BMark_N_a2_m4_e2"];

(* load them all *)
map (fn s => use_thy ("benchmarks/N/"^s)) theory_names;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Different versions of rippling *)
val techniques = 
[
("rtechn_dsum",RippleRTechn_dsum.induct_ripple_conj),
(* ("wdsum",RippleRTechn_wdsum.induct_ripple_conj), *)
("rtechn_compound_sinkr_flat",RippleRTechn_compound_sinkr_flat.induct_ripple_conj)
];

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Peano Arithmetic Theorems *)
val N_theorems = [
("add_0_left", "0 + a = (a :: N)"),
("add_left_commute", "a + (b + c) = b + (a + (c :: N))"),
("add_mult_distrib2", "k * (m + n) = (k * m) + ((k * n)::N)"),
("power_mult", "i ^ (j * k) = (i ^ j) ^ (k ::N)")
]; (* 23 theorems *)

val N_specialised_theorems = [
("SP_add_0_0_left", "0 + 0 + a = (a :: N)"),
("SP_add_0_a_right", "a + 0 + a = (a :: N) + a")
]; (* 12 specialised theorems *)

val N_nontheorems = [
("NT_add_0_left", "0 + a = (0 :: N)"),
("NT_mult_1_right1", "n * (suc 0) = suc 0"),
("NT_power_mult4", "i ^ (j * k) = (i + j) * (k ::N)")
]; (* 55 non-theorems *)

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
