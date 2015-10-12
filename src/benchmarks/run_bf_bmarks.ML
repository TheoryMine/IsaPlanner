(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      benchmarks/run_bf_bmarks.ML
    Author:     Moa Johanson, University of Edinburgh
                
    Created:    2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    An ML file that when used will run through the benchmarks for 
    best-first rippling with sum of distance measure. Note
    that if one of the benchmarks is non-terminating you can hit
    control-C and it will note that benchmark as having raised an
    exception (failed).

    Benchmarks will be pretty printed to standard output. 

    FIXME: add timeout features. 

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* use "benchmarks/run_bmarks.ML"; *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Peano Arithmetic - add, mult are left recursive *)

val N1_problem_names = [
("N_add_0_left", "0 + a = (a :: N)"),
("N_add_0_right", "a + 0 = (a :: N)"),
("N_add_suc_right", "a + (suc b) = suc (a + b)"),
("N_add_commute", "a + b = b + (a :: N)"),
("N_add_assoc", "b + c + a = b + (c + (a :: N))"),
("N_add_left_commute", "a + (b + c) = b + (a + (c :: N))"),
("N_add_left_cancel", "(k + m = k + n) = (m = (n :: N))"),
("N_add_right_cancel", "(m + k = n + k) = (m = (n :: N))"),
("N_mult_0_left", "0 * (m::N)= 0"),
("N_mult_0_right", "(m::N) * 0 = 0"),
("N_mult_suc_right", "m * suc b = m + (m * b)"),
("N_mult_1_left", "(suc 0) * n = n"),
("N_mult_1_right", "n * (suc 0) = n"),
("N_mult_commute", "m * n = n * (m::N)"),
("N_add_mult_distrib", "(m + n) * k = (m * k) + ((n * k)::N)"),
("N_add_mult_distrib2", "k * (m + n) = (k * m) + ((k * n)::N)"),
("N_mult_assoc", "(m * n) * k = m * ((n * k)::N)"),
("N_mult_left_commute", "x * (y * z) = y * ((x * z)::N)"),
("N_mult_right_commute", "(x * y) * z = (x * z) * (y::N)"),
("N_power_squared", "x ^ (suc (suc 0)) = x * x"),
("N_power_1", "x ^ (suc 0) = x"),
("N_power_add", "i ^ (j + k) = i ^ j * i ^ (k ::N)")
(* ("N_power_mult", "i ^ (j * k) = (i ^ j) ^ (k ::N)") 
-- non terminating, unless you use counter example checking... *)
];



use_thy "benchmarks/BMark_N1";
val N1_problems = IsaPBenchmarks.mk_problems "BMark_N1" N1_problem_names;
val msearch = RState.search (MSearch.depthfs());
val N1_P = IsaPBenchmarks.pretty_one_benchmark_problems msearch 
                                  Bf_Rippling_dsum.induct_ripple_conj
                                  N1_problems;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Peano Arithmetic - add, mult are right recursive *)

val N2_problem_names = [
("N_add_0_left", "0 + a = (a :: N)"),
("N_add_0_right", "a + 0 = (a :: N)"),
("N_add_suc_right", "a + (suc b) = suc (a + b)"),
("N_add_commute", "a + b = b + (a :: N)"),
("N_add_assoc", "b + c + a = b + (c + (a :: N))"),
("N_add_left_commute", "a + (b + c) = b + (a + (c :: N))"),
("N_add_left_cancel", "(k + m = k + n) = (m = (n :: N))"),
("N_add_right_cancel", "(m + k = n + k) = (m = (n :: N))"),
("N_mult_0_left", "0 * (m::N)= 0"),
("N_mult_0_right", "(m::N) * 0 = 0"),
("N_mult_suc_right", "m * suc b = m + (m * b)"),
("N_mult_1_left", "(suc 0) * n = n"),
("N_mult_1_right", "n * (suc 0) = n"),
("N_mult_commute", "m * n = n * (m::N)"),
("N_add_mult_distrib", "(m + n) * k = (m * k) + ((n * k)::N)"),
("N_add_mult_distrib2", "k * (m + n) = (k * m) + ((k * n)::N)"),
("N_mult_assoc", "(m * n) * k = m * ((n * k)::N)"),
("N_mult_left_commute", "x * (y * z) = y * ((x * z)::N)"),
("N_mult_right_commute", "(x * y) * z = (x * z) * (y::N)"),
("N_power_squared", "x ^ (suc (suc 0)) = x * x"),
("N_power_1", "x ^ (suc 0) = x"),
("N_power_add", "i ^ (j + k) = i ^ j * i ^ (k ::N)"),
("N_power_mult", "i ^ (j * k) = (i ^ j) ^ (k ::N)")
];


use_thy "benchmarks/BMark_N2";

val N2_problems = IsaPBenchmarks.mk_problems "BMark_N2" N2_problem_names;

val N2_P = IsaPBenchmarks.pretty_one_benchmark_problems msearch
                                  Bf_Rippling_dsum.induct_ripple_conj 
                                  N2_problems;

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
(* , ("", "") *)
];
use_thy "benchmarks/BMark_NL";

val NL_problems = IsaPBenchmarks.mk_problems "BMark_NL" NL_problem_names;

val NL_P = IsaPBenchmarks.pretty_one_benchmark_problems msearch 
                                  Bf_Rippling_dsum.induct_ripple_conj 
                                  NL_problems;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Orinal Arithmetic *)
(*
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

use_thy "theories/BMark_O";

val O_problems = IsaPBenchmarks.mk_problems "BMark_O" O_problem_names;

val O_P = IsaPBenchmarks.benchmark_problems msearch
                                  Bf_Rippling_dsum.induct_and_ripple_rtechn 
                                  O_problems;
*)
Pretty.writeln 
  (Pretty.chunks 
   [Pretty.str "\n --- Peano Arithmetic 1 (recursive on left) ---",
    N1_P,
    Pretty.str "\n --- Peano Arithmetic 2 (recursive on right) ---",
    N2_P,
    Pretty.str "\n --- Peano Arithmetic 1 + Lists ---",
    NL_P]);
   (* Pretty.str "\n --- Ordinal Arithmetic ---",
    O_P]); *)
(*
 IsaPBenchmarks.benchmark_problems PPInterface.depth_fs
                                  IndAndSimpIsarRTechn.my_simp_and_induct_techn 
                                  N1_problems;


use_thy "theories/BMark_N2";

val N2_problems = IsaPBenchmarks.mk_problems "BMark_N2" N_problem_names;

IsaPBenchmarks.benchmark_problems PPInterface.depth_fs
                                  Bf_RipplingRTechn.induct_and_ripple_rtechn 
                                  N2_problems;

IsaPBenchmarks.benchmark_problems PPInterface.depth_fs
                                  IndAndSimpIsarRTechn.my_simp_and_induct_techn 
                                  N2_problems;
*)
