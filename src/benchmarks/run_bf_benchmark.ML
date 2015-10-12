(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      bestFirstTest.ML
    Author:     Moa Johansson
    Created:    24/1 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

   Examples to test and evaluate Best-first rippling. Runs best-first and
   ordinary rippling on a various problems.

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
val depthfs = RState.search (MSearch.depthfs()); 
val bestfs = RState.search (MSearch.bestfs(Bf_Rippling_dsum.compare_rsts));


val bestfs_delayed =  RState.delayed_search (MSearch.bestfs(Bf_Rippling_dsum.compare_rsts));
  

val techs = [
("bf_basic", (Bf_Rippling_dsum.induct_ripple_conj 
                Bf_Rippling_dsum.basic_bf_steps) ),

("bf_eager", (Bf_Rippling_dsum.induct_ripple_conj 
                Bf_Rippling_dsum.basic_bf_eager_steps)),

("bf_global", (Bf_Rippling_dsum.induct_ripple_conj 
                Bf_Rippling_dsum.global_bf_steps)),

("bf_lemma", (Bf_Rippling_dsum.induct_ripple_conj 
                Bf_Rippling_dsum.bf_lemmaconj_steps)),

("bf_dsum", (RippleRTechn_dsum.induct_ripple_conj))
];

val techs_2 = [
("bf_basic_stacked", (Bf_Rippling_dsum.st_induct_ripple_conj 
                Bf_Rippling_dsum.basic_bf_steps) ),

("bf_eager_stacked", (Bf_Rippling_dsum.st_induct_ripple_conj 
                Bf_Rippling_dsum.basic_bf_eager_steps)),

("bf_global_stacked", (Bf_Rippling_dsum.st_induct_ripple_conj 
                Bf_Rippling_dsum.global_bf_steps)),

("dsum", (RippleRTechn_dsum.induct_ripple_conj)),

("simp", (RippleRTechn_dsum.induct_simp_conj))
];

val techs_3 = [
("bf_basic_delay", (Bf_Rippling_dsum.d_induct_ripple_conj 
                Bf_Rippling_dsum.basic_bf_steps) ),

("bf_eager_delay", (Bf_Rippling_dsum.d_induct_ripple_conj 
                Bf_Rippling_dsum.basic_bf_eager_steps)),

("bf_global_delay", (Bf_Rippling_dsum.d_induct_ripple_conj 
                Bf_Rippling_dsum.global_bf_steps))
]

val techs_2step_bf =[
("bf_basic", (Bf_Rippling_dsum.induct_ripple_conj_with_rule  
                Bf_Rippling_dsum.basic_bf_steps "two_step") ),

("bf_eager", (Bf_Rippling_dsum.induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.basic_bf_eager_steps "two_step")),


("bf_global", (Bf_Rippling_dsum.induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.global_bf_steps "two_step")),

("bf_lemma", (Bf_Rippling_dsum.induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.bf_lemmaconj_steps "two_step")),

("bf_dsum", (RippleRTechn_dsum.induct_ripple_conj_with_rule "two_step"))

];

val techs_2step_df =[
("bf_basic_stacked", (Bf_Rippling_dsum.st_induct_ripple_conj_with_rule  
                Bf_Rippling_dsum.basic_bf_steps "two_step") ),

("bf_eager_stacked", (Bf_Rippling_dsum.st_induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.basic_bf_eager_steps "two_step")),

("bf_global_stacked", (Bf_Rippling_dsum.st_induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.global_bf_steps "two_step")),

("dsum", (RippleRTechn_dsum.induct_ripple_conj_with_rule "two_step")),

("simp", (RippleRTechn_dsum.induct_simp_conj_rule "two_step"))

]; 

val techs_3_2step = [
("bf_basic_delay", (Bf_Rippling_dsum.d_induct_ripple_conj_with_rule  
                Bf_Rippling_dsum.basic_bf_steps "two_step") ),

("bf_eager_delay", (Bf_Rippling_dsum.d_induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.basic_bf_eager_steps "two_step")),

("bf_global_delay", (Bf_Rippling_dsum.d_induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.global_bf_steps "two_step"))
]

val techs_3step_bf =[
("bf_basic", (Bf_Rippling_dsum.induct_ripple_conj_with_rule  
                Bf_Rippling_dsum.basic_bf_steps "three_step") ),

("bf_eager", (Bf_Rippling_dsum.induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.basic_bf_eager_steps "three_step")),

("bf_global", (Bf_Rippling_dsum.induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.global_bf_steps "three_step")),

("bf_lemma", (Bf_Rippling_dsum.induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.bf_lemmaconj_steps "three_step")),

("bf_dsum", (RippleRTechn_dsum.induct_ripple_conj_with_rule "three_step"))

];
val techs_3step_df =[
("bf_basic_stacked", (Bf_Rippling_dsum.st_induct_ripple_conj_with_rule  
                Bf_Rippling_dsum.basic_bf_steps "three_step") ),

("bf_eager_stacked", (Bf_Rippling_dsum.st_induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.basic_bf_eager_steps "three_step")),

("bf_global_stacked", (Bf_Rippling_dsum.st_induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.global_bf_steps "three_step")),

("dsum", (RippleRTechn_dsum.induct_ripple_conj_with_rule "three_step")),

("simp", (RippleRTechn_dsum.induct_simp_conj_rule "three_step"))

]; 


val techs_3_3step = [
("bf_basic_delay", (Bf_Rippling_dsum.d_induct_ripple_conj_with_rule  
                Bf_Rippling_dsum.basic_bf_steps "three_step") ),

("bf_eager_delay", (Bf_Rippling_dsum.d_induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.basic_bf_eager_steps "three_step")),

("bf_global_delay", (Bf_Rippling_dsum.d_induct_ripple_conj_with_rule 
                Bf_Rippling_dsum.global_bf_steps "three_step"))
];


use_thy "benchmarks/BMark_N1";
val theory_names = ["BMark_N1"];
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Peano Arithmetic Theorems *)
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
      (Time.fromSeconds 30) srchf (technname,techn) 
      (IsaPBenchmarksSql.mk_problems (theory thry) problems);

(* now run benchmarks on all combinations of theories and techniques *)
map 
  (bmarkit 
     bestfs
     all_PA_problems)
  (IsaPLib.all_pairs theory_names techs);

map 
  (bmarkit 
     depthfs
     all_PA_problems)
  (IsaPLib.all_pairs theory_names techs_2);

map 
  (bmarkit 
     bestfs_delayed
     all_PA_problems)
  (IsaPLib.all_pairs theory_names techs_3);

(*------------------------------------------------------------------*)
(* Lists                                                            *)
(*------------------------------------------------------------------*)  
use_thy "benchmarks/BMark_NL";
val theory_names_l = ["BMark_NL"];

(* Peano Arith and Lists *)
val NL_problem_names = [
("L_append_assoc", "(x @ y) @ z = x @ (y @ z)"),
("L_append_nil2", "l = l @ []"),
("L_len_append", "len (x @ y) = (len x) + (len y)"),
("L_map_append", "map f (x @ y) = (map f x) @ (map f y)"),
("L_rev_rev", "rev (rev x) = x"),
("L_rev_rev_append", "rev (rev t @ l) = rev l @ t"),
("L_rev_append_distr", "rev (a @ b) = rev b @ rev a"),
("L_rev_map", "rev (map f x) = map f (rev x)"),
("L_rev_qrev", "rev x = qrev x []"),
("L_rev_qrev_gen", "(qrev x y)= (rev x) @ y"),
("L_qrev_qrev", "qrev (qrev x []) [] = x"),
("L_qrev_qrev_gen", "qrev (qrev xs ys) zs = xs @ qrev ys zs"),
("L_len_qrev", "len (qrev x []) = len x"),
("L_qrev_map", "qrev (map f x) [] = map f (qrev x [])"),
("L_len_rev", "len (rev x) = len x"),
("L_len_map", "len (map f x) = len x"),
("L_rot_append", "rot (len l, l @ k) = k @ l"),
("L_rot_len", "rot (len l, l) = l")
];
(* 18 theorems *)

map 
  (bmarkit 
     bestfs
     NL_problem_names)
  (IsaPLib.all_pairs theory_names_l techs);

map 
  (bmarkit 
     depthfs
     NL_problem_names)
  (IsaPLib.all_pairs theory_names_l techs_2);

map 
  (bmarkit 
     bestfs_delayed
     NL_problem_names)
  (IsaPLib.all_pairs theory_names_l techs_3);

(*------------------------------------------------------------------*)
(* Specialities for best first                                      *)
(*------------------------------------------------------------------*)
use_thy "benchmarks/BestF_N";
val theory_names_bf = ["BestF_N"];

val bf_PN = [
("BF_PN_binom_minus", "binom(x, suc 0) - (x ::N) = 0"),
("BF_PN_evenR_times2_r", "evenR(suc(suc(0)) * (n::N))"),
("BF_PN_evenR_times2_l", "evenR((n::N) * suc(suc 0))"),
("BF_PN_evenM_times2_r", "evenM(suc(suc(0)) * (n::N))"),
("BF_PN_evenM_times2_l", "evenM((n::N) * suc(suc 0))"),
("BF_PN_ZeroMod_times3_r","ZMT (suc(suc(suc 0)) * (n::N))"),
("BF_PN_ZeroMod_times3_l","ZMT ((n::N) * suc(suc(suc 0)))"),
("BF_PN_Manning7", "(x::N) + ((suc(suc z)) * y) = x + (y * (suc(suc z)))"),
("BF_PN_destr_Add","x~=0 --> x + y = suc((pre x) + y)"),
("BF_PN_destr_Mult","x~=0 --> (x::N) * y = ((pre x) * y) + y"),
("BF_PN_destr_sum", "sum (n::N) = sum(pre n) + n"),
("BF_PN_destr_double", "n~=0 --> double n = suc(suc(double(pre n)))")
]; 
(* 12 theorems *)

map 
  (bmarkit 
     bestfs
     bf_PN)
  (IsaPLib.all_pairs theory_names_bf techs);

map 
  (bmarkit 
     depthfs
     bf_PN)
  (IsaPLib.all_pairs theory_names_bf techs_2);

map 
  (bmarkit 
     bestfs_delayed
     bf_PN)
  (IsaPLib.all_pairs theory_names_bf techs_3);

(* Two step induction *)
val bf_2step_PN = [
("2ST_Mut_even_or_suc" , "evenM(n::N) | evenM(suc n)"),
("2ST_Mut_even_or_odd", "evenM(n::N) | oddM(n)"),
("2ST_Mut_even_not_odd", "evenM(n::N) = (~oddM(n))"),
("2ST_Mut_even_not_suc", "evenM(n::N) = (~evenM(suc n))"),
("2ST_Mut_plus2_r", "evenM(n::N) = evenM(n + suc(suc(0)))"), 
("2ST_Mut_plus2_l", "evenM(n::N) = evenM(suc(suc(0)) + n)"),
("2ST_Mut_add_evens","(evenM(n::N) = evenM(m::N))= evenM(n+m)")
];(* 7 theorems *)

map 
  (bmarkit 
     bestfs
     bf_2step_PN)
  (IsaPLib.all_pairs theory_names_bf techs_2step_bf);

map 
  (bmarkit 
     depthfs
     bf_2step_PN)
  (IsaPLib.all_pairs theory_names_bf techs_2step_df);

map 
  (bmarkit 
     bestfs_delayed
     bf_2step_PN)
  (IsaPLib.all_pairs theory_names_bf techs_3_2step);

(*Three (!) step induction *)
val bf_3step = [
("3ST_Mod3_disj", "ZMT n | OMT n| TMT n"),
("3ST_Zero_Mod3", "ZMT n | ZMT (suc n) | ZMT (suc (suc n))"),
("3ST_Zero_Mod3_times3_r", "ZMT (n::N)= ZMT(suc(suc(suc 0)) + n)"),
("3ST_Zero_Mod3_times3_l", "ZMT (n::N)= ZMT(n + suc(suc(suc 0)) )")
];  (*4 theorems*)

map 
  (bmarkit 
     bestfs
     bf_3step)
  (IsaPLib.all_pairs theory_names_bf techs_3step_bf);

map 
  (bmarkit 
     depthfs
     bf_3step)
  (IsaPLib.all_pairs theory_names_bf techs_3step_df);

map 
  (bmarkit 
     bestfs_delayed
     bf_3step)
  (IsaPLib.all_pairs theory_names_bf techs_3_3step);

use_thy "benchmarks/BestF_L";
val theory_names_L = ["BestF_L"];

(* Lists *)
val bf_lists = [
("BF_L_len_app", "(len (x @ y)) = (len (y@x))"),
("BF_L_double_len_app", "double(len (x @ y)) = double(len (y@x))"),
("BF_L_rev_upto_downto", "(down_to (n+m)) = rev(up_to (n+m))"),
("BF_L_len_rev_upto_downto","len((up_to (n+m))) = len(rev(down_to (n+m)))"),
("BF_L_evenM_pairify", "evenM(len (pairify l))"),
("BF_L_destr_pairify","l~=[] --> pairify(l) = (head l)#(head l)#(pairify (tail l))"),
("BF_L_Gen_destr_len","pre(len l) = len(tail l)"),
("BF_L_destr_len","l~= [] --> len l = suc(len(tail l))"),
("BF_L_destr_rev", "l~=[] --> rev(l) = rev(tail l) @ ((head l)#[])"),
("BF_L_destr_qrev", "l~=[] --> qrev l [] = qrev(tail l) [] @ ((head l)#[])"),
("BF_L_destr_map","l~= [] --> map f l = f(head l) # (map f (tail l))"),
("BF_L_destr_app","l~= [] --> l @ m = (head l)#((tail l) @ m )"),
("BF_L_destr_mem", "l~= [] --> x mem l = (if x=(head l) then True else x mem (tail l))"),
("BF_L_destr_upto","n~=0 --> up_to n = (up_to (pre n))@(n#[])"),
("BF_L_destr_downto", "n~=0 --> down_to n = n#(down_to (pre n))"),
("BF_L_zip_pairify", "zip l l = pairify l")
]; (* 15 theorems *)

map 
  (bmarkit 
     bestfs
     bf_lists)
  (IsaPLib.all_pairs theory_names_L techs);

map 
  (bmarkit 
     depthfs
     bf_lists)
  (IsaPLib.all_pairs theory_names_L techs_2);

map 
  (bmarkit 
     bestfs_delayed
     bf_lists)
  (IsaPLib.all_pairs theory_names_L techs_3);
