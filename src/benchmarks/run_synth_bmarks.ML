
use "synthesis/synth_prf_tools.ML";
use "synthesis/constInfo.ML";
use "synthesis/synthesise.ML";


use_thy "benchmarks/synth_theories/N_plus_mult";
use_thy "benchmarks/synth_theories/N_plus_mult_exp";
use_thy "benchmarks/synth_theories/Tree_size_height";
use_thy "benchmarks/synth_theories/List_rev_len";
use_thy "benchmarks/synth_theories/List_rev_map";
use_thy "benchmarks/synth_theories/List_rev_qrev";
use_thy "benchmarks/synth_theories/List_rev_len_plus";
use_thy "benchmarks/synth_theories/List_fold";

use "benchmarks/synth_benchmarks.ML";
(*
val thys = map theory ["N_plus_mult", "List_rev_len", "List_rev_map",
                       "List_rev_qrev", "Tree_size_height", "N_plus_mult_exp",
                       "List_rev_len_plus"]; 

(* Don't run on expeonetiation, it raises exceptions on size 9. *) 
val thys2 = map theory ["N_plus_mult","List_rev_len", "List_rev_map",
                       "Tree_size_height", "List_rev_qrev",
                       "List_rev_len_plus"]; 
*)
(*
(* Run with minsize =3, max_size = 8, max_vars = 2 *)
map (SynthBenchmarks.bmarks_of_thy_ac (3, 8) 2) thys;
(* Run with minsize =3, max_size = 8, max_vars = 3 *)
map (SynthBenchmarks.bmarks_of_thy_ac (3, 8) 3) thys;

(* Run with minsize =3, max_size = 10, max_vars = 2 *)
map (SynthBenchmarks.bmarks_of_thy_ac (3, 10) 2) thys2;
(* Run with minsize =3, max_size = 10, max_vars = 3 *)
map (SynthBenchmarks.bmarks_of_thy_ac (3, 10) 3) thys2;
*)
(*SynthBenchmarks.bmarks_of_thy_ac (3, 10) 2 (theory "Tree_size_height"); *)
val thy1 = theory "N_plus_mult";
val thy2 = theory "N_plus_mult_exp";
val thy3 = theory "Tree_size_height";
val thy4 = theory "List_rev_len";
val thy5 = theory "List_rev_map";
val thy6 = theory "List_rev_qrev";
val thy7 = theory "List_rev_len_plus";
val thy8 = theory "List_fold";

fun benchmark_thy_2 thy =
    SynthBenchmarks.bmarks_of_thy_ac (3, 14) 2 thy;

fun benchmark_thy_3 thy =
    SynthBenchmarks.bmarks_of_thy_ac (3, 14) 3 thy;

fun benchmark_thy_4 thy =
    SynthBenchmarks.bmarks_of_thy_ac (3, 14) 4 thy;

benchmark_thy_3 thy3;

(* Run benchmarks again! *)
(* Exp only runs up to 8 then counterex run out of memory *)
(* SynthBenchmarks.bmarks_of_thy_ac (3, 8) 2 thy2;*)
(*SynthBenchmarks.bmarks_of_thy_ac (3, 8) 3 thy2; *)

(* nat mult *)
(* DONE benchmark_thy_3 thy1; *)

(* Lists *)
(*
benchmark_thy_2 thy4;
benchmark_thy_2 thy5;
benchmark_thy_3 thy4;
benchmark_thy_3 thy5;

(* This is going to be slow *)
benchmark_thy_3 thy8;
benchmark_thy_4 thy8;

(* These will be slow because they miss so many proofs *)
SynthBenchmarks.bmarks_of_thy_ac (3, 12) 2 thy3;
SynthBenchmarks.bmarks_of_thy_ac (3, 12) 3 thy3;
SynthBenchmarks.bmarks_of_thy_ac (3, 12) 2 thy6;
SynthBenchmarks.bmarks_of_thy_ac (3, 12) 3 thy6;
*)
