
(* -------------------------------------------------- *)
(* IsaCoSy demo                                       *)
(* -------------------------------------------------- *)

(* Load binary trees *)
use_thy "benchmarks/synth_theories/Tree_size_height";
val thy0 = theory "Tree_size_height";

structure Synthesis = ConstrSynthesis;

(* Create initial constant-informations,
   including looking for AC-properties *)
val (cs, thy) = Constraints.mk_const_infos_ac thy0;

(* Alt. without AC pre-processing *)
(* val cs = Constraints.mk_const_infos_no_ac thy0 *)

(* Synthesise from size 3 up to size 8, with max 2 variables *)
Synthesis.synth_print_thrms (3, 8) 2 thy cs;
(* Synthesis.synth_w_stats (3, 8) 2 thy cs; *)

(* Getting some timings *)
Time.toString (!SynthPrfTools.counterex_time);
Time.toString (!SynthPrfTools.prf_time);
Time.toString (!Synthesis.synth_time);


use_thy "benchmarks/synth_theories/List_rev_map2";
val thy0 = theory "List_rev_map2";
val (cs, thy) = Constraints.mk_const_infos_ac thy0;
reset_timers();
Synthesis.synth_print_thrms (3, 9) 2 thy cs;

fun reset_timers() = 
    let val _ = Synthesis.synth_time := Time.zeroTime
        val _ = Synthesis.upd_constr_time := Time.zeroTime
        val _ = Synthesis.subsumpt_time := Time.zeroTime    
        val _ = SynthPrfTools.prf_time := Time.zeroTime
    in SynthPrfTools.counterex_time := Time.zeroTime end

(* -------------------------------------------------- *)
(* Case-split demo                                    *)
(* -------------------------------------------------- *)
use_thy "benchmarks/CaseAnalysis_L2"; 
val thy = theory "CaseAnalysis_L2";
val rippling = RippleLemCalc.induct_ripple_lemcalc;

val rst = PPInterface.ipp thy (rippling "a") ("a","(take n xs) @ (drop
n xs) = xs");

(* -------------------------------------------------- *)
(* Lemma Speculation demo  ?                          *)
(* -------------------------------------------------- *)
Trm.drop_var_args_flag := false;
use_thy "benchmarks/lemspec_theories/Ireland";
val thy = theory "Ireland";
val rippling = RippleLemSpec.induct_ripple_lemspec;
val rst = PPInterface.ipp thy (rippling "a") ("a", "rev(rev(x@y)) = rev(rev x) @ rev(rev y)");

(* Speculated lemma 5, middle-out step 1 *)



use_thy "benchmarks/lemspec_theories/Ineq";
val thy = theory "Ineq";
val rippling = RippleLemSpec.induct_ripple_lemspec;
val rst = PPInterface.ipp thy (rippling "a") ("a","x leq (y + x)");

(* Speculated lemma 2 *)

