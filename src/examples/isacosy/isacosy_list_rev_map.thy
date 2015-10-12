theory isacosy_list_rev_map
imports "src/benchmarks/synth_theories/List_rev_map2"
begin

ML {* 
val thy0 = theory "List_rev_map2";
val (cs, thy) = ConstInfo.mk_const_infos_ac thy0;
reset_timers();
Synthesis.synth_print_thrms (3, 9) 2 thy cs;
*}

end;

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

