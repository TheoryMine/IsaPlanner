theory run_naive
imports IsaP
begin


ML {*
use "src/synthesis/naive_synth.ML";
use_thy "src/benchmarks/synth_theories/N_plus_mult";
use_thy "src/benchmarks/synth_theories/List_fold";
use_thy "src/benchmarks/synth_theories/List_rev_map";
use_thy "src/benchmarks/synth_theories/List_rev_len";
use_thy "src/benchmarks/synth_theories/List_rev_qrev";
use_thy "src/benchmarks/synth_theories/Tree_size_height";

val nat_thy = theory "N_plus_mult";
val fold_thy = theory "List_fold";
val map_thy = theory "List_rev_map";
val len_thy = theory "List_rev_len";
val qrev_thy = theory "List_rev_qrev";
val tree_thy = theory "Tree_size_height";

*}
(* Max sizes for generation *)
ML {* 
PrintMode.setmp []
  (fn () => NaiveSynth.print_one_size 11 "N_plus_mult" nat_thy) ();
*}
ML {* 
PrintMode.setmp []
  (fn () => NaiveSynth.print_one_size 12 "List_fold" fold_thy) ();
*}
ML {* 
PrintMode.setmp []
  (fn () => NaiveSynth.print_one_size 11 "List_rev_map" map_thy) ();
*}
ML {* 
PrintMode.setmp []
  (fn () => NaiveSynth.print_one_size 11 "List_rev_len" len_thy) ();
*}
ML {* 
PrintMode.setmp []
  (fn () => NaiveSynth.print_one_size 10 "List_rev_qrev" qrev_thy) ();
*}
ML {* 
PrintMode.setmp []
  (fn () => NaiveSynth.print_one_size 11 "Tree_size_height" tree_thy) ();
*}
end