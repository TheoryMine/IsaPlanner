structure Synthesis = ConstrSynthesis;

Trm.drop_var_args_flag := false;

use_thy "benchmarks/synth_theories/List_fold";
val thry = theory "List_fold";
val rst0 = RstPP.init thry;

(* Set up initital constant-information from theory *)
val (cs, thy) = Constraints.mk_const_infos_ac thy0;
(* Generate the one theorem you find before the big one about fold,
    get a new constant-info. *)
val ((cs,thy), _) = Synthesis.synth_w_stats (3,5) 3 thy cs;
(* Run again on size 14. This takes a while unless you do that filtering thing because it's lots of things to counter-example check *)
val ((cs,thy), _) = Synthesis.synth_w_stats (14,14) 3 thy cs; 



set show_types;

val t = RstPP.read_top_term rst "fold");

val (bc,rst) = 
    rst |> RstPP.new_conj 
        ("base case", 
         

val (sc,rst) = 
    rst |>  RstPP.new_conj 
        ("step case", 
         RstPP.read_top_term rst "(!! Y Z. (t @ (Y#Z) = (?G t Y Z) @ Z)) ==> ((h#t) @ (Y#Z) = (?G (h#t) Y Z) @ Z)");



(* Set up initital constant-information from theory *)
val (cs, thy) = Constraints.mk_const_infos_ac thy0;

(* Generate the one theorem you find before the big one about fold,
    get a new constant-info. *)
val ((cs,thy), _) = Synthesis.synth_w_stats (3,5) 3 thy cs;

(* Run again on size 14. This takes a while unless you do that filtering thing because it's lots of things to counter-example check *)
val ((cs,thy), _) = Synthesis.synth_w_stats (14,14) 3 thy cs; 
