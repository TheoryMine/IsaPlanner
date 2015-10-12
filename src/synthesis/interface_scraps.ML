(* ------------------------------------------------------------------------*)
(* Theory Data to hold an ordering function on terms *)
(* ------------------------------------------------------------------------*)

(* How about also putting the var_not_allowed function in here?      *)
(* Why are these usually always called T? *)
datatype synth_data = SynthThyData of 
         {
          prover : prover_f,
          cex_finder : cexfinder_f,
          result_processor : result_config_f
         };
val empty = ConstrThyData{term_ord = fn (t1,t2) => EQUAL};
fun get_term_ord (ConstrThyData rep) = (#term_ord rep); 
fun update_term_ord f (ConstrThyData rep) = 
    ConstrThyData{term_ord = f (#term_ord rep)};
val set_term_ord = update_term_ord o K;

fun pretty_constr_data ctxt (ConstrThyData rep) = 
    Pretty.chunks[
    Pretty.block [Pretty.str "Term order function: " (* How to pretty print an ML-function?*)]
    ];
val print_constr_data = Pretty.writeln oo pretty_constr_data;

structure ThyData = Theory_Data
   (
      type T = ConstrData
      val empty = empty
      val extend = I
      fun merge (t1, t2) = t1 (* Can't really merge functions, just take first. *)
    );
val of_thy = ThyData.get;
val of_ctxt = ThyData.get o ProofContext.theory_of;
