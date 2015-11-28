theory IsaCoSy
imports 
  "~~/src/HOL/Library/Refute"
  "../build/HOL_IsaP"
begin 
(* {* Synthesis tools: IsaCoSy v2 *} *)

ML_file "../synthesis/synth_prf_tools.ML"
ML_file "../synthesis/filter_subsumed.ML"
ML_file "../synthesis/synth_output.ML"
ML_file "../synthesis/constraint_param_schemes.ML"
ML_file "../synthesis/constraint_params.ML" 
ML_file "../synthesis/thy_constraint_params.ML" 
ML_file "../synthesis/constraints.ML"
ML_file "../synthesis/order_terms.ML"
ML_file "../synthesis/constr_synth.ML"
ML_file "../synthesis/naive_synth.ML"
ML_file "../synthesis/synth_interface.ML"

end