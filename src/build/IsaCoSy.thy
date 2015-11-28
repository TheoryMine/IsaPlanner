theory IsaCoSy
imports 
  "~~/src/HOL/Library/Refute"
  "../build/HOL_IsaP"
begin 
(* {* Synthesis tools *} *)

ML_file "../IsaCoSy/synth_output.ML"
ML_file "../IsaCoSy/synth_prf_tools.ML" (* Update this *)
ML_file "../IsaCoSy/synth_lib.ML"
ML_file "../IsaCoSy/constraint_param_schemes.ML"
ML_file "../IsaCoSy/constraint_params.ML"
ML_file "../IsaCoSy/synthNames.ML"
ML_file "../IsaCoSy/thyConstr.ML"
ML_file "../IsaCoSy/constInfo.ML"
ML_file "../IsaCoSy/theoryConstraints.ML"
ML_file "../IsaCoSy/synthConstr.ML"
ML_file "../IsaCoSy/sterm.ML"
ML_file "../IsaCoSy/term_synhesis.ML"
ML_file "../IsaCoSy/order_terms.ML"
ML_file "../IsaCoSy/synth_interface.ML"

end